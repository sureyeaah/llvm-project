//===-- TweakTests.cpp ------------------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "Annotations.h"
#include "SourceCode.h"
#include "TestTU.h"
#include "refactor/Tweak.h"
#include "clang/AST/Expr.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Tooling/Core/Replacement.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include "llvm/Testing/Support/Error.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include <cassert>

using llvm::Failed;
using llvm::Succeeded;

namespace clang {
namespace clangd {
namespace {

std::string markRange(llvm::StringRef Code, Range R) {
  size_t Begin = llvm::cantFail(positionToOffset(Code, R.start));
  size_t End = llvm::cantFail(positionToOffset(Code, R.end));
  assert(Begin <= End);
  if (Begin == End) // Mark a single point.
    return (Code.substr(0, Begin) + "^" + Code.substr(Begin)).str();
  // Mark a range.
  return (Code.substr(0, Begin) + "[[" + Code.substr(Begin, End - Begin) +
          "]]" + Code.substr(End))
      .str();
}

void checkAvailable(StringRef ID, llvm::StringRef Input, bool Available) {
  Annotations Code(Input);
  ASSERT_TRUE(0 < Code.points().size() || 0 < Code.ranges().size())
      << "no points of interest specified";
  TestTU TU;
  TU.Filename = "foo.cpp";
  TU.Code = Code.code();

  ParsedAST AST = TU.build();

  auto CheckOver = [&](Range Selection) {
    unsigned Begin = cantFail(positionToOffset(Code.code(), Selection.start));
    unsigned End = cantFail(positionToOffset(Code.code(), Selection.end));
    auto T = prepareTweak(ID, Tweak::Selection(AST, Begin, End));
    if (Available)
      EXPECT_THAT_EXPECTED(T, Succeeded())
          << "code is " << markRange(Code.code(), Selection);
    else
      EXPECT_THAT_EXPECTED(T, Failed())
          << "code is " << markRange(Code.code(), Selection);
  };
  for (auto P : Code.points())
    CheckOver(Range{P, P});
  for (auto R : Code.ranges())
    CheckOver(R);
}

/// Checks action is available at every point and range marked in \p Input.
void checkAvailable(StringRef ID, llvm::StringRef Input) {
  return checkAvailable(ID, Input, /*Available=*/true);
}

/// Same as checkAvailable, but checks the action is not available.
void checkNotAvailable(StringRef ID, llvm::StringRef Input) {
  return checkAvailable(ID, Input, /*Available=*/false);
}
llvm::Expected<std::string> apply(StringRef ID, llvm::StringRef Input) {
  Annotations Code(Input);
  Range SelectionRng;
  if (Code.points().size() != 0) {
    assert(Code.ranges().size() == 0 &&
           "both a cursor point and a selection range were specified");
    SelectionRng = Range{Code.point(), Code.point()};
  } else {
    SelectionRng = Code.range();
  }
  TestTU TU;
  TU.Filename = "foo.cpp";
  TU.Code = Code.code();

  ParsedAST AST = TU.build();
  unsigned Begin = cantFail(positionToOffset(Code.code(), SelectionRng.start));
  unsigned End = cantFail(positionToOffset(Code.code(), SelectionRng.end));
  Tweak::Selection S(AST, Begin, End);

  auto T = prepareTweak(ID, S);
  if (!T)
    return T.takeError();
  auto Replacements = (*T)->apply(S);
  if (!Replacements)
    return Replacements.takeError();
  return applyAllReplacements(Code.code(), *Replacements);
}

void checkTransform(llvm::StringRef ID, llvm::StringRef Input,
                    std::string Output) {
  auto Result = apply(ID, Input);
  ASSERT_TRUE(bool(Result)) << llvm::toString(Result.takeError()) << Input;
  EXPECT_EQ(Output, std::string(*Result)) << Input;
}

TEST(TweakTest, SwapIfBranches) {
  llvm::StringLiteral ID = "SwapIfBranches";

  checkAvailable(ID, R"cpp(
    void test() {
      ^i^f^^(^t^r^u^e^) { return 100; } ^e^l^s^e^ { continue; }
    }
  )cpp");

  checkNotAvailable(ID, R"cpp(
    void test() {
      if (true) {^return ^100;^ } else { ^continue^;^ }
    }
  )cpp");

  llvm::StringLiteral Input = R"cpp(
    void test() {
      ^if (true) { return 100; } else { continue; }
    }
  )cpp";
  llvm::StringLiteral Output = R"cpp(
    void test() {
      if (true) { continue; } else { return 100; }
    }
  )cpp";
  checkTransform(ID, Input, Output);

  Input = R"cpp(
    void test() {
      ^if () { return 100; } else { continue; }
    }
  )cpp";
  Output = R"cpp(
    void test() {
      if () { continue; } else { return 100; }
    }
  )cpp";
  checkTransform(ID, Input, Output);

  // Available in subexpressions of the condition.
  checkAvailable(ID, R"cpp(
    void test() {
      if(2 + [[2]] + 2) { return 2 + 2 + 2; } else { continue; }
    }
  )cpp");
  // But not as part of the branches.
  checkNotAvailable(ID, R"cpp(
    void test() {
      if(2 + 2 + 2) { return 2 + [[2]] + 2; } else { continue; }
    }
  )cpp");
  // Range covers the "else" token, so available.
  checkAvailable(ID, R"cpp(
    void test() {
      if(2 + 2 + 2) { return 2 + [[2 + 2; } else { continue;]] }
    }
  )cpp");
  // Not available in compound statements in condition.
  checkNotAvailable(ID, R"cpp(
    void test() {
      if([]{return [[true]];}()) { return 2 + 2 + 2; } else { continue; }
    }
  )cpp");
  // Not available if both sides aren't braced.
  checkNotAvailable(ID, R"cpp(
    void test() {
      ^if (1) return; else { return; }
    }
  )cpp");
  // Only one if statement is supported!
  checkNotAvailable(ID, R"cpp(
    [[if(1){}else{}if(2){}else{}]]
  )cpp");
}

TEST(TweakTest, RawStringLiteral) {
  llvm::StringLiteral ID = "RawStringLiteral";

  checkAvailable(ID, R"cpp(
    const char *A = ^"^f^o^o^\^n^";
    const char *B = R"(multi )" ^"token " "str\ning";
  )cpp");

  checkNotAvailable(ID, R"cpp(
    const char *A = ^"f^o^o^o^"; // no chars need escaping
    const char *B = R"(multi )" ^"token " u8"str\ning"; // not all ascii
    const char *C = ^R^"^(^multi )" "token " "str\ning"; // chunk is raw
    const char *D = ^"token\n" __FILE__; // chunk is macro expansion
    const char *E = ^"a\r\n"; // contains forbidden escape character
  )cpp");

  const char *Input = R"cpp(
    const char *X = R"(multi
token)" "\nst^ring\n" "literal";
    }
  )cpp";
  const char *Output = R"cpp(
    const char *X = R"(multi
token
string
literal)";
    }
  )cpp";
  checkTransform(ID, Input, Output);
}

TEST(TweakTest, ExtractVariable) {
  llvm::StringLiteral ID = "ExtractVariable";
  checkAvailable(ID, R"cpp(
    int xyz() {
      return 1;
    }
    void f() {
      int a = 5 + [[4 * [[^xyz()]]]];
      // FIXME: add test case for multiple variable initialization once
      // SelectionTree commonAncestor bug is fixed
      switch(a) {
        case 1: {
          a = ^1;
          break;
        }
        default: {
          a = ^3; 
        }
      }
      if(^1) {}
      if(a < ^3)
        if(a == 4)
          a = 5;
        else
          a = 6;
      else if (a < 4) {
        a = ^4;
      }
      else {
        a = ^5;
      }
      // for loop testing
      for(a = ^1; a > ^3+^4; a++) 
        a = 2;
      // while testing
      while(a < ^1) {
        ^a++;
      }
      // do while testing
      do
        a = 1;
      while(a < ^3);
    }
  )cpp");
  checkNotAvailable(ID, R"cpp(
    void g() {
      class T {
        void f(int a = ^1) {}
      };
    }
    void f(int b = ^1) {
      int a = 5 + 4 * 3;
      // switch testing
      switch(a) {
        case 1: 
          a = ^1;
          break;
        default:
          a = ^3; 
      }
      // if testing
      if(a < 3)
        if(a == ^4)
          a = ^5;
        else
          a = ^6;
      else if (a < ^4) {
        a = 4;
      }
      else {
        a = 5;
      }
      // for loop testing
      for(int a = 1, b = 2, c = 3; ^a > ^b ^+ ^c; ^a++) 
        a = ^2;
      // while testing
      while(a < 1) {
        a++;
      }
      // do while testing
      do
        a = ^1;
      while(a < 3);
      // testing in cases where braces are required
      if (true)
        do
          a = 1;
        while(a < ^1);
      // check whether extraction breaks scope
      int a = 1, b = ^a + 1;
      // lambda testing
      auto lam = [&^a](int p = ^1) {};
    }
  )cpp");
  // vector of pairs of input and output strings
  const std::vector<std::pair<llvm::StringLiteral, llvm::StringLiteral>>
      InputOutputs = {
          // extraction from variable declaration/assignment
          {R"cpp(void varDecl() {
                   int a = 5 * (4 + (3 [[- 1)]]);
                 })cpp",
           R"cpp(void varDecl() {
                   auto dummy = (3 - 1); int a = 5 * (4 + dummy);
                 })cpp"},
          // extraction from for loop init/cond/incr
          {R"cpp(void forLoop() {
                   for(int a = 1; a < ^3; a++) {
                     a = 5 + 4 * 3;
                   }
                 })cpp",
           R"cpp(void forLoop() {
                   auto dummy = 3; for(int a = 1; a < dummy; a++) {
                     a = 5 + 4 * 3;
                   }
                 })cpp"},
          // extraction inside for loop body
          {R"cpp(void forBody() {
                   for(int a = 1; a < 3; a++) {
                     a = 5 + [[4 * 3]];
                   }
                 })cpp",
           R"cpp(void forBody() {
                   for(int a = 1; a < 3; a++) {
                     auto dummy = 4 * 3; a = 5 + dummy;
                   }
                 })cpp"},
          // extraction inside while loop condition
          {R"cpp(void whileLoop(int a) {
                   while(a < 5 + [[4 * 3]]) 
                     a += 1;
                 })cpp",
           R"cpp(void whileLoop(int a) {
                   auto dummy = 4 * 3; while(a < 5 + dummy) 
                     a += 1;
                 })cpp"},
          // extraction inside while body condition
          {R"cpp(void whileBody(int a) {
                   while(a < 1) {
                     a += ^7 * 3;
                   }
                 })cpp",
           R"cpp(void whileBody(int a) {
                   while(a < 1) {
                     auto dummy = 7; a += dummy * 3;
                   }
                 })cpp"},
          // extraction inside do-while loop condition
          {R"cpp(void doWhileLoop(int a) {
                   do
                     a += 3;
                   while(a < ^1);
                 })cpp",
           R"cpp(void doWhileLoop(int a) {
                   auto dummy = 1; do
                     a += 3;
                   while(a < dummy);
                 })cpp"},
          // extraction inside do-while body
          {R"cpp(void doWhileBody(int a) {
                   do {
                     a += ^3;
                   }
                   while(a < 1);
                 })cpp",
           R"cpp(void doWhileBody(int a) {
                   do {
                     auto dummy = 3; a += dummy;
                   }
                   while(a < 1);
                 })cpp"},
          // extraction inside switch condition
          {R"cpp(void switchLoop(int a) {
                   switch(a = 1 + [[3 * 5]]) {
                     default:
                       break;
                   }
                 })cpp",
           R"cpp(void switchLoop(int a) {
                   auto dummy = 3 * 5; switch(a = 1 + dummy) {
                     default:
                       break;
                   }
                 })cpp"},
          // extraction inside case body
          {R"cpp(void caseBody(int a) {
                   switch(1) {
                     case 1: {
                       a = ^1;
                       break;
                     }
                     default:
                       break;
                   }
                 })cpp",
           R"cpp(void caseBody(int a) {
                   switch(1) {
                     case 1: {
                       auto dummy = 1; a = dummy;
                       break;
                     }
                     default:
                       break;
                   }
                 })cpp"},
      };
  for (const auto &IO : InputOutputs) {
    checkTransform(ID, IO.first, IO.second);
  }
}

} // namespace
} // namespace clangd
} // namespace clang
