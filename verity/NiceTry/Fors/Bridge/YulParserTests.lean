import NiceTry.Fors.Bridge.YulParser

/-!
# Executable tests for the FORS optimized-Yul parser

These examples are kernel-checked computations. They intentionally avoid
`native_decide`, tactics that execute external code, and parser-specific axioms.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul.Ast

example :
    YulParser.lex
        "/* block */ $value := 17 // line\nhex\"00ff\" \"ok\" 0x2a" =
      .ok [.ident "$value", .assign, .number 17, .hexString "00ff",
        .string "ok", .number 42] := by
  rfl

example : YulParser.canonicalIdentifier "usr$tree" = "usr_tree" := by
  rfl

example :
    YulParser.importSourceExpr (.call "memoryguard" [.literal 128]) =
      .ok (.Lit (UInt256.ofNat 128)) := by
  rfl

example :
    YulParser.importSourceExpr (.call "add" [.literal 1, .literal 2]) =
      .ok (.Call (.inl .ADD)
        [.Lit (UInt256.ofNat 1), .Lit (UInt256.ofNat 2)]) := by
  rfl

def parserGrammarFixture : String :=
  "object \"C\" { code { { let x, y := f(1, 0x2) x, y := g() " ++
  "if x { leave } switch x case 0 { break } default { continue } " ++
  "for {} lt(x, 10) { x := add(x, 1) } { mstore(0, x) } } " ++
  "function f(a, b) -> r { { let z } r := add(a, b) } } " ++
  "object \"C_deployed\" { code { { return(0, 0) } } " ++
  "data \".metadata\" hex\"00\" } data \"outer\" hex\"aabb\" }"

example : (YulParser.parseSourceObject parserGrammarFixture).isOk = true := by
  rfl

def parserMinimalRuntime : String :=
  "object \"C\" { code {} object \"C_deployed\" { " ++
  "code { { mstore(0, memoryguard(0x80)) return(0, 0x20) } " ++
  "function f(a) -> r { r := a } } data \".metadata\" hex\"00\" } }"

example : (YulParser.parseDeployedRuntime parserMinimalRuntime).isOk = true := by
  rfl

example : (YulParser.lex "/* unterminated").isOk = false := by
  rfl

example : (YulParser.lex "0x").isOk = false := by
  rfl

example : (YulParser.lex "hex\"0\"").isOk = false := by
  rfl

example : (YulParser.lex "\"unterminated").isOk = false := by
  rfl

example : (YulParser.lex ";").isOk = false := by
  rfl

example :
    (YulParser.parseSourceObject "object \"C\" { code { { mstore(0, 1) } }").isOk =
      false := by
  rfl

example :
    (YulParser.parseSourceObject
      "object \"C\" { code { { let x := f(1, 2 } } }").isOk = false := by
  rfl

example :
    (YulParser.parseSourceObject
      "object \"C\" { code { function f( { } }").isOk = false := by
  rfl

example :
    (YulParser.parseSourceObject
      "object \"C\" { data \"x\" \"not-hex\" }").isOk = false := by
  rfl

def parserCollisionRuntime : String :=
  "object \"C\" { code {} object \"C_deployed\" { code { " ++
  "{ let usr$x := 0 let usr_x := 1 } } } }"

example :
    (YulParser.parseDeployedRuntime parserCollisionRuntime).isOk = false := by
  rfl

def parserDuplicateFunctionRuntime : String :=
  "object \"C\" { code {} object \"C_deployed\" { code { " ++
  "{ return(0, 0) } function f() { } function f() { } } } }"

example :
    (YulParser.parseDeployedRuntime parserDuplicateFunctionRuntime).isOk =
      false := by
  rfl

example :
    (YulParser.parseDeployedRuntime
      "object \"C\" { code { { return(0, 0) } } }").isOk = false := by
  rfl

def parserAmbiguousRuntime : String :=
  "object \"C\" { code {} " ++
  "object \"A_deployed\" { code { { return(0, 0) } } } " ++
  "object \"B_deployed\" { code { { return(0, 0) } } } }"

example :
    (YulParser.parseDeployedRuntime parserAmbiguousRuntime).isOk = false := by
  rfl

def parserUnsupportedStringRuntime : String :=
  "object \"C\" { code {} object \"C_deployed\" { " ++
  "code { { let x := \"unsupported\" } } } }"

example :
    (YulParser.parseDeployedRuntime parserUnsupportedStringRuntime).isOk =
      false := by
  rfl

def parserNonemptyForInitRuntime : String :=
  "object \"C\" { code {} object \"C_deployed\" { code { { " ++
  "for { let i := 0 } lt(i, 1) { i := add(i, 1) } { } } } } }"

example :
    (YulParser.parseDeployedRuntime parserNonemptyForInitRuntime).isOk =
      false := by
  rfl

def parserInvalidMemoryguardRuntime : String :=
  "object \"C\" { code {} object \"C_deployed\" { " ++
  "code { { mstore(0, memoryguard()) } } } }"

example :
    (YulParser.parseDeployedRuntime parserInvalidMemoryguardRuntime).isOk =
      false := by
  rfl

end NiceTry.Fors.Bridge
