import EvmYul.Yul.YulNotation

/-!
# Total parser for the optimized-Yul subset used by `ForsVerifier`

This module parses the raw `solc --ir-optimized` object syntax into a small
source AST, selects the unique deployed object, and imports its runtime into
EVMYulLean's `YulContract`.

The implementation is deliberately computational:

* no `partial`, `unsafe`, FFI, or metaprogramming;
* comments and the complete object wrapper are parsed, not pre-stripped;
* unsupported syntax and ambiguous runtime objects are rejected;
* identifier normalization (`$` to `_`) rejects collisions.

The parser is FORS-first, but the lexer, source AST, and runtime importer are
kept independent of the FORS model.
-/

namespace NiceTry.Fors.Bridge.YulParser

open EvmYul EvmYul.Yul EvmYul.Yul.Ast

inductive Token where
  | ident (value : String)
  | number (value : Nat)
  | string (value : String)
  | hexString (value : String)
  | lbrace
  | rbrace
  | lparen
  | rparen
  | comma
  | assign
  | arrow
  deriving Repr, BEq, DecidableEq

@[reducible] private def isAsciiLower (c : Char) : Bool :=
  'a' ≤ c && c ≤ 'z'

@[reducible] private def isAsciiUpper (c : Char) : Bool :=
  'A' ≤ c && c ≤ 'Z'

@[reducible] private def isAsciiDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

@[reducible] private def isHexDigit (c : Char) : Bool :=
  isAsciiDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

@[reducible] private def isIdentStart (c : Char) : Bool :=
  isAsciiLower c || isAsciiUpper c || c = '_' || c = '$'

@[reducible] private def isIdentRest (c : Char) : Bool :=
  isIdentStart c || isAsciiDigit c || c = '.'

@[reducible] private def takeWhileChars
    (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
      if p c then
        let (taken, rest) := takeWhileChars p cs
        (c :: taken, rest)
      else
        ([], c :: cs)

@[reducible] private def skipLineComment : List Char → List Char
  | [] => []
  | '\n' :: cs => cs
  | _ :: cs => skipLineComment cs

@[reducible] private def skipBlockComment :
    List Char → Except String (List Char)
  | [] => .error "unterminated block comment"
  | '*' :: '/' :: cs => .ok cs
  | _ :: cs => skipBlockComment cs

@[reducible] private def readQuotedChars :
    List Char → List Char → Except String (String × List Char)
  | [], _ => .error "unterminated string literal"
  | '"' :: cs, acc => .ok (String.mk acc.reverse, cs)
  | '\\' :: '"' :: cs, acc => readQuotedChars cs ('"' :: acc)
  | '\\' :: '\\' :: cs, acc => readQuotedChars cs ('\\' :: acc)
  | '\\' :: 'n' :: cs, acc => readQuotedChars cs ('\n' :: acc)
  | '\\' :: 'r' :: cs, acc => readQuotedChars cs ('\r' :: acc)
  | '\\' :: 't' :: cs, acc => readQuotedChars cs ('\t' :: acc)
  | '\\' :: c :: cs, acc => readQuotedChars cs (c :: acc)
  | c :: cs, acc => readQuotedChars cs (c :: acc)

@[reducible] private def hexDigitValue (c : Char) : Nat :=
  if isAsciiDigit c then
    c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then
    10 + c.toNat - 'a'.toNat
  else
    10 + c.toNat - 'A'.toNat

@[reducible] private def parseNumberToken
    (chars : List Char) : Except String Nat :=
  match chars with
  | '0' :: 'x' :: [] => .error "hexadecimal literal has no digits"
  | '0' :: 'x' :: digits =>
      .ok (digits.foldl (fun value digit => value * 16 + hexDigitValue digit) 0)
  | [] => .error "decimal literal has no digits"
  | digits =>
      .ok
        (digits.foldl
          (fun value digit => value * 10 + digit.toNat - '0'.toNat) 0)

private structure LexState where
  chars : List Char
  tokensRev : List Token

@[reducible] private def pushToken
    (state : LexState) (token : Token) (rest : List Char) :
    LexState :=
  { chars := rest, tokensRev := token :: state.tokensRev }

@[reducible] private def lexOne (state : LexState) : Except String LexState :=
  match state.chars with
  | [] => .ok state
  | c :: cs =>
      if c.isWhitespace then
        .ok { state with chars := cs }
      else
        match c, cs with
        | '/', '/' :: rest =>
            .ok { state with chars := skipLineComment rest }
        | '/', '*' :: rest =>
            return { state with chars := ← skipBlockComment rest }
        | '{', rest => .ok (pushToken state .lbrace rest)
        | '}', rest => .ok (pushToken state .rbrace rest)
        | '(', rest => .ok (pushToken state .lparen rest)
        | ')', rest => .ok (pushToken state .rparen rest)
        | ',', rest => .ok (pushToken state .comma rest)
        | ':', '=' :: rest => .ok (pushToken state .assign rest)
        | '-', '>' :: rest => .ok (pushToken state .arrow rest)
        | '"', rest => do
            let (value, tail) ← readQuotedChars rest []
            .ok (pushToken state (.string value) tail)
        | _, _ => do
            if isAsciiDigit c then
              let (suffix, rest) :=
                if c = '0' then
                  match cs with
                  | 'x' :: tail =>
                      let (digits, rest) := takeWhileChars isHexDigit tail
                      ('x' :: digits, rest)
                  | _ => takeWhileChars isAsciiDigit cs
                else
                  takeWhileChars isAsciiDigit cs
              let value ← parseNumberToken (c :: suffix)
              .ok (pushToken state (.number value) rest)
            else if isIdentStart c then
              let (suffix, rest) := takeWhileChars isIdentRest cs
              let name := String.mk (c :: suffix)
              if name = "hex" then
                match rest with
                | '"' :: tail => do
                    let (value, remaining) ← readQuotedChars tail []
                    if value.data.all isHexDigit && value.length % 2 = 0 then
                      .ok (pushToken state (.hexString value) remaining)
                    else
                      .error "invalid hex string literal"
                | _ => .ok (pushToken state (.ident name) rest)
              else
                .ok (pushToken state (.ident name) rest)
            else
              .error s!"unexpected character '{c}'"

@[reducible] private def lexSteps : Nat → LexState → Except String LexState
  | 0, state => .ok state
  | steps + 1, state =>
      match state.chars with
      | [] => .ok state
      | _ => do
          lexSteps steps (← lexOne state)

@[reducible] private def lexChunks : Nat → LexState → Except String (List Token)
  | 0, _ => .error "lexer exhausted fuel"
  | fuel + 1, state => do
      let next ← lexSteps 64 state
      match next.chars with
      | [] => .ok next.tokensRev.reverse
      | _ => lexChunks fuel next

def lexWithFuel (fuel : Nat) (source : String) : Except String (List Token) :=
  lexChunks fuel { chars := source.data, tokensRev := [] }

/-- Lex up to 262,144 tokenization steps. Inputs beyond that FORS-scoped bound
    are rejected rather than relying on partial recursion. -/
def lex (source : String) : Except String (List Token) :=
  lexWithFuel 4096 source

inductive SourceExpr where
  | literal (value : Nat)
  | identifier (name : String)
  | string (value : String)
  | call (name : String) (args : List SourceExpr)
  deriving Repr, BEq

inductive SourceStmt where
  | block (body : List SourceStmt)
  | let_ (names : List String) (value : Option SourceExpr)
  | assign (names : List String) (value : SourceExpr)
  | expr (value : SourceExpr)
  | if_ (condition : SourceExpr) (body : List SourceStmt)
  | switch
      (value : SourceExpr)
      (cases : List (Nat × List SourceStmt))
      (defaultBody : Option (List SourceStmt))
  | for_
      (init : List SourceStmt)
      (condition : SourceExpr)
      (post : List SourceStmt)
      (body : List SourceStmt)
  | break_
  | continue_
  | leave
  | function_
      (name : String)
      (params : List String)
      (returns : List String)
      (body : List SourceStmt)
  deriving Repr, BEq

structure SourceData where
  name : String
  bytes : String
  deriving Repr, BEq

inductive SourceObject where
  | mk
      (name : String)
      (code : List (List SourceStmt))
      (objects : List SourceObject)
      (data : List SourceData)
  deriving Repr, BEq

namespace SourceObject

def name : SourceObject → String
  | .mk name _ _ _ => name

def code : SourceObject → List (List SourceStmt)
  | .mk _ code _ _ => code

def objects : SourceObject → List SourceObject
  | .mk _ _ objects _ => objects

def data : SourceObject → List SourceData
  | .mk _ _ _ data => data

end SourceObject

private def expectToken (expected : Token) :
    List Token → Except String (Unit × List Token)
  | actual :: rest =>
      if actual == expected then
        .ok ((), rest)
      else
        .error s!"expected {repr expected}, found {repr actual}"
  | [] => .error s!"expected {repr expected}, found end of input"

private def takeIdent : List Token → Except String (String × List Token)
  | .ident value :: rest => .ok (value, rest)
  | actual :: _ => .error s!"expected identifier, found {repr actual}"
  | [] => .error "expected identifier, found end of input"

private def takeString : List Token → Except String (String × List Token)
  | .string value :: rest => .ok (value, rest)
  | actual :: _ => .error s!"expected string, found {repr actual}"
  | [] => .error "expected string, found end of input"

private def parseIdentifierTail
    (fuel : Nat) (first : String) (tokens : List Token) :
    Except String (List String × List Token) :=
  match fuel with
  | 0 => .error "identifier-list parser exhausted fuel"
  | fuel + 1 =>
      match tokens with
      | .comma :: rest => do
          let (next, tail) ← takeIdent rest
          let (names, remaining) ← parseIdentifierTail fuel next tail
          .ok (first :: names, remaining)
      | _ => .ok ([first], tokens)

private def scanAssignmentNames
    (fuel : Nat) (tokens : List Token) :
    Option (List String × List Token) :=
  match fuel, tokens with
  | 0, _ => none
  | _ + 1, .ident first :: rest =>
      let rec scan : Nat → List String → List Token →
          Option (List String × List Token)
        | 0, _, _ => none
        | _ + 1, names, .assign :: tail => some (names.reverse, tail)
        | n + 1, names, .comma :: .ident next :: tail =>
            scan n (next :: names) tail
        | _, _, _ => none
      scan fuel [first] rest
  | _, _ => none

mutual
  private def parseExpr :
      Nat → List Token → Except String (SourceExpr × List Token)
    | 0, _ => .error "expression parser exhausted fuel"
    | _ + 1, [] => .error "expected expression, found end of input"
    | _ + 1, .number value :: rest => .ok (.literal value, rest)
    | _ + 1, .string value :: rest => .ok (.string value, rest)
    | fuel + 1, .ident name :: .lparen :: rest => do
        let (args, tail) ← parseExprArgs fuel rest
        .ok (.call name args, tail)
    | _ + 1, .ident name :: rest => .ok (.identifier name, rest)
    | _ + 1, actual :: _ =>
        .error s!"expected expression, found {repr actual}"

  private def parseExprArgs :
      Nat → List Token → Except String (List SourceExpr × List Token)
    | 0, _ => .error "argument parser exhausted fuel"
    | _ + 1, .rparen :: rest => .ok ([], rest)
    | fuel + 1, tokens => do
        let (arg, tail) ← parseExpr fuel tokens
        match tail with
        | .rparen :: rest => .ok ([arg], rest)
        | .comma :: rest =>
            let (args, remaining) ← parseExprArgs fuel rest
            .ok (arg :: args, remaining)
        | actual :: _ =>
            .error s!"expected ',' or ')', found {repr actual}"
        | [] => .error "expected ',' or ')', found end of input"

  private def parseBlock :
      Nat → List Token → Except String (List SourceStmt × List Token)
    | 0, _ => .error "block parser exhausted fuel"
    | fuel + 1, tokens => do
        let (_, rest) ← expectToken .lbrace tokens
        parseStmtList fuel rest

  private def parseStmtList :
      Nat → List Token → Except String (List SourceStmt × List Token)
    | 0, _ => .error "statement-list parser exhausted fuel"
    | _ + 1, [] => .error "unterminated block"
    | _ + 1, .rbrace :: rest => .ok ([], rest)
    | fuel + 1, tokens => do
        let (stmt, tail) ← parseStmt fuel tokens
        let (stmts, remaining) ← parseStmtList fuel tail
        .ok (stmt :: stmts, remaining)

  private def parseStmt :
      Nat → List Token → Except String (SourceStmt × List Token)
    | 0, _ => .error "statement parser exhausted fuel"
    | fuel + 1, .lbrace :: rest => do
        let (body, tail) ← parseStmtList fuel rest
        .ok (.block body, tail)
    | fuel + 1, .ident "let" :: rest => do
        let (first, tail) ← takeIdent rest
        let (names, remaining) ← parseIdentifierTail fuel first tail
        match remaining with
        | .assign :: afterAssign =>
            let (value, tail) ← parseExpr fuel afterAssign
            .ok (.let_ names (some value), tail)
        | _ => .ok (.let_ names none, remaining)
    | fuel + 1, .ident "if" :: rest => do
        let (condition, tail) ← parseExpr fuel rest
        let (body, remaining) ← parseBlock fuel tail
        .ok (.if_ condition body, remaining)
    | fuel + 1, .ident "switch" :: rest => do
        let (value, tail) ← parseExpr fuel rest
        let (cases, defaultBody, remaining) ← parseSwitchCases fuel tail
        if cases.isEmpty && defaultBody.isNone then
          .error "switch must contain at least one case or default"
        else
          .ok (.switch value cases defaultBody, remaining)
    | fuel + 1, .ident "for" :: rest => do
        let (init, afterInit) ← parseBlock fuel rest
        let (condition, afterCondition) ← parseExpr fuel afterInit
        let (post, afterPost) ← parseBlock fuel afterCondition
        let (body, tail) ← parseBlock fuel afterPost
        .ok (.for_ init condition post body, tail)
    | _ + 1, .ident "break" :: rest => .ok (.break_, rest)
    | _ + 1, .ident "continue" :: rest => .ok (.continue_, rest)
    | _ + 1, .ident "leave" :: rest => .ok (.leave, rest)
    | fuel + 1, .ident "function" :: rest => do
        let (name, afterName) ← takeIdent rest
        let (_, afterLParen) ← expectToken .lparen afterName
        let (params, afterParams) ← parseDelimitedIdentifiers fuel afterLParen
        let (returns, afterReturns) ←
          match afterParams with
          | .arrow :: tail => parseReturnIdentifiers fuel tail
          | _ => .ok ([], afterParams)
        let (body, tail) ← parseBlock fuel afterReturns
        .ok (.function_ name params returns body, tail)
    | fuel + 1, tokens =>
        match scanAssignmentNames fuel tokens with
        | some (names, afterAssign) => do
            let (value, tail) ← parseExpr fuel afterAssign
            .ok (.assign names value, tail)
        | none => do
            let (value, tail) ← parseExpr fuel tokens
            .ok (.expr value, tail)

  private def parseSwitchCases :
      Nat → List Token →
        Except String
          (List (Nat × List SourceStmt) × Option (List SourceStmt) × List Token)
    | 0, _ => .error "switch parser exhausted fuel"
    | fuel + 1, .ident "case" :: .number value :: rest => do
        let (body, tail) ← parseBlock fuel rest
        let (cases, defaultBody, remaining) ← parseSwitchCases fuel tail
        .ok ((value, body) :: cases, defaultBody, remaining)
    | _ + 1, .ident "case" :: actual :: _ =>
        .error s!"switch case must use a numeric literal, found {repr actual}"
    | fuel + 1, .ident "default" :: rest => do
        let (body, tail) ← parseBlock fuel rest
        match tail with
        | .ident "case" :: _ =>
            .error "switch cases cannot follow default"
        | .ident "default" :: _ =>
            .error "switch cannot contain multiple defaults"
        | _ => .ok ([], some body, tail)
    | _ + 1, tokens => .ok ([], none, tokens)

  private def parseDelimitedIdentifiers :
      Nat → List Token → Except String (List String × List Token)
    | 0, _ => .error "parameter parser exhausted fuel"
    | _ + 1, .rparen :: rest => .ok ([], rest)
    | fuel + 1, tokens => do
        let (first, tail) ← takeIdent tokens
        let (names, remaining) ← parseIdentifierTail fuel first tail
        let (_, rest) ← expectToken .rparen remaining
        .ok (names, rest)

  private def parseReturnIdentifiers :
      Nat → List Token → Except String (List String × List Token)
    | 0, _ => .error "return-list parser exhausted fuel"
    | fuel + 1, tokens => do
        let (first, tail) ← takeIdent tokens
        parseIdentifierTail fuel first tail

  private def parseObject :
      Nat → List Token → Except String (SourceObject × List Token)
    | 0, _ => .error "object parser exhausted fuel"
    | fuel + 1, .ident "object" :: rest => do
        let (name, afterName) ← takeString rest
        let (_, afterBrace) ← expectToken .lbrace afterName
        let (code, objects, data, tail) ← parseObjectItems fuel afterBrace
        .ok (.mk name code objects data, tail)
    | _ + 1, actual :: _ =>
        .error s!"expected object, found {repr actual}"
    | _ + 1, [] => .error "expected object, found end of input"

  private def parseObjectItems :
      Nat → List Token →
        Except String
          (List (List SourceStmt) × List SourceObject × List SourceData × List Token)
    | 0, _ => .error "object-item parser exhausted fuel"
    | _ + 1, [] => .error "unterminated object"
    | _ + 1, .rbrace :: rest => .ok ([], [], [], rest)
    | fuel + 1, .ident "code" :: rest => do
        let (body, tail) ← parseBlock fuel rest
        let (codes, objects, data, remaining) ← parseObjectItems fuel tail
        .ok (body :: codes, objects, data, remaining)
    | fuel + 1, .ident "object" :: rest => do
        let (object, tail) ← parseObject fuel (.ident "object" :: rest)
        let (codes, objects, data, remaining) ← parseObjectItems fuel tail
        .ok (codes, object :: objects, data, remaining)
    | fuel + 1, .ident "data" :: rest => do
        let (name, afterName) ← takeString rest
        match afterName with
        | .hexString bytes :: tail =>
            let (codes, objects, data, remaining) ← parseObjectItems fuel tail
            .ok (codes, objects, { name, bytes } :: data, remaining)
        | actual :: _ =>
            .error s!"expected hex string after data label, found {repr actual}"
        | [] => .error "expected hex string after data label"
    | _ + 1, actual :: _ =>
        .error s!"unsupported object item {repr actual}"
end

def parseSourceTokens (tokens : List Token) : Except String SourceObject := do
  let (object, rest) ← parseObject 128 tokens
  match rest with
  | [] => .ok object
  | actual :: _ => .error s!"unexpected trailing token {repr actual}"

def parseSourceObject (source : String) : Except String SourceObject := do
  parseSourceTokens (← lex source)

private def containsDollar : List Char → Bool
  | [] => false
  | c :: cs => c == '$' || containsDollar cs

def canonicalIdentifier (name : String) : String :=
  if containsDollar name.data then
    String.mk <| name.data.map fun c => if c = '$' then '_' else c
  else
    name

@[reducible] private def identifiersOfExpr : SourceExpr → List String
  | .literal _ | .string _ => []
  | .identifier name => [name]
  | .call name args => name :: args.flatMap identifiersOfExpr

@[reducible] def identifiersOfStmtFuel : Nat → SourceStmt → List String
  | 0, _ => []
  | fuel + 1, .block body =>
      body.flatMap (identifiersOfStmtFuel fuel)
  | _ + 1, .let_ names value =>
      names ++ value.toList.flatMap identifiersOfExpr
  | _ + 1, .assign names value => names ++ identifiersOfExpr value
  | _ + 1, .expr value => identifiersOfExpr value
  | fuel + 1, .if_ condition body =>
      identifiersOfExpr condition ++
        body.flatMap (identifiersOfStmtFuel fuel)
  | fuel + 1, .switch value cases defaultBody =>
      identifiersOfExpr value ++
        cases.flatMap
          (fun entry => entry.2.flatMap (identifiersOfStmtFuel fuel)) ++
        defaultBody.toList.flatMap
          (fun body => body.flatMap (identifiersOfStmtFuel fuel))
  | fuel + 1, .for_ init condition post body =>
      init.flatMap (identifiersOfStmtFuel fuel) ++
        identifiersOfExpr condition ++
        post.flatMap (identifiersOfStmtFuel fuel) ++
        body.flatMap (identifiersOfStmtFuel fuel)
  | _ + 1, .break_ | _ + 1, .continue_ | _ + 1, .leave => []
  | fuel + 1, .function_ name params returns body =>
      name :: params ++ returns ++ body.flatMap (identifiersOfStmtFuel fuel)

def identifiersOfStmts (stmts : List SourceStmt) : List String :=
  stmts.flatMap (identifiersOfStmtFuel 128)

def validateCanonicalUniqueNames
    (uniqueNames : List String) : Except String Unit := do
  let dollarNames := uniqueNames.filter (containsDollar ·.data)
  for raw in dollarNames do
    let canonical := canonicalIdentifier raw
    match uniqueNames.find? (fun other =>
        other != raw && canonicalIdentifier other == canonical) with
    | none => pure ()
    | some prior =>
        throw s!"identifier normalization collision: '{prior}' and '{raw}' both become '{canonical}'"

def validateCanonicalNames (names : List String) : Except String Unit :=
  validateCanonicalUniqueNames names.eraseDups

def tokenIdentifiers (tokens : List Token) : List String :=
  tokens.filterMap fun
    | .ident name => some name
    | _ => none

def validateTokenIdentifierCollisions
    (tokens : List Token) : Except String Unit :=
  validateCanonicalNames (tokenIdentifiers tokens)

@[reducible] def primitiveOfChars : List Char → Option PrimOp
  | ['a', 'd', 'd'] => some .ADD
  | ['a', 'n', 'd'] => some .AND
  | ['c', 'a', 'l', 'l', 'd', 'a', 't', 'a', 'l', 'o', 'a', 'd'] =>
      some .CALLDATALOAD
  | ['c', 'a', 'l', 'l', 'd', 'a', 't', 'a', 's', 'i', 'z', 'e'] =>
      some .CALLDATASIZE
  | ['c', 'a', 'l', 'l', 'v', 'a', 'l', 'u', 'e'] => some .CALLVALUE
  | ['e', 'q'] => some .EQ
  | ['g', 't'] => some .GT
  | ['i', 's', 'z', 'e', 'r', 'o'] => some .ISZERO
  | ['k', 'e', 'c', 'c', 'a', 'k', '2', '5', '6'] => some .KECCAK256
  | ['l', 't'] => some .LT
  | ['m', 'l', 'o', 'a', 'd'] => some .MLOAD
  | ['m', 's', 't', 'o', 'r', 'e'] => some .MSTORE
  | ['n', 'o', 't'] => some .NOT
  | ['o', 'r'] => some .OR
  | ['r', 'e', 't', 'u', 'r', 'n'] => some .RETURN
  | ['r', 'e', 'v', 'e', 'r', 't'] => some .REVERT
  | ['s', 'h', 'l'] => some .SHL
  | ['s', 'h', 'r'] => some .SHR
  | ['s', 'l', 't'] => some .SLT
  | ['s', 'u', 'b'] => some .SUB
  | ['x', 'o', 'r'] => some .XOR
  | _ => none

@[reducible] def primitiveOfName (name : String) : Option PrimOp :=
  primitiveOfChars name.data

@[reducible] def sourceExprSupportedFuel : Nat → SourceExpr → Bool
  | 0, _ => false
  | _ + 1, .literal _ | _ + 1, .identifier _ => true
  | _ + 1, .string _ => false
  | fuel + 1, .call "memoryguard" [arg] =>
      sourceExprSupportedFuel fuel arg
  | _ + 1, .call "memoryguard" _ => false
  | fuel + 1, .call _ args =>
      args.all (sourceExprSupportedFuel fuel)

@[reducible] def lowerSourceExprFuel : Nat → SourceExpr → Expr
  | 0, _ => .Lit (UInt256.ofNat 0)
  | _ + 1, .literal value => .Lit (UInt256.ofNat value)
  | _ + 1, .identifier name => .Var (canonicalIdentifier name)
  | _ + 1, .string _ => .Lit (UInt256.ofNat 0)
  | fuel + 1, .call "memoryguard" [arg] => lowerSourceExprFuel fuel arg
  | _ + 1, .call "memoryguard" _ => .Lit (UInt256.ofNat 0)
  | fuel + 1, .call name args =>
      let functionName := canonicalIdentifier name
      let importedArgs := args.map (lowerSourceExprFuel fuel)
      match primitiveOfName functionName with
      | some primitive => .Call (.inl primitive) importedArgs
      | none => .Call (.inr functionName) importedArgs

@[reducible] def importSourceExprFuel
    (fuel : Nat) (expr : SourceExpr) : Except String Expr :=
  if sourceExprSupportedFuel fuel expr then
    .ok (lowerSourceExprFuel fuel expr)
  else
    .error "unsupported Yul expression"

@[reducible] def importSourceExpr (expr : SourceExpr) : Except String Expr :=
  importSourceExprFuel 16 expr

@[reducible] def sourceStmtSupportedFuel : Nat → SourceStmt → Bool
  | 0, _ => false
  | fuel + 1, .block body =>
      body.all (sourceStmtSupportedFuel fuel)
  | _ + 1, .let_ _ value =>
      value.all (sourceExprSupportedFuel 16)
  | _ + 1, .assign _ value | _ + 1, .expr value =>
      sourceExprSupportedFuel 16 value
  | fuel + 1, .if_ condition body =>
      sourceExprSupportedFuel 16 condition &&
        body.all (sourceStmtSupportedFuel fuel)
  | fuel + 1, .switch value cases defaultBody =>
      sourceExprSupportedFuel 16 value &&
        cases.all
          (fun entry => entry.2.all (sourceStmtSupportedFuel fuel)) &&
        defaultBody.all (fun body =>
          body.all (sourceStmtSupportedFuel fuel))
  | fuel + 1, .for_ init condition post body =>
      init.isEmpty &&
        sourceExprSupportedFuel 16 condition &&
        post.all (sourceStmtSupportedFuel fuel) &&
        body.all (sourceStmtSupportedFuel fuel)
  | _ + 1, .break_ | _ + 1, .continue_ | _ + 1, .leave => true
  | _ + 1, .function_ .. => false

@[reducible] def sourceStmtsSupportedFuel
    (fuel : Nat) (stmts : List SourceStmt) : Bool :=
  stmts.all (sourceStmtSupportedFuel fuel)

@[reducible] def lowerSourceStmtFuel : Nat → SourceStmt → Stmt
  | 0, _ => .Break
  | fuel + 1, .block body =>
      .Block (body.map (lowerSourceStmtFuel fuel))
  | _ + 1, .let_ names value =>
      .Let (names.map canonicalIdentifier)
        (value.map (lowerSourceExprFuel 16))
  | _ + 1, .assign names value =>
      .Let (names.map canonicalIdentifier)
        (some (lowerSourceExprFuel 16 value))
  | _ + 1, .expr value =>
      .ExprStmtCall (lowerSourceExprFuel 16 value)
  | fuel + 1, .if_ condition body =>
      .If (lowerSourceExprFuel 16 condition)
        (body.map (lowerSourceStmtFuel fuel))
  | fuel + 1, .switch value cases defaultBody =>
      .Switch (lowerSourceExprFuel 16 value)
        (cases.map fun (literal, body) =>
          (UInt256.ofNat literal, body.map (lowerSourceStmtFuel fuel)))
        (match defaultBody with
        | some body => body.map (lowerSourceStmtFuel fuel)
        | none => [.Break])
  | fuel + 1, .for_ _ condition post body =>
      .For (lowerSourceExprFuel 16 condition)
        (post.map (lowerSourceStmtFuel fuel))
        (body.map (lowerSourceStmtFuel fuel))
  | _ + 1, .break_ => .Break
  | _ + 1, .continue_ => .Continue
  | _ + 1, .leave => .Leave
  | _ + 1, .function_ .. => .Break

@[reducible] def lowerSourceStmtsFuel
    (fuel : Nat) (stmts : List SourceStmt) : List Stmt :=
  stmts.map (lowerSourceStmtFuel fuel)

@[reducible] def importSourceStmtFuel
    (fuel : Nat) (stmt : SourceStmt) : Except String Stmt :=
  if sourceStmtSupportedFuel fuel stmt then
    .ok (lowerSourceStmtFuel fuel stmt)
  else
    .error "unsupported Yul statement"

@[reducible] def importSourceStmtsFuel
    (fuel : Nat) (stmts : List SourceStmt) : Except String (List Stmt) :=
  if sourceStmtsSupportedFuel fuel stmts then
    .ok (lowerSourceStmtsFuel fuel stmts)
  else
    .error "unsupported Yul statement list"

@[reducible] def importSourceStmt (stmt : SourceStmt) : Except String Stmt :=
  importSourceStmtFuel 16 stmt

@[reducible] def importSourceStmts
    (stmts : List SourceStmt) : Except String (List Stmt) :=
  importSourceStmtsFuel 16 stmts

@[reducible] def importSourceFunction :
    SourceStmt → Except String (String × FunctionDefinition)
  | .function_ name params returns body =>
      if sourceStmtsSupportedFuel 16 body then
        .ok
          (canonicalIdentifier name,
            .Def (params.map canonicalIdentifier)
              (returns.map canonicalIdentifier)
              (lowerSourceStmtsFuel 16 body))
      else
        .error "unsupported Yul function body"
  | _ => .error "expected function definition"

private def sourceFunctionName? : SourceStmt → Option String
  | .function_ name _ _ _ => some name
  | _ => none

@[reducible] private def collectCallsExpr : SourceExpr → List String
  | .literal _ | .identifier _ | .string _ => []
  | .call name args => name :: args.flatMap collectCallsExpr

@[reducible] def collectCallsStmtFuel : Nat → SourceStmt → List String
  | 0, _ => []
  | fuel + 1, .block body =>
      body.flatMap (collectCallsStmtFuel fuel)
  | _ + 1, .let_ _ value => value.toList.flatMap collectCallsExpr
  | _ + 1, .assign _ value | _ + 1, .expr value => collectCallsExpr value
  | fuel + 1, .if_ condition body =>
      collectCallsExpr condition ++ body.flatMap (collectCallsStmtFuel fuel)
  | fuel + 1, .switch value cases defaultBody =>
      collectCallsExpr value ++
        cases.flatMap
          (fun entry => entry.2.flatMap (collectCallsStmtFuel fuel)) ++
        defaultBody.toList.flatMap
          (fun body => body.flatMap (collectCallsStmtFuel fuel))
  | fuel + 1, .for_ init condition post body =>
      init.flatMap (collectCallsStmtFuel fuel) ++
        collectCallsExpr condition ++
        post.flatMap (collectCallsStmtFuel fuel) ++
        body.flatMap (collectCallsStmtFuel fuel)
  | _ + 1, .break_ | _ + 1, .continue_ | _ + 1, .leave => []
  | fuel + 1, .function_ _ _ _ body =>
      body.flatMap (collectCallsStmtFuel fuel)

def collectCallsStmts (stmts : List SourceStmt) : List String :=
  stmts.flatMap (collectCallsStmtFuel 128)

def validateCall
    (functionNames : List String) (name : String) : Except String Unit :=
  let canonical := canonicalIdentifier name
  if canonical = "memoryguard" then
    .ok ()
  else
    match primitiveOfName canonical with
    | some _ => .ok ()
    | none =>
        let userFunction := canonical
        if functionNames.contains userFunction then
          .ok ()
        else
          .error s!"call to undefined Yul function '{userFunction}'"

def validateCalls
    (functionNames : List String) (stmts : List SourceStmt) :
    Except String Unit := do
  let _ ← (collectCallsStmts stmts).eraseDups.mapM
    (validateCall functionNames)
  .ok ()

private def startsWithChars : List Char → List Char → Bool
  | _, [] => true
  | [], _ :: _ => false
  | value :: values, prefixChar :: prefixChars =>
      value == prefixChar && startsWithChars values prefixChars

private def endsWithChars (value suffix : List Char) : Bool :=
  startsWithChars value.reverse suffix.reverse

private def selectDeployedObject (root : SourceObject) :
    Except String SourceObject :=
  match root.objects.filter
      (fun object => endsWithChars object.name.data "_deployed".data) with
  | [deployed] => .ok deployed
  | [] => .error "no nested deployed Yul object found"
  | _ => .error "multiple nested deployed Yul objects found"

def deployedCode (root : SourceObject) :
    Except String (List SourceStmt) := do
  let deployed ← selectDeployedObject root
  match deployed.code with
  | [code] => .ok code
  | [] => .error "deployed object has no code block"
  | _ => .error "deployed object has multiple code blocks"

structure SourceRuntimeParts where
  dispatcher : SourceStmt
  functions : List SourceStmt
  deriving Repr, BEq

def extractDeployedRuntimeParts
    (root : SourceObject) : Except String SourceRuntimeParts := do
  let code ← deployedCode root
  let functionStmts := code.filter (fun stmt => (sourceFunctionName? stmt).isSome)
  let dispatcherStmts := code.filter (fun stmt => (sourceFunctionName? stmt).isNone)
  let dispatcher ←
    match dispatcherStmts with
    | [dispatcher] => .ok dispatcher
    | [] => .error "deployed code has no dispatcher statement"
    | _ => .error "deployed code has multiple dispatcher statements"
  .ok { dispatcher, functions := functionStmts }

def sourceTopStmtSupported : SourceStmt → Bool
  | .function_ _ _ _ body => sourceStmtsSupportedFuel 16 body
  | stmt => sourceStmtSupportedFuel 16 stmt

def validateDeployedRuntime (root : SourceObject) : Except String Unit := do
  let code ← deployedCode root
  if code.all sourceTopStmtSupported then
    pure ()
  else
    .error "deployed code contains unsupported Yul syntax"
  let parts ← extractDeployedRuntimeParts root
  let functionNames :=
    parts.functions.filterMap (fun stmt =>
      (sourceFunctionName? stmt).map canonicalIdentifier)
  if functionNames.eraseDups.length = functionNames.length then
    .ok ()
  else
    .error "deployed code contains duplicate function definitions"

def importRuntimeDispatcher
    (parts : SourceRuntimeParts) : Except String Stmt :=
  importSourceStmt parts.dispatcher

def importRuntimeFunction
    (stmt : SourceStmt) : Except String (String × FunctionDefinition) :=
  importSourceFunction stmt

def assembleRuntime
    (dispatcher : Stmt) (functions : List (String × FunctionDefinition)) :
    YulContract :=
  let functionMap :=
    functions.foldl
      (fun acc entry => acc.insert entry.1 entry.2)
      (∅ : Finmap (fun (_ : YulFunctionName) ↦ FunctionDefinition))
  { dispatcher, functions := functionMap }

def importRuntimeParts
    (parts : SourceRuntimeParts) : Except String YulContract := do
  let dispatcher ← importRuntimeDispatcher parts
  let functions ← parts.functions.mapM importRuntimeFunction
  .ok (assembleRuntime dispatcher functions)

def importDeployedRuntimeUnchecked
    (root : SourceObject) : Except String YulContract := do
  importRuntimeParts (← extractDeployedRuntimeParts root)

def importDeployedRuntime (root : SourceObject) : Except String YulContract := do
  validateDeployedRuntime root
  importDeployedRuntimeUnchecked root

def parseDeployedRuntimeTokens
    (tokens : List Token) : Except String YulContract := do
  validateTokenIdentifierCollisions tokens
  importDeployedRuntime (← parseSourceTokens tokens)

def parseDeployedRuntime (source : String) : Except String YulContract := do
  parseDeployedRuntimeTokens (← lex source)

end NiceTry.Fors.Bridge.YulParser
