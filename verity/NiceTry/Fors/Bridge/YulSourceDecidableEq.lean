import NiceTry.Fors.Bridge.YulParser

/-!
# Executable equality for optimized-Yul source syntax

The source AST is recursive, so this module supplies fuel-bounded equality for
the kernel-checked artifact bridge without changing the parser's public data
types. Matching constructors are compared structurally; the classical fallback
is reached only if the explicit depth budget is exhausted.
-/

namespace NiceTry.Fors.Bridge.YulSourceDecidableEq

open YulParser

noncomputable section

mutual
  private def exprDecEqFuel :
      Nat → (left right : SourceExpr) → Decidable (left = right)
    | 0, left, right => Classical.decEq _ left right
    | _ + 1, .literal value, .literal value' =>
        if h : value = value' then
          isTrue <| by cases h; rfl
        else
          isFalse fun equality => h (by cases equality; rfl)
    | _ + 1, .identifier name, .identifier name' =>
        if h : name = name' then
          isTrue <| by cases h; rfl
        else
          isFalse fun equality => h (by cases equality; rfl)
    | _ + 1, .string value, .string value' =>
        if h : value = value' then
          isTrue <| by cases h; rfl
        else
          isFalse fun equality => h (by cases equality; rfl)
    | fuel + 1, .call name args, .call name' args' =>
        letI : DecidableEq SourceExpr := fun left right =>
          exprDecEqFuel fuel left right
        if h : (name, args) = (name', args') then
          isTrue <| by cases h; rfl
        else
          isFalse fun equality => h (by cases equality; rfl)
    | _ + 1, left, right => Classical.decEq _ left right

  private def stmtDecEqFuel :
      Nat → (left right : SourceStmt) → Decidable (left = right)
    | 0, left, right => Classical.decEq _ left right
    | fuel + 1, .block body, .block body' =>
        letI : DecidableEq SourceStmt := fun left right =>
          stmtDecEqFuel fuel left right
        if h : body = body' then
          isTrue <| by cases h; rfl
        else
          isFalse fun equality => h (by cases equality; rfl)
    | fuel + 1, .let_ names value, .let_ names' value' =>
        letI : DecidableEq SourceExpr := fun left right =>
          exprDecEqFuel fuel left right
        if h : (names, value) = (names', value') then
          isTrue <| by cases h; rfl
        else
          isFalse fun equality => h (by cases equality; rfl)
    | fuel + 1, .assign names value, .assign names' value' =>
        letI : DecidableEq SourceExpr := fun left right =>
          exprDecEqFuel fuel left right
        if h : (names, value) = (names', value') then
          isTrue <| by cases h; rfl
        else
          isFalse fun equality => h (by cases equality; rfl)
    | fuel + 1, .expr value, .expr value' =>
        letI : DecidableEq SourceExpr := fun left right =>
          exprDecEqFuel fuel left right
        if h : value = value' then
          isTrue <| by cases h; rfl
        else
          isFalse fun equality => h (by cases equality; rfl)
    | fuel + 1, .if_ condition body, .if_ condition' body' =>
        letI : DecidableEq SourceExpr := fun left right =>
          exprDecEqFuel fuel left right
        letI : DecidableEq SourceStmt := fun left right =>
          stmtDecEqFuel fuel left right
        if h : (condition, body) = (condition', body') then
          isTrue <| by cases h; rfl
        else
          isFalse fun equality => h (by cases equality; rfl)
    | fuel + 1, .switch value cases defaultBody,
        .switch value' cases' defaultBody' =>
        letI : DecidableEq SourceExpr := fun left right =>
          exprDecEqFuel fuel left right
        letI : DecidableEq SourceStmt := fun left right =>
          stmtDecEqFuel fuel left right
        if h : (value, cases, defaultBody) =
            (value', cases', defaultBody') then
          isTrue <| by cases h; rfl
        else
          isFalse fun equality => h (by cases equality; rfl)
    | fuel + 1, .for_ init condition post body,
        .for_ init' condition' post' body' =>
        letI : DecidableEq SourceExpr := fun left right =>
          exprDecEqFuel fuel left right
        letI : DecidableEq SourceStmt := fun left right =>
          stmtDecEqFuel fuel left right
        if h : (init, condition, post, body) =
            (init', condition', post', body') then
          isTrue <| by cases h; rfl
        else
          isFalse fun equality => h (by cases equality; rfl)
    | _ + 1, .break_, .break_ => isTrue rfl
    | _ + 1, .continue_, .continue_ => isTrue rfl
    | _ + 1, .leave, .leave => isTrue rfl
    | fuel + 1, .function_ name params returns body,
        .function_ name' params' returns' body' =>
        letI : DecidableEq SourceStmt := fun left right =>
          stmtDecEqFuel fuel left right
        if h : (name, params, returns, body) =
            (name', params', returns', body') then
          isTrue <| by cases h; rfl
        else
          isFalse fun equality => h (by cases equality; rfl)
    | _ + 1, left, right => Classical.decEq _ left right
end

private def dataDecEq : DecidableEq SourceData := fun left right =>
  if h : (left.name, left.bytes) = (right.name, right.bytes) then
    isTrue <| by cases left; cases right; cases h; rfl
  else
    isFalse fun equality =>
      h (congrArg (fun value => (value.name, value.bytes)) equality)

private def objectDecEqFuel :
    Nat → (left right : SourceObject) → Decidable (left = right)
  | 0, left, right => Classical.decEq _ left right
  | fuel + 1, .mk name code objects data, .mk name' code' objects' data' =>
      letI : DecidableEq SourceStmt := fun left right =>
        stmtDecEqFuel fuel left right
      letI : DecidableEq SourceObject := fun left right =>
        objectDecEqFuel fuel left right
      letI : DecidableEq SourceData := dataDecEq
      if h : (name, code, objects, data) =
          (name', code', objects', data') then
        isTrue <| by cases h; rfl
      else
        isFalse fun equality => h (by cases equality; rfl)

def expr : DecidableEq SourceExpr :=
  exprDecEqFuel 128

def stmt : DecidableEq SourceStmt :=
  stmtDecEqFuel 128

def object : DecidableEq SourceObject :=
  objectDecEqFuel 128

end

end NiceTry.Fors.Bridge.YulSourceDecidableEq
