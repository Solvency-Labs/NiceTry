import NiceTry.Fors.Bridge.ForsRuntime
import NiceTry.Fors.Bridge.ForsYulRuntimeParts
import NiceTry.Fors.Bridge.ForsYulSource
import NiceTry.Fors.Bridge.ForsYulTokens
import NiceTry.Fors.Bridge.YulParser
import NiceTry.Fors.Bridge.YulSourceDecidableEq

/-!
# Kernel-checked import of the pinned `ForsVerifier` optimized Yul

The compiler artifact is included as source text. `parseDeployedRuntime` lexes
and parses the complete solc object, selects its deployed object, and imports
that runtime into EVMYulLean.

`parse_pinned_fors_runtime` is checked by Lean's kernel computation. It is the
certificate connecting the compiler artifact to the stable runtime scaffold
used by the execution proof.
-/

namespace NiceTry.Fors.Bridge

open EvmYul.Yul.Ast

noncomputable section

local instance : DecidableEq YulParser.SourceExpr :=
  YulSourceDecidableEq.expr

local instance : DecidableEq YulParser.SourceStmt :=
  YulSourceDecidableEq.stmt

local instance : DecidableEq YulParser.SourceObject :=
  YulSourceDecidableEq.object

local instance : DecidableEq YulParser.SourceRuntimeParts := fun left right =>
  if h :
      (left.dispatcher, left.functions) =
        (right.dispatcher, right.functions) then
    isTrue <| by cases left; cases right; cases h; rfl
  else
    isFalse fun equality =>
      h (congrArg (fun value => (value.dispatcher, value.functions)) equality)

def pinnedForsOptimizedYul : String :=
  include_str ".." / ".." / ".." / "artifacts" /
    "fors-verifier-runtime" / "ForsVerifier.irOptimized.yul"

private def chunkTokens : Nat → List YulParser.Token → List (List YulParser.Token)
  | 0, tokens => [tokens]
  | _ + 1, [] => []
  | fuel + 1, tokens =>
      tokens.take 32 :: chunkTokens fuel (tokens.drop 32)

private theorem flatten_chunkTokens
    (fuel : Nat) (tokens : List YulParser.Token) :
    (chunkTokens fuel tokens).flatten = tokens := by
  induction fuel generalizing tokens with
  | zero => simp [chunkTokens]
  | succ fuel ih =>
      cases tokens with
      | nil => simp [chunkTokens]
      | cons token tokens =>
          simp only [chunkTokens, List.flatten_cons, ih]
          exact List.take_append_drop 32 (token :: tokens)

def lexedPinnedForsOptimizedYulTokens : List YulParser.Token :=
  match YulParser.lex pinnedForsOptimizedYul with
  | .ok tokens => tokens
  | .error _ => []

private theorem except_eq_ok_value
    {ε α : Type} (fallback : α) (result : Except ε α)
    (hOk : result.isOk = true) :
    result = .ok (match result with
      | .ok value => value
      | .error _ => fallback) := by
  cases result with
  | error _ => cases hOk
  | ok _ => rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private theorem lex_pinned_fors_yul_raw :
    YulParser.lex pinnedForsOptimizedYul =
      .ok lexedPinnedForsOptimizedYulTokens := by
  have hOk : (YulParser.lex pinnedForsOptimizedYul).isOk = true := by
    decide +kernel
  exact except_eq_ok_value [] _ hOk

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private theorem lexed_pinned_tokens_eq :
    lexedPinnedForsOptimizedYulTokens = pinnedForsOptimizedYulTokens := by
  have hchunks :
      chunkTokens 64 lexedPinnedForsOptimizedYulTokens =
        pinnedForsOptimizedYulTokenChunks := by
    apply of_decide_eq_true
    decide +kernel
  rw [← flatten_chunkTokens 64 lexedPinnedForsOptimizedYulTokens,
    hchunks]
  rfl

theorem lex_pinned_fors_yul :
    YulParser.lex pinnedForsOptimizedYul =
      .ok pinnedForsOptimizedYulTokens := by
  rw [lex_pinned_fors_yul_raw, lexed_pinned_tokens_eq]

def parsedPinnedForsSource : YulParser.SourceObject :=
  match YulParser.parseSourceTokens pinnedForsOptimizedYulTokens with
  | .ok sourceObject => sourceObject
  | .error _ => pinnedForsOptimizedYulSource

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private theorem parse_pinned_fors_source_raw :
    YulParser.parseSourceTokens pinnedForsOptimizedYulTokens =
      .ok parsedPinnedForsSource := by
  have hOk :
      (YulParser.parseSourceTokens
        pinnedForsOptimizedYulTokens).isOk = true := by
    decide +kernel
  exact except_eq_ok_value pinnedForsOptimizedYulSource _ hOk

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private theorem parsed_pinned_fors_source_eq :
    parsedPinnedForsSource = pinnedForsOptimizedYulSource := by
  apply of_decide_eq_true
  decide +kernel

private theorem parse_pinned_fors_source :
    YulParser.parseSourceTokens pinnedForsOptimizedYulTokens =
      .ok pinnedForsOptimizedYulSource := by
  rw [parse_pinned_fors_source_raw, parsed_pinned_fors_source_eq]

def parsedPinnedForsRuntimeParts : YulParser.SourceRuntimeParts :=
  match YulParser.extractDeployedRuntimeParts pinnedForsOptimizedYulSource with
  | .ok parts => parts
  | .error _ => pinnedForsRuntimeParts

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private theorem extract_pinned_fors_runtime_parts_raw :
    YulParser.extractDeployedRuntimeParts pinnedForsOptimizedYulSource =
      .ok parsedPinnedForsRuntimeParts := by
  have hOk :
      (YulParser.extractDeployedRuntimeParts
        pinnedForsOptimizedYulSource).isOk = true := by
    decide +kernel
  exact except_eq_ok_value pinnedForsRuntimeParts _ hOk

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private theorem parsed_pinned_fors_runtime_parts_eq :
    parsedPinnedForsRuntimeParts = pinnedForsRuntimeParts := by
  apply of_decide_eq_true
  decide +kernel

private theorem extract_pinned_fors_runtime_parts :
    YulParser.extractDeployedRuntimeParts pinnedForsOptimizedYulSource =
      .ok pinnedForsRuntimeParts := by
  rw [extract_pinned_fors_runtime_parts_raw,
    parsed_pinned_fors_runtime_parts_eq]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private theorem validate_pinned_fors_source :
    YulParser.validateDeployedRuntime pinnedForsOptimizedYulSource =
      .ok () := by
  rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private theorem validate_pinned_fors_tokens :
    YulParser.validateTokenIdentifierCollisions
        pinnedForsOptimizedYulTokens =
      .ok () := by
  rfl

private theorem pinned_fors_function_sources :
    pinnedForsRuntimeParts.functions =
      [pinnedForsConstSource, pinnedForsRecoverSource] := by
  rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private theorem pinned_fors_dispatcher_supported :
    YulParser.sourceStmtSupportedFuel 16 pinnedForsDispatcherSource = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private theorem lower_pinned_fors_dispatcher :
    YulParser.lowerSourceStmtFuel 16 pinnedForsDispatcherSource =
      forsDispatcher := by
  unfold pinnedForsDispatcherSource forsDispatcher
  rfl

private theorem import_pinned_fors_dispatcher :
    YulParser.importRuntimeDispatcher pinnedForsRuntimeParts =
      .ok forsDispatcher := by
  simp only [YulParser.importRuntimeDispatcher, pinnedForsRuntimeParts,
    YulParser.importSourceStmt, YulParser.importSourceStmtFuel,
    pinned_fors_dispatcher_supported, if_true,
    lower_pinned_fors_dispatcher]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private theorem pinned_fors_const_supported :
    YulParser.sourceStmtsSupportedFuel 16 pinnedForsConstBodySource = true := by
  decide +kernel

private def pinnedForsConstBody : List Stmt :=
  match forsConstSigLen with
  | .Def _ _ body => body

private theorem lower_pinned_fors_const_body :
    YulParser.lowerSourceStmtsFuel 16 pinnedForsConstBodySource =
      pinnedForsConstBody := by
  unfold pinnedForsConstBodySource pinnedForsConstBody forsConstSigLen
  rfl

private theorem import_pinned_fors_const :
    YulParser.importRuntimeFunction pinnedForsConstSource =
      .ok ("constant_FORS_SIG_LEN", forsConstSigLen) := by
  simp only [YulParser.importRuntimeFunction, YulParser.importSourceFunction,
    pinnedForsConstSource, pinned_fors_const_supported, if_true,
    lower_pinned_fors_const_body]
  rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private theorem pinned_fors_recover_supported :
    YulParser.sourceStmtsSupportedFuel 16 pinnedForsRecoverBodySource = true := by
  decide +kernel

private def pinnedForsRecoverBody : List Stmt :=
  match forsFunRecover with
  | .Def _ _ body => body

private theorem lower_pinned_fors_recover_body :
    YulParser.lowerSourceStmtsFuel 16 pinnedForsRecoverBodySource =
      pinnedForsRecoverBody := by
  unfold pinnedForsRecoverBodySource pinnedForsRecoverBody forsFunRecover
  rfl

private theorem import_pinned_fors_recover :
    YulParser.importRuntimeFunction pinnedForsRecoverSource =
      .ok ("fun_recover", forsFunRecover) := by
  simp only [YulParser.importRuntimeFunction, YulParser.importSourceFunction,
    pinnedForsRecoverSource, pinned_fors_recover_supported, if_true,
    lower_pinned_fors_recover_body]
  rfl

private theorem import_pinned_fors_functions :
    [pinnedForsConstSource, pinnedForsRecoverSource].mapM
        YulParser.importRuntimeFunction =
      .ok
        [("constant_FORS_SIG_LEN", forsConstSigLen),
          ("fun_recover", forsFunRecover)] := by
  change (do
    let constEntry ← YulParser.importRuntimeFunction pinnedForsConstSource
    let recoverEntry ← YulParser.importRuntimeFunction pinnedForsRecoverSource
    .ok [constEntry, recoverEntry]) = _
  rw [import_pinned_fors_const, import_pinned_fors_recover]
  rfl

private theorem import_pinned_fors_runtime_parts :
    YulParser.importRuntimeParts pinnedForsRuntimeParts =
      .ok forsVerifierRuntime := by
  unfold YulParser.importRuntimeParts
  rw [import_pinned_fors_dispatcher, pinned_fors_function_sources,
    import_pinned_fors_functions]
  unfold YulParser.assembleRuntime forsVerifierRuntime
  rfl

private theorem import_pinned_fors_runtime :
    YulParser.importDeployedRuntime pinnedForsOptimizedYulSource =
      .ok forsVerifierRuntime := by
  unfold YulParser.importDeployedRuntime
  rw [validate_pinned_fors_source]
  change YulParser.importDeployedRuntimeUnchecked
      pinnedForsOptimizedYulSource = .ok forsVerifierRuntime
  unfold YulParser.importDeployedRuntimeUnchecked
  rw [extract_pinned_fors_runtime_parts]
  exact import_pinned_fors_runtime_parts

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem parse_pinned_fors_runtime :
    YulParser.parseDeployedRuntime pinnedForsOptimizedYul =
      .ok forsVerifierRuntime := by
  unfold YulParser.parseDeployedRuntime
  rw [lex_pinned_fors_yul]
  change YulParser.parseDeployedRuntimeTokens
      pinnedForsOptimizedYulTokens = .ok forsVerifierRuntime
  unfold YulParser.parseDeployedRuntimeTokens
  rw [validate_pinned_fors_tokens, parse_pinned_fors_source]
  exact import_pinned_fors_runtime

end

end NiceTry.Fors.Bridge
