import Lake
open Lake DSL

package NiceTryForsVerity where
  version := v!"0.1.0"

require verity from git
  "https://github.com/lfglabs-dev/verity.git"@"bd211c574f45cda31d66feab1bbc7e9d08dc5486"

lean_lib NiceTry where
  srcDir := "."
  roots := #[
    `NiceTry.Fors.Types,
    `NiceTry.Fors.Hash,
    `NiceTry.Fors.Model,
    `NiceTry.Fors.TreeShape,
    `NiceTry.Fors.TreeKeccak,
    `NiceTry.Fors.FullKeccak,
    `NiceTry.Fors.RawKeccak,
    `NiceTry.Fors.Spec,
    `NiceTry.Fors.Proofs.Basic,
    `NiceTry.Fors.Proofs.TreeShape,
    `NiceTry.Fors.Proofs.TreeKeccak,
    `NiceTry.Fors.Proofs.FullKeccak,
    `NiceTry.Fors.Proofs.RawKeccak,
    `NiceTry.Fors.Verity.GuardKernel,
    `NiceTry.Fors.Verity.TreeShapeKernel,
    `NiceTry.Fors.Verity.TreeKeccakKernel,
    `NiceTry.Fors.Verity.FullVerifierKernel,
    `NiceTry.Fors.Bridge.Oracle,
    `NiceTry.Fors.Bridge.Equivalence,
    `NiceTry.Fors.Bridge.MemoryLayout,
    `NiceTry.Fors.Bridge.EvmFfiSpec,
    `NiceTry.Fors.Bridge.ByteArrayLemmas,
    `NiceTry.Fors.Bridge.EvmMemory,
    `NiceTry.Fors.Bridge.ForsRuntime,
    `NiceTry.Fors.Bridge.EvmRun,
    `NiceTry.Fors.Bridge.AddressShape,
    `NiceTry.Fors.Bridge.Interp,
    `NiceTry.Fors.Bridge.Refinement
  ]
