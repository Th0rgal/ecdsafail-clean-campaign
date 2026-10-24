import Lake
open Lake DSL

package «lean_verifier» where
  moreLeancArgs := #["-O3"]

lean_lib «EcdsaVerifier» where
  -- Library containing CanonicalSpec, OptimizedChecker, EquivalenceProofs, DiffTest

@[default_target]
lean_exe «lean-verifier» where
  root := `Main
