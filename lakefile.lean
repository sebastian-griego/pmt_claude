import Lake
open Lake DSL

package «StrongPNT» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Scaffold» where
  -- fast target to keep CI/dev builds green
  roots := #[`StrongPNT.PNT0_Scaffold]

-- Full library (build explicitly with: `lake build PNT`)
lean_lib «PNT» where
  roots := #[
    `StrongPNT.PNT1_ComplexAnalysis,
    `StrongPNT.PNT2_LogDerivative,
    `StrongPNT.PNT3_RiemannZeta,
    `StrongPNT.PNT4_ZeroFreeRegion,
    `StrongPNT.PNT5_StrongPNT
  ]
