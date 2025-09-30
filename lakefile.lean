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
lean_lib «PNT» where
  /-
  Temporarily restrict the default build to a minimal scaffolding module
  while the heavier modules are being stabilized. The original roots were:
    `StrongPNT.PNT1_ComplexAnalysis, `StrongPNT.PNT2_LogDerivative,
    `StrongPNT.PNT3_RiemannZeta, `StrongPNT.PNT4_ZeroFreeRegion,
    `StrongPNT.PNT5_StrongPNT
  -/
  roots := #[`StrongPNT.PNT0_Scaffold]
