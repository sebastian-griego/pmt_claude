import Lake
open Lake DSL

package «pnt» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «PNT1_ComplexAnalysis» {
  -- add library configuration options here
}

lean_lib «PNT2_LogDerivative» {
  -- add library configuration options here
}

lean_lib «PNT3_RiemannZeta» {
  -- add library configuration options here
}

lean_lib «PNT4_ZeroFreeRegion» {
  -- add library configuration options here
}

lean_lib «PNT5_StrongPNT» {
  -- add library configuration options here
}
