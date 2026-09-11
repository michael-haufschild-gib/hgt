# HB: original principal Dirichlet coercivity

Stage: 3-formalized. Seven public theorems passed scratch checking and the exact leaf build. RH, physical left-QNM action and fixed-clock extinction remain unproved.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

On the original completed radial Dirichlet graph, Lean proves

||u′+tanh(x)u||²+2||sech(x)u||²=||u′||²+||u||².

The proof establishes integration by parts on the original compact radial core, then extends its continuous sesquilinear form through the closed span. The domain and endpoint condition are the existing ones.

For m with 0≤Re(m)≤2 and Re(w)>3/2, set

b(u,v)=⟨u′,v′⟩+w²⟨u,v⟩−m(m−1)⟨sech·u,sech·v⟩.

The precise inner-product convention is given by `principalDirichletFormOperator_inner`. Its rotation by conjugate(w) is coercive with constant Re(w)−3/2 in the original graph norm. Completing squares handles Im(m) without bounding it. The existing coercive-operator inverse theorem then supplies a bounded two-sided inverse and a unique solution of the literal original form equation for every radial L² forcing F. Its value satisfies

||u||≤||F||/((Re(w)−3/2)|w|).

For all three actual exponents m=2ρ,1,2−2ρ, the proved Xi strip supplies the exponent conditions. At Re(w)≥7/4 the resulting bound is 4||F||/|w|. This solves the original stationary form problem; identifying this solution with the actual causal time-family transform is a separate obligation.

Module: [ThetaCuspHawkingBMPrincipalDirichletCoercivity.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPrincipalDirichletCoercivity.lean), namespace `RHTower.D4BMJointWave`.

Verification: `lake env lean` accepted the combined scratch containing the exact source. `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPrincipalDirichletCoercivity` passed in an isolated directory using cached dependencies, compiling only this new leaf (two jobs). The exact source and five build artifacts were installed, and one import was added to `RHTower.lean`. No umbrella build ran. No axiom-print checks or numerical experiments ran.

The next causal landing uses the [native circle-kernel growth argument](../1-in-progress/hb-principal-growth-energy.md), which gives a rate strictly below two for the actual kernels and can avoid constructing a separate Hardy evolution from this inverse.

Final formal lint passed with existing large-file warnings. Module imports and local report links were verified. All owned checks completed; temporary audit and scratch files were removed. No owned Lean process remains.
