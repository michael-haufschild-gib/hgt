# BM folded horizon-boundary rigidity (2026-08-26)

Mission: test whether nonlinear horizon/boundary evolution forces folded dark-kernel occurrence at every Xi divisor copy.

Result: affirmative forcing is false at the exact first nonlinear BM radiation order. For reflected/conjugated transfers (T_r,T_c), any opposite-helicity pair with common nonzero ingoing horizon value (H) has folded radiation
[
F_q=(0,0,0,(T_r-T_c)H)
]
and exact optical flux
[
|F_q|^2=operatorname{normSq}(T_r-T_c)operatorname{normSq}(H).
]
Thus arbitrary nonlinear dependence of (H) on source state factors out. Transfer collision rigidity gives (F_q=0) iff (Re q=1/2); off line the defect flux is strictly positive. Canonical unit-horizon darkness at every Xi copy is exactly equivalent to RH, not independently forced by Einstein causality, gauge constraints, real structure, or horizon matching.

Conjecture loop:
1. Real Einstein data identify conjugate modes but not FE-reflected modes: failed.
2. Theta modular inversion as horizon/boundary spacetime gauge symmetry: failed because BM horizon and AdS boundary Frobenius data are inequivalent and no such spacetime action exists.
3. Family-index/topological kernel forcing: failed after horizon matching reduces the map to multiplication (Hmapsto(T_r-T_c)H) between one-complex-dimensional spaces.
Positive survivor: exact horizon-boundary defect factorization/classification above.

New Lean module:
- `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFoldedHorizonBoundaryRigidity.lean`
- imported by `formal/GaloisForLFunctions/RHTower.lean`

Key declarations:
- `d4BMXiFESchwarzFoldedOrthogonalRadiation_eq_boundaryDefect`
- `d4BMXiFESchwarzFoldedHorizonBoundaryDefectFlux_eq`
- `d4BMXiFESchwarzHorizonNormalizedFoldedOrthogonalRadiation_eq_zero_iff`
- `d4BMXiFESchwarzFoldedHorizonBoundaryDefectFlux_pos`
- `d4BMXiFESchwarzNonlinearCarrierFoldedOrthogonalRadiation_eq_zero_iff`
- `d4BMXiCanonicalHorizonFoldedDarkAtEveryCopy_iff_riemannHypothesis`

Verification:
- direct targeted source compile passed
- all 15 new declarations axiom-audited: only `propext`, `Classical.choice`, `Quot.sound`
- custom corpus research indexes the module
- forbidden-token scan clean
- global static lint still fails only on unrelated pre-existing unreachable modules; new module is umbrella-reachable
- scratch and generated target olean removed
- no git, endpoint, frontier ledger, or pipeline-card edits

Literature audit remained focused: Birmingham–Mokhtari supplies exact KI hypergeometric QNMs; Green et al. supplies conserved bilinear Teukolsky current/QNM projection; Sberna et al. shows nonlinear absorption excites rather than generically erases modes; Warnick gives discrete horizon-regular AdS QNM semigroup. None supplies FE-reflection Cauchy-data identification or forced folded darkness.