# Route R graded det2 scalar-descent counterboundary (2026-08-03)

Formalized independent equal-grade boundary in `formal/GaloisForLFunctions/RHTower/PrimeDepthBVWoldGradedDet2ScalarDescentBoundary.lean`.

Core identity: consecutive BV-mass/Wold-clock increment area
`dm(i,j) dl(j,k) - dl(i,j) dm(j,k)` equals existing scalar curvature `kappa(i,j,k)`. Using actual essential-edge occupation quadratic trace `q = Tr(Q^2) = zeta(2) != 0`, crossed parity-diagonal occupation legs have supertrace `a*kappa`. Their graded Hilbert-Carleman anomaly `exp(-Str(AB))` is exact inverse scalar triangle holonomy.

Unconditional Lean results:
- `primeDepthBVWoldGradedOccupationSupertracePair_source_cross`
- `primeDepthBVWoldTransport_mul_gradedDet2Anomaly`
- `primeDepthBVWoldCovariantD1_comp_D0_add_gradedDet2Boundary`
- `primeDepthBVWoldXiCovariantD1_comp_D0_add_gradedDet2Boundary_leadingConormal`
- boundary vanishing on exact Xi witness iff critical line
- global explicit boundary triviality iff RH.

Honest frontier: corrected square is unconditional but does not prove RH. Missing scientific theorem is source Stokes/Cartier trivialization of this explicit graded det2 boundary on actual leading Xi conormal. Boundary triviality is RH-equivalent.

Card: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-r-graded-det2-scalar-descent-counterboundary.md`. Frontier map updated. Module wired into `GaloisForLFunctions/RHTower.lean`.

Verification: direct `lake env lean` passed; targeted `lake build GaloisForLFunctions.RHTower.PrimeDepthBVWoldGradedDet2ScalarDescentBoundary` passed (10317/10317); forbidden-declaration scan clean; `#print axioms` reports only propext/Classical.choice/Quot.sound. Repository lint still fails only on unrelated pre-existing unreachable modules; new module is reachable and absent from lint errors.

Novelty audit: parent det2 product formula arXiv:2007.12834 and higher-product treatment arXiv:2202.12923; no exact collision located. Status remains candidate new scientific knowledge, not unrestricted priority claim.