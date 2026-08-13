Route U quantitative hard-edge compactification formalized.

New module:
formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeCofinalLinearFiniteHankelDimension.lean

Key exact definitions/theorems:
- routeUExplicitFiniteChebyshevCutoff n k = (n+1)(k+1)+1.
- routeURealEvenCompactApproximation_eq_zero_of_explicitCutoff: canonical scaled cutoff support gives exact finite sampling cutoff.
- natDegree_routeUFiniteChebyshevPacketPolynomial_le.
- routeUExplicitFiniteHankelSize_le_linear: exact reciprocal-pullback coefficient size S(n,k) <= (n+1)(k+1)+2.
- routeUExplicitFiniteHankelQuadratic_eq_sampleDivisorSum.
- routeUHardEdgeMass_sq_lt_parabolic_size_sq_of_explicitQuadratic_neg: negative packet implies (k+1)^2 < routeUParabolicDegreeHorizon*S^2.
- XiShiftedHardEdgeCofinalLinearNegativePhase.
- not_rh_iff_xiShiftedHardEdgeCofinalLinearNegativePhase.
- riemannHypothesis_or_xiShiftedHardEdgeCofinalLinearNegativePhase.

Mathematical progress: false RH now forces one fixed polynomial-Gaussian carrier and cutoff index with a negative literal finite shifted-Hankel packet for every sufficiently large integral hard-edge mass, not merely an unnamed subsequence. Exact dimension is trapped on Theta(sqrt(y)) scale. This closes the formal quantitative gap in mass-shifted-hard-edge-paley-wiener-compactification and removes arbitrary packet-size escape. It is not RH: remaining exact open core is an unconditional prime-Gamma completed-source sign/budget for this single cofinal finite-type family before divisor aggregation. The speculative cross-degree determinant-line budget is no longer needed for compactification and remains unproved.

Audit:
- lake env lean module passed.
- lake build GaloisForLFunctions.RHTower.XiShiftedHardEdgeCofinalLinearFiniteHankelDimension passed 11977/11977.
- imported at RHTower.lean line ~7180.
- forbidden scan clean: no sorry/admit/axiom/opaque/unsafe/native_decide/#eval/#reduce.
- all public theorems only [propext, Classical.choice, Quot.sound].
- repo lint failed only because unrelated dirty/untracked modules were umbrella-unreachable.
- no task-owned stale Lean processes.
- Stage3 card: docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-u-hard-edge-cofinal-linear-finite-hankel-dimension.md
- frontier map appended around line 10506.

User explicitly objected to computation theatre. No numerical computation was used.