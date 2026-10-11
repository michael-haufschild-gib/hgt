# Exact normalized mass limit along cubic cluster starts

Status: formalized; native leaf builds and complete axiom/API audit passed.
Date: 2026-10-10. Local Lean corpus only.

Use the predecessor `finite-weil-relative-mass-error.md` and the corpus's proved Wallis limit. Set n=r+1, k_r=2n³, m_r=floor(r/2)+1, G_r=arithmetic nodal mass, S_r=logarithmic nodal mass at k_r.

Paper proof:
1. Since n>=1, k_r+2>=2n³>=2n². The relative mass error gives abs(S_r/G_r-1)<=2n²/(2n³+2)<=1/n. The last comparison follows by clearing positive denominators and using 2n³<=2n³+2. Thus S_r/G_r tends to one.
2. m_r tends to infinity: r>=2b implies m_r>=b. The existing corpus result `tendsto_sqrtNat_mul_normalizedCentralBinom` therefore gives sqrt(m_r)c_(m_r) -> 1/sqrt(pi).
3. The exact previously proved identity G_r*c_(m_r)=1 gives G_r/sqrt(m_r)=1/(sqrt(m_r)c_(m_r)). Since pi>0, inversion is continuous at the nonzero limit. Hence G_r/sqrt(m_r) -> sqrt(pi).
4. S_r/sqrt(m_r)=(S_r/G_r)*(G_r/sqrt(m_r)), since G_r>=2. Multiplying the two limits gives S_r/sqrt(m_r) -> sqrt(pi).

Completed receiver: an unconditional theorem for an explicit natural cluster sequence, for all moment orders, with exact normalization by sqrt(floor(r/2)+1). No unknown asymptotic premise, no experimental numerical fit, no external novelty claim. This transfers the corpus's central-binomial limit to canonical logarithmic moment-annihilator mass.

Sources: WeilLogShiftArithmeticSqrt exact mass identity; WeilLogShiftRelativeMass finite error; HTGeometry.CentralBinomialWallisAsymptotic line72. Prior local mass-asymptotic search found only the unrelated deficit-log-block bound already recorded on the predecessor card.

`WeilLogShiftCubicMassLimit.lean` exposes six declarations: cubic-start definition (line10), width (line12), reciprocal-order relative error (line21), mass-ratio limit (line39), arithmetic half-order-normalized mass limit (line50), and `tendsto_finiteWeilCanonicalCluster_cubic_mass_div_sqrt_halfOrder` (line81).

All 10 declarations across both leaves and 22 explicit API terms passed `/tmp/hgt-relative-final-audit.lean`. Both native leaf builds have empty final logs. Axioms are contained in `propext`, `Classical.choice`, `Quot.sound`. Source/direct-dependency freshness, exact umbrella counts, exhaustive incoming-import scope, and axiom coverage passed. Lint has only the three unrelated missing imports recorded on the predecessor card.

Lean lesson: an unannotated composed Wallis limit retained a function-composition expression that `simpa only` would not reduce. Giving that local limit its explicit function type fixed elaboration without changing the theorem or introducing a new premise.

Follow-up completed: `finite-weil-standard-mass-normalization.md` removes parity from the normalization and proves S_r/sqrt(r+1)->sqrt(pi/2). The companion `finite-weil-polynomial-mass-limit.md` extends the limit to every polynomial degree at least three, including arbitrarily varying degrees. All 13 new declarations passed native builds and complete axiom audit.

Local index refresh exited0. Exact post-index lookup found `tendsto_finiteWeilCanonicalCluster_cubic_mass_div_sqrt_halfOrder` at source line81. All owned build, audit, lint, index, and search sessions are terminal.
