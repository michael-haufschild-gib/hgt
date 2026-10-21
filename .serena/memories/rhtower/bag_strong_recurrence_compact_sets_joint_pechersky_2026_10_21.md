# BAG: RH ⟺ ZetaStronglyRecurrent (Bagchi on compact sets) — Lean, 2026-10-21

Main theorem: `RHTower.riemannHypothesis_iff_zetaStronglyRecurrent` in
`formal/GaloisForLFunctions/RHTower/ZetaStrongRecurrenceOnCompactSets.lean` (axioms: propext,
Classical.choice, Quot.sound). RH ⟹ was the missing non-disc universality step.

Modules (all wired into RHTower.lean, built with `lake --old env lean -j 1 -o`):
1. `PrimeSumDivergenceOfHorizontalExtent` — `exists_primeLogWeightedSum_gt_of_negRay`: divergence of
   `Σ_{p<N} p^{−σ}‖Φ(log p)‖` needs only the negative-ray rate `b < 1 − σ`, not the full type.
2. `HardyDiscTuplesAndJointPechersky` — `DiscTuple ι = PiLp 2 (fun _ => HardyDisk)`, `primeTuple`,
   `tuplePairing` (= Σ_i e^{−conj(z i) ξ} Φ_{e i}(ξ)), `primeSpan` (closed span of prime tuples),
   `exists_unimodular_primeTuple_sum_approx_extend` (joint Pechersky with prescribed initial phases).
3. `ExponentialTuplesAndAnalyticMembershipInPrimeSpan` — `expTuple`, `inner_expTuple`,
   `expTuple_mem_primeSpan` (via `Submodule.orthogonal_orthogonal`), `monoTuple_mem_primeSpan`
   (finite differences `(−1)^k h^{−k} Σ C(k,j)(−1)^{k−j} e^{c₀jh} E_{jh}` + Cauchy estimate
   `norm_le_of_hardyFun_eq_of_circle_bound`), `mem_of_differentiableOn_ball_of_monoTuple_mem`
   (Taylor step for any closed submodule containing the monomial tuples),
   `mem_primeSpan_of_differentiableOn_ball`, `exists_mem_primeSpan_of_differentiableOn_ball`,
   `exists_ball_re_gt_of_forall_lt` / `_lt_` (finitely many discs of a half plane lie in a disc of it).
4. `PrimeSpanIsThePolynomialClosure` — `primeSpan = expTupleSpan = polyTupleSpan c₀` (any centre),
   `primeSpanᗮ = {e : F_e ≡ 0}` (`mem_orthogonal_primeSpan_iff_tuplePairing_eq_zero`),
   `primeSpan_eq_top_of_unique` (one disc), `primeVector_eq_expVector`.
5. `PhasedEulerProductsApproximateExponentialsOnDiscUnions` — joint phases approximating
   `exp(L_i)` on all discs (`exists_unimodular_eulerProduct_approx_exp_tuple`).
6. `UniformEulerTargetDensityOnDiscUnions` — `exists_mem_primeSpan_exp_eq_zeta` (log ζ tuple:
   `ℓ + (−log(1−s) + iπ)`, ℓ = analytic log of zetaPoleFilled on a zero-free disc),
   general-target `exists_pos_density_eulerTargetReturnSet_exp_union` and
   `exists_uniform_pos_density_eulerTargetReturnSet_exp_union` (random sum in the direct sum),
   `…_zeta_union` versions derived.
7. `ZetaStrongRecurrenceOnCompactSets` — union tail law, `zetaDiscStronglyRecurrentOn_iUnion_closedBall_of_zeroFree`,
   `zetaDiscStronglyRecurrentOn_of_riemannHypothesis_of_isCompact` (cover by discs of radius
   ρ₀/2, ρ₀ = min(a−1/2, 1−b')/4), `riemannHypothesis_iff_zetaStronglyRecurrent`.
8. `ZetaVoroninUniversalityOnCompactSets` — unconditional
   `exists_pos_density_zetaTargetReturnSet_of_isCompact` (K compact in the strip, inside an open
   disc on which g is analytic and nonvanishing; the disc may leave the strip), corollaries for
   nonzero constants and nonvanishing entire functions.

Lean lessons: `Differentiable.fun_sum`/`DifferentiableOn.fun_sum` for lambda-form finite sums;
`ring` treats `exp(-(a*b))` and `exp(-a*b)` as different atoms (use `simp only [neg_mul]` first);
`omit [Fintype ι] in` must precede the docstring; BSD sed has no `\b`; `IsMaxOn` with
`(f := fun s => …)` + `beta_reduce at` for linarith.

Open: targets analytic only on a neighbourhood of K (needs Runge/Mergelyan, not in corpus);
primeSpan = ⊤ iff discs pairwise disjoint (Borel-transform support argument, not formalized).
