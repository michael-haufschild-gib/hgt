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
   `norm_le_of_hardyFun_eq_of_circle_bound`), `mem_primeSpan_of_differentiableOn_ball` and
   `exists_mem_primeSpan_of_differentiableOn_ball` (Taylor on a disc containing the discs),
   `exists_ball_re_gt_of_forall_lt` / `_lt_` (finitely many discs of a half plane lie in a disc of it).
4. `PhasedEulerProductsApproximateExponentialsOnDiscUnions` — joint phases approximating
   `exp(L_i)` on all discs (`exists_unimodular_eulerProduct_approx_exp_tuple`).
5. `UniformEulerTargetDensityOnDiscUnions` — `exists_mem_primeSpan_exp_eq_zeta` (log ζ tuple:
   `ℓ + (−log(1−s) + iπ)`, ℓ = analytic log of zetaPoleFilled on a zero-free disc),
   `exists_pos_density_eulerTargetReturnSet_zeta_union`,
   `exists_uniform_pos_density_eulerTargetReturnSet_zeta_union` (random sum in the direct sum).
6. `ZetaStrongRecurrenceOnCompactSets` — union tail law, `zetaDiscStronglyRecurrentOn_iUnion_closedBall_of_zeroFree`,
   `zetaDiscStronglyRecurrentOn_of_riemannHypothesis_of_isCompact` (cover by discs of radius
   ρ₀/2, ρ₀ = min(a−1/2, 1−b')/4), `riemannHypothesis_iff_zetaStronglyRecurrent`.

Lean lessons: `Differentiable.fun_sum`/`DifferentiableOn.fun_sum` for lambda-form finite sums;
`ring` treats `exp(-(a*b))` and `exp(-a*b)` as different atoms (use `simp only [neg_mul]` first);
`omit [Fintype ι] in` must precede the docstring; BSD sed has no `\b`.

Next conjectures: (i) primeSpan = closure of polynomial tuples = closure of exponential tuples;
(ii) unconditional Voronin universality on compact sets for targets analytic and nonvanishing on a
disc containing K (generalise module 5 from ζ to any `exp(hardyFun (L i))` target).
