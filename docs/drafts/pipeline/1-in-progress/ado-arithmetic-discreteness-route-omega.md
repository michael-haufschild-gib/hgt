# Route Ω — arithmetic discreteness (obstacles-summary review-0511 §2.4)

- **ID:** ADO
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (programme)
- **Source:** docs/reports/review-0511/obstacles-summary.md §2.4, §2.7.4 (Field IV), B54
- **Statement:** purity by (i) a pure member, (ii) continuity of the zeros along a deformation,
  (iii) a discrete structure on near-coincidences forcing collide-or-repel.

## Goal
Decide what discreteness can and cannot produce, calibrate it exactly over `𝔽_q`, find the form of
discreteness an Euler product actually carries, and state the exact test for `ζ`.

## Lean
Folder `formal/GaloisForLFunctions/ArithmeticDiscreteness/` (README there), umbrella
`ArithmeticDiscreteness.lean`, wired into `MainTheorems.lean`.

## Conjectures

| # | Statement | Status |
|---|---|---|
| Ω1 | Distinct roots of every monic `f ∈ ℤ[X]` with roots in `|z| ≤ R` repel: `1 ≤ |α−β|(2R)^{(n−1)²+n−2}` | Lean: `one_le_norm_sub_mul_pow_of_ne` |
| Ω1′ | The exponent must grow with `n` | Lean: `mignotte_close_roots` (separation `< 2a^{−(m+1)}`, degree `2m`, height `2a²`) |
| Ω2 | Impurity is quantized; near purity is purity | Lean: `impurity_is_quantized`, `isPureTrace_of_near`, `frobenius_collide_or_repel` |
| Ω3 | Integrality forces purity | FALSE: `exists_impure_integral` |
| Ω4 | Power sums bounded at `N` consecutive orders past an explicit `M₀` certify integral purity; real configurations are never certified at finitely many orders | Lean: `isPureTrace_of_bounded_powerSums`, `eventually_isPureTrace_of_bounded_powerSums`, `not_certified_at_finitely_many_orders`; depth gap `exists_deep_eigenvalue_of_not_pure` |
| Ω5 | An integral structure acts along a deformation path | FALSE: integral continuous families are constant (`eq_of_continuousOn_intCoeff`); survivor below |
| Ω5′ | Uniform repulsion along a continuous real family carries reality, with no integrality | Lean: `splits_of_uniform_repulsion`, `exists_near_collision_of_not_splits` |
| Ω6 | Euler carriers `∏_{p∈S}(1−p^{−s})` collide or repel at polynomial scale | Lean: `eulerCarrier_collide_or_repel` (effective Baker `RHTower.Matveev.effectiveBakerBound_holds`) |
| Ω6′ | Uniform repulsion for Euler carriers | FALSE: `eulerColumns_near_coincidence` (distance `≤ 2π/((n+1)log p')` at height `≤ 2πn/log p`) |
| Ω7 | Rank one (`P(p^{−s})`, `P ∈ ℤ[X]` monic): uniform repulsion; rank two: none | Lean: `onePrime_uniform_repulsion`, `twoPrime_no_uniform_repulsion` |
| Ω8 | A near-coincidence of `ζ` flattens `ζ'`; a lower bound for `|ζ'(ρ)|` gives collide-or-repel at `ρ` | Lean: `norm_deriv_riemannZeta_mul_le_of_near_zero`, `separation_of_norm_deriv_riemannZeta_ge` |
| Ω9 | A finite-prime carrier repels uniformly when its Bohr lift has no tangency consistent with the moduli `|p^{−s}| = p^{−σ}` | Lean: `uniform_repulsion_of_no_consistent_tangency` (compactness of `K[a,b]`); explicit instance `trinomial_uniform_repulsion` (`≥ min(1/4, (log 3 − log 2)/224)`) |
| Ω9″ | Converse: a consistent tangency forces near-coincidences at every scale | Lean for isolated tangencies of finite order `≥ 2`: `exists_zeros_near_tangency`, `exists_collision_or_close_pair` (corpus Kronecker + `HTGeometry.exists_local_zeroSet`); explicit Euler instance `twoPrime_no_uniform_repulsion` |
| Ω9′ | Generic three-prime integral carriers have consistent tangencies, hence near-coincidences at every scale | open (paper sketch: six real equations in six unknowns); for two primes and integer `G` a consistent tangency at a torsion point needs `∇G = 0` there (`log 2/log 3 ∉ ℚ`), e.g. `(1−2^{−s})² − (1−3^{−s})³` |
| Ω10 | Collide or repel at polynomial scale for integral Dirichlet polynomials over a fixed finite prime set | open: needs Baker for inhomogeneous forms with transcendental tangency points |
| Ω11 | B54 for `ζ` | open (RH-independent, sub) |
| Ω12 | Integral pure degree-two Euler carriers collide or repel at polynomial scale | Lean: `pow_twelve_eq_one_of_satake` (Kronecker in degree two), `degTwoCarrier_collide_or_repel` |
| Ω12′ | The same for real pure local data `a = 2cos θ` | FALSE: `real_pure_carrier_not_polynomial_repulsion` (Liouville angle, zeros `e^{−|k|}`-close at height `≍ |k|`) |
| Ω13 | Integral pure Euler carriers of every degree collide or repel at polynomial scale | Lean: `exists_pow_eq_one_of_pure` (Kronecker), `pureCarrier_collide_or_repel` |
| Ω14 | Near-coincidences at every scale need an Euler product | FALSE: the cusp carrier `(1−2^{−s})² − (1−3^{−s})³` has them (`cuspCarrier_collision_or_close_pair`) |
| Ω15 | The depth of an FE pair is read on the line: `|ζ(½+iγ)| ≤ 480e²(|γ|+2)(|γ|+5)δ²`; a lower bound for `|ζ(½+iγ)|` at the ordinate gives a depth gap | Lean: `norm_zeta_center_le_of_offline_zero`, `depth_ge_of_norm_zeta_center_ge` |
| Ω16 | An FE pair of depth `≤ η` makes `|ζ(½+it)| ≲ γ²η²` on a whole interval `|t−γ| ≤ η`, so a small-value measure bound on the line is a depth gap; and depth `≥ |ζ'(ρ)|/(Cγ²)` | Lean: `norm_zeta_line_le_of_offline_zero`, `depth_gt_of_small_value_measure`, `depth_ge_of_norm_deriv`; for an on-line simple zero the flatness is only linear (the statement is false there) |
| Ω17 | Polynomial repulsion of real pure carriers holds for almost every Satake angle | Lean: `ae_inhomogeneous_gap` (Borel–Cantelli), `ae_realPureCarrier_repulsion` (scale `C/T²`); with Ω12′ the failure set is a nonempty null set, so integrality is a certificate against Liouville-type local data, not a generic necessity |
| Ω18 | Two-prime near-coincidences need a singular lift or non-integral coefficients | Lean: the affine carrier `−(log 3 − log 2) + log 3·2^{−s} − log 2·3^{−s}` (smooth tangency at `(1,1)`) has them (`logTrinomial_collision_or_close_pair`); the integer trinomial `1 + 2^{−s} + 3^{−s}` repels uniformly; for integer `G` a torsion tangency is singular since `log 3/log 2 ∉ ℚ` (`lam23_ne_zero`) |
| Ω19 | Every near-coincidence of `ζ` is a joint small value of `(ζ, ζ')` at its midpoint | Lean: `joint_small_values_of_close_zeros` (`|ζ(c)| ≤ K‖h‖²`, `|ζ'(c)| ≤ K‖h‖`); B54 ⇐ emptiness of the joint small-value set — the `ℤ` analogue of the discriminant bound for `(P, P')` |
| Ω20 | Converse of Ω19: joint small values of `(F, F')` with `F''(c)` bounded below force exactly two zeros (with multiplicity) within `r` | Lean: `two_zeros_of_joint_small_values` (third-order Taylor `norm_taylor_two_remainder_le` + corpus Rouché); with Ω19, B54 ⇔ emptiness of the nondegenerate joint small-value set of `(ζ, ζ')` up to constants |
| Ω21 | The finite certificate needs `≳ q^{1/4}` orders | Lean: `quarter_power_mimic` (impure `X − (⌊2√q⌋+1)` passes `|S_ν| ≤ 2e q^{ν/2}` for `9ν⁴ ≤ q`) |
| Ω22 | For algebraic carriers, consistent tangencies at algebraic points are singular points of the Bohr lift (any number of primes) | Lean: `algebraic_tangency_is_singular`, `pderiv_eval_eq_zero_of_algebraic_tangency` (corpus Baker `primeLog_linearForm_transcendental`); generalizes Ω18 |
| Ω23 | The prime Kronecker flow is Diophantine at torsion points: `max_i |p_i^{−it} − u_i| ≥ c(2+|t|)^{−C}` for `|t| ≥ 1` and any roots of unity `u_i` | Lean: `primeFlow_diophantine_at_torsion` — the standalone form of the discreteness the Euler product carries; with a local (Łojasiewicz-type) estimate at a singular torsion tangency it would give Ω10 for algebraic carriers whose tangencies are all torsion |
| Ω24 | A non-product carrier with a torsion cusp collides or repels at polynomial scale near the cusp | Lean: `cusp_local_repulsion` (joint small values + cusp algebra `|b|³ ≲ h²`, `|a|³ ≲ h²` + Ω23); global polynomial repulsion for the cusp carrier also needs its other tangency points `τ` (roots of `(2 log 2 − 3 log 3)τ² + (2 log 2 − 3 log 3)τ + 2 log 2`) to be inconsistent, which is a numerical check |

## No-go closure (deformation half)
- **Exact killing theorem/mechanism:** a continuous family of polynomials with integer coefficients
  on a preconnected parameter set is constant (`eq_of_continuousOn_intCoeff`); uniform repulsion
  along a path already carries reality without integrality (`splits_of_uniform_repulsion`), and its
  hypothesis is the absence of collisions. Limits of integral pure members add nothing beyond
  closedness of purity (`ZeroConfigurationGeometry.isClosed_pure`).
- **Strongest positive survivor:** discreteness of a fixed member quantizes impurity (Ω2) and turns
  approximate purity or a finite-order size bound into exact purity (Ω4); for Euler products the
  discreteness is Diophantine and gives collide-or-repel at polynomial scale, not uniformly (Ω6, Ω7).
- **New insight:** the obstruction to transferring the `𝔽_q` mechanism is the rank of the frequency
  module together with the Euler product: rank one (all frequencies multiples of `log q`) gives
  uniform repulsion from integrality; at rank `≥ 2` near-coincidences occur at every scale exactly
  when the Bohr lift has a tangency consistent with the moduli — the Euler product over `{2, 3}`
  has one, the trinomial `1 + 2^{−s} + 3^{−s}` does not — and then only a transcendence bound in the
  height (Baker) separates them. Integrality of the local Hecke data certifies that the bound
  is polynomial: integral pure Satake parameters are roots of unity (Ω12, Ω13); real ones give
  polynomial repulsion for almost every angle (Ω17) but fail on a Liouville null set (Ω12′). Discreteness amplifies; it never produces purity (fake integral configurations exist in
  every degree).
- **Status:** all survivors formalized (modules above).

## Route analysis
- The `𝔽_q` sketch of §2.4 is not a path mechanism: integrality and continuity cannot coexist
  nontrivially. What integrality does is quantize impurity and make a finite certificate exact.
- For `ζ` the analogue of quantized impurity is a depth gap (B54 restricted to FE pairs); an
  amplifier also needs approximate purity at the gap scale, and the only corpus producer of it is
  window positivity (F6), i.e. Σ. Route Ω therefore reduces to Σ plus B54.
- The form of B54 that the corpus can attack: B54 follows from a polynomial lower bound for `|ζ'|`
  at the zeros (Ω8); for Euler carriers the corresponding statement holds by effective Baker (Ω6).
- A lattice that moves with the parameter does not help: if the cluster symmetric functions lie in
  `λ(t)ℤ` with `λ` continuous, `e_k(t)/λ(t)` is a continuous integer, so the cluster only rescales.
- A Kronecker–Baker mechanism for `ζ`'s own zeros is excluded: integral Arakelov coordinates that
  are Galois-faithful cannot be unitary (`RHTower.not_xiArakelovIntegral_faithful_unitary`), so the
  torsion structure that makes integral pure Euler carriers Baker-accessible (Ω12, Ω13) cannot
  exist on the zeros themselves.
- B54 for FE pairs is a lower-bound problem for `|ζ(½ + it)|` at the positive local minima of `|Z|`
  (Ω15), and B54 in general follows from a lower bound for `|ζ'|` at the zeros (Ω8).
- For `ζ` at height `T` the relevant carrier (approximate functional equation) has rank
  `≍ π(√T)`; the effective Baker exponent grows with the rank, so Diophantine discreteness of the
  Euler-carrier kind cannot give B54 at polynomial scale for `ζ` directly.
- Three scales coincide at height `T`: the camera's unresolved scale `e^{−c log³ T}`, the Liouville
  scale of an integral configuration of degree `≍ log T` and height `T^{O(1)}` (Ω1), and the
  two-logarithm Baker bound `|k log p − k' log p'| ≥ exp(−C log p log p' log H)` for primes up to
  `√T` and heights `H ≤ T` (`exp(−C log³ T)`). The last is not in the corpus (only an existential
  exponent for a fixed prime family); recorded as heuristic.
- At the local complexity of `ζ` at height `T` (degree `≍ log T`, height `T^{O(1)}`), the separation
  integrality could guarantee lies between `e^{−C log³ T}` (Ω1, the camera's unresolved scale) and
  `e^{−c log² T}` (Ω1′).

## Log
- 2026-11-05 — created; Ω1–Ω9″, Ω12, Ω13, Ω15–Ω24 formalized; Ω3, Ω5, Ω6′, Ω12′, Ω14 falsified with
  survivors; Ω9′, Ω10, Ω11 open.
