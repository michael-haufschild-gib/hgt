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
| Ω9 | Generic two-prime integral Dirichlet polynomials repel uniformly (no tangency in the Bohr closure: four real tangency equations, three parameters); generic three-prime ones do not | open (paper sketch only) |
| Ω10 | Collide or repel at polynomial scale for integral Dirichlet polynomials over a fixed finite prime set | open: needs Baker for inhomogeneous forms with transcendental tangency points |
| Ω11 | B54 for `ζ` | open (RH-independent, sub) |

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
  module: rank one (all frequencies multiples of `log q`) gives uniform repulsion from integrality;
  rank `≥ 2` forces near-coincidences at every scale by Kronecker density, and only a transcendence
  bound in the height (Baker) separates them. Discreteness amplifies; it never produces purity
  (fake integral configurations exist in every degree).
- **Status:** all survivors formalized (modules above).

## Route analysis
- The `𝔽_q` sketch of §2.4 is not a path mechanism: integrality and continuity cannot coexist
  nontrivially. What integrality does is quantize impurity and make a finite certificate exact.
- For `ζ` the analogue of quantized impurity is a depth gap (B54 restricted to FE pairs); an
  amplifier also needs approximate purity at the gap scale, and the only corpus producer of it is
  window positivity (F6), i.e. Σ. Route Ω therefore reduces to Σ plus B54.
- The form of B54 that the corpus can attack: B54 follows from a polynomial lower bound for `|ζ'|`
  at the zeros (Ω8); for Euler carriers the corresponding statement holds by effective Baker (Ω6).
- At the local complexity of `ζ` at height `T` (degree `≍ log T`, height `T^{O(1)}`), the separation
  integrality could guarantee lies between `e^{−C log³ T}` (Ω1, the camera's unresolved scale) and
  `e^{−c log² T}` (Ω1′).

## Log
- 2026-11-05 — created; Ω1–Ω8 formalized; Ω3, Ω5, Ω6′ falsified with survivors; Ω9, Ω10 open.
