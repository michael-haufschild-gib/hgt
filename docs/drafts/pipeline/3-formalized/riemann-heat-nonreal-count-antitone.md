# The nonreal zero count of the de Bruijn–Newman flow is nonincreasing

- **ID:** riemann-heat-nonreal-count-antitone
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** loop card `1-in-progress/rh-goal-loop-opus-2026-09-29.md`, row 148.
- **Statement:** For `0 < s < t`, the number of nonreal zeros of `H_t` (finite by `riemannHeat_nonreal_zeros_finite`) is at most that of `H_s`, counted with multiplicity.

## Why
`WeilIndexExtinctionTime` reads `Λ` as the extinction time of the Weil index `½N_off(t)`, but `flowIndex_mono` there is arithmetic on a given inequality, and `FinitenessTransition.nonreal_count_mono` assumes antitonicity. No corpus module proves the monotonicity for the actual `riemannHeat`. The statement is RH-blind: it makes the extinction-time reading genuine without bearing on RH.

## Proof plan (paper)
1. **Hermite–Poulain step.** For a real polynomial `p` and `c > 0`, `Z_c(p ∓ cp′) ≤ Z_c(p)`.
   - Apply Rolle to `e^{∓x/c}p`, which vanishes at the real zeros of `p` and at `±∞`.
   - This gives `#ℝ-zeros(p ∓ cp′) ≥ #ℝ-zeros(p)` with multiplicity, and the degree is unchanged.
2. Since `p − ap″ = (1 − √aD)(1 + √aD)p`, the operator `1 − aD²` does not increase `Z_c`.
3. Write `e^{−τD²} = lim (1 − τD²/n)ⁿ`, acting on polynomial approximants of `H_s` that converge locally uniformly. One choice is the Jensen-type truncations of the cosine transform. Apply Hurwitz on a compact region containing all nonreal zeros of `H_t`, which is bounded by Ki–Kim–Lee effective reality plus the strip bound.
4. The semigroup law `H_t = e^{−(t−s)D²}H_s` holds on the transform side: `e^{tx²}` multiplies.

## Lean status
Nothing formal. The likely cost is step 3, the approximation plus uniform zero control; steps 1–2 are short. Reusable corpus pieces: `hasDerivAt_iteratedDeriv_riemannHeat_time`, `iteratedDeriv_riemannHeat_eq` (`DeBruijnLaguerreEvolution`), the Ki–Kim–Lee modules, and `riemannHeat_zeros_im_sq_le`.

## Lean plan for step 1 (checked against this toolchain, row 150)
- **Interleaving.** `Finset.card_le_sdiff_of_interleaved` with Rolle (`exists_hasDerivAt_eq_zero`) on `f(x) = e^{−x/c}p(x)`. Here `f′ = −(1/c)e^{−x/c}(p − cp′)`. This is the pattern of Mathlib's `card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ`.
- **Multiplicities.** `derivative_rootMultiplicity_of_root` and `le_rootMultiplicity_iff` give `rootMultiplicity x (p − C c·p′) ≥ rootMultiplicity x p − 1`.
- **Assembly.** Follow the `calc` of Mathlib's `card_roots_le_derivative`. The result is `card p.roots ≤ card (p − C c·p′).roots + 1`.
- **Extra root by parity.** `RiemannGaussian.realPolynomial_realRoot_card_add_two_mul_upperRoot_card` gives `card(real roots) ≡ natDegree (mod 2)`, and `natDegree (p − C c·p′) = natDegree p` by `natDegree_sub_eq_left_of_natDegree_lt` and `natDegree_derivative_lt`. Still missing: a bridge `card (realPolynomialRealRootMultiset A) = card A.roots`, via `count_map_roots`-type lemmas for the injective `ofReal`.

## Update (row 154): steps 1–2 are formal
`HTGeometry/LaguerreShiftRealRootCount` (STATUS MUST-659):
- `card_roots_le_sub_C_mul_derivative`: `#ℝ-roots(p) ≤ #ℝ-roots(p − cp′)`.
- `card_roots_le_heatStep` and `nonrealCount_heatStep_le` for `p − ap″`, `a > 0`.
- The parity bridge `card_roots_add_two_mul_eq_natDegree`.

Remaining: step 3, i.e. `(1 − τD²/n)ⁿ → e^{−τD²}` on polynomial approximants of `H_s`, plus Hurwitz on a KKL-bounded region.

## Closed (rows 157–160): the entire-function theorem is formal (STATUS MUST-661)
The proof does not use polynomial approximation of `H_s`; it follows row 157's route.

**Modules and main declarations.**
- `HTGeometry/HermiteRealRoots`: `realHermite_roots_nodup_card`. Rolle on Gaussian derivatives, with half-line Rolle via a reparametrisation.
- `HTGeometry/HermiteSignChanges`:
  - `eval_heatPoly_eq`: `Q_k = √2^k Heₖ(·/√2)`, from the explicit Hermite coefficients and `(2m)! = 2^m m!(2m−1)‼`;
  - `exists_heatPoly_sign_changes`.
- `RHTower/DeBruijnHeatForwardModel`: `exists_norm_riemannHeat_sub_heatModelFwd_le`.
- `RHTower/DeBruijnHeatForwardRealZeros`: `exists_real_zeros_forward`, giving `k` distinct real zeros within `qS` of `x₀`.
- `RHTower/DeBruijnNonrealCountLocal`:
  - `tendstoLocallyUniformly_riemannHeat_nhds`;
  - `eventually_zeroSumBall_riemannHeat_eq_of_sphere`;
  - `exists_ball_real_zeros_forward`.
- `RHTower/DeBruijnNonrealCountAntitone`:
  - `sum_le_nonrealZeroCount`;
  - `exists_local_nonrealZeroCount`;
  - `le_of_local_right_and_lsc` (real induction);
  - `nonrealZeroCount_antitoneOn`.

**Audit.** Every module is clean under `lake env lean` and builds with `--old`. Axioms are `propext`, `Classical.choice`, `Quot.sound`. There are 0 collisions and lint is clean. All modules are wired into the HTGeometry/RHTower umbrellas.

**Reading.** RH-blind. It makes `Λ = inf{t > 0 : N(t) = 0}` an actual extinction time of the integer-valued, nonincreasing nonreal count.

## Closed (rows 163–165): finiteness transition at t = 0 (STATUS MUST-664)

If `Ξ` has finitely many nonreal zeros, `K` with multiplicity, then `N(t) ≤ K` for all `t > 0`
(`RHTower.DeBruijn.nonrealZeroCount_le_of_finite_nonreal_zeros`). The plan of row 163 was carried out
without the Hadamard split `Ξ = P·G`. Real approximants are `Ξ(0)∏(1−z/a)` over finite zero sets closed
under `±` and conjugation; they have at most `K` nonreal roots and a uniform Gaussian bound
`|Ξ(0)|exp(2Σ|a|⁻²|z|²)`. Polynomial Gaussian averages are polynomial heat flows (Gaussian moments).
Dominated convergence for `8St < 1`, then Pólya (MUST-663), Hurwitz, and MUST-661 for larger `t`.
Modules: `RHTower/DeBruijnPolynomialGaussianAverage`, `RHTower/DeBruijnNonrealCountApprox`,
`RHTower/DeBruijnNonrealCountFinitenessTransition`; wired into `RHTower.lean`; axioms
`propext, Classical.choice, Quot.sound`.

## Closed (rows 169–170): right-continuity at t = 0 (STATUS MUST-666)

`N(0⁺) = Z_c(Ξ)` in `ℕ ∪ {∞}`. Finite case: `N(t) = K` for all small `t > 0`. Infinite case:
`N(t) → ∞`. Consequences: RH ⟺ `N(t) = 0` for all small `t > 0`, and finitely many off-line zeros ⟺
`sup_{t>0} N(t) < ∞`. Module `RHTower/DeBruijnNonrealCountRightLimit` (wired); axioms standard.
`DeBruijnNonrealCountLocal` now exposes `exists_radius_zeroSumBall_riemannHeat_eq` for `t ≥ 0`, and
`HTGeometry.eventually_ne_zero_on_sphere` takes any filter.
