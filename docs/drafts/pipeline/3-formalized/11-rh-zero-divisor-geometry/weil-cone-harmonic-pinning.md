# Harmonic pinning: the only free scalar of the notch-small Weil cone

- **ID:** MC-183
- **Stage:** 3-formalized (STATUS MUST-619)
- **Type:** THEOREM (Lean)
- **Source:** MC conjecture loop cycle 183; uses MUST-606 (fibre Bochner law) and MUST-614 (nonnegative multiples law)
- **Statement:** A nonnegative full-cone Weil-positive `lam` with notch-small deviation equals `Λ` iff `Σ_n (lam − Λ)(n)/n = 0`. In general `(1+t²)T + tN^{−½}(T + Γ_N) ≤ 0` for every twist `|1 + tN^{iτ}|²`.

## Goal
Cycles 180–182 left two survivor classes:
- balanced semiprime floors with compensating prime deficits, which are notch-small and pass every fixed-prime twist;
- prime deviations of size `Λ`.

The fixed-prime analysis showed that the Bochner constraints can always be absorbed by a sufficiently negative total `T`. This cycle proves the converse sharply: `T` is the only freedom. Once `T = 0`, all notch information vanishes and `d = 0`.

## Paper proof
1. **gcd main weight.** Take `P` = primes of `N`, `A = {0, vec N}`, `c = (1, t)`. The twist norms are `twistNorm(n, 0) = n`, `twistNorm(n, −vec N) = nN` and `twistNorm(n, vec N) = nN/gcd(n,N)²`, by exponents: `|v − g| + 2min(v,g) = v + g`. Hence `√n W(n) = 1 + t² + tN^{−½}(gcd(n,N) + 1)`.
2. **Law.** If the fibre sums `(1+t²)T_k + tN^{−½}(T_k + Γ_k)` converge to `X > 0`, they stay above `X/2`, which contradicts MUST-606.
3. **Pinning.** With `T = 0` and `t = ±1`, `Γ_N = 0`. Since `Γ_N = Σ_{e∣N}φ(e)U_e` (sum over `e ∣ gcd` of `φ(e)`), strong induction gives `U_e = 0` for all `e`.
4. **Inclusion–exclusion.** Let `Z_m(S) = Σ_{k: q∤k ∀q∈S} d(mk)/(mk)`. Then `Z_m(S∪{p}) = Z_m(S) − Z_{mp}(S)` (reindex `k = pj`, using that the primes in `S` do not divide `p`) and `Z_m(∅) = U_m`, so `Z_m(S) = 0`.
5. **Isolation.** For `S` = primes `≤ y`, the terms `2 ≤ k ≤ y` vanish, so `d(e)/e = −(tail over k > y)`, which tends to 0.
6. **Nonnegative case.** `Σ_{e∣n}|d(n)|/n < ∞` for `e ≥ 2` follows from MUST-614 together with `Σ_{p∣n}Λ(n)/n ≤ log p`.

## Lean
- Module `WeilConeHarmonicPinning`:
  - twist norms: `vecNum_mul_vecDen_eq_prod`, `twistNorm_eq_mul_prod`, `twistNorm_zero_eq`, `twistNorm_neg_vecOf_eq`, `twistNorm_vecOf_mul_gcd_sq`, `gcd_eq_prod_min`;
  - gcd twist: `twistMainWeight_gcd_eq`, `sum_gcdTwist_eq`, `le_zero_of_tendsto_gcdTwist`, `nonpos_of_tendsto_harmonicSum`;
  - uniqueness: `mul_gcd_div_eq_sum_totient`, `eq_vonMangoldt_of_harmonicPinning`, `summable_multiples_abs_coneDeviation_of_nonneg`, `eq_vonMangoldt_of_nonneg_of_harmonicPinning`.
- Audit:
  - compiles cleanly with `lake env lean` (olean written with `-o`);
  - `#print axioms` gives the standard three;
  - wired after `WeilConeAsymptoticPrimeSupport`;
  - one rename against `HTGeometry.prod_primeFactors_pow_factorization` (ours is `prod_coe_primeFactors_pow_factorization`);
  - `lake build` deferred: upstream chain invalidated by other agents.

## Open
- **Lower bound `Σ(lam − Λ)/n ≥ 0`.** Weil positivity gives only upper bounds at `s = 1`: the pole budget and `Re H_lam(1) ≥ 0`. A lower bound needs input beyond Weil positivity, or a new test family.
- **Prime deviations of size `Λ`** are not notch-small; they remain the `α ≥ 1` regime.
- **Convergence of `T`.** For notch-small `d` without local mass → 0, the convergence of `T` is assumed.

## Log
- 2026-10-01: created and formalized (cycle 183).
- 2026-10-01: added the criterion `riemannHypothesis_iff_exists_nonneg_harmonicConstant_nonneg`: RH ⟺ ∃ nonnegative full-cone Weil-positive `lam` with notch-small deviation and a convergent harmonic constant `T ≥ 0`. The proof uses `T ≤ 0` plus harmonic pinning. Standard axioms; compiles cleanly.
- 2026-10-01 (cycle 184, STATUS MUST-621): local-mass form.
  - **Generalization:** `WeilOneSided.exists_tendsto_sum_coneDeviation_div_of_localMass` (the `o(Λ)` convergence lemma, now under vanishing local mass; the `o(Λ)` version is a corollary).
  - **New pieces:** `notchSmall_of_localMassTendsZero`, `NotchBounded.mono_level`, `NotchBounded.of_eq_of_ge`; `notchBounded_of_localMassBounded` now gives the level `5M`.
  - **Results:** `exists_harmonicConstant_of_nonneg_of_localMassTendsZero` (`T` exists, `T ≤ 0`, `T = 0 ⇒ lam = Λ`) and `riemannHypothesis_iff_exists_nonneg_localMass_harmonicConstant_nonneg`.
  - **Audit:** all touched modules re-elaborated with `lake env lean -o`, cleanly; standard axioms.
