# Formalization certificate — `ccm-radial-prime-first-row-reduction`

- **Card:** `ccm-radial-prime-first-row-reduction.md`
- **Stage:** 3-formalized
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMRadialPrimeFirstRow.lean`
- **Namespace:** `GaloisForLFunctions.RHTower`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on every declaration
- **Build:** `lake build GaloisForLFunctions.RHTower.CCMRadialPrimeFirstRow` — success

## Certified statements

New in `CCMRadialPrimeFirstRow` (20 theorems / 3 definitions):

- `Icc_one_eq_insert_Icc_two`, `radialPrimeRow_split` — the radial row `1 ≤ j ≤ K` splits as
  first row, diagonal, and strict off-diagonal sector.
- `radialPrimeCharge_split` — equations `(10)`–`(11)`: for an arbitrary Gram array and arbitrary
  prime weight, the raw charge `−2 ∑_{k=2}^K a(k) ∑_{j=1}^K G(j,k)` equals
  `D_{λ,K} + E_{λ,K} + N_{λ,K}` exactly.
- `truncatedVonMangoldtCharge`, `truncatedVonMangoldtCharge_nonneg`,
  `truncatedVonMangoldtCharge_le_log` — the exact finite-aperture weight
  `a_λ(k) = ∑_{q ∣ k, 2 ≤ q ≤ λ²} Λ(q)` is nonnegative and dominated by `log k`; this is the
  domination hypothesis that carries `(12)`–`(13)` to the exact finite aperture.
- `radialLimitPhase`, `hasDerivAt_radialLimitPhase`, `hasDerivAt_radialLimitPhase_scaled` —
  equation `(6)`, `d/dx ξ_∞(k x) = k² x/√(k²x²−1)`.
- `radialDiffPhaseDeriv`, `hasDerivAt_radialDiffPhase` — the difference phase and its derivative.
- `radialCoalescePoint`, `radialCoalescePoint_sq`, `one_lt_radialCoalescePoint`,
  `radialDiffPhaseDeriv_coalescePoint`, `radialDiffPhaseDeriv_eq_zero_iff` — equation `(15)`:
  `x_k = √(1 + 1/k²)` is a stationary point of `ξ_∞(x) − ξ_∞(kx)` and, on the radial exterior
  `x > 1`, the **only** one.
- `radialLimitPhase_coalescePoint`, `radialLimitPhase_scaled_coalescePoint`,
  `hasDerivAt_radialLimitPhaseDeriv`, `hasDerivAt_radialLimitPhaseDeriv_scaled`,
  `hasDerivAt_radialDiffPhaseDeriv`, `radialDiffPhase_secondDeriv_coalescePoint` — equation `(20)`:
  `ρ(x_k) = 1/k`, `ρ(k x_k) = k`, and the second derivative of the difference phase at `x_k` is
  exactly `−(k³ − 1/k)`.
- `tendsto_radialCoalescePoint`, `tendsto_radialCoalesceRate` — equation `(16)`:
  `k²(x_k − 1) → 1/2`, i.e. `x_k − 1 ∼ 1/(2k²)`, the coalescence rate that puts the stationary
  point at the endpoint scale exactly when `k ≍ c`.

Reused from the existing tree, not rebuilt:

- `GaloisForLFunctions.constrainedProlate_sum_vonMangoldt_divisors_ge_two` — the divisor identity
  `(3)`.
- `RHTower.radialRowSum_le`, `RHTower.rowBound_le`, `RHTower.summable_weighted_rowMajorant`,
  `RHTower.summable_weighted_rowBound` (`RadialGramOffDiagonalDecay`) — the Hilbert-kernel row
  estimate `(8)` and the weighted sector convergence `(9)`.
- `radialPhaseDeriv_critical`, `radialPhaseSecondDeriv_critical` (`CCMLimitingRadialWeber`) —
  the exterior Weber critical point and curvature `(23f)`.
- `constrainedProlatePrimeSeriesTerm` and its summability (`ConstrainedProlateExteriorWeil`) —
  the diagonal limit series of `(12)`.

## Deliberately outside the Lean statement

Dunster's uniform radial Liouville–Green expansion `(5)` with differentiated Olver remainders; the
phase-preserving nonstationary Gram bound `(4)`/`(7)`; one-dimensional stationary phase and the
estimates `(21)`–`(24)`, `(23d)`; the Weber Gaussian–Bessel transform `(23b)` with Abel
continuation; the exact PSWF remainder transfer.  All are cited parents of the card.
