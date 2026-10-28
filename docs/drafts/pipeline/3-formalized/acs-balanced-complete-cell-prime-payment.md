# Balanced complete-cell prime payment

- **ID:** acs-balanced-complete-cell-prime-payment
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** ACS: source sections → Riemann–Roch and ampleness → Hodge index → RH.
- **Parent:** [acs-complete-cell-haar-effectivity](../1-in-progress/acs-complete-cell-haar-effectivity.md)
- **Statement:** On actual balanced adjacent whole-cell sections, the full signed prime energy has an upper bound with logarithmic coefficient strictly below one and a mass error independent of the support horizon.

## Exact theorem

Let `l_a = logCellWidth (2*a)`, `r_a = logCellWidth (2*a+1)`,
`L_a = r_a/(l_a+r_a)`, `R_a = l_a/(l_a+r_a)`, and `M_a = l_a*r_a/(l_a+r_a)`.
The actual half-line Hilbert vector is
`H_a = L_a • cellAtom (2*a) - R_a • cellAtom (2*a+1)`.
For arbitrary `c : ℕ → ℝ` and `X : ℕ`, put `u = Σ a∈[1,X], c_a H_a`.

Lean proves

```
Σ' m, (2 * vonMangoldt m / sqrt m) * Re ⟪T_(log m) u, u⟫
  ≤ Σ a∈[1,X], (16 + log(2*a+1)/sqrt 2) * M_a * c_a^2.
```

There is no sign restriction on `c`, no assumed analytic estimate, and no discarded prime tail.
Also `1/sqrt 2 < 1`. The full Weil lower bound is a separate open target.

The literal compact BV representative `haarSectionProfile c X` has this same original
`RHTower.primeSum` and square mass `Σ M_a c_a²`. On each pair interval
`(log(2*a), log(2*a+2))`, its integral is zero and its square integral is `M_a c_a²`.
These are checked source identities, not assumptions for subsequent estimates.

## Proof, matched by Lean

1. `L_a l_a = R_a r_a = M_a` and `L_a+R_a=1`. The real Gram matrix is diagonal with diagonal `M_a`, hence the square mass of `u` is `Σ M_a c_a²`.
2. Translating a whole cell by `log m` gives all consecutive successor cells. Across a child pair, a constant parent value cancels because the two child weighted widths equal `M_b`. Only a parent boundary can survive. The two outer parent boundaries have even integer indices; the middle boundary has index `(2*a+1)*m`. Consequently the actual translated real pairing is `M_b` exactly when `(2*a+1)*m=2*b+1`, and zero otherwise. Every even multiplier vanishes.
3. The reciprocal endpoint estimates for logarithmic widths give
   `1/(4*a+3) ≤ M_a ≤ 1/(4*a+1)`. On an incidence edge, `m*M_b ≤ 2*M_a`.
4. Write the directed edge weight as `K_ab = Σ_(2≤m≤2X+1) Λ(m) M_b / sqrt m`, retaining only the exact incidence edges. Outgoing row sums are at most `2*M_a Σ Λ(m)/(m*sqrt m) ≤ 16*M_a`, using the existing unconditional uniform tail estimate. Incoming column sums are at most `M_b log(2*b+1)/sqrt 2`: each multiplier has at most one parent, is a divisor of `2*b+1`, and `Σ_(m|n) Λ(m)=log n`.
5. Apply `2*c_a*c_b ≤ c_a²+c_b²` to each nonnegative edge weight and add the row and column charges. The actual prime series is finite by source support: every term above `2X+1` vanishes. This proves the displayed estimate for the entire series.

## Lean declarations

Namespace: `GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells`.

- `HaarCellPrimeCompression.lean`: `inner_shift_cellAtom_entry`, `haarCoeff_mass`, `re_inner_haarAtom`, `haarMass_bounds`, `haarMass_mul_le`, `inner_shift_haarAtom`, `re_inner_haarSection_self`, `haarPrimeEnergy_eq`, `inner_shift_haarSection_even`.
- `HaarCellPrimeBound.lean`: `haarPrimeMatrix_row_le`, `haarPrimeMatrix_column_le`, `haarPrimeEnergy_matrix`, `haarPrimeEnergy_le`, `haarPrime_log_coefficient_lt_one`.
- `HaarCellProfiles.lean`: `haarSectionProfile_bv`, `haarSectionProfile_compact`, `haarSectionProfile_supported`, `haarPrimeEnergy_eq_primeSum`, `integral_haarSectionProfile_sq`, `setIntegral_haarSectionProfile_pair`, `setIntegral_haarSectionProfile_pair_sq`.
- Reused arithmetic input: `ArithmeticOrientationTheory.sum_Icc_vonMangoldt_div_mul_sqrt_le_eight` and `ArithmeticFunction.vonMangoldt_sum`.

All three exact project files passed `lake --old env lean` without warnings. Fourteen transitive `#print axioms` audits contain only `propext`, `Classical.choice`, and `Quot.sound`. All three modules are imported by the ACS umbrella; the umbrella was not compiled.

## Scope

This discharges the prime estimate for a concrete signed source subspace of complete cells. It does not prove the Gamma lower bound, pole payment, positivity of the full Weil form, or full-source effectivity. Those remain on the parent card. This card went directly from active Lean work to stage 3; no paper-only stage-2 result was parked.

## Log

- 2026-10-28 — Exact actual-source cancellation and the horizon-independent signed prime bound formalized and audited.
