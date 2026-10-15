/-
Copyright (c) 2026 Michael. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GaloisForLFunctions.RHTower.WeilLevyThirdWindowDoubleTransport

/-!
# Weil–Lévy Fifth-Window Two-Step Double-Collar Core Transport & Positivity on `(0, 9 / 22)`

In `WeilLevyThirdWindowDoubleTransport.lean` (Cycle 72), we introduced the **Double-Collar Core
Transport** mechanism on `x ∈ [L / 3, L / 2]`, where the central core `Ioc x (L - x)` has length
`L - 2 * x ≤ x` and is reached in one step from **both** collars simultaneously, proving
`D_h(x) ≥ (24 / 41) * ∫ h²` (within `0.00042` of `2 - √2 ≈ 0.585786`) and establishing
unconditional `WindowPositive` on `(0, 2 / 5)` (`= (0, 0.40)`, `57.71%` of `(0, log 2)`).

In this file, we extend the double-collar core transport mechanism to **odd multi-step chains** on
`x ∈ [L / 5, L / 4]` (`m = 5`, where the path-graph spectral floor is
`2 - 2 * cos(π / 6) = 2 - √3 ≈ 0.267949`):

1. **Two-Step Double-Collar Core Transport on `[L / 5, L / 4]` (`4 / 15 ≈ 0.266667`, within
   `0.00128` of `2 - √3 ≈ 0.267949` and `+37.1%` stronger than `7 / 36 ≈ 0.194444`)**:
   On `x ∈ [L / 5, L / 4]`, the core `Ioc x (L - x)` decomposes into three disjoint layers:
   `Ioc x (2 * x)`, the central core `Ioc (2 * x) (L - 2 * x)` (of length `L - 4 * x ≥ 0`), and
   `Ioc (L - 2 * x) (L - x)`. Because `x ≥ L / 5 ⇔ L - 3 * x ≤ 2 * x`, the four shift intervals
   - `J_{L,1} = Ioc 0 x` (shifting by `+x` onto `Ioc x (2 * x)`),
   - `J_{L,2} = Ioc x (L - 3 * x) ⊆ Ioc x (2 * x)` (shifting by `+x` onto the **entire** central
     core `Ioc (2 * x) (L - 2 * x)`),
   - `J_{R,2} = Ioc (2 * x) (L - 2 * x)` (shifting by `+x` onto
     `Ioc (3 * x) (L - x) ⊆ Ioc (L - 2 * x) (L - x)`), and
   - `J_{R,1} = Ioc (L - 2 * x) (L - x)` (shifting by `+x` onto `Ioc (L - x) L`)
   satisfy `0 ≤ x ≤ L - 3 * x ≤ 2 * x ≤ L - 2 * x ≤ L - x` and are **pairwise disjoint** inside
   `Ioc 0 (L - x)`!
   Using the Pell-convergent (`26 / 15 ≈ √3`, `15 / 13 ≈ 2 / √3`) SOS identities
   `(p - q)² - ((11 / 26) * p² - (11 / 15) * q²) = (15 / 26) * (p - (26 / 15) * q)² ≥ 0`,
   `(p - q)² - ((2 / 15) * p² - (2 / 13) * q²) = (13 / 15) * (p - (15 / 13) * q)² ≥ 0`,
   gives collar weight `1 - 11 / 15 = 4 / 15`, first interior layer weight
   `11 / 26 - 2 / 13 = 7 / 26 = 105 / 390 ≥ 104 / 390 = 4 / 15`, and central core weight
   `2 * (2 / 15) = 4 / 15` (counted **twice**!), proving:
   `(4 / 15) * ∫ u, h u ^ 2 ≤ ∫ u, (h u - h (u + x)) ^ 2` for **all** `x ≥ L / 5`.

2. **Sharpened `(0, log 2)` Plastic Floor and Eight-Point Reflected Potential**:
   Splitting `(L / 6, L / 4)` into `(L / 6, L / 5)` (weight `7 / 72`) and `(L / 5, L / 4)` (weight
   `2 / 15`) reduces the universal constant deficit on `(0, log 2)` from `-0.0258` down to
   **`-0.0221`**, and yields the eight-point reflected potential with weights
   `(3/50, 67/1800, 13/360, 2/35, 88/861, 17/41, 88/861, 4/21)` at
   `(L/8, L/6, L/5, L/4, L/3, L/2, 2L/3, c)`.

3. **Unconditional Archimedean Weil Positivity on `(0, 9 / 22)` (`59.02%` of `(0, log 2)`),
   `(0, 11 / 27)`, and `(0, 13 / 32)`**:
   Evaluating the eight-point potential at `L = 9 / 22` (`≈ 0.409091`) proves unconditional
   `WindowPositive` on `(0, 9 / 22)` (`59.02%` of `(0, log 2)`), `(0, 11 / 27)`, and `(0, 13 / 32)`.
-/

open MeasureTheory Set Filter Real
open scoped Topology
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.QuantileTransport

namespace RHTower.WeilLevyFifthWindow

noncomputable section

open WeilLevyPole RHTower.NonnegativeCone RHTower.WeilLevyPoleGauss
open RHTower.WeilLevyCoshCrossover RHTower.WeilLevyBoundaryEscape
open RHTower.WeilLevyCollarCoupling RHTower.WeilLevyOsculatingFloor
open RHTower.WeilLevyQuarterWindow RHTower.WeilLevySymmetricThreePoint
open RHTower.WeilLevySixthWindow RHTower.WeilLevyFibonacciStaircase
open RHTower.WeilLevyEighthWindow RHTower.WeilLevyThirdWindow

/-! ## Section 1: Exact Two-Step Double-Collar Core Transport on `[L / 5, L / 4]` (`4 / 15`) -/

/-- **First-Step Pell-Convergent (`26 / 15 ≈ √3`) SOS Identity**:
for all `p, q : ℝ`, `(11 / 26) * p² - (11 / 15) * q² ≤ (p - q)²`, with exact remainder
`(15 / 26) * (p - (26 / 15) * q)² ≥ 0`. -/
theorem eleven_twenty_sixths_sq_sub_eleven_fifteenths_sq_le_sub_sq (p q : ℝ) :
    (11 / 26 : ℝ) * p ^ 2 - (11 / 15 : ℝ) * q ^ 2 ≤ (p - q) ^ 2 := by
  have h : 0 ≤ (15 / 26 : ℝ) * (p - (26 / 15 : ℝ) * q) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  linarith [show (p - q) ^ 2 - ((11 / 26 : ℝ) * p ^ 2 - (11 / 15 : ℝ) * q ^ 2) =
    (15 / 26 : ℝ) * (p - (26 / 15 : ℝ) * q) ^ 2 by ring]

/-- **Second-Step Double-Transport (`15 / 13 ≈ 2 / √3`) SOS Identity**:
for all `p, q : ℝ`, `(2 / 15) * p² - (2 / 13) * q² ≤ (p - q)²`, with exact remainder
`(13 / 15) * (p - (15 / 13) * q)² ≥ 0`. -/
theorem two_fifteenths_sq_sub_two_thirteenths_sq_le_sub_sq (p q : ℝ) :
    (2 / 15 : ℝ) * p ^ 2 - (2 / 13 : ℝ) * q ^ 2 ≤ (p - q) ^ 2 := by
  have h : 0 ≤ (13 / 15 : ℝ) * (p - (15 / 13 : ℝ) * q) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  linarith [show (p - q) ^ 2 - ((2 / 15 : ℝ) * p ^ 2 - (2 / 13 : ℝ) * q ^ 2) =
    (13 / 15 : ℝ) * (p - (15 / 13 : ℝ) * q) ^ 2 by ring]

/-- **First-Step Forward Transport (`Ioc u₀ (u₀ + ℓ) → Ioc (u₀ + x) (u₀ + ℓ + x)`)**:
`(11 / 26) * ∫_{Ioc (u₀ + x) (u₀ + ℓ + x)} h² - (11 / 15) * ∫_{Ioc u₀ (u₀ + ℓ)} h²`
`≤ ∫_{u ∈ Ioc u₀ (u₀ + ℓ)} (h u - h (u + x))²`. -/
theorem eleven_twenty_sixths_shift_sub_le_setIntegral_Ioc {A : Set ℝ} {h : ℝ → ℝ}
    {C : ℝ} (hh : BddSupp A h C) (u₀ ℓ x : ℝ) :
    (11 / 26 : ℝ) * (∫ u in Ioc (u₀ + x) (u₀ + ℓ + x), h u ^ 2) -
        (11 / 15 : ℝ) * (∫ u in Ioc u₀ (u₀ + ℓ), h u ^ 2) ≤
      ∫ u in Ioc u₀ (u₀ + ℓ), (h u - h (u + x)) ^ 2 := by
  have h2 : Integrable (fun u => h u ^ 2) volume := hh.integrable_sq
  have h2_shift : Integrable (fun u => h (u + x) ^ 2) volume :=
    h2.comp_add_right x
  have hjump : Integrable (fun u => (h u - h (u + x)) ^ 2) volume := by
    have hdiff : (fun u => (h u - h (u + x)) ^ 2) =
        fun u => h u ^ 2 + h (u + x) ^ 2 - 2 * (h u * h (u + x)) := by
      ext u; ring
    rw [hdiff]
    exact (h2.add h2_shift).sub ((hh.integrable_mul_shift x).const_mul 2)
  have hshift_eq : (∫ u in Ioc u₀ (u₀ + ℓ), h (u + x) ^ 2) =
      ∫ u in Ioc (u₀ + x) (u₀ + ℓ + x), h u ^ 2 :=
    setIntegral_Ioc_add_right (fun v => h v ^ 2) u₀ (u₀ + ℓ) x
  rw [← hshift_eq, ← integral_const_mul, ← integral_const_mul,
    ← integral_sub (h2_shift.integrableOn.const_mul _) (h2.integrableOn.const_mul _)]
  exact setIntegral_mono_on
    ((h2_shift.integrableOn.const_mul _).sub (h2.integrableOn.const_mul _))
    hjump.integrableOn measurableSet_Ioc fun u _ => by
      have hpt := eleven_twenty_sixths_sq_sub_eleven_fifteenths_sq_le_sub_sq (h (u + x)) (h u)
      linarith [show (h u - h (u + x)) ^ 2 = (h (u + x) - h u) ^ 2 by ring]

/-- **First-Step Backward Transport (`Ioc (u₀ + x) (u₀ + ℓ + x) → Ioc u₀ (u₀ + ℓ)`)**:
`(11 / 26) * ∫_{Ioc u₀ (u₀ + ℓ)} h² - (11 / 15) * ∫_{Ioc (u₀ + x) (u₀ + ℓ + x)} h²`
`≤ ∫_{u ∈ Ioc u₀ (u₀ + ℓ)} (h u - h (u + x))²`. -/
theorem eleven_twenty_sixths_base_sub_le_setIntegral_Ioc {A : Set ℝ} {h : ℝ → ℝ}
    {C : ℝ} (hh : BddSupp A h C) (u₀ ℓ x : ℝ) :
    (11 / 26 : ℝ) * (∫ u in Ioc u₀ (u₀ + ℓ), h u ^ 2) -
        (11 / 15 : ℝ) * (∫ u in Ioc (u₀ + x) (u₀ + ℓ + x), h u ^ 2) ≤
      ∫ u in Ioc u₀ (u₀ + ℓ), (h u - h (u + x)) ^ 2 := by
  have h2 : Integrable (fun u => h u ^ 2) volume := hh.integrable_sq
  have h2_shift : Integrable (fun u => h (u + x) ^ 2) volume :=
    h2.comp_add_right x
  have hjump : Integrable (fun u => (h u - h (u + x)) ^ 2) volume := by
    have hdiff : (fun u => (h u - h (u + x)) ^ 2) =
        fun u => h u ^ 2 + h (u + x) ^ 2 - 2 * (h u * h (u + x)) := by
      ext u; ring
    rw [hdiff]
    exact (h2.add h2_shift).sub ((hh.integrable_mul_shift x).const_mul 2)
  have hshift_eq : (∫ u in Ioc u₀ (u₀ + ℓ), h (u + x) ^ 2) =
      ∫ u in Ioc (u₀ + x) (u₀ + ℓ + x), h u ^ 2 :=
    setIntegral_Ioc_add_right (fun v => h v ^ 2) u₀ (u₀ + ℓ) x
  rw [← hshift_eq, ← integral_const_mul, ← integral_const_mul,
    ← integral_sub (h2.integrableOn.const_mul _) (h2_shift.integrableOn.const_mul _)]
  exact setIntegral_mono_on
    ((h2.integrableOn.const_mul _).sub (h2_shift.integrableOn.const_mul _))
    hjump.integrableOn measurableSet_Ioc fun u _ =>
      eleven_twenty_sixths_sq_sub_eleven_fifteenths_sq_le_sub_sq (h u) (h (u + x))

/-- **Second-Step Left-to-Center Transport (`Ioc x (L - 3 * x) → Ioc (2 * x) (L - 2 * x)`)**:
for `x ≥ L / 5` (so `L - 3 * x ≤ 2 * x`), shifting `Ioc x (L - 3 * x) ⊆ Ioc x (2 * x)`
by `+x` onto the **entire** central core `Ioc (2 * x) (L - 2 * x)` yields:
`(2 / 15) * ∫_{Ioc (2 * x) (L - 2 * x)} h² - (2 / 13) * ∫_{Ioc x (2 * x)} h²`
`≤ ∫_{u ∈ Ioc x (L - 3 * x)} (h u - h (u + x))²`. -/
theorem left_layer_central_core_transport_le_setIntegral_Ioc {A : Set ℝ} {h : ℝ → ℝ}
    {C L x : ℝ} (hh : BddSupp A h C) (hL5 : L / 5 ≤ x) :
    (2 / 15 : ℝ) * (∫ u in Ioc (2 * x) (L - 2 * x), h u ^ 2) -
        (2 / 13 : ℝ) * (∫ u in Ioc x (2 * x), h u ^ 2) ≤
      ∫ u in Ioc x (L - 3 * x), (h u - h (u + x)) ^ 2 := by
  have h2 : Integrable (fun u => h u ^ 2) volume := hh.integrable_sq
  have h2_shift : Integrable (fun u => h (u + x) ^ 2) volume :=
    h2.comp_add_right x
  have hjump : Integrable (fun u => (h u - h (u + x)) ^ 2) volume := by
    have hdiff : (fun u => (h u - h (u + x)) ^ 2) =
        fun u => h u ^ 2 + h (u + x) ^ 2 - 2 * (h u * h (u + x)) := by
      ext u; ring
    rw [hdiff]
    exact (h2.add h2_shift).sub ((hh.integrable_mul_shift x).const_mul 2)
  have hshift_eq : (∫ u in Ioc x (L - 3 * x), h (u + x) ^ 2) =
      ∫ u in Ioc (2 * x) (L - 2 * x), h u ^ 2 := by
    have h1 := setIntegral_Ioc_add_right (fun v => h v ^ 2) x (L - 3 * x) x
    rw [show x + x = 2 * x by ring, show L - 3 * x + x = L - 2 * x by ring] at h1
    exact h1
  have hsub_le : (∫ u in Ioc x (L - 3 * x), h u ^ 2) ≤ ∫ u in Ioc x (2 * x), h u ^ 2 :=
    setIntegral_mono_set h2.integrableOn
      (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall (Ioc_subset_Ioc le_rfl (by linarith)))
  have hpt : (2 / 15 : ℝ) * (∫ u in Ioc x (L - 3 * x), h (u + x) ^ 2) -
      (2 / 13 : ℝ) * (∫ u in Ioc x (L - 3 * x), h u ^ 2) ≤
      ∫ u in Ioc x (L - 3 * x), (h u - h (u + x)) ^ 2 := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub (h2_shift.integrableOn.const_mul _) (h2.integrableOn.const_mul _)]
    exact setIntegral_mono_on
      ((h2_shift.integrableOn.const_mul _).sub (h2.integrableOn.const_mul _))
      hjump.integrableOn measurableSet_Ioc fun u _ => by
        have hstep := two_fifteenths_sq_sub_two_thirteenths_sq_le_sub_sq (h (u + x)) (h u)
        linarith [show (h u - h (u + x)) ^ 2 = (h (u + x) - h u) ^ 2 by ring]
  rw [hshift_eq] at hpt
  linarith

/-- **Second-Step Center-to-Right Transport (`Ioc (2 * x) (L - 2 * x) → Ioc (3 * x) (L - x)`)**:
for `x ≥ L / 5` (so `L - 2 * x ≤ 3 * x`), shifting the **entire** central core
`Ioc (2 * x) (L - 2 * x)` by `+x` onto `Ioc (3 * x) (L - x) ⊆ Ioc (L - 2 * x) (L - x)` yields:
`(2 / 15) * ∫_{Ioc (2 * x) (L - 2 * x)} h² - (2 / 13) * ∫_{Ioc (L - 2 * x) (L - x)} h²`
`≤ ∫_{u ∈ Ioc (2 * x) (L - 2 * x)} (h u - h (u + x))²`. -/
theorem central_core_right_layer_transport_le_setIntegral_Ioc {A : Set ℝ} {h : ℝ → ℝ}
    {C L x : ℝ} (hh : BddSupp A h C) (hL5 : L / 5 ≤ x) :
    (2 / 15 : ℝ) * (∫ u in Ioc (2 * x) (L - 2 * x), h u ^ 2) -
        (2 / 13 : ℝ) * (∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) ≤
      ∫ u in Ioc (2 * x) (L - 2 * x), (h u - h (u + x)) ^ 2 := by
  have h2 : Integrable (fun u => h u ^ 2) volume := hh.integrable_sq
  have h2_shift : Integrable (fun u => h (u + x) ^ 2) volume :=
    h2.comp_add_right x
  have hjump : Integrable (fun u => (h u - h (u + x)) ^ 2) volume := by
    have hdiff : (fun u => (h u - h (u + x)) ^ 2) =
        fun u => h u ^ 2 + h (u + x) ^ 2 - 2 * (h u * h (u + x)) := by
      ext u; ring
    rw [hdiff]
    exact (h2.add h2_shift).sub ((hh.integrable_mul_shift x).const_mul 2)
  have hshift_eq : (∫ u in Ioc (2 * x) (L - 2 * x), h (u + x) ^ 2) =
      ∫ u in Ioc (3 * x) (L - x), h u ^ 2 := by
    have h1 := setIntegral_Ioc_add_right (fun v => h v ^ 2) (2 * x) (L - 2 * x) x
    rw [show 2 * x + x = 3 * x by ring, show L - 2 * x + x = L - x by ring] at h1
    exact h1
  have hsub_le : (∫ u in Ioc (3 * x) (L - x), h u ^ 2) ≤
      ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2 :=
    setIntegral_mono_set h2.integrableOn
      (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall (Ioc_subset_Ioc (by linarith) le_rfl))
  have hpt : (2 / 15 : ℝ) * (∫ u in Ioc (2 * x) (L - 2 * x), h u ^ 2) -
      (2 / 13 : ℝ) * (∫ u in Ioc (2 * x) (L - 2 * x), h (u + x) ^ 2) ≤
      ∫ u in Ioc (2 * x) (L - 2 * x), (h u - h (u + x)) ^ 2 := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub (h2.integrableOn.const_mul _) (h2_shift.integrableOn.const_mul _)]
    exact setIntegral_mono_on
      ((h2.integrableOn.const_mul _).sub (h2_shift.integrableOn.const_mul _))
      hjump.integrableOn measurableSet_Ioc fun u _ =>
        two_fifteenths_sq_sub_two_thirteenths_sq_le_sub_sq (h u) (h (u + x))
  rw [hshift_eq] at hpt
  linarith

/-- **Four-Slice Disjoint Interior Jump Bound on `Ioc 0 (L - x)` (`x ∈ [L / 5, L / 4]`)**:
for `0 ≤ x` and `L / 5 ≤ x ≤ L / 4`, the four intervals `Ioc 0 x`, `Ioc x (L - 3 * x)`,
`Ioc (2 * x) (L - 2 * x)`, and `Ioc (L - 2 * x) (L - x)` satisfy
`0 ≤ x ≤ L - 3 * x ≤ 2 * x ≤ L - 2 * x ≤ L - x` and are pairwise disjoint inside `Ioc 0 (L - x)`. -/
theorem disjoint_two_step_double_transport_slices_le_interior_jump_sq
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C)
    (_hx0 : 0 ≤ x) (hL5 : L / 5 ≤ x) (hx4 : x ≤ L / 4) :
    (∫ u in Ioc 0 x, (h u - h (u + x)) ^ 2) +
        (∫ u in Ioc x (L - 3 * x), (h u - h (u + x)) ^ 2) +
        (∫ u in Ioc (2 * x) (L - 2 * x), (h u - h (u + x)) ^ 2) +
        (∫ u in Ioc (L - 2 * x) (L - x), (h u - h (u + x)) ^ 2) ≤
      ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 := by
  have h2 : Integrable (fun u => h u ^ 2) volume := hh.integrable_sq
  have h2_shift : Integrable (fun u => h (u + x) ^ 2) volume :=
    h2.comp_add_right x
  have hjump : Integrable (fun u => (h u - h (u + x)) ^ 2) volume := by
    have hdiff : (fun u => (h u - h (u + x)) ^ 2) =
        fun u => h u ^ 2 + h (u + x) ^ 2 - 2 * (h u * h (u + x)) := by
      ext u; ring
    rw [hdiff]
    exact (h2.add h2_shift).sub ((hh.integrable_mul_shift x).const_mul 2)
  set S1 := Ioc 0 x
  set S2 := Ioc x (L - 3 * x)
  set S3 := Ioc (2 * x) (L - 2 * x)
  set S4 := Ioc (L - 2 * x) (L - x)
  have hd12 : Disjoint S1 S2 :=
    disjoint_left.mpr fun u hu1 hu2 => not_lt_of_ge hu1.2 hu2.1
  have hd12_3 : Disjoint (S1 ∪ S2) S3 := by
    rw [disjoint_union_left]
    exact ⟨disjoint_left.mpr fun u hu1 hu3 => by linarith [hu1.2, hu3.1],
      disjoint_left.mpr fun u hu2 hu3 => by linarith [hu2.2, hu3.1]⟩
  have hd123_4 : Disjoint (S1 ∪ S2 ∪ S3) S4 := by
    rw [disjoint_union_left, disjoint_union_left]
    exact ⟨⟨disjoint_left.mpr fun u hu1 hu4 => by linarith [hu1.2, hu4.1],
      disjoint_left.mpr fun u hu2 hu4 => by linarith [hu2.2, hu4.1]⟩,
      disjoint_left.mpr fun u hu3 hu4 => not_lt_of_ge hu3.2 hu4.1⟩
  have hsub : S1 ∪ S2 ∪ S3 ∪ S4 ⊆ Ioc 0 (L - x) := by
    intro u hu
    rcases hu with ((hu | hu) | hu) | hu
    · exact ⟨hu.1, by linarith [hu.2]⟩
    · exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    · exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    · exact ⟨by linarith [hu.1], hu.2⟩
  have hmono : (∫ u in S1 ∪ S2 ∪ S3 ∪ S4, (h u - h (u + x)) ^ 2) ≤
      ∫ u in Ioc 0 (L - x), (h u - h (u + x)) ^ 2 :=
    setIntegral_mono_set hjump.integrableOn
      (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall hsub)
  have hI12 : IntegrableOn (fun u => (h u - h (u + x)) ^ 2) (S1 ∪ S2) :=
    hjump.integrableOn
  have hI123 : IntegrableOn (fun u => (h u - h (u + x)) ^ 2) (S1 ∪ S2 ∪ S3) :=
    hjump.integrableOn
  rw [setIntegral_union hd123_4 measurableSet_Ioc hI123 hjump.integrableOn,
    setIntegral_union hd12_3 measurableSet_Ioc hI12 hjump.integrableOn,
    setIntegral_union hd12 measurableSet_Ioc hjump.integrableOn hjump.integrableOn] at hmono
  exact hmono

/-- **Three-Layer Decomposition of `coreMass` (`x ≤ L / 4`)**:
for `0 ≤ x` and `x ≤ L / 4`, `Ioc x (L - x)` splits into the three disjoint layers
`Ioc x (2 * x)`, `Ioc (2 * x) (L - 2 * x)`, and `Ioc (L - 2 * x) (L - x)`:
`coreMass h L x = ∫_{Ioc x (2 * x)} h² + ∫_{Ioc (2 * x) (L - 2 * x)} h² + ∫_{Ioc (L - 2 * x) (L - x)} h²`. -/
theorem coreMass_eq_three_layers {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hx0 : 0 ≤ x) (hx4 : x ≤ L / 4) :
    coreMass h L x =
      (∫ u in Ioc x (2 * x), h u ^ 2) +
        (∫ u in Ioc (2 * x) (L - 2 * x), h u ^ 2) +
        ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2 := by
  have h2 : Integrable (fun u => h u ^ 2) volume := hh.integrable_sq
  unfold coreMass
  have h12 : x ≤ 2 * x := by linarith
  have h2_L2 : 2 * x ≤ L - 2 * x := by linarith
  have hL2_L1 : L - 2 * x ≤ L - x := by linarith
  have hd12 : Disjoint (Ioc x (2 * x)) (Ioc (2 * x) (L - 2 * x)) :=
    disjoint_left.mpr fun u hu1 hu2 => not_lt_of_ge hu1.2 hu2.1
  have hd12_3 : Disjoint (Ioc x (2 * x) ∪ Ioc (2 * x) (L - 2 * x))
      (Ioc (L - 2 * x) (L - x)) := by
    rw [Ioc_union_Ioc_eq_Ioc h12 h2_L2]
    exact disjoint_left.mpr fun u hu1 hu2 => not_lt_of_ge hu1.2 hu2.1
  have hunion : Ioc x (2 * x) ∪ Ioc (2 * x) (L - 2 * x) ∪ Ioc (L - 2 * x) (L - x) =
      Ioc x (L - x) := by
    rw [Ioc_union_Ioc_eq_Ioc h12 h2_L2, Ioc_union_Ioc_eq_Ioc (by linarith) hL2_L1]
  rw [← hunion,
    setIntegral_union hd12_3 measurableSet_Ioc h2.integrableOn h2.integrableOn,
    setIntegral_union hd12 measurableSet_Ioc h2.integrableOn h2.integrableOn]

/-- **Fifth-Window Two-Step Double-Transport Coercivity (`D_h(x) ≥ (4 / 15) * ∫ h²` for `x ≥ L / 5`)**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L ≥ 0`) and any `x ≥ L / 5`,
`(4 / 15) * ∫ u, h u ^ 2 ≤ ∫ u, (h u - h (u + x)) ^ 2`.
Note `4 / 15 ≈ 0.266667` is within `0.00128` of the spectral limit
`2 - 2 * cos(π / 6) = 2 - √3 ≈ 0.267949` and improves on the sixth-window constant
`7 / 36 ≈ 0.194444` by `+37.1%`. -/
theorem four_fifteenths_mul_integral_sq_le_integral_jump_sq_of_fifth_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL : 0 ≤ L) (hx : L / 5 ≤ x) :
    (4 / 15 : ℝ) * (∫ u, h u ^ 2) ≤ ∫ u, (h u - h (u + x)) ^ 2 := by
  rcases le_or_gt x (L / 4) with hx4 | hx4
  · have hx0 : 0 ≤ x := by linarith
    have hx2 : x ≤ L / 2 := by linarith
    have h2 : Integrable (fun u => h u ^ 2) volume := hh.integrable_sq
    have hcol_int := collarMass_add_interior_le_integral_jump_sq hh hsupp hx0 le_rfl
    have hcons := collarMass_add_coreMass_eq hh hx2
    have hcore := coreMass_eq_three_layers hh hx0 hx4
    have hdisj := disjoint_two_step_double_transport_slices_le_interior_jump_sq hh hx0 hx hx4
    have hsub_L : (∫ u in Ioc 0 x, h u ^ 2) ≤ ∫ u in Iic x, h u ^ 2 :=
      setIntegral_mono_set h2.integrableOn (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall fun u hu => hu.2)
    have hsub_R : (∫ u in Ioc (L - x) L, h u ^ 2) ≤ ∫ u in Ioi (L - x), h u ^ 2 :=
      setIntegral_mono_set h2.integrableOn (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall fun u hu => hu.1)
    have hL1 : (11 / 26 : ℝ) * (∫ u in Ioc x (2 * x), h u ^ 2) -
        (11 / 15 : ℝ) * (∫ u in Iic x, h u ^ 2) ≤
        ∫ u in Ioc 0 x, (h u - h (u + x)) ^ 2 := by
      have h1 := eleven_twenty_sixths_shift_sub_le_setIntegral_Ioc hh 0 x x
      rw [zero_add, show x + x = 2 * x by ring] at h1
      linarith
    have hR1 : (11 / 26 : ℝ) * (∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2) -
        (11 / 15 : ℝ) * (∫ u in Ioi (L - x), h u ^ 2) ≤
        ∫ u in Ioc (L - 2 * x) (L - x), (h u - h (u + x)) ^ 2 := by
      have h1 := eleven_twenty_sixths_base_sub_le_setIntegral_Ioc hh (L - 2 * x) x x
      rw [show L - 2 * x + x = L - x by ring, show L - x + x = L by ring] at h1
      linarith
    have hL2 := left_layer_central_core_transport_le_setIntegral_Ioc hh hx
    have hR2 := central_core_right_layer_transport_le_setIntegral_Ioc hh hx
    have hpos_L : 0 ≤ ∫ u in Ioc x (2 * x), h u ^ 2 :=
      setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _
    have hpos_R : 0 ≤ ∫ u in Ioc (L - 2 * x) (L - x), h u ^ 2 :=
      setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _
    unfold collarMass at hcol_int hcons
    linarith
  · have hqtr := eight_twenty_firsts_mul_integral_sq_le_integral_jump_sq_of_quarter_le
      hh hsupp hL hx4.le
    have hsq : 0 ≤ ∫ u, h u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    linarith

/-- **Autocorrelation Upper Bound on the Fifth-Window Tail (`x ≥ L / 5`)**:
`2 * autocorr h x ≤ (26 / 15) * ∫ u, h u ^ 2`. -/
theorem two_mul_autocorr_le_twenty_six_fifteenths_mul_integral_sq_of_fifth_le
    {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL : 0 ≤ L) (hx : L / 5 ≤ x) :
    2 * autocorr h x ≤ (26 / 15 : ℝ) * ∫ u, h u ^ 2 := by
  have h1 := integral_jump_sq hh x
  have h2 := four_fifteenths_mul_integral_sq_le_integral_jump_sq_of_fifth_le hh hsupp hL hx
  linarith

/-! ## Section 2: Five-Shell Jump Coercivity and Sharpened `(0, log 2)` Plastic Floor -/

/-- **Fifth-Window Potential-Difference Coercivity on `Ioo (L / 5) b`**:
for any `BddSupp A h C` vanishing outside `Ioo 0 L` (`L > 0`) and any `b` with
`L / 5 ≤ b ≤ screwSignThreshold`,
`(2 / 15) * (levyCoshPotential (L / 5) - levyCoshPotential b) * ∫ u, h u ^ 2`
`≤ ∫ x in Ioo (L / 5) b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem two_fifteenths_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L b : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL0 : 0 < L) (hL5b : L / 5 ≤ b)
    (hbt : b ≤ screwSignThreshold) :
    (2 / 15 : ℝ) * (levyCoshPotential (L / 5) - levyCoshPotential b) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 5) b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL5_pos : 0 < L / 5 := by linarith
  have hb0 : 0 < b := lt_of_lt_of_le hL5_pos hL5b
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 5) b) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL5_pos hx.1).neg
  have hIK : IntegrableOn (fun x => -screwRegularKernel x) (Ioo (L / 5) b) :=
    hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hFm : Measurable (fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2) := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hIF : IntegrableOn (fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2)
      (Ioo (L / 5) b) := by
    refine (hIK.mul_const (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL5_pos hx.1) (hx.2.le.trans hbt))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hval : (∫ x in Ioo (L / 5) b, (-screwRegularKernel x) * ((4 / 15 : ℝ) * ∫ u, h u ^ 2)) =
      (2 / 15 : ℝ) * (levyCoshPotential (L / 5) - levyCoshPotential b) * ∫ u, h u ^ 2 := by
    rw [integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hL5b]
    have hFTC := integral_two_mul_screwRegularKernel hL5_pos hb0
    have hneg : (∫ x in (L / 5)..b, -screwRegularKernel x) =
        -(1 / 2) * ∫ x in (L / 5)..b, 2 * screwRegularKernel x := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun x _ => by ring
    rw [hneg, hFTC]
    ring
  rw [← hval]
  refine setIntegral_mono_on (hIK.mul_const _) hIF measurableSet_Ioo fun x hx => ?_
  have hK0 : 0 ≤ -screwRegularKernel x :=
    neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
      (lt_trans hL5_pos hx.1) (hx.2.le.trans hbt))
  exact mul_le_mul_of_nonneg_left
    (four_fifteenths_mul_integral_sq_le_integral_jump_sq_of_fifth_le
      hh hsupp hL0.le hx.1.le) hK0

/-- **Two-Shell `(L / 6, L / 5) ∪ (L / 5, b)` Jump-Integral Coercivity**:
for `L / 5 ≤ b ≤ screwSignThreshold`,
`((7 / 72) * Φ(L / 6) + (13 / 360) * Φ(L / 5) - (2 / 15) * Φ(b)) * ∫ u, h u ^ 2`
`≤ ∫ x in Ioo (L / 6) b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem sixth_add_fifth_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L b : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL0 : 0 < L) (hL5b : L / 5 ≤ b)
    (hbt : b ≤ screwSignThreshold) :
    ((7 / 72 : ℝ) * levyCoshPotential (L / 6) +
        (13 / 360 : ℝ) * levyCoshPotential (L / 5) -
        (2 / 15 : ℝ) * levyCoshPotential b) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 6) b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL6_pos : 0 < L / 6 := by linarith
  have hL6_5 : L / 6 ≤ L / 5 := by linarith
  have hL5_t : L / 5 ≤ screwSignThreshold := le_trans hL5b hbt
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 6) b) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL6_pos hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 6) b) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL6_pos hx.1) (hx.2.le.trans hbt))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_left_Ioc : IntegrableOn F (Ioc (L / 6) (L / 5)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL5b)
  have hIF_right_Ioc : IntegrableOn F (Ioc (L / 5) b) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL6_5 le_rfl)
  have hdisj : Disjoint (Ioc (L / 6) (L / 5)) (Ioc (L / 5) b) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 6) b, F x) =
      (∫ x in Ioo (L / 6) (L / 5), F x) + ∫ x in Ioo (L / 5) b, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc hL6_5 hL5b,
      setIntegral_union hdisj measurableSet_Ioc hIF_left_Ioc hIF_right_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h6 := seven_seventy_seconds_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 le_rfl hL6_5 hL5_t
  have h5 := two_fifteenths_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 hL5b hbt
  dsimp only [F] at hsplit
  linarith

/-- **Three-Shell `(L / 8, L / 6) ∪ (L / 6, L / 5) ∪ (L / 5, b)` Jump-Integral Coercivity**:
for `L / 5 ≤ b ≤ screwSignThreshold`,
`((3 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (13 / 360) * Φ(L / 5) - (2 / 15) * Φ(b)) * ∫ u, h u ^ 2`
`≤ ∫ x in Ioo (L / 8) b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem eighth_add_sixth_add_fifth_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L b : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL0 : 0 < L) (hL5b : L / 5 ≤ b)
    (hbt : b ≤ screwSignThreshold) :
    ((3 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (67 / 1800 : ℝ) * levyCoshPotential (L / 6) +
        (13 / 360 : ℝ) * levyCoshPotential (L / 5) -
        (2 / 15 : ℝ) * levyCoshPotential b) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 8) b, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL8_pos : 0 < L / 8 := by linarith
  have hL8_6 : L / 8 ≤ L / 6 := by linarith
  have hL6_b : L / 6 ≤ b := by linarith
  have hL6_t : L / 6 ≤ screwSignThreshold := le_trans hL6_b hbt
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 8) b) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL8_pos hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 8) b) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL8_pos hx.1) (hx.2.le.trans hbt))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_left_Ioc : IntegrableOn F (Ioc (L / 8) (L / 6)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL6_b)
  have hIF_right_Ioc : IntegrableOn F (Ioc (L / 6) b) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL8_6 le_rfl)
  have hdisj : Disjoint (Ioc (L / 8) (L / 6)) (Ioc (L / 6) b) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 8) b, F x) =
      (∫ x in Ioo (L / 8) (L / 6), F x) + ∫ x in Ioo (L / 6) b, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc hL8_6 hL6_b,
      setIntegral_union hdisj measurableSet_Ioc hIF_left_Ioc hIF_right_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h8 := three_fiftieths_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 le_rfl hL8_6 hL6_t
  have h65 := sixth_add_fifth_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 hL5b hbt
  dsimp only [F] at hsplit
  linarith

/-- **Five-Shell `(L / 8, L / 6) ∪ (L / 6, L / 5) ∪ (L / 5, L / 4) ∪ (L / 4, L / 3) ∪ (L / 3, c)` Jump Coercivity**:
for `L / 3 ≤ c ≤ screwSignThreshold`,
`((3 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) - (12 / 41) * Φ(c)) * ∫ u, h u ^ 2`
`≤ ∫ x in Ioo (L / 8) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2`. -/
theorem eighth_to_third_with_fifth_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L c : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL0 : 0 < L) (hL3c : L / 3 ≤ c)
    (hct : c ≤ screwSignThreshold) :
    ((3 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (67 / 1800 : ℝ) * levyCoshPotential (L / 6) +
        (13 / 360 : ℝ) * levyCoshPotential (L / 5) +
        (2 / 35 : ℝ) * levyCoshPotential (L / 4) +
        (88 / 861 : ℝ) * levyCoshPotential (L / 3) -
        (12 / 41 : ℝ) * levyCoshPotential c) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 8) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL8_pos : 0 < L / 8 := by linarith
  have hL8_4 : L / 8 ≤ L / 4 := by linarith
  have hL5_4 : L / 5 ≤ L / 4 := by linarith
  have hL4_3 : L / 4 ≤ L / 3 := by linarith
  have hL4_c : L / 4 ≤ c := by linarith
  have hL4_t : L / 4 ≤ screwSignThreshold := le_trans hL4_c hct
  have hL3_t : L / 3 ≤ screwSignThreshold := le_trans hL3c hct
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 8) c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL8_pos hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 8) c) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL8_pos hx.1) (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_1_Ioc : IntegrableOn F (Ioc (L / 8) (L / 4)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL4_c)
  have hIF_2_Ioc : IntegrableOn F (Ioc (L / 4) (L / 3)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL8_4 hL3c)
  have hIF_3_Ioc : IntegrableOn F (Ioc (L / 3) c) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo (hL8_4.trans hL4_3) le_rfl)
  have hIF_12_Ioc : IntegrableOn F (Ioc (L / 8) (L / 3)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL3c)
  have hdisj_12 : Disjoint (Ioc (L / 8) (L / 4)) (Ioc (L / 4) (L / 3)) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hdisj_123 : Disjoint (Ioc (L / 8) (L / 3)) (Ioc (L / 3) c) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 8) c, F x) =
      (∫ x in Ioo (L / 8) (L / 4), F x) + (∫ x in Ioo (L / 4) (L / 3), F x) +
        ∫ x in Ioo (L / 3) c, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc (hL8_4.trans hL4_3) hL3c,
      setIntegral_union hdisj_123 measurableSet_Ioc hIF_12_Ioc hIF_3_Ioc,
      ← Ioc_union_Ioc_eq_Ioc hL8_4 hL4_3,
      setIntegral_union hdisj_12 measurableSet_Ioc hIF_1_Ioc hIF_2_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h865 := eighth_add_sixth_add_fifth_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 hL5_4 hL4_t
  have h4 := four_twenty_firsts_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 le_rfl hL4_3 hL3_t
  have h3 := twelve_forty_firsts_mul_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL0 le_rfl hL3c hct
  dsimp only [F] at hsplit
  linarith

/-- **Five-Shell `(L / 8, L / 6, L / 5, L / 4, L / 3, c)` Lévy–Cosh Crossover Inequality**:
for every `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`L > 0`) and any `c` with
`L / 3 ≤ c ≤ screwSignThreshold`,
`(A(0) + (3 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (29 / 41) * Φ(c)) * ∫ f²`
`+ ∫∫ f(u)f(v)(2 cosh((u-v)/2) - K_c(|u-v|)) ≤ W_∞(f ⋆ f̃)`. -/
theorem eighth_to_third_with_fifth_levyCosh_crossover_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {L c : ℝ} (hL : 0 < L)
    (hL3c : L / 3 ≤ c) (hct : c ≤ screwSignThreshold) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (3 / 50) * levyCoshPotential (L / 8) +
        (67 / 1800) * levyCoshPotential (L / 6) +
        (13 / 360) * levyCoshPotential (L / 5) +
        (2 / 35) * levyCoshPotential (L / 4) +
        (88 / 861) * levyCoshPotential (L / 3) +
        (29 / 41) * levyCoshPotential c) * (∫ u, f u ^ 2) +
      (∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL8 : 0 < L / 8 := by linarith
  have hL8c : L / 8 ≤ c := by linarith
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL8 hL8c hct
  have hsub := eighth_to_third_with_fifth_sub_levyCoshPotential_le_setIntegral_Ioo
    hB hsupp hL hL3c hct
  linarith

/-- **Sharpened `(0, log 2)` Plastic-Floor Theorem with Fifth-Window Double Transport**:
for every nonnegative `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 (log 2)`, the universal constant floor is
boosted to `A(0) + (3 / 50) * Φ((log 2)/8) + (67 / 1800) * Φ((log 2)/6) + (13 / 360) * Φ((log 2)/5) + (2 / 35) * Φ((log 2)/4) + (88 / 861) * Φ((log 2)/3) + (29 / 41) * Φ(screwSignThreshold)`
(reducing the universal constant deficit on `(0, log 2)` from `-0.0258` down to **`-0.0221`**). -/
theorem fifth_window_log_two_plastic_floor_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    (hsupp : ∀ u ∉ Ioo 0 (Real.log 2), f u = 0) :
    (EF.gammaBracket 0 + (3 / 50) * levyCoshPotential (Real.log 2 / 8) +
        (67 / 1800) * levyCoshPotential (Real.log 2 / 6) +
        (13 / 360) * levyCoshPotential (Real.log 2 / 5) +
        (2 / 35) * levyCoshPotential (Real.log 2 / 4) +
        (88 / 861) * levyCoshPotential (Real.log 2 / 3) +
        (29 / 41) * levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : Real.log 2 / 3 ≤ screwSignThreshold := by
    linarith [Real.log_two_lt_d9, screwSignThreshold_gt_6036_over_21509]
  have hmain := eighth_to_third_with_fifth_levyCosh_crossover_le_weilArchRe
    hf hfc hlog2 hlt le_rfl hsupp
  have hpair_nn : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
  linarith

/-! ## Section 3: Eight-Point Reflected Potential and Unconditional Positivity on `(0, 9 / 22)` (`59.02%` of `(0, log 2)`) -/

/-- **Eight-Point Reflected Shell Jump-Integral Coercivity on `Ioo (L / 8) c` (`2 * L / 3 ≤ c ≤ 3 * L / 4`)**:
combining `(L / 8, L / 6)`, `(L / 6, L / 5)`, `(L / 5, L / 4)` with the reflected `(L / 4, c)`
shell yields:
`((3 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 41) * Φ(L / 2) + (88 / 861) * Φ(2 * L / 3) - (17 / 21) * Φ(c)) * ∫ h² ≤ ∫_{x ∈ Ioo (L / 8) c} (-screwRegularKernel x) D_h(x) dx`. -/
theorem eight_point_sub_levyCoshPotential_le_setIntegral_Ioo
    {A : Set ℝ} {h : ℝ → ℝ} {C L c : ℝ} (hh : BddSupp A h C)
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL : 0 < L) (h23c : 2 * L / 3 ≤ c)
    (hc34 : c ≤ 3 * L / 4) (hct : c ≤ screwSignThreshold) :
    ((3 / 50 : ℝ) * levyCoshPotential (L / 8) +
        (67 / 1800 : ℝ) * levyCoshPotential (L / 6) +
        (13 / 360 : ℝ) * levyCoshPotential (L / 5) +
        (2 / 35 : ℝ) * levyCoshPotential (L / 4) +
        (88 / 861 : ℝ) * levyCoshPotential (L / 3) +
        (17 / 41 : ℝ) * levyCoshPotential (L / 2) +
        (88 / 861 : ℝ) * levyCoshPotential (2 * L / 3) -
        (17 / 21 : ℝ) * levyCoshPotential c) * (∫ u, h u ^ 2) ≤
      ∫ x in Ioo (L / 8) c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
  have hL8 : 0 < L / 8 := by linarith
  have hL8_4 : L / 8 ≤ L / 4 := by linarith
  have hL5_4 : L / 5 ≤ L / 4 := by linarith
  have hL4c : L / 4 ≤ c := by linarith
  have hL4t : L / 4 ≤ screwSignThreshold := le_trans hL4c hct
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 :=
    fun x => integral_nonneg fun _ => sq_nonneg _
  let F : ℝ → ℝ := fun x => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2
  have hFm : Measurable F := by
    refine Measurable.mul ?_ (measurable_jump hh)
    unfold screwRegularKernel; fun_prop
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc (L / 8) c) :=
    (WeilLevyCoshCrossover.continuousOn_screwRegularKernel.mono
      fun x hx => lt_of_lt_of_le hL8 hx.1).neg
  have hIF : IntegrableOn F (Ioo (L / 8) c) := by
    refine ((hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self).mul_const
      (4 * ∫ u, h u ^ 2)).mono' hFm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hL8 hx.1) (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hIF_left_Ioc : IntegrableOn F (Ioc (L / 8) (L / 4)) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo le_rfl hL4c)
  have hIF_right_Ioc : IntegrableOn F (Ioc (L / 4) c) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hIF.mono_set (Ioo_subset_Ioo hL8_4 le_rfl)
  have hdisj : Disjoint (Ioc (L / 8) (L / 4)) (Ioc (L / 4) c) :=
    disjoint_left.mpr fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2.1
  have hsplit : (∫ x in Ioo (L / 8) c, F x) =
      (∫ x in Ioo (L / 8) (L / 4), F x) + ∫ x in Ioo (L / 4) c, F x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← Ioc_union_Ioc_eq_Ioc hL8_4 hL4c,
      setIntegral_union hdisj measurableSet_Ioc hIF_left_Ioc hIF_right_Ioc,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have h865 := eighth_add_sixth_add_fifth_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL hL5_4 hL4t
  have h43 := quarter_third_reflected_sub_levyCoshPotential_le_setIntegral_Ioo
    hh hsupp hL h23c hc34 hct
  dsimp only [F] at hsplit
  linarith

/-- **Eight-Point Reflected Lévy–Cosh Crossover Inequality on `(0, L)` (`2 * L / 3 ≤ c ≤ 3 * L / 4`)**:
for every `f ∈ C²_c(ℝ)` vanishing outside `Ioo 0 L` (`L > 0`),
`(A(0) + (3 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 41) * Φ(L / 2) + (88 / 861) * Φ(2 * L / 3) + (4 / 21) * Φ(c)) * ∫ f² + ... ≤ W_∞(f ⋆ f̃)`. -/
theorem eight_point_levyCosh_crossover_le_weilArchRe
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {L c : ℝ} (hL : 0 < L)
    (h23c : 2 * L / 3 ≤ c) (hc34 : c ≤ 3 * L / 4) (hct : c ≤ screwSignThreshold)
    (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    (EF.gammaBracket 0 + (3 / 50) * levyCoshPotential (L / 8) +
        (67 / 1800) * levyCoshPotential (L / 6) +
        (13 / 360) * levyCoshPotential (L / 5) +
        (2 / 35) * levyCoshPotential (L / 4) +
        (88 / 861) * levyCoshPotential (L / 3) +
        (17 / 41) * levyCoshPotential (L / 2) +
        (88 / 861) * levyCoshPotential (2 * L / 3) +
        (4 / 21) * levyCoshPotential c) * (∫ u, f u ^ 2) +
      (∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hL8 : 0 < L / 8 := by linarith
  have hL8c : L / 8 ≤ c := by linarith
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hL8 hL8c hct
  have height := eight_point_sub_levyCoshPotential_le_setIntegral_Ioo
    hB hsupp hL h23c hc34 hct
  linarith

/-- **Osculating Lower Bound for the Eight-Point Reflected Potential (`L > 0`, `c > 0`)**:
combining `osculating_le_seven_point_potential` with the `(13 / 360)` shift from `L / 4` to `L / 5`
(where `log(1 / (2π(L / 5))) - log(1 / (2π(L / 4))) = log(5 / 4)` and
`(7 / 2) * (L / 5 - L / 4) = -(7 / 40) * L`) yields for **every** `L > 0` and `c > 0`:
`log(1 / (π * L)) + (7 / 72) * log 2 + (1931 / 12600) * log(4 / 3) + (13 / 360) * log(5 / 4) + (88 / 861) * log(9 / 8) + (4 / 21) * log((21 / 8) * L) + (13031 / 10800) * L + 4 / 21 - γ`
`≤ EF.gammaBracket 0 + (3 / 50) * Φ(L / 8) + (67 / 1800) * Φ(L / 6) + (13 / 360) * Φ(L / 5) + (2 / 35) * Φ(L / 4) + (88 / 861) * Φ(L / 3) + (17 / 41) * Φ(L / 2) + (88 / 861) * Φ(2 * L / 3) + (4 / 21) * Φ(c)`. -/
theorem osculating_le_eight_point_potential {L c : ℝ} (hL : 0 < L) (hc0 : 0 < c) :
    Real.log (1 / (Real.pi * L)) + (7 / 72 : ℝ) * Real.log 2 +
        (1931 / 12600 : ℝ) * Real.log (4 / 3) +
        (13 / 360 : ℝ) * Real.log (5 / 4) +
        (88 / 861 : ℝ) * Real.log (9 / 8) +
        (4 / 21 : ℝ) * Real.log ((21 / 8 : ℝ) * L) +
        (13031 / 10800 : ℝ) * L + 4 / 21 - eulerMascheroniConstant ≤
      EF.gammaBracket 0 + (3 / 50) * levyCoshPotential (L / 8) +
        (67 / 1800) * levyCoshPotential (L / 6) +
        (13 / 360) * levyCoshPotential (L / 5) +
        (2 / 35) * levyCoshPotential (L / 4) +
        (88 / 861) * levyCoshPotential (L / 3) +
        (17 / 41) * levyCoshPotential (L / 2) +
        (88 / 861) * levyCoshPotential (2 * L / 3) +
        (4 / 21) * levyCoshPotential c := by
  have h1 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 8)
  have h2 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 6)
  have h5_pt := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 5)
  have h3 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 4)
  have h4 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 3)
  have h5 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < L / 2)
  have h6 := log_inv_two_pi_add_seven_halves_le_gammaBracket_add_levyCoshPotential
    (by linarith : 0 < 2 * L / 3)
  have h7 := log_seven_div_four_pi_add_one_le_gammaBracket_add_levyCoshPotential hc0
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  have hlog3 : Real.log 3 = 2 * Real.log 2 - Real.log (4 / 3) := by
    rw [Real.log_div (by norm_num) (by norm_num), hlog4]; ring
  have hlog1 : Real.log (1 / (2 * Real.pi * (L / 8))) =
      Real.log (1 / (Real.pi * L)) + 2 * Real.log 2 := by
    rw [← hlog4, ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog2 : Real.log (1 / (2 * Real.pi * (L / 6))) =
      Real.log (1 / (Real.pi * L)) + 2 * Real.log 2 - Real.log (4 / 3) := by
    rw [show Real.log (1 / (Real.pi * L)) + 2 * Real.log 2 - Real.log (4 / 3) =
        Real.log (1 / (Real.pi * L)) + Real.log 3 by linarith [hlog3],
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog_fifth : Real.log (1 / (2 * Real.pi * (L / 5))) =
      Real.log (1 / (Real.pi * L)) + Real.log 2 + Real.log (5 / 4) := by
    rw [← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog3_pt : Real.log (1 / (2 * Real.pi * (L / 4))) =
      Real.log (1 / (Real.pi * L)) + Real.log 2 := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog46_pair : Real.log (1 / (2 * Real.pi * (L / 3))) +
      Real.log (1 / (2 * Real.pi * (2 * L / 3))) =
      2 * Real.log (1 / (Real.pi * L)) + Real.log (9 / 8) := by
    rw [← Real.log_mul (by positivity) (by positivity),
      show (2 : ℝ) * Real.log (1 / (Real.pi * L)) =
        Real.log (1 / (Real.pi * L)) + Real.log (1 / (Real.pi * L)) by ring,
      add_assoc, ← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog5_pt : Real.log (1 / (2 * Real.pi * (L / 2))) =
      Real.log (1 / (Real.pi * L)) := by
    congr 1; field_simp
  have hlog7_pt : Real.log (7 / (4 * Real.pi)) =
      Real.log (1 / (Real.pi * L)) + Real.log (4 / 3) - Real.log 2 +
        Real.log ((21 / 8 : ℝ) * L) := by
    rw [← Real.log_mul (by positivity) (by positivity),
      ← Real.log_div (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  linarith

/-- Rational lower bounds `2 / 9 < Real.log (5 / 4)` and `26 / 365 < Real.log (189 / 176)`. -/
theorem two_ninths_lt_log_five_fourths : (2 : ℝ) / 9 < Real.log (5 / 4) := by
  have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1 / 4)
  norm_num at h ⊢
  exact h

theorem twenty_six_three_hundred_sixty_fifths_lt_log_189_176 :
    (26 : ℝ) / 365 < Real.log (189 / 176) := by
  have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 13 / 176)
  norm_num at h ⊢
  exact h

/-- Lower bound on `log(1 / (π * (9 / 22)))` derived from `two_mul_log_five_sub_five_mul_log_two_le_log_inv_pi_mul_two_fifths`
and `log(45 / 44) ≤ 1 / 44`:
`2 * log 5 - 5 * log 2 + 43 / 44 - 5 * π / 16 ≤ log(1 / (π * (9 / 22)))`. -/
theorem log_inv_pi_mul_nine_twenty_seconds_ge :
    2 * Real.log 5 - 5 * Real.log 2 + 43 / 44 - 5 * Real.pi / 16 ≤
      Real.log (1 / (Real.pi * (9 / 22))) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsplit : Real.log (1 / (Real.pi * (2 / 5))) =
      Real.log (1 / (Real.pi * (9 / 22))) + Real.log (45 / 44) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp; ring
  have hlog45_44 : Real.log (45 / 44 : ℝ) ≤ 1 / 44 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 45 / 44)
    linarith
  have hbase := two_mul_log_five_sub_five_mul_log_two_le_log_inv_pi_mul_two_fifths
  linarith

/-- **Strict Positivity of the Eight-Point Reflected Potential at `L = 9 / 22` (`≈ 0.409091`)**:
`0 ≤ EF.gammaBracket 0 + (3 / 50) * Φ((9/22)/8) + (67 / 1800) * Φ((9/22)/6) + (13 / 360) * Φ((9/22)/5) + (2 / 35) * Φ((9/22)/4) + (88 / 861) * Φ((9/22)/3) + (17 / 41) * Φ((9/22)/2) + (88 / 861) * Φ(2*(9/22)/3) + (4 / 21) * Φ(screwSignThreshold)`. -/
theorem zero_le_eight_point_potential_nine_twenty_seconds :
    0 ≤ EF.gammaBracket 0 + (3 / 50) * levyCoshPotential ((9 / 22 : ℝ) / 8) +
        (67 / 1800) * levyCoshPotential ((9 / 22 : ℝ) / 6) +
        (13 / 360) * levyCoshPotential ((9 / 22 : ℝ) / 5) +
        (2 / 35) * levyCoshPotential ((9 / 22 : ℝ) / 4) +
        (88 / 861) * levyCoshPotential ((9 / 22 : ℝ) / 3) +
        (17 / 41) * levyCoshPotential ((9 / 22 : ℝ) / 2) +
        (88 / 861) * levyCoshPotential (2 * (9 / 22 : ℝ) / 3) +
        (4 / 21) * levyCoshPotential screwSignThreshold := by
  have hosc := osculating_le_eight_point_potential
    (by norm_num : (0 : ℝ) < 9 / 22) screwSignThreshold_pos
  rw [show (21 / 8 : ℝ) * (9 / 22) = 189 / 176 by norm_num] at hosc
  have hlog_pi := log_inv_pi_mul_nine_twenty_seconds_ge
  have hlog2_lt := Real.log_two_lt_d9
  have hlog2_gt := Real.log_two_gt_d9
  have hlog5 := Real.log_five_gt_d9
  have hlog43 := two_sevenths_lt_log_four_thirds
  have hlog54 := two_ninths_lt_log_five_fourths
  have hlog98 := two_seventeenths_lt_log_nine_eighths
  have hlog189 := twenty_six_three_hundred_sixty_fifths_lt_log_189_176
  have hpi := Real.pi_lt_d4
  have hgamma :=
    RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  linarith

/-- **Unconditional Archimedean Weil Positivity on `(0, 9 / 22)` (`≈ (0, 0.409091)`, `59.02%` of `(0, log 2)`)**:
for every nonnegative `f ∈ C²_c(ℝ)` supported in `Ioo 0 L` with `L ≤ 9 / 22`,
`0 ≤ WeilOneSided.weilArchRe (EF.weilTest f f)`. -/
theorem weilArchRe_nonneg_of_support_Ioo_le_nine_twenty_seconds {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    {L : ℝ} (hL : L ≤ 9 / 22) (hsupp : ∀ u ∉ Ioo 0 L, f u = 0) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hsupp_9_22 : ∀ u ∉ Ioo (0 : ℝ) (9 / 22), f u = 0 :=
    fun u hu => hsupp u fun huL => hu ⟨huL.1, huL.2.trans_le hL⟩
  have hmain := eight_point_levyCosh_crossover_le_weilArchRe
    hf hfc (by norm_num : (0 : ℝ) < 9 / 22)
    (by linarith [screwSignThreshold_gt_6036_over_21509])
    (by linarith [screwSignThreshold_lt_two_sevenths])
    le_rfl hsupp_9_22
  have hpot := zero_le_eight_point_potential_nine_twenty_seconds
  have hsq : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hterm1 : 0 ≤ (EF.gammaBracket 0 + (3 / 50) * levyCoshPotential ((9 / 22 : ℝ) / 8) +
        (67 / 1800) * levyCoshPotential ((9 / 22 : ℝ) / 6) +
        (13 / 360) * levyCoshPotential ((9 / 22 : ℝ) / 5) +
        (2 / 35) * levyCoshPotential ((9 / 22 : ℝ) / 4) +
        (88 / 861) * levyCoshPotential ((9 / 22 : ℝ) / 3) +
        (17 / 41) * levyCoshPotential ((9 / 22 : ℝ) / 2) +
        (88 / 861) * levyCoshPotential (2 * (9 / 22 : ℝ) / 3) +
        (4 / 21) * levyCoshPotential screwSignThreshold) * ∫ u, f u ^ 2 :=
    mul_nonneg hpot hsq
  have hpair : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
  linarith

/-- **Unconditional `WindowPositive` on `(0, 9 / 22)` (`≈ (0, 0.409091)`, `59.02%` of `(0, log 2)`)**:
for every nonnegative `f ∈ C²_c(ℝ)` with `tsupport f ⊆ Ioo 0 (9 / 22)`, `0 ≤ weilArchRe`. -/
theorem windowPositive_nine_twenty_seconds (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (9 / 22)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_nine_twenty_seconds hf hfc hf0 le_rfl
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-- **Unconditional `WindowPositive` on `(0, 11 / 27)` (`≈ (0, 0.407407)`, `58.78%` of `(0, log 2)`)**:
immediate corollary since `11 / 27 ≤ 9 / 22` (`242 ≤ 243`). -/
theorem windowPositive_eleven_twenty_sevenths (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (11 / 27)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_nine_twenty_seconds hf hfc hf0 (by norm_num : (11 : ℝ) / 27 ≤ 9 / 22)
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

/-- **Unconditional `WindowPositive` on `(0, 13 / 32)` (`= (0, 0.40625)`, `58.61%` of `(0, log 2)`)**:
immediate corollary since `13 / 32 ≤ 9 / 22`. -/
theorem windowPositive_thirteen_thirty_seconds (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ioo 0 (13 / 32)) (hf0 : ∀ u, 0 ≤ f u) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_support_Ioo_le_nine_twenty_seconds hf hfc hf0 (by norm_num : (13 : ℝ) / 32 ≤ 9 / 22)
    (fun _ hu => image_eq_zero_of_notMem_tsupport fun h => hu (hf_supp h))

end

end RHTower.WeilLevyFifthWindow
