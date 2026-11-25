import GaloisForLFunctions.FamilyContinuationTheory.TheTrueVertexBelowSevenEighths
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.ChosenMomentInputs
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.FinalAssemblyData

/-!
# Complete-factor detector row counts and sub-`4199/4800` exponent certificate

Complete-factor selection on top-level plain-marked moments upgrades the plain capacity slope from
`9/2 + 12 Δ` to `16/5 + 12 Δ` across the dyadic witness window `33/100 ≤ m < 1/2`. Substituting the
resulting crossing weight `rowD₃₂ x = 3 - 9 x / 4` and prime-amplitude slope
`rowP₃₂ x = (2 - 5 x / 4) (1 - x)` into the adaptive detector cutoff moves the admissible edge
geometry `(lx, ly, ℓ)` along `lx + ly + ℓ = 1` to `(17/48, 287/600, 67/400)`, lowering the low
boundary in both Gram regimes to `4199/4800 < 40535/46328 < 20999/24000`:

* **Exact sum-of-squares certificate (`endpoint_certificate_sub4199`).** Across every balanced bin
  `0 ≤ δ ≤ 5/6` and prime-amplitude ratio `0 ≤ x ≤ 1/2`, clearing `rowJ₃₂ δ x > 0` expresses
  `-endpointExponent` at `(17/48, 287/600, 67/400)` and `σ₀ = 4199/4800` via
  `1843200 A0₃₂(y) sub4199Numerator δ x = (12 A0₃₂(y) δ - B0₃₂(y))² + 346 A0₃₂(y) + R0₃₂(y)` in
  `y = 1/2 - x ≥ 0`, with strictly positive coefficients in `A0₃₂` and `R0₃₂`. Hence
  `endpointExponent ≤ -173/2304000` uniformly, while high bins `5/6 ≤ δ ≤ 1` satisfy
  `endpointExponent ≤ -43/600`.
* **Complete-factor adaptive row counts (`adaptive_source_count_from_raw_moments₃₂`,
  `actual_nonfloor_class_from_raw_moments₃₂`).** Raw moment interfaces `Moments₃₂`,
  `SourceMomentsAt₃₂`, and `SourceMomentBound₃₂` propagate the `16/5 + 12 Δ` plain-marked capacity
  into the dyadic nonfloor cube arithmetic sum.
-/

namespace GaloisForLFunctions.FamilyContinuationTheory.Budget

noncomputable section

/-! ### The sub-`4199/4800` edge geometry `(17/48, 287/600, 67/400)` -/

theorem lowBoundary_sub4199 :
    lowBoundary (17 / 48) (287 / 600) (67 / 400) = 4199 / 4800 := by
  unfold lowBoundary
  rw [show (17 : ℝ) / 48 + 287 / 600 + 67 / 400 - 1 = 0 by ring, max_self]
  norm_num

theorem lowBoundaryGen_sub4199 :
    lowBoundaryGen (17 / 48) (287 / 600) (67 / 400) = 4199 / 4800 := by
  rw [lowBoundaryGen_eq_of_le (67 / 400) (by norm_num), lowBoundary_sub4199]

theorem sub4199_lt_farkas_wall : (4199 / 4800 : ℝ) < 40535 / 46328 := by norm_num

/-- On `(M, ℓ) = (333/400, 67/400)` we have `1 + 3ℓ = 601/400 ≤ 666/400 = 2M`, so the reflected
allowance of unselected slots is nonpositive. -/
theorem tupleExponent_reflectedAllowance_sub4199 {d : ℝ} (hd : 0 ≤ d) :
    tupleExponent d (reflectedAllowance (333 / 400) (67 / 400) d) ≤ 0 :=
  tupleExponent_reflectedAllowance_nonpos hd (by norm_num)

/-! ### Complete-factor (`16/5`) balanced row-count polynomials and SOS certificate -/

/-- Crossing weight of the inverse and complete-factor (`16/5`) plain counts at ratio `x`. -/
def rowD₃₂ (x : ℝ) : ℝ := 3 - 9 * x / 4

/-- Slope of the short count under `16/5` plain capacity at amplitude ratio `x`. -/
def rowP₃₂ (x : ℝ) : ℝ := (2 - 5 * x / 4) * (1 - x)

/-- Balance denominator at bin `δ` and amplitude ratio `x` under `16/5` plain capacity. -/
def rowJ₃₂ (δ x : ℝ) : ℝ := (5 / 6 - δ) * rowD₃₂ x + δ * rowP₃₂ x

/-- Balanced row-count exponent of bin `δ` at amplitude ratio `x` under `16/5` plain capacity. -/
def rowCount₃₂ (δ x : ℝ) : ℝ := 1 - δ + (5 / 6 - δ) * δ * rowP₃₂ x / (2 * rowJ₃₂ δ x)

theorem rowJ₃₂_pos {δ x : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6) (hx : x ≤ 1 / 2) :
    55 / 96 ≤ rowJ₃₂ δ x := by
  unfold rowJ₃₂ rowD₃₂ rowP₃₂
  have hD : 11 / 16 ≤ 3 - 9 * x / 4 := by linarith
  have hP : 11 / 16 ≤ (2 - 5 * x / 4) * (1 - x) := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hδ) (sub_nonneg.mpr hD),
    mul_nonneg hδ0 (sub_nonneg.mpr hP)]

theorem rowJ₃₂_le {δ x : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    rowJ₃₂ δ x ≤ 5 / 2 := by
  have hx1 : 0 ≤ 1 - x := by linarith
  unfold rowJ₃₂ rowD₃₂ rowP₃₂
  have hD : 3 - 9 * x / 4 ≤ 3 := by linarith
  have hP : (2 - 5 * x / 4) * (1 - x) ≤ 2 := by nlinarith [mul_nonneg hx0 hx1]
  nlinarith [mul_nonneg (sub_nonneg.mpr hδ) (sub_nonneg.mpr hD),
    mul_nonneg hδ0 (sub_nonneg.mpr hP)]

/-- Positive cubic polynomial in `y = 1/2 - x` scaling the quadratic form in `δ`. -/
def A0₃₂ (y : ℝ) : ℝ := 2680 * y ^ 3 + 6964 * y ^ 2 + 7666 * y + 2635

/-- Linear shift of the square in `δ`, as a quadratic in `y = 1/2 - x`. -/
def B0₃₂ (y : ℝ) : ℝ := 6500 * y ^ 2 + 23396 * y + 12261

/-- Positive quartic remainder in `y = 1/2 - x` after extracting `346 · A0₃₂ y`. -/
def R0₃₂ (y : ℝ) : ℝ :=
  142348400 * y ^ 4 + 328437040 * y ^ 3 + 218592320 * y ^ 2 + 45158052 * y + 5169

/-- Cleared-denominator numerator of `-endpointExponent` at `(17/48, 287/600, 67/400)` and
`σ₀ = 4199/4800` with `rowCount₃₂`. -/
def sub4199Numerator (δ x : ℝ) : ℝ :=
  rowJ₃₂ δ x * (-(1 + δ) * (1 - 287 / 600) / 2 + 4199 / 4800 + (67 / 400) / 2
      - (x * δ) * (67 / 400) - (1 - 17 / 48 + 67 / 400) * (1 - δ / 2 - 1 / 6))
    - (1 - 17 / 48 + 67 / 400) * ((5 / 6 - δ) * δ * rowP₃₂ x / 2)

theorem A0₃₂_pos {y : ℝ} (hy : 0 ≤ y) : 0 < A0₃₂ y := by
  unfold A0₃₂
  positivity

theorem R0₃₂_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ R0₃₂ y := by
  unfold R0₃₂
  positivity

/-- Exact algebraic sum-of-squares identity for `sub4199Numerator`. -/
theorem sub4199Numerator_sos (δ x : ℝ) :
    1843200 * A0₃₂ (1 / 2 - x) * sub4199Numerator δ x =
      (12 * A0₃₂ (1 / 2 - x) * δ - B0₃₂ (1 / 2 - x)) ^ 2 +
        346 * A0₃₂ (1 / 2 - x) + R0₃₂ (1 / 2 - x) := by
  unfold sub4199Numerator rowJ₃₂ rowD₃₂ rowP₃₂ A0₃₂ B0₃₂ R0₃₂
  ring

theorem sub4199Numerator_ge {δ x : ℝ} (hx : x ≤ 1 / 2) :
    173 / 921600 ≤ sub4199Numerator δ x := by
  have hy : 0 ≤ 1 / 2 - x := by linarith
  have hA : 0 < A0₃₂ (1 / 2 - x) := A0₃₂_pos hy
  have hR : 0 ≤ R0₃₂ (1 / 2 - x) := R0₃₂_nonneg hy
  have hsq : 0 ≤ (12 * A0₃₂ (1 / 2 - x) * δ - B0₃₂ (1 / 2 - x)) ^ 2 := sq_nonneg _
  have hid := sub4199Numerator_sos δ x
  have hmul : 346 * A0₃₂ (1 / 2 - x) ≤
      1843200 * A0₃₂ (1 / 2 - x) * sub4199Numerator δ x := by
    linarith
  nlinarith

/-- **Sub-`4199/4800` balanced endpoint certificate.** Across all `0 ≤ δ ≤ 5/6` and `0 ≤ x ≤ 1/2`,
`endpointExponent` at `(17/48, 287/600, 67/400)` and `σ₀ = 4199/4800` with `rowCount₃₂ δ x` is at
most `-173/2304000`. -/
theorem endpoint_certificate_sub4199 {δ x : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6)
    (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    endpointExponent (17 / 48) (287 / 600) (67 / 400) (4199 / 4800)
      δ (x * δ) (rowCount₃₂ δ x) ≤ -(173 / 2304000) := by
  have hJ := rowJ₃₂_pos hδ0 hδ hx
  have hJ0 : 0 < rowJ₃₂ δ x := by linarith
  have hJle := rowJ₃₂_le hδ0 hδ hx0 hx
  have hN := sub4199Numerator_ge (δ := δ) hx
  have hE : endpointExponent (17 / 48) (287 / 600) (67 / 400) (4199 / 4800)
      δ (x * δ) (rowCount₃₂ δ x) = -(sub4199Numerator δ x / rowJ₃₂ δ x) := by
    unfold endpointExponent rowCount₃₂ sub4199Numerator
    field_simp
    ring
  rw [hE, neg_le_neg_iff, le_div_iff₀ hJ0]
  nlinarith

/-- Positive row-length slope of `rowCount₃₂ δ x` relative to `z₀ = 17/50`. -/
theorem rowCount₃₂_slope_bounds {δ x : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6) (_hx0 : 0 ≤ x)
    (hx : x ≤ 1 / 2) :
    73 / 300 ≤ rowCount₃₂ δ x + δ / 2 - 17 / 50 ∧ rowCount₃₂ δ x + δ / 2 - 17 / 50 ≤ 3 := by
  have hJ := rowJ₃₂_pos hδ0 hδ hx
  have hJ0 : 0 < rowJ₃₂ δ x := by linarith
  have hD0 : 0 ≤ rowD₃₂ x := by unfold rowD₃₂; linarith
  have hP0 : 0 ≤ rowP₃₂ x := by unfold rowP₃₂; exact mul_nonneg (by linarith) (by linarith)
  have hge : 1 - δ ≤ rowCount₃₂ δ x := by
    unfold rowCount₃₂
    have hq : 0 ≤ (5 / 6 - δ) * δ * rowP₃₂ x / (2 * rowJ₃₂ δ x) :=
      div_nonneg (mul_nonneg (mul_nonneg (by linarith) hδ0) hP0) (by linarith)
    linarith
  have hle : rowCount₃₂ δ x ≤ 17 / 12 := by
    unfold rowCount₃₂
    have hPJ : δ * rowP₃₂ x ≤ rowJ₃₂ δ x := by
      unfold rowJ₃₂
      nlinarith [mul_nonneg (sub_nonneg.mpr hδ) hD0]
    have hnum : (5 / 6 - δ) * δ * rowP₃₂ x ≤ (5 / 6) * rowJ₃₂ δ x := by
      have h1 : (5 / 6 - δ) * (δ * rowP₃₂ x) ≤ (5 / 6 - δ) * rowJ₃₂ δ x :=
        mul_le_mul_of_nonneg_left hPJ (by linarith)
      nlinarith
    have hdiv : (5 / 6 - δ) * δ * rowP₃₂ x / (2 * rowJ₃₂ δ x) ≤ 5 / 12 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith
  exact ⟨by linarith, by linarith⟩

/-- Balanced-bin certificate across all row lengths `d ≤ 61/75 + ζ` (`61/75 = 1 - 17/48 + 67/400`). -/
theorem rowExponent_balanced_sub4199 {δ x d ζ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6)
    (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (_hζ : 0 ≤ ζ) (hd : d ≤ 61 / 75 + ζ) :
    rowExponent (17 / 48) (287 / 600) (67 / 400) (4199 / 4800) (17 / 50)
      δ (x * δ) (rowCount₃₂ δ x) d ≤ -(173 / 2304000) + 3 * ζ := by
  have htop := endpoint_certificate_sub4199 hδ0 hδ hx0 hx
  have hsl := rowCount₃₂_slope_bounds hδ0 hδ hx0 hx
  have hrel : rowExponent (17 / 48) (287 / 600) (67 / 400) (4199 / 4800) (17 / 50)
      δ (x * δ) (rowCount₃₂ δ x) d =
      endpointExponent (17 / 48) (287 / 600) (67 / 400) (4199 / 4800)
        δ (x * δ) (rowCount₃₂ δ x) +
      (d - 61 / 75) * (rowCount₃₂ δ x + δ / 2 - 17 / 50) := by
    unfold rowExponent endpointExponent
    ring
  rw [hrel]
  rcases le_total d (61 / 75) with hd0 | hd0
  · have hnonpos : (d - 61 / 75) * (rowCount₃₂ δ x + δ / 2 - 17 / 50) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hsl.1])
    linarith
  · have hbd : (d - 61 / 75) * (rowCount₃₂ δ x + δ / 2 - 17 / 50) ≤ 3 * ζ := by
      nlinarith [hsl.1, hsl.2]
    linarith

/-- High-`δ` certificate (`5/6 ≤ δ ≤ 1`, `q ≤ δ/2`, `R = 1 - δ`) at `(17/48, 287/600, 67/400)`. -/
theorem endpoint_high_delta_sub4199 {δ q : ℝ} (hδ0 : 5 / 6 ≤ δ) (_hδ1 : δ ≤ 1)
    (hq : q ≤ δ / 2) :
    endpointExponent (17 / 48) (287 / 600) (67 / 400) (4199 / 4800) δ q (1 - δ) ≤
      -(43 / 600) := by
  unfold endpointExponent
  linarith

/-- High-`δ` certificate across all row lengths `d ≤ 61/75 + ζ` (`ζ ≥ 0`). -/
theorem rowExponent_high_delta_sub4199 {δ q d ζ : ℝ} (hδ0 : 5 / 6 ≤ δ) (hδ1 : δ ≤ 1)
    (hq : q ≤ δ / 2) (_hζ : 0 ≤ ζ) (hd : d ≤ 61 / 75 + ζ) :
    rowExponent (17 / 48) (287 / 600) (67 / 400) (4199 / 4800) (17 / 50)
      δ q (1 - δ) d ≤ -(43 / 600) + ζ := by
  have htop := endpoint_high_delta_sub4199 hδ0 hδ1 hq
  have hrel : rowExponent (17 / 48) (287 / 600) (67 / 400) (4199 / 4800) (17 / 50)
      δ q (1 - δ) d =
      endpointExponent (17 / 48) (287 / 600) (67 / 400) (4199 / 4800) δ q (1 - δ) +
      (d - 61 / 75) * (33 / 50 - δ / 2) := by
    unfold rowExponent endpointExponent
    ring
  rw [hrel]
  rcases le_total d (61 / 75) with hd0 | hd0
  · have hnonpos : (d - 61 / 75) * (33 / 50 - δ / 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  · have hbd : (d - 61 / 75) * (33 / 50 - δ / 2) ≤ ζ := by nlinarith
    linarith

end

end GaloisForLFunctions.FamilyContinuationTheory.Budget

noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Classical Topology ContDiff SchwartzMap ComplexConjugate

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open GaloisForLFunctions.FamilyContinuationTheory

/-! ### Complete-factor (`16/5`) crossing, plain capacity, and balanced cutoff -/

namespace HeckeDetectorRowCount

def denominator₃₂ (x : ℝ) : ℝ := 3 - 9 * x / 4

def primeWeight₃₂ (x : ℝ) : ℝ := (2 - 5 * x / 4) * (1 - x)

def crossing₃₂ (x t : ℝ) : ℝ := ((2 - 5 * x / 4) * t - 3 * x / 8) / denominator₃₂ x

def plainExponent₃₂ (δ x t r : ℝ) : ℝ := 1 - δ * (5 * x / 8 + (2 - 5 * x / 4) * (t - r))

def shortExponent₃₂ (δ x t : ℝ) : ℝ := 1 - δ + δ * primeWeight₃₂ x / denominator₃₂ x * (3 / 2 - t)

def balancedCutoff₃₂ (δ x : ℝ) : ℝ :=
  1 + δ * Budget.rowP₃₂ x / (2 * Budget.rowJ₃₂ δ x)

lemma denominator₃₂_lower {x : ℝ} (hx : x ≤ 1 / 2) : 15 / 8 ≤ denominator₃₂ x := by
  unfold denominator₃₂
  linarith

theorem crossing₃₂_bounds {x t : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2)
    (ht : 1 ≤ t) (ht' : t ≤ 3 / 2) :
    23 / 37 ≤ crossing₃₂ x t ∧ crossing₃₂ x t ≤ 1 ∧
      1 / 3 ≤ t - crossing₃₂ x t ∧ t - crossing₃₂ x t ≤ 1 / 2 := by
  have hd : 0 < denominator₃₂ x := lt_of_lt_of_le (by norm_num) (denominator₃₂_lower hx')
  have hp : 0 ≤ 2 - 5 * x / 4 := by linarith
  have hpt := mul_le_mul_of_nonneg_left ht hp
  have hpt' := mul_le_mul_of_nonneg_left ht' hp
  have hm : 0 ≤ 1 - x := by linarith
  have hmt := mul_le_mul_of_nonneg_left ht hm
  have hmt' := mul_le_mul_of_nonneg_left ht' hm
  have he : t - crossing₃₂ x t = ((1 - x) * t + 3 * x / 8) / denominator₃₂ x := by
    unfold crossing₃₂
    apply (eq_div_iff hd.ne').mpr
    rw [sub_mul, div_mul_cancel₀ _ hd.ne']
    unfold denominator₃₂
    ring
  refine ⟨(le_div_iff₀ hd).mpr ?_, (div_le_iff₀ hd).mpr ?_, ?_, ?_⟩
  · unfold denominator₃₂
    nlinarith
  · unfold denominator₃₂
    nlinarith
  · rw [he]
    apply (le_div_iff₀ hd).mpr
    unfold denominator₃₂
    nlinarith
  · rw [he]
    apply (div_le_iff₀ hd).mpr
    unfold denominator₃₂
    nlinarith

lemma inverse_at_crossing₃₂ (δ x t : ℝ) (hd : denominator₃₂ x ≠ 0) :
    inverseExponent δ x (crossing₃₂ x t) = shortExponent₃₂ δ x t := by
  unfold inverseExponent crossing₃₂ shortExponent₃₂ primeWeight₃₂
  field_simp
  unfold denominator₃₂
  ring

lemma plain_at_crossing₃₂ (δ x t : ℝ) (hd : denominator₃₂ x ≠ 0) :
    plainExponent₃₂ δ x t (crossing₃₂ x t) = shortExponent₃₂ δ x t := by
  unfold plainExponent₃₂ crossing₃₂ shortExponent₃₂ primeWeight₃₂
  field_simp
  unfold denominator₃₂
  ring

theorem selected_short_bound₃₂ {δ x t r : ℝ} (hδ : 0 ≤ δ) (_hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    (r ≤ crossing₃₂ x t → plainExponent₃₂ δ x t r ≤ shortExponent₃₂ δ x t) ∧
      (crossing₃₂ x t ≤ r → inverseExponent δ x r ≤ shortExponent₃₂ δ x t) := by
  have hd : denominator₃₂ x ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (denominator₃₂_lower hx'))
  constructor
  · intro hr
    rw [← plain_at_crossing₃₂ δ x t hd]
    unfold plainExponent₃₂
    have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 - 5 * x / 4 by linarith)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]
  · intro hr
    rw [← inverse_at_crossing₃₂ δ x t hd]
    unfold inverseExponent
    have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 1 - x by linarith)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]

lemma short₃₂_ge_base {δ x t : ℝ} (hδ : 0 ≤ δ) (_hx : 0 ≤ x) (hx' : x ≤ 1 / 2)
    (ht : t ≤ 3 / 2) : 1 - δ ≤ shortExponent₃₂ δ x t := by
  have hd : 0 < denominator₃₂ x := lt_of_lt_of_le (by norm_num) (denominator₃₂_lower hx')
  have hp : 0 ≤ primeWeight₃₂ x := mul_nonneg (by linarith) (by linarith)
  unfold shortExponent₃₂
  exact le_add_of_nonneg_right (mul_nonneg (div_nonneg (mul_nonneg hδ hp) hd.le) (by linarith))

theorem capacity_loss₃₂ {q m Δ γ : ℝ} (_hq : 0 ≤ q) (hq' : q ≤ 1 / 2)
    (hm : 1 / 3 - γ ≤ m) (_hm' : m ≤ 1 / 2) (hΔ : 0 ≤ Δ) (hΔ' : Δ ≤ 1 / 8) (hγ : 0 ≤ γ) :
    2 * q * (1 - 2 * m) * (5 / 16 - 1 / (16 / 5 + 12 * Δ)) ≤ Δ / 2 + 2 * γ := by
  have hd : 0 < 16 / 5 + 12 * Δ := by linarith
  have hden : (256 / 25 : ℝ) ≤ (16 / 5) * (16 / 5 + 12 * Δ) := by nlinarith
  have hqmul : q * (1 - 2 * m) ≤ (1 / 2) * (1 / 3 + 2 * γ) :=
    mul_le_mul hq' (by linarith) (by linarith) (by norm_num)
  have hn := mul_le_mul_of_nonneg_right hqmul (show 0 ≤ 24 * Δ by positivity)
  have hg := mul_le_mul_of_nonneg_left hΔ' (show 0 ≤ 24 * γ by positivity)
  have he : 2 * q * (1 - 2 * m) * (5 / 16 - 1 / (16 / 5 + 12 * Δ)) =
      24 * q * (1 - 2 * m) * Δ / ((16 / 5) * (16 / 5 + 12 * Δ)) := by
    field_simp
    ring
  rw [he]
  apply (div_le_iff₀ (show 0 < (16 / 5) * (16 / 5 + 12 * Δ) by positivity)).mpr
  have hb := mul_le_mul_of_nonneg_left hden (show 0 ≤ Δ / 2 + 2 * γ by positivity)
  nlinarith

theorem plain_capacity_comparison₃₂ {δ x Δ t r m γ : ℝ}
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (hx : 0 ≤ x) (hx' : x ≤ 1 / 2)
    (hΔ : 0 ≤ Δ) (hΔ' : Δ ≤ 1 / 8) (hm : 1 / 3 - γ ≤ m) (hm' : m ≤ 1 / 2)
    (hγ : 0 ≤ γ) (hlength : t - r - γ ≤ m) :
    1 - 2 * δ * m - 2 * (δ * x) * (1 - 2 * m) / (16 / 5 + 12 * Δ) ≤
      plainExponent₃₂ δ x t r + Δ / 2 + 4 * γ := by
  have hq : 0 ≤ δ * x := mul_nonneg hδ hx
  have hq' : δ * x ≤ 1 / 2 := (mul_le_mul hδ' hx' hx (by norm_num)).trans_eq (by ring)
  have hloss := capacity_loss₃₂ hq hq' hm hm' hΔ hΔ' hγ
  have hc : 0 ≤ δ * (2 - 5 * x / 4) := mul_nonneg hδ (by linarith)
  have hc' : δ * (2 - 5 * x / 4) ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_right hδ' (show 0 ≤ 2 - 5 * x / 4 by linarith)
    nlinarith
  have hlinear := mul_le_mul_of_nonneg_left (show t - r - m ≤ γ by linarith) hc
  have herror := mul_le_mul_of_nonneg_right hc' hγ
  have hid : (1 - 2 * δ * m - 2 * (δ * x) * (1 - 2 * m) * (5 / 16)) - plainExponent₃₂ δ x t r =
      δ * (2 - 5 * x / 4) * (t - r - m) := by unfold plainExponent₃₂; ring
  have hid' : 1 - 2 * δ * m - 2 * (δ * x) * (1 - 2 * m) / (16 / 5 + 12 * Δ) =
      (1 - 2 * δ * m - 2 * (δ * x) * (1 - 2 * m) * (5 / 16)) +
      2 * (δ * x) * (1 - 2 * m) * (5 / 16 - 1 / (16 / 5 + 12 * Δ)) := by ring
  rw [hid']
  linarith

theorem count_bound_of_source_branches₃₂ (B C U δ x Δ t r m ε ν γ : ℝ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδ' : δ ≤ 5 / 6)
    (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) (hΔ : 0 ≤ Δ) (hΔ' : Δ ≤ 1 / 8)
    (ht : 1 ≤ t) (ht' : t ≤ 3 / 2) (hν : 0 ≤ ν) (hγ : 0 ≤ γ)
    (hleft : t - r - γ ≤ m) (hright : r ≤ t + γ)
    (hI0 : B ≤ C * U ^ (max 1 ((1 + 5 * r) / 6) - δ * r + ε))
    (hP0 : B ≤ C * U ^ (1 - 2 * δ * m + ε))
    (hI : 23 / 37 ≤ r → r < 1 → ν < (1 - r) / 2 → B ≤ C * U ^ (inverseExponent δ x r + ε))
    (hP : r ≤ crossing₃₂ x t → m < 1 / 2 → ν < (1 - 2 * m) / (16 / 5 + 12 * Δ) →
      B ≤ C * U ^ (1 - 2 * δ * m - 2 * (δ * x) * (1 - 2 * m) / (16 / 5 + 12 * Δ) + ε)) :
    B ≤ C * U ^ (max (shortExponent₃₂ δ x t) (longExponent δ t) + Δ / 2 + ε + 6 * ν + 5 * γ) := by
  let target := max (shortExponent₃₂ δ x t) (longExponent δ t) + Δ / 2 + ε + 6 * ν + 5 * γ
  have hshort : shortExponent₃₂ δ x t ≤ max (shortExponent₃₂ δ x t) (longExponent δ t) :=
    le_max_left _ _
  have hlong : longExponent δ t ≤ max (shortExponent₃₂ δ x t) (longExponent δ t) :=
    le_max_right _ _
  have hbase := short₃₂_ge_base hδ hx hx' ht'
  have hcross := crossing₃₂_bounds hx hx' ht ht'
  have hchoose := selected_short_bound₃₂ (t := t) (r := r) hδ hx hx'
  have promote (p : ℝ) (hp : B ≤ C * U ^ p) (hpt : p ≤ target) : B ≤ C * U ^ target :=
    hp.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hpt) hC)
  by_cases hr1 : 1 ≤ r
  · have hmax : max 1 ((1 + 5 * r) / 6) = (1 + 5 * r) / 6 := max_eq_right (by linarith)
    rw [hmax] at hI0
    apply promote _ hI0
    have hl := long_count_bound hδ' hγ hright
    dsimp [target]
    have hcγ : (5 / 6 - δ) * γ ≤ γ := by nlinarith [mul_nonneg hδ hγ]
    nlinarith
  have hr1' : r < 1 := lt_of_not_ge hr1
  have hmax : max 1 ((1 + 5 * r) / 6) = 1 := max_eq_left (by linarith)
  rw [hmax] at hI0
  by_cases hrc : crossing₃₂ x t ≤ r
  · by_cases hcap : (1 - r) / 2 ≤ ν
    · apply promote _ hI0
      have hz := inverse_zero_capacity hδ hcap
      have hv : 2 * δ * ν ≤ 6 * ν := by nlinarith [mul_nonneg (sub_nonneg.mpr hδ') hν]
      dsimp [target]
      linarith
    · apply promote _ (hI (hcross.1.trans hrc) hr1' (lt_of_not_ge hcap))
      have hs := hchoose.2 hrc
      dsimp [target]
      linarith
  have hrc' : r ≤ crossing₃₂ x t := (lt_of_not_ge hrc).le
  by_cases hm : 1 / 2 ≤ m
  · apply promote _ hP0
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    dsimp [target]
    linarith
  have hm' : m < 1 / 2 := lt_of_not_ge hm
  by_cases hcap : (1 - 2 * m) / (16 / 5 + 12 * Δ) ≤ ν
  · apply promote _ hP0
    have hk0 : 0 < 8 / 15 + 2 * Δ := by linarith
    have hk1 : 8 / 15 + 2 * Δ ≤ 1 := by linarith
    have hz := plain_zero_capacity hδ hk0 hk1 hν
      (show (1 - 2 * m) / (6 * (8 / 15 + 2 * Δ)) ≤ ν by
        convert hcap using 1; ring)
    have hv : 6 * δ * ν ≤ 6 * ν := by nlinarith [mul_nonneg (sub_nonneg.mpr hδ') hν]
    dsimp [target]
    linarith
  · apply promote _ (hP hrc' hm' (lt_of_not_ge hcap))
    have hmm : 1 / 3 - γ ≤ m := by linarith [hcross.2.2.1]
    have hp := plain_capacity_comparison₃₂ hδ (show δ ≤ 1 by linarith) hx hx' hΔ hΔ'
      hmm hm'.le hγ hleft
    have hs := hchoose.1 hrc'
    dsimp [target]
    linarith

theorem balanced_cutoff₃₂_bounds {δ x : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 5 / 6)
    (_hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    1 ≤ balancedCutoff₃₂ δ x ∧ balancedCutoff₃₂ δ x ≤ 3 / 2 := by
  have hJ := Budget.rowJ₃₂_pos hδ hδ' hx'
  have hD0 : 0 ≤ Budget.rowD₃₂ x := by unfold Budget.rowD₃₂; linarith
  have hP0 : 0 ≤ Budget.rowP₃₂ x := by
    unfold Budget.rowP₃₂; exact mul_nonneg (by linarith) (by linarith)
  unfold balancedCutoff₃₂
  constructor
  · exact le_add_of_nonneg_right (div_nonneg (mul_nonneg hδ hP0) (by linarith))
  · have hnum : δ * Budget.rowP₃₂ x ≤ Budget.rowJ₃₂ δ x := by
      unfold Budget.rowJ₃₂
      nlinarith [mul_nonneg (sub_nonneg.mpr hδ') hD0]
    have hh : δ * Budget.rowP₃₂ x / (2 * Budget.rowJ₃₂ δ x) ≤ 1 / 2 :=
      (div_le_iff₀ (by linarith)).mpr (by linarith)
    linarith

theorem balanced_count_identity₃₂ {δ x : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 5 / 6)
    (_hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    max (shortExponent₃₂ δ x (balancedCutoff₃₂ δ x))
        (longExponent δ (balancedCutoff₃₂ δ x)) =
      Budget.rowCount₃₂ δ x := by
  have hD0 : 0 < denominator₃₂ x := lt_of_lt_of_le (by norm_num) (denominator₃₂_lower hx')
  have hJ := Budget.rowJ₃₂_pos hδ hδ' hx'
  have hJ0 : 0 < Budget.rowJ₃₂ δ x := by linarith
  have hl : longExponent δ (balancedCutoff₃₂ δ x) = Budget.rowCount₃₂ δ x := by
    unfold longExponent balancedCutoff₃₂ Budget.rowCount₃₂
    field_simp [hJ0.ne']
    ring
  have hs : shortExponent₃₂ δ x (balancedCutoff₃₂ δ x) = Budget.rowCount₃₂ δ x := by
    unfold shortExponent₃₂ balancedCutoff₃₂ Budget.rowCount₃₂
    have hD_eq : denominator₃₂ x = Budget.rowD₃₂ x := rfl
    have hP_eq : primeWeight₃₂ x = Budget.rowP₃₂ x := rfl
    rw [hD_eq, hP_eq]
    generalize hDd : Budget.rowD₃₂ x = D at *
    generalize hPd : Budget.rowP₃₂ x = P at *
    generalize hJd : Budget.rowJ₃₂ δ x = J at *
    have hJdef : J = (5 / 6 - δ) * D + δ * P := by
      rw [← hJd, Budget.rowJ₃₂, hDd, hPd]
    have hD : D ≠ 0 := by rw [← hDd]; exact hD0.ne'
    have hJ' : J ≠ 0 := hJ0.ne'
    field_simp [hD, hJ']
    rw [hJdef]
    ring
  rw [hl, hs, max_self]

end HeckeDetectorRowCount

namespace HeckeDetectorBranchBudget
open HeckeDetectorRowCount

theorem plain_marked_loss₃₂ (m δ x Δ ε εm mesh ν : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (_hx : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hε : 0 ≤ ε) (hmesh : 0 ≤ mesh) (hν : 0 ≤ ν) :
    1 - 2 * δ * m - 2 * (δ * x) * ((1 - 2 * m) / (16 / 5 + 12 * Δ) - ν) +
      4 * ε + δ * mesh + εm ≤
      1 - 2 * δ * m - 2 * (δ * x) * (1 - 2 * m) / (16 / 5 + 12 * Δ) +
        commonLoss ε εm mesh ν := by
  have hq : 2 * (δ * x) ≤ 1 := by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hx1), hδ1]
  have hm := mul_le_mul_of_nonneg_right hδ1 hmesh
  have hn := mul_le_mul_of_nonneg_right hq hν
  unfold commonLoss
  have heq : 2 * (δ * x) * ((1 - 2 * m) / (16 / 5 + 12 * Δ) - ν) =
      2 * (δ * x) * (1 - 2 * m) / (16 / 5 + 12 * Δ) - 2 * (δ * x) * ν := by ring
  rw [heq]
  linarith

theorem plain_requested_capacity₃₂ (Δ x t r m ε ν : ℝ)
    (hΔ : 0 ≤ Δ) (hx : 0 ≤ x) (hx1 : x ≤ 1 / 2) (ht : 1 ≤ t) (ht1 : t ≤ 3 / 2)
    (hr : r ≤ crossing₃₂ x t) (hleft : t - r - ε ≤ m) (hε : ε ≤ 1 / 1000)
    (hν : 0 ≤ ν) (hνcap : ν < (1 - 2 * m) / (16 / 5 + 12 * Δ)) :
    33 / 100 ≤ m ∧
      0 ≤ (1 - 2 * m) / (16 / 5 + 12 * Δ) - ν ∧
      (1 - 2 * m) / (16 / 5 + 12 * Δ) - ν ≤ 7 / 37 ∧
      2 * m + 6 * (8 / 15 + 2 * Δ) * ((1 - 2 * m) / (16 / 5 + 12 * Δ) - ν) ≤ 1 := by
  have hcross := crossing₃₂_bounds hx hx1 ht ht1
  have hm : 33 / 100 ≤ m := by linarith [hcross.2.2.1]
  have hd : 0 < 16 / 5 + 12 * Δ := by linarith
  have hc : (1 - 2 * m) / (16 / 5 + 12 * Δ) ≤ 7 / 37 := (div_le_iff₀ hd).mpr (by nlinarith)
  refine ⟨hm, by linarith, by linarith, ?_⟩
  have heq : 6 * (8 / 15 + 2 * Δ) = 16 / 5 + 12 * Δ := by ring
  rw [heq, mul_sub, mul_div_cancel₀ _ hd.ne']
  nlinarith [mul_nonneg hd.le hν]

end HeckeDetectorBranchBudget

namespace HeckeDetectorAdaptiveCutoff
open HeckeDetectorRowCount

def cutoff₃₂ (δ q : ℝ) : ℝ :=
  if δ ≤ 5 / 6 then balancedCutoff₃₂ δ (min (1 / 2) (max 0 (q / δ))) else 3 / 2

theorem cutoff₃₂_bounds (δ q : ℝ) (hδ : 0 ≤ δ) :
    1 ≤ cutoff₃₂ δ q ∧ cutoff₃₂ δ q ≤ 3 / 2 := by
  unfold cutoff₃₂
  split_ifs with hd
  · exact balanced_cutoff₃₂_bounds hδ hd (le_min (by norm_num) (le_max_left _ _)) (min_le_left _ _)
  · norm_num

theorem cutoff₃₂_eq_balanced (δ q : ℝ) (hδ : 0 < δ) (hd : δ ≤ 5 / 6)
    (hq : 0 ≤ q) (hq' : q ≤ δ / 2) :
    cutoff₃₂ δ q = balancedCutoff₃₂ δ (q / δ) := by
  have hx : 0 ≤ q / δ := div_nonneg hq hδ.le
  have hx' : q / δ ≤ 1 / 2 := (div_le_iff₀ hδ).mpr (by linarith)
  simp only [cutoff₃₂, if_pos hd, max_eq_right hx, min_eq_right hx']

theorem cutoff₃₂_eq_high (δ q : ℝ) (hδ : 5 / 6 < δ) : cutoff₃₂ δ q = 3 / 2 := by
  simp only [cutoff₃₂, if_neg (not_le_of_gt hδ)]

end HeckeDetectorAdaptiveCutoff

/-! ### Upgraded raw-fiber moments and fixed-amplitude row counts -/

namespace HeckeDetectorRawFiber
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorWitnessRows
open HeckeDetectorSupportedWitness HeckeDetectorPlainFiberCount HeckeDetectorRowwisePolynomial
open HeckeDetectorDyadicProfiles HeckeDetectorCoefficientTransfer

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

/-- The four moment estimates with the complete-factor `16/5 + 12 Δ` plain-marked capacity on
`33/100 ≤ F.m < 1/2`. -/
structure Moments₃₂ (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (Δ c κ C height εm : ℝ) : Prop where
  inverse_raw : ∀ n : ℕ, n ≤ 2 → ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (-height) height,
    let W := twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t
    RawMoment F.rowData W c κ C ∧ RawMoment F.rowData (scaleProfile W) c κ C
  inverse_marked : ∀ selected : Finset Slot, selected ⊆ F.slots →
    F.r + 2 * (∑ s ∈ selected, F.widths s) < 1 →
    2 * F.r + 8 * (∑ s ∈ selected, F.widths s) < 3 →
    ∀ n : ℕ, n ≤ 2 → ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (-height) height,
      ∑ u ∈ F.rows, ‖polynomial (F.family u F.label) true ((logProfile^[n]) F.inverseProfile)
        (U ^ F.r) s t * F.physicalProduct selected u‖ ^ 2 ≤ C * U ^ (1 + εm)
  plain_marked : 33 / 100 ≤ F.m → F.m < 1 / 2 →
    ∀ selected : Finset Slot, selected ⊆ F.slots →
    2 * F.m + (16 / 5 + 12 * Δ) * (∑ s ∈ selected, F.widths s) ≤ 1 →
    ∀ j k : ℕ, j + k ≤ 2 → ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (-height) height,
      ∑ u ∈ F.rows, ‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
          (U ^ F.m) s t *
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
          (U ^ F.m) s t *
        F.physicalProduct selected u‖ ^ 2 ≤ C * U ^ (1 + εm)
  plain_unmarked : ∀ j k : ℕ, j + k ≤ 2 → ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (-height) height,
      ∑ u ∈ F.rows, ‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
          (U ^ F.m) s t *
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
          (U ^ F.m) s t‖ ^ 2 ≤
        C * U ^ (max 1 (2 * F.m) + εm)

theorem Fiber.inverse_marked_count₃₂ (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {Δ c κ C height εm : ℝ} (moments : Moments₃₂ F Δ c κ C height εm)
    (hU : 1 < U) (ha : 1 / 2 ≤ a) (hC : 0 ≤ C) (hh : 0 ≤ height)
    (hf : 2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height)
    (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 7 / 37) (hcap1 : F.r + 2 * z < 1)
    (hcap2 : 2 * F.r + 8 * z < 3) :
    (F.rows.card : ℝ) ≤
      (12 * (1 + height) * C) * U ^ (1 - (2 * a - 1) * F.r - 2 * F.q * z +
        2 * ε + (2 * a - 1) * F.mesh + εm) :=
  HeckeDetectorInverseFiberCount.inverse_fiber_count M H F.rows F.nonempty F.family U a ε tstar T
    allowance i hU ha (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label
    F.fixed_left F.fixed_right F.slots (fun u => u.val) F.profile F.upper F.widths F.bin
    F.external F.mesh F.binWidth z εm C height F.mesh_nonneg F.binWidth_pos F.widths_pos
    F.widths_mesh (by linarith [F.supply]) hz (hz'.trans F.supply) F.fixed_bin hC hh hf
    hcap1 hcap2 moments.inverse_marked

theorem Fiber.plain_marked_count₃₂ (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {Δ c κ C height εm : ℝ} (moments : Moments₃₂ F Δ c κ C height εm)
    (hU : 1 < U) (ha : 1 / 2 ≤ a) (hΔ : 0 ≤ Δ) (hC : 0 ≤ C) (hh : 0 ≤ height)
    (hf : 2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height)
    (hm0 : 33 / 100 ≤ F.m) (hm1 : F.m < 1 / 2)
    (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 7 / 37) (hcap : 2 * F.m + 6 * (8 / 15 + 2 * Δ) * z ≤ 1) :
    (F.rows.card : ℝ) ≤
      (192 * (1 + height) * C) * U ^ (1 - 2 * (2 * a - 1) * F.m - 2 * F.q * z +
        4 * ε + (2 * a - 1) * F.mesh + εm) := by
  refine plain_fiber_count M H F.rows F.nonempty F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left
    F.fixed_right F.slots (fun u => u.val) F.profile F.upper F.widths F.bin F.external F.mesh
    F.binWidth z (8 / 15 + 2 * Δ) εm C height F.mesh_nonneg F.binWidth_pos F.widths_pos
    F.widths_mesh (by linarith [F.supply]) hz (hz'.trans F.supply) F.fixed_bin (by linarith)
    hC hh hf hcap ?_
  intro selected hsub hcap_sel
  change 2 * F.m + 6 * (8 / 15 + 2 * Δ) * (∑ s ∈ selected, F.widths s) ≤ 1 at hcap_sel
  have hcap_sel' : 2 * F.m + (16 / 5 + 12 * Δ) * (∑ s ∈ selected, F.widths s) ≤ 1 := by
    linarith
  exact moments.plain_marked hm0 hm1 selected hsub hcap_sel'

theorem Fiber.plain_unmarked_count₃₂ (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {Δ c κ C height εm : ℝ} (moments : Moments₃₂ F Δ c κ C height εm)
    (hU : 1 < U) (ha : 0 ≤ a) (hC : 0 ≤ C) (hh : 0 ≤ height)
    (hf : 2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height) :
    (F.rows.card : ℝ) ≤
      (192 * (1 + height) * C) * U ^ (max 1 (2 * F.m) - 2 * (2 * a - 1) * F.m + 4 * ε + εm) :=
  HeckeDetectorNoSlotPlainCount.no_slot_plain_count F.rows F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left
    F.fixed_right εm C height hC hh hf moments.plain_unmarked

end HeckeDetectorRawFiber

namespace HeckeDetectorCountFromMoments
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBranchBudget
open HeckeDetectorRowCount HeckeDetectorBatch

theorem count_from_raw_moments₃₂
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ c κ K₀ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < κ ∧ 0 ≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε tstar T allowance Δ ν C height : ℝ) (i : ℕ),
      1 < U → 51 / 100 < a → 2 * a - 1 ≤ 5 / 6 → 0 ≤ ε → ε ≤ 1 / 1000 →
      1 ≤ tstar → tstar ≤ 3 / 2 → 0 ≤ Δ → Δ ≤ 1 / 8 → 0 < ν → 0 ≤ C → 0 ≤ height →
      2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
      ∀ {Label Slot : Type*} (F : Fiber M H Label Slot U a ε tstar T allowance i),
      Moments₃₂ F Δ c κ C height εm →
      (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
        U ^ (max (shortExponent₃₂ (2 * a - 1) (F.q / (2 * a - 1)) tstar)
          (longExponent (2 * a - 1) tstar) + Δ / 2 + 159 * ε + εm + F.mesh + 7 * ν) := by
  obtain ⟨c, κ, K₀, hc, hc1, hκ, hK, hamp⟩ :=
    HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c, κ, K₀, hc, hc1, hκ, hK, ?_⟩
  filter_upwards [hamp] with U hamp
  intro a ε tstar T allowance Δ ν C height i hU ha hδcap hε hεsmall ht ht' hΔ hΔ' hν hC hh hf
    Label Slot F moments
  let δ := 2 * a - 1
  let x := F.q / δ
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have ha' : 1 / 2 ≤ a := by linarith
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
  obtain ⟨hq0, hqδ⟩ := F.mean_bounds ha'
  have hx : 0 ≤ x := div_nonneg hq0 hδ.le
  have hx' : x ≤ 1 / 2 := (div_le_iff₀ hδ).mpr (by dsimp [δ]; linarith)
  have hqx : δ * x = F.q := by dsimp [x]; field_simp
  have hgeom := F.lengths hU
  have hr0 : 0 ≤ F.r := by linarith [hgeom.2.2.2.1]
  have hr2 : F.r ≤ 2 := by linarith [hgeom.2.1]
  have hUp : 0 < U := zero_lt_one.trans hU
  obtain ⟨hconst, hconstP, hconstI, hconstI0⟩ := fiberConstant_bounds C height K₀ hC hh hK
  have promote (C' p q : ℝ) (hC' : C' ≤ fiberConstant C height K₀)
      (hb : (F.rows.card : ℝ) ≤ C' * U ^ p) (hpq : p ≤ q) :
      (F.rows.card : ℝ) ≤ fiberConstant C height K₀ * U ^ q :=
    hb.trans ((mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hUp.le _)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hpq) hconst))
  have hi0 := hamp F.rows F.family a ε tstar T allowance i hU ha'
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left
    F.fixed_right hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff
    moments.inverse_raw
  have hI0 : (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
      U ^ (max 1 ((1 + 5 * F.r) / 6) - δ * F.r + commonLoss ε εm F.mesh ν) := by
    apply promote _ _ _ hconstI0 hi0
    exact no_slot_inverse_loss F.r δ ε εm F.mesh ν hε F.mesh_nonneg hν.le
  have hp0 := F.plain_unmarked_count₃₂ moments hU (by linarith) hC hh hf
  have hP0 : (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
      U ^ (1 - 2 * δ * F.m + commonLoss ε εm F.mesh ν) := by
    apply promote _ _ _ hconstP hp0
    exact no_slot_plain_loss F.m δ ε εm F.mesh ν hε hgeom.2.2.1 F.mesh_nonneg hν.le
  have hI : 23 / 37 ≤ F.r → F.r < 1 → ν < (1 - F.r) / 2 →
      (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
        U ^ (inverseExponent δ x F.r + commonLoss ε εm F.mesh ν) := by
    intro hr hr1 hv
    obtain ⟨hz, hz', hcap1, hcap2⟩ := inverse_requested_capacity F.r ν hr hr1 hν hv
    have hb := F.inverse_marked_count₃₂ moments hU ha' hC hh hf ((1 - F.r) / 2 - ν) hz hz'
      hcap1 hcap2
    apply promote _ _ _ hconstI hb
    have hl := inverse_marked_loss F.r δ x ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
    rwa [hqx] at hl
  have hP : F.r ≤ crossing₃₂ x tstar → F.m < 1 / 2 → ν < (1 - 2 * F.m) / (16 / 5 + 12 * Δ) →
      (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
        U ^ (1 - 2 * δ * F.m - 2 * (δ * x) * (1 - 2 * F.m) / (16 / 5 + 12 * Δ) +
          commonLoss ε εm F.mesh ν) := by
    intro hr hm hv
    obtain ⟨hm33, hz, hz', hcap⟩ := plain_requested_capacity₃₂ Δ x tstar F.r F.m ε ν hΔ hx hx'
      ht ht' hr hgeom.1 hεsmall hν.le hv
    have hb := F.plain_marked_count₃₂ moments hU ha' hΔ hC hh hf hm33 hm
      ((1 - 2 * F.m) / (16 / 5 + 12 * Δ) - ν) hz hz' hcap
    apply promote _ _ _ hconstP hb
    have hl := plain_marked_loss₃₂ F.m δ x Δ ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
    simpa only [hqx] using hl
  have hc' := count_bound_of_source_branches₃₂ (F.rows.card : ℝ) (fiberConstant C height K₀) U
    δ x Δ tstar F.r F.m (commonLoss ε εm F.mesh ν) ν ε hconst hU.le hδ.le hδcap hx hx' hΔ hΔ'
    ht ht' hν.le hε hgeom.1 hgeom.2.1 hI0 hP0 hI hP
  convert hc' using 1; congr 2
  unfold commonLoss
  ring

theorem high_count_from_raw_moments₃₂
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ c κ K₀ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < κ ∧ 0 ≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height : ℝ) (i : ℕ),
      1 < U → 5 / 6 ≤ 2 * a - 1 → a ≤ 1 → 0 ≤ ε → ε ≤ 1 / 1000 → 0 ≤ C → 0 ≤ height →
      2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
      ∀ {Label Slot : Type*} [Fintype Label]
        (B : Batch M H Label Slot U a ε (3 / 2) T allowance i),
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        Moments₃₂ (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ) *
        (HeckeDetectorWitnessRows.dyadicLength U : ℝ) ^ 2 *
        fiberConstant C height K₀ * (Fintype.card B.Bin : ℝ) *
        U ^ (1 - (2 * a - 1) + 78 * ε + εm) := by
  obtain ⟨c, κ, K₀, hc, hc1, hκ, hK, hamp⟩ :=
    HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c, κ, K₀, hc, hc1, hκ, hK, ?_⟩
  filter_upwards [hamp] with U hamp
  intro a ε T allowance Δ C height i hU ha ha' hε _hεsmall hC hh hf Label Slot _ B moments
  have hb := B.card_bound (fiberConstant C height K₀) (fun _ => 1 - (2 * a - 1) + 78 * ε + εm)
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
      intro bin j J K hne
      let F := B.fiber bin j J K hne
      have hgeom := F.lengths hU
      have hr0 : 0 ≤ F.r := by linarith [hgeom.2.2.2.1]
      have hr2 : F.r ≤ 2 := by linarith [hgeom.2.1]
      obtain ⟨hconst, _, _, hconstI⟩ := fiberConstant_bounds C height K₀ hC hh hK
      have hi := hamp F.rows F.family a ε (3 / 2) T allowance i hU (by linarith)
        (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left
        F.fixed_right hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff
        (moments bin j J K hne).inverse_raw
      have hbi : (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
          U ^ (max 1 ((1 + 5 * F.r) / 6) - (2 * a - 1) * F.r + (2 * ε + εm)) := by
        apply hi.trans
        convert mul_le_mul_of_nonneg_right hconstI
          (Real.rpow_nonneg (zero_lt_one.trans hU).le
            (max 1 ((1 + 5 * F.r) / 6) - (2 * a - 1) * F.r + 2 * ε + εm)) using 1 <;>
          congr 2; ring
      have hout := high_bin_count hconst hU.le ha (show 2 * a - 1 ≤ 1 by linarith)
        (show 0 ≤ 76 * ε by positivity) (show 1 - 76 * ε ≤ F.r by linarith [hgeom.2.2.2.1]) hbi
      convert hout using 1; congr 2; ring)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hb

end HeckeDetectorCountFromMoments

/-! ### Complete-factor adaptive source counts and nonfloor amplitude classes -/

namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff HeckeDetectorFiberPartition
open ProbePhysical ProbeMellinBoundary ProbeRaySlots

local notation "O" => Eisenstein.O

theorem balanced_adaptive_count_from_raw_moments₃₂
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ c κ K₀ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < κ ∧ 0 ≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ ν C height q : ℝ) (i : ℕ),
      1 < U → 51 / 100 < a → 2 * a - 1 ≤ 5 / 6 → 0 ≤ ε → ε ≤ 1 / 1000 →
      0 ≤ Δ → Δ ≤ 1 / 8 → 0 < ν → 0 ≤ C → 0 ≤ height →
      2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
      ∀ {Label Slot : Type*} [Fintype Label]
        (B : Batch M H Label Slot U a ε (cutoff₃₂ (2 * a - 1) q) T allowance i),
      B.rows.Nonempty →
      (∀ u ∈ B.rows, rowMean B.slots U ((2 * a - 1) / 2) B.binWidth B.widths
        (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external U) u = q) →
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        Moments₃₂ (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ) * (dyadicLength U : ℝ) ^ 2 *
        fiberConstant C height K₀ * (Fintype.card B.Bin : ℝ) *
        U ^ (Budget.rowCount₃₂ (2 * a - 1) (q / (2 * a - 1)) +
          Δ / 2 + 159 * ε + εm + B.mesh + 7 * ν) := by
  obtain ⟨c, κ, K₀, hc, hc1, hκ, hK, hcount⟩ :=
    HeckeDetectorCountFromMoments.count_from_raw_moments₃₂
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c, κ, K₀, hc, hc1, hκ, hK, ?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance Δ ν C height q i hU ha hd hε hε' hΔ hΔ' hν hC hh hf Label Slot _ B
    hne hq hmom
  have hδ : 0 < 2 * a - 1 := by linarith
  have hqb := HeckeDetectorFixedAmplitudeCount.batch_mean_bounds B hne (by linarith) q hq
  have hx : 0 ≤ q / (2 * a - 1) := div_nonneg hqb.1 hδ.le
  have hx' : q / (2 * a - 1) ≤ 1 / 2 := (div_le_iff₀ hδ).mpr (by linarith [hqb.2])
  have ht := cutoff₃₂_bounds (2 * a - 1) q hδ.le
  have hb := B.card_bound (fiberConstant C height K₀)
    (fun _ => Budget.rowCount₃₂ (2 * a - 1) (q / (2 * a - 1)) +
      Δ / 2 + 159 * ε + εm + B.mesh + 7 * ν)
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
      intro bin j J K hnef
      have hc' := hcount a ε (cutoff₃₂ (2 * a - 1) q) T allowance Δ ν C height i
        hU ha hd hε hε' ht.1 ht.2 hΔ hΔ' hν hC hh hf
        (B.fiber bin j J K hnef) (hmom bin j J K hnef)
      rw [HeckeDetectorFixedAmplitudeCount.fiber_mean_eq B q hq bin j J K hnef] at hc'
      have he : max (shortExponent₃₂ (2 * a - 1) (q / (2 * a - 1)) (cutoff₃₂ (2 * a - 1) q))
          (longExponent (2 * a - 1) (cutoff₃₂ (2 * a - 1) q)) =
          Budget.rowCount₃₂ (2 * a - 1) (q / (2 * a - 1)) := by
        rw [cutoff₃₂_eq_balanced (2 * a - 1) q hδ hd hqb.1 hqb.2]
        exact balanced_count_identity₃₂ hδ.le hd hx hx'
      rwa [he] at hc')
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hb

theorem high_adaptive_count_from_raw_moments₃₂
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ c κ K₀ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < κ ∧ 0 ≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height q : ℝ) (i : ℕ),
      1 < U → 5 / 6 < 2 * a - 1 → a ≤ 1 → 0 ≤ ε → ε ≤ 1 / 1000 → 0 ≤ C → 0 ≤ height →
      2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
      ∀ {Label Slot : Type*} [Fintype Label]
        (B : Batch M H Label Slot U a ε (cutoff₃₂ (2 * a - 1) q) T allowance i),
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        Moments₃₂ (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ) * (dyadicLength U : ℝ) ^ 2 *
        fiberConstant C height K₀ * (Fintype.card B.Bin : ℝ) *
        U ^ (1 - (2 * a - 1) + 78 * ε + εm) := by
  obtain ⟨c, κ, K₀, hc, hc1, hκ, hK, hcount⟩ :=
    HeckeDetectorCountFromMoments.high_count_from_raw_moments₃₂
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c, κ, K₀, hc, hc1, hκ, hK, ?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance Δ C height q i hU ha ha' hε hε' hC hh hf
  rw [cutoff₃₂_eq_high (2 * a - 1) q ha]
  exact hcount a ε T allowance Δ C height i hU ha.le ha' hε hε' hC hh hf

/-- Adaptive row-count exponent under complete-factor (`16/5`) plain capacity. -/
def adaptiveRowExponent₃₂ (δ q Δ ε εm slotMesh ν : ℝ) : ℝ :=
  if δ ≤ 5 / 6 then Budget.rowCount₃₂ δ (q / δ) + Δ / 2 + 159 * ε + εm + slotMesh + 7 * ν
  else 1 - δ + 78 * ε + εm

section WithModulus
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Moment bounds for every retained source batch under `cutoff₃₂` and `Moments₃₂`. -/
def SourceMomentsAt₃₂ {N : ℕ} (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (η : Character) (rows : Finset FreeRow) (ell : Fin N → ℝ) (W : Fin N → ℝ → ℂ)
    (Z d a ε τ dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (Δ c κ C height εm : ℝ) : Prop :=
  ∀ q : ℝ, ∀ B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
      (Z ^ d) a ε (cutoff₃₂ (2 * a - 1) q) (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i,
    B.rows ⊆ rows → B.data = sourceMomentData M H hH S hS η →
    B.reverse = sourceMomentReverse M H → B.slots = Finset.univ →
    B.widths = (fun j => ell j / d) → B.profile = W → B.upper = (fun _ => b) →
    B.external = (fun _ => z) → B.mesh = slotMesh → B.binWidth = binWidth →
    (∀ u ∈ B.rows, ∀ j, B.family u j = sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) →
    ∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
      Moments₃₂ (B.fiber bin j J K hne) Δ c κ C height εm

theorem actual_source_amplitude_batches₃₂ (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀ P ∈ S, P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth : ℝ) (I : ℕ)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hdtop : dmax ≤ 37 / 42) (hτ : 0 < τ)
    (hτzero : τ < dmin / 2) (hτheight : 4 * τ < dmin * heightCost)
    (hε : 0 < ε) (he : 0 < e) (he' : e < 1 / 1000) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hheightCost : 0 ≤ heightCost) (hmargin : 0 < margin) (hm : 0 ≤ mesh) (hb : 0 < binWidth)
    (hbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κ + 2 * heightCost ≤ ε / 2) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
    ∀ (U : ℝ) (rows : Finset FreeRow), rows.Nonempty → rows ⊆ rowBand (Z ^ (1 / 100 : ℝ)) U →
      (∀ u ∈ rows, (calibrationForSet S hmax).residueMonoid u.val ≠ 0) →
      (∀ u ∈ rows, rowNorm u ≤ Z ^ (d - margin)) →
    ∀ (a : ℝ) (i : ℕ), i ≤ I → 51 / 100 < a → a ≤ 1 →
      (∀ u ∈ rows, detectorMaximum
        (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e) →
      (∀ u ∈ rows, a ≤ detectorMaximum
        (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3 * i : ℕ) * Z ^ τ)) →
    ∀ (N : ℕ) (ell : Fin N → ℝ), (∀ j, 0 < ell j) → (∀ j, ell j ≤ dmin * mesh) →
      (∑ j, ell j) = 1 / 6 →
    ∀ (W : Fin N → ℝ → ℂ) (upper : Fin N → ℝ) (z : Fin N → ℂ),
    let Q := physical M H (fun u : FreeRow => u.val) W upper (fun j => ell j / d) z (Z ^ d)
    ∀ bin : BinLabel (Finset.univ : Finset (Fin N)) ((2 * a - 1) / 2) binWidth,
    let rows' := amplitudeRows rows Finset.univ (Z ^ d) ((2 * a - 1) / 2) binWidth hb
      (fun j => ell j / d) Q bin
    rows'.Nonempty →
    let q := classMean Finset.univ ((2 * a - 1) / 2) binWidth (fun j => ell j / d) bin
    ∃ B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z ^ d) a ε (cutoff₃₂ (2 * a - 1) q) (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i,
      B.rows = rows' ∧ B.data = sourceMomentData M H hH S hS.prime η ∧
      B.reverse = sourceMomentReverse M H ∧ B.slots = Finset.univ ∧
      B.widths = (fun j => ell j / d) ∧ B.profile = W ∧ B.upper = upper ∧ B.external = z ∧
      B.mesh = mesh ∧ B.binWidth = binWidth ∧
      (∀ u ∈ rows', ∀ j, B.family u j =
        sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) ∧
      (∀ u ∈ B.rows, rowMean B.slots (Z ^ d) ((2 * a - 1) / 2) B.binWidth B.widths
        (physical M H (fun u : FreeRow => u.val)
          B.profile B.upper B.widths B.external (Z ^ d)) u = q) := by
  have hbatches := actual_source_batch M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin mesh binWidth I hdmin hdmax hdtop hτ hτzero hτheight
    hε he he' hκ hκ' hheightCost hmargin hm hb hbudget
  filter_upwards [hbatches] with Z hbatch
  intro d hd hd' U rows _hne hrows hcal hrow a i hi ha ha' hnext hcurrent N ell hell hsmall hsum
    W upper z
  dsimp only
  intro bin hne'
  let Q := physical M H (fun u : FreeRow => u.val) W upper (fun j => ell j / d) z (Z ^ d)
  let rows' := amplitudeRows rows Finset.univ (Z ^ d) ((2 * a - 1) / 2) binWidth hb
    (fun j => ell j / d) Q bin
  let q := classMean Finset.univ ((2 * a - 1) / 2) binWidth (fun j => ell j / d) bin
  have hsub : rows' ⊆ rows := Finset.filter_subset _ _
  have hcut := cutoff₃₂_bounds (2 * a - 1) q (by linarith)
  obtain ⟨B, hBr, hBd, hRev, hSlots, hWidths, hW, hUpper, hZ, hMesh, hBin, hFam⟩ :=
    hbatch d hd hd' U rows' hne' (hsub.trans hrows)
      (fun u hu => hcal u (hsub hu)) (fun u hu => hrow u (hsub hu)) a i hi ha ha'
      (fun u hu => hnext u (hsub hu)) (fun u hu => hcurrent u (hsub hu))
      (cutoff₃₂ (2 * a - 1) q) hcut.1 hcut.2 N ell hell hsmall hsum W upper z
  refine ⟨B, hBr, hBd, hRev, hSlots, hWidths, hW, hUpper, hZ, hMesh, hBin, hFam, ?_⟩
  intro u hu
  have hu' : u ∈ rows' := hBr ▸ hu
  rw [hSlots, hWidths, hW, hUpper, hZ, hBin]
  exact rowMean_eq rows Finset.univ (Z ^ d) ((2 * a - 1) / 2) binWidth hb
    (fun j => ell j / d) Q bin u hu'

end WithModulus
end ProbeHighRowFamily

namespace ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff HeckeDetectorFiberPartition
open ProbeHighRowFamily ProbePhysical ProbeMellinBoundary ProbeRaySlots Parameters

local notation "O" => Eisenstein.O

structure CountParameters₃₂ (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (εm : ℝ) where
  cB : ℝ
  kB : ℝ
  cH : ℝ
  kH : ℝ
  cB_pos : 0 < cB
  cB_one : cB ≤ 1
  kB_pos : 0 < kB
  cH_pos : 0 < cH
  cH_one : cH ≤ 1
  kH_pos : 0 < kH
  balanced : ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ ν C height q : ℝ) (i : ℕ),
      1 < U → 51 / 100 < a → 2 * a - 1 ≤ 5 / 6 → 0 ≤ ε → ε ≤ 1 / 1000 →
      0 ≤ Δ → Δ ≤ 1 / 8 → 0 < ν → 0 ≤ C → 0 ≤ height →
      2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
      ∀ {Label Slot : Type} [Fintype Label]
        (B : Batch M H Label Slot U a ε (cutoff₃₂ (2 * a - 1) q) T allowance i),
      B.rows.Nonempty →
      (∀ u ∈ B.rows, rowMean B.slots U ((2 * a - 1) / 2) B.binWidth B.widths
        (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external U) u = q) →
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        Moments₃₂ (B.fiber bin j J K hne) Δ cB kB C height εm) →
      (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ) * (dyadicLength U : ℝ) ^ 2 *
        fiberConstant C height K₀ * (Fintype.card B.Bin : ℝ) *
        U ^ (Budget.rowCount₃₂ (2 * a - 1) (q / (2 * a - 1)) +
          Δ / 2 + 159 * ε + εm + B.mesh + 7 * ν)
  high : ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height q : ℝ) (i : ℕ),
      1 < U → 5 / 6 < 2 * a - 1 → a ≤ 1 → 0 ≤ ε → ε ≤ 1 / 1000 → 0 ≤ C → 0 ≤ height →
      2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
      ∀ {Label Slot : Type} [Fintype Label]
        (B : Batch M H Label Slot U a ε (cutoff₃₂ (2 * a - 1) q) T allowance i),
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        Moments₃₂ (B.fiber bin j J K hne) Δ cH kH C height εm) →
      (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ) * (dyadicLength U : ℝ) ^ 2 *
        fiberConstant C height K₀ * (Fintype.card B.Bin : ℝ) *
        U ^ (1 - (2 * a - 1) + 78 * ε + εm)

theorem exists_count_parameters₃₂
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    Nonempty (CountParameters₃₂ M H εm) := by
  obtain ⟨cB, kB, KB, hcB, hcB1, hkB, hKB, hbalanced⟩ :=
    balanced_adaptive_count_from_raw_moments₃₂ M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  obtain ⟨cH, kH, KH, hcH, hcH1, hkH, hKH, hhigh⟩ :=
    high_adaptive_count_from_raw_moments₃₂ M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  exact ⟨⟨cB, kB, cH, kH, hcB, hcB1, hkB, hcH, hcH1, hkH, ⟨KB, hKB, hbalanced⟩, ⟨KH, hKH, hhigh⟩⟩⟩

theorem source_count_parameters₃₂ {Δ : ℝ} {D : HighData Δ} (F : SourceData D) :
    Nonempty (CountParameters₃₂ F.modulus ⊤ D.t) :=
  exists_count_parameters₃₂ F.modulus ⊤ le_top F.S F.w F.smooth F.compact
    F.positive_support (fun x => (F.bounded x).1) F.nonzero 1 2 1 (by norm_num) (by norm_num)
    (by norm_num) F.support (fun x => (F.bounded x).2) D.t D.t_pos

lemma moments₃₂_mono_constant {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    {F : Fiber M H Label Slot U a ε tstar T allowance i}
    {Δ c κ C D height εm : ℝ} (hU : 0 ≤ U) (h : Moments₃₂ F Δ c κ C height εm) (hCD : C ≤ D) :
    Moments₃₂ F Δ c κ D height εm where
  inverse_raw n hn s hs t ht :=
    ⟨rawMoment_mono_constant (h.inverse_raw n hn s hs t ht).1 hCD,
      rawMoment_mono_constant (h.inverse_raw n hn s hs t ht).2 hCD⟩
  inverse_marked selected hsel hcap1 hcap2 n hn s hs t ht :=
    (h.inverse_marked selected hsel hcap1 hcap2 n hn s hs t ht).trans
      (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hU _))
  plain_marked hm0 hm1 selected hsel hcap j k hj s hs t ht :=
    (h.plain_marked hm0 hm1 selected hsel hcap j k hj s hs t ht).trans
      (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hU _))
  plain_unmarked j k hj s hs t ht :=
    (h.plain_unmarked j k hj s hs t ht).trans
      (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hU _))

/-- Uniform raw moment estimates for all retained source rows under `Moments₃₂`. -/
def SourceMomentBound₃₂ {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (counts : CountParameters₃₂ F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) : Prop :=
  ∀ rows : Finset FreeRow, ∀ d a : ℝ, (1 / 200 : ℝ) ≤ d → d ≤ 7 / 8 → 51 / 100 < a → a ≤ 1 →
    (∀ u ∈ rows, u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧ rowNorm u ≤ Z ^ (d - D.t)) →
    ∀ i : ℕ, ∀ z : ℂ, z.re = 17 / 50 → |z.im| ≤ height →
    SourceMomentsAt₃₂ F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell
      (fun _ y => (F.w y : ℂ)) Z d a D.ε τ (7 / 8) 2 D.t D.t i z Δ
      (if 2 * a - 1 ≤ 5 / 6 then counts.cB else counts.cH)
      (if 2 * a - 1 ≤ 5 / 6 then counts.kB else counts.kH) C height D.t

lemma SourceMomentBound₃₂.mono_constant {Δ : ℝ} {D : HighData Δ} {F : SourceData D}
    {counts : CountParameters₃₂ F.modulus ⊤ D.t} {η : Character} {Z τ C C' height : ℝ}
    (hZ : 0 ≤ Z) (h : SourceMomentBound₃₂ F counts η Z τ C height) (hC : C ≤ C') :
    SourceMomentBound₃₂ F counts η Z τ C' height := by
  intro rows d a hd hd' ha ha' hrows i z hz hzh q B hBr hBd hRev hSlots hW hP hU hE hM hB hF
    bin j J K hne
  exact moments₃₂_mono_constant (Real.rpow_nonneg hZ _)
    (h rows d a hd hd' ha ha' hrows i z hz hzh q B hBr hBd hRev hSlots hW hP hU hE hM hB hF
      bin j J K hne) hCD
where
  hCD : C ≤ C' := hC

theorem balanced_source_count_from_raw_moments₃₂
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth εm : ℝ)
    (hdmin : 0 < dmin) (hdmax : 0 < dmax) (hτ : 0 < τ)
    (hl : 0 < logCost) (hh : τ < heightCost) (hb : 0 < binWidth)
    (counts : CountParameters₃₂ M H εm) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ (a ε Δ ν C q : ℝ) (i : ℕ), i ≤ n → 51 / 100 < a → 2 * a - 1 ≤ 5 / 6 → a ≤ 1 →
        0 ≤ ε → ε ≤ 1 / 1000 → 0 ≤ Δ → Δ ≤ 1 / 8 → 0 < ν → 0 ≤ C →
      ∀ {Slot : Type} (B : Batch M H Label Slot (Z ^ d) a ε
        (cutoff₃₂ (2 * a - 1) q) (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i),
      B.slots.card ≤ N → B.binWidth = binWidth → B.rows.Nonempty →
      (∀ u ∈ B.rows, rowMean B.slots (Z ^ d) ((2 * a - 1) / 2) B.binWidth B.widths
        (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external (Z ^ d))
          u = q) →
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        Moments₃₂ (B.fiber bin j J K hne) Δ counts.cB counts.kB
          (C * Z ^ momentCost) (Z ^ heightCost) εm) →
      (B.rows.card : ℝ) ≤ K * C * Z ^ (logCost + heightCost + momentCost) *
        (Z ^ d) ^ (Budget.rowCount₃₂ (2 * a - 1) (q / (2 * a - 1)) +
          Δ / 2 + 159 * ε + εm + B.mesh + 7 * ν) := by
  obtain ⟨K₀, hK₀, hcount⟩ := counts.balanced
  obtain ⟨K, hK, hpref⟩ := source_count_prefactor_eventually (Label := Label)
    N dmin dmax logCost heightCost momentCost binWidth K₀ hdmin hdmax hl (by linarith) hb
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_all_rpow_ge hcount dmin hdmin, hpref,
    source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    eventually_all_rpow_ge (eventually_gt_atTop (1 : ℝ)) dmin hdmin,
    eventually_ge_atTop (1 : ℝ)] with Z hcount hpref hfreq hU hZ
  intro d hd hd' a ε Δ ν C q i hi ha haδ ha' hε hε' hΔ hΔ' hν hC Slot B hslots hbin hne hq hmom
  have hcard := hcount d hd a ε (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) Δ ν
    (C * Z ^ momentCost) (Z ^ heightCost) q i (hU d hd) ha haδ hε hε' hΔ hΔ' hν (by positivity)
    (by positivity) (hfreq d hd' i hi) B hne hq hmom
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (cutoff₃₂ (2 * a - 1) q) (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i
      hC ha' B hslots hbin) (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)

theorem high_source_count_from_raw_moments₃₂
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth εm : ℝ)
    (hdmin : 0 < dmin) (hdmax : 0 < dmax) (hτ : 0 < τ)
    (hl : 0 < logCost) (hh : τ < heightCost) (hb : 0 < binWidth)
    (counts : CountParameters₃₂ M H εm) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ (a ε Δ C q : ℝ) (i : ℕ), i ≤ n → 5 / 6 < 2 * a - 1 → a ≤ 1 →
        0 ≤ ε → ε ≤ 1 / 1000 → 0 ≤ C →
      ∀ {Slot : Type} (B : Batch M H Label Slot (Z ^ d) a ε
        (cutoff₃₂ (2 * a - 1) q) (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i),
      B.slots.card ≤ N → B.binWidth = binWidth →
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        Moments₃₂ (B.fiber bin j J K hne) Δ counts.cH counts.kH
          (C * Z ^ momentCost) (Z ^ heightCost) εm) →
      (B.rows.card : ℝ) ≤ K * C * Z ^ (logCost + heightCost + momentCost) *
        (Z ^ d) ^ (1 - (2 * a - 1) + 78 * ε + εm) := by
  obtain ⟨K₀, hK₀, hcount⟩ := counts.high
  obtain ⟨K, hK, hpref⟩ := source_count_prefactor_eventually (Label := Label)
    N dmin dmax logCost heightCost momentCost binWidth K₀ hdmin hdmax hl (by linarith) hb
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_all_rpow_ge hcount dmin hdmin, hpref,
    source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    eventually_all_rpow_ge (eventually_gt_atTop (1 : ℝ)) dmin hdmin,
    eventually_ge_atTop (1 : ℝ)] with Z hcount hpref hfreq hU hZ
  intro d hd hd' a ε Δ C q i hi ha ha' hε hε' hC Slot B hslots hbin hmom
  have hcard := hcount d hd a ε (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) Δ
    (C * Z ^ momentCost) (Z ^ heightCost) q i (hU d hd) ha ha' hε hε' (by positivity)
    (by positivity) (hfreq d hd' i hi) B hmom
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (cutoff₃₂ (2 * a - 1) q) (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i
      hC ha' B hslots hbin) (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)

theorem adaptive_source_count_from_raw_moments₃₂
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth εm : ℝ)
    (hdmin : 0 < dmin) (hdmax : 0 < dmax) (hτ : 0 < τ)
    (hl : 0 < logCost) (hh : τ < heightCost) (hb : 0 < binWidth)
    (counts : CountParameters₃₂ M H εm) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ (a ε Δ ν C q : ℝ) (i : ℕ), i ≤ n → 51 / 100 < a → a ≤ 1 →
        0 ≤ ε → ε ≤ 1 / 1000 → 0 ≤ Δ → Δ ≤ 1 / 8 → 0 < ν → 0 ≤ C →
      ∀ {Slot : Type} (B : Batch M H Label Slot (Z ^ d) a ε
        (cutoff₃₂ (2 * a - 1) q) (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i),
      B.slots.card ≤ N → B.binWidth = binWidth → B.rows.Nonempty →
      (∀ u ∈ B.rows, rowMean B.slots (Z ^ d) ((2 * a - 1) / 2) B.binWidth B.widths
        (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external (Z ^ d))
          u = q) →
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        Moments₃₂ (B.fiber bin j J K hne) Δ
          (if 2 * a - 1 ≤ 5 / 6 then counts.cB else counts.cH)
          (if 2 * a - 1 ≤ 5 / 6 then counts.kB else counts.kH)
          (C * Z ^ momentCost) (Z ^ heightCost) εm) →
      (B.rows.card : ℝ) ≤ K * C * Z ^ (logCost + heightCost + momentCost) *
        (Z ^ d) ^ (adaptiveRowExponent₃₂ (2 * a - 1) q Δ ε εm B.mesh ν) := by
  obtain ⟨KB, hKB, hbalanced⟩ := balanced_source_count_from_raw_moments₃₂
    M H Label N n dmin dmax τ logCost heightCost momentCost binWidth εm hdmin hdmax hτ hl hh hb
    counts
  obtain ⟨KH, hKH, hhigh⟩ := high_source_count_from_raw_moments₃₂
    M H Label N n dmin dmax τ logCost heightCost momentCost binWidth εm hdmin hdmax hτ hl hh hb
    counts
  refine ⟨max KB KH, lt_of_lt_of_le hKB (le_max_left _ _), ?_⟩
  filter_upwards [hbalanced, hhigh, eventually_ge_atTop (1 : ℝ)] with Z hb' hh' _hZ
  intro d hd hd' a ε Δ ν C q i hi ha ha' hε hε' hΔ hΔ' hν hC Slot B hslots hbin hne hq hmom
  by_cases hδ : 2 * a - 1 ≤ 5 / 6
  · simp only [if_pos hδ] at hmom
    have hc := hb' d hd hd' a ε Δ ν C q i hi ha hδ ha' hε hε' hΔ hΔ' hν hC B hslots hbin hne hq hmom
    simp only [adaptiveRowExponent₃₂, if_pos hδ]
    exact hc.trans (by gcongr; exact le_max_left _ _)
  · simp only [if_neg hδ] at hmom
    have hc := hh' d hd hd' a ε Δ C q i hi (lt_of_not_ge hδ) ha' hε hε' hC B hslots hbin hmom
    simp only [adaptiveRowExponent₃₂, if_neg hδ]
    exact hc.trans (by gcongr; exact le_max_right _ _)

section NonfloorClass
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Fixed complete-factor count parameters give the upgraded nonfloor amplitude-class estimate. -/
theorem actual_nonfloor_class_from_raw_moments₃₂
    (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0 < e) (he1 : e < 1 / 1000) (heps : 0 < eps) (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A)
    (hR : 0 ≤ R) (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax) (hrmin : 0 < rmin)
    (hτ : 0 < τ) (hε : 0 < ε) (hκ : 0 < κ) (hcost : 0 ≤ cost) (hmesh : 0 < mesh)
    (hbudget : 8 * e * R + κ ≤ ε) (hgap : ε < rmin * mesh) (hmargin : 0 < margin)
    (hheight : 2 * τ < dmin * cost) (hloss : τ * (2 + 4 * eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4 * e) S)
    (hmax : ∀ P ∈ S, P.IsMaximal)
    (ell : Fin N → ℝ) (hell : Function.Injective ell)
    (hello : ∀ j, dmax * rmin ≤ ell j) (hellhi : ∀ j, ell j ≤ dmin * R)
    (W : Fin N → ℝ → ℂ)
    (hWs : ∀ j, Function.support (W j) ⊆ Ioo c b) (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hWB : ∀ j t, ‖W j t‖ ≤ A) (hellsum : ∑ j, ell j = 1 / 6)
    (hdtop : dmax ≤ 37 / 42) (hε1 : ε ≤ 1 / 1000) (hκ1 : κ ≤ 1)
    (hτzero : τ < dmin / 2) (hτheight : 4 * τ < dmin * cost)
    (hwbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κ + 2 * cost ≤ ε / 2)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (_hεm : 0 < εm) (hΔ : 0 ≤ Δ) (hΔ1 : Δ ≤ 1 / 8) (hν : 0 < ν)
    (hlog : 0 < logCost) (hMomentHeight : τ < heightCost)
    (counts : CountParameters₃₂ M H εm) :
    ∃ C : ℝ, 0 < C ∧
    ∀ η : Character, ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax → ∀ (v a C0 : ℝ), 0 ≤ v → 51 / 100 < a → a ≤ 1 → 0 ≤ C0 →
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val ≠ 0 ∧ rowNorm u ≤ Z ^ (d - margin)) →
      (∀ u ∈ rows, Z ^ v ≤ rowNorm u ∧ rowNorm u ≤ 2 * Z ^ v) →
      ∀ i : ℕ, i ≤ n →
      (∀ u ∈ rows, detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e) →
      (∀ u ∈ rows, a ≤ detectorMaximum
        (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3 * i : ℕ) * Z ^ τ)) →
      let Y : Fin N → ℝ := fun j => Z ^ (ell j)
      let T : Fin N → Finset ProbePhysical.PrimeIdeal :=
        fun j => pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀ t : HeightSpace,
        ((|t.1.1| ≤ (3 * i + 1 : ℕ) * Z ^ τ ∧ |t.2| ≤ (3 * i + 1 : ℕ) * Z ^ τ) ∧
          |t.1.2| ≤ (3 * i + 1 : ℕ) * Z ^ τ) →
      let z : ℂ := (17 / 50 : ℂ) + t.1.2 * Complex.I
      SourceMomentsAt₃₂ M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i z Δ
        (if 2 * a - 1 ≤ 5 / 6 then counts.cB else counts.cH)
        (if 2 * a - 1 ≤ 5 / 6 then counts.kB else counts.kH)
        (C0 * Z ^ momentCost) (Z ^ heightCost) εm →
      let Q := physical M H (fun u : FreeRow => u.val) W (fun _ => b)
        (fun j => ell j / d) (fun _ => z) (Z ^ d)
      ∀ bin : BinLabel (Finset.univ : Finset (Fin N)) ((2 * a - 1) / 2) mesh,
      let rows' := amplitudeRows rows Finset.univ (Z ^ d) ((2 * a - 1) / 2) mesh hmesh
        (fun j => ell j / d) Q bin
      let q := classMean Finset.univ ((2 * a - 1) / 2) mesh (fun j => ell j / d) bin
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2 * a - 1) / 2 ∧
      ‖cubeArithmeticSum S hS hmax η rows' T (nonfloorPoolOutside M H S N c b Y) W Y a e t‖ ≤
        C * C0 * (η.modulus.absNorm : ℝ) ^ (2 * eps) *
          Z ^ (logCost + heightCost + momentCost +
            d * adaptiveRowExponent₃₂ (2 * a - 1) q Δ ε εm R ν +
            v * (a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50) + loss - 2 / 75 + q / 6 + mesh / 6) := by
  have hdmax0 : 0 < dmax := hdmin.trans_le hdRange
  obtain ⟨K, hK, hcount⟩ :=
    adaptive_source_count_from_raw_moments₃₂ M H
      (Sum Bool (RayQuotient.Characters M H)) N n dmin dmax τ logCost heightCost momentCost mesh εm
      hdmin hdmax0 hτ hlog hMomentHeight hmesh counts
  obtain ⟨C, hC, hphysical⟩ :=
    actual_class_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh
      (1 / 100) margin loss he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost
      hmesh (by norm_num) hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello
      hellhi W hWs hW hWB hellsum
  refine ⟨C * K, mul_pos hC hK, ?_⟩
  intro η
  have hbatches := actual_source_amplitude_batches₃₂ M H hH S hS hmax η
    dmin dmax τ ε e κ cost margin R mesh n hdmin hdRange hdtop hτ hτzero hτheight
    hε he he1 hκ hκ1 hcost hmargin hR hmesh hwbudget
  filter_upwards [hphysical η, hcount, hbatches, eventually_gt_atTop (1 : ℝ)] with Z hphysical
    hcount hbatch hZ
  intro d hd hd' v a C0 hv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro t ht hmom bin hne
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hd0 : 0 < d := hdmin.trans_le hd
  let z : ℂ := (17 / 50 : ℂ) + t.1.2 * Complex.I
  let Q := physical M H (fun u : FreeRow => u.val) W (fun _ => b)
    (fun j => ell j / d) (fun _ => z) (Z ^ d)
  let rows' := amplitudeRows rows Finset.univ (Z ^ d) ((2 * a - 1) / 2) mesh hmesh
    (fun j => ell j / d) Q bin
  let q := classMean Finset.univ ((2 * a - 1) / 2) mesh (fun j => ell j / d) bin
  have hsub : rows' ⊆ rows := Finset.filter_subset _ _
  have hrowne : rows.Nonempty := hne.mono hsub
  have hband : rows ⊆ rowBand (Z ^ (1 / 100 : ℝ)) (2 * Z ^ v + 1) := by
    intro u hu
    exact mem_rowBand.mpr ⟨(hrows u hu).1, (hrows u hu).2.1, by linarith [(hnorm u hu).2]⟩
  have hellpos (j : Fin N) : 0 < ell j := (mul_pos hdmax0 hrmin).trans_le (hello j)
  obtain ⟨B, hBr, hBd, hRev, hSlots, hWidths, hW', hUpper, hExternal, hMesh, hBin, hFam, hMean⟩ :=
    hbatch d hd hd' (2 * Z ^ v + 1) rows hrowne hband (fun u hu => (hrows u hu).2.2.1)
      (fun u hu => (hrows u hu).2.2.2) a i hi ha ha' hnext hcurrent
      N ell hellpos hellhi hellsum W (fun _ => b) (fun _ => z) bin hne
  have hBsub : B.rows ⊆ rows := hBr ▸ hsub
  have hBfam : ∀ u ∈ B.rows, ∀ j,
      B.family u j = sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j :=
    fun u hu j => hFam u (hBr ▸ hu) j
  have hraw := hmom q B hBsub hBd hRev hSlots hWidths hW' hUpper hExternal hMesh hBin hBfam
  have hcard := hcount d hd hd' a ε Δ ν C0 q i hi ha ha' hε.le hε1 hΔ hΔ1 hν hC0 B
    (by rw [hSlots]; simp) hBin (hBr.symm ▸ hne) hMean hraw
  rw [hBr, hMesh] at hcard
  have hqb := classMean_bounds rows Finset.univ (Z ^ d) (2 * a - 1) mesh hmesh
    (fun j => ell j / d) Q bin (by linarith) (fun j _ => div_nonneg (hellpos j).le hd0.le)
    (by rw [source_slot_length_sum Finset.univ ell d hellsum]; positivity) hne
  refine ⟨hqb.1, hqb.2, ?_⟩
  have hp := hphysical d hd hd' v a q (K * C0 * Z ^ (logCost + heightCost + momentCost))
    (adaptiveRowExponent₃₂ (2 * a - 1) q Δ ε εm R ν) hv ha.le ha' (by positivity) rows'
    (fun u hu => hrows u (hsub hu)) (fun u hu => hnorm u (hsub hu)) hcard i hi
    (fun u hu => hnext u (hsub hu)) t ht
    (fun u hu => source_amplitude_class_mean M H ell W Z d b a mesh z hZp hd0.ne' hmesh rows bin u hu)
  apply hp.trans_eq
  rw [show logCost + heightCost + momentCost +
      d * adaptiveRowExponent₃₂ (2 * a - 1) q Δ ε εm R ν +
      v * (a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50) + loss - 2 / 75 + q / 6 + mesh / 6 =
      (logCost + heightCost + momentCost) + (d * adaptiveRowExponent₃₂ (2 * a - 1) q Δ ε εm R ν +
      v * (a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50) + loss - 2 / 75 + q / 6 + mesh / 6) by ring,
    Real.rpow_add hZp (logCost + heightCost + momentCost)]
  ring

end NonfloorClass
end ProbeFinalAssembly

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
