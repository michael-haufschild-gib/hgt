import GaloisForLFunctions.FamilyContinuationTheory.TheSevenEighthsGeometryIsAVertex
import GaloisForLFunctions.FamilyContinuationTheory.TheBudgetInTheTwistExponent

/-!
# The true cubic-probe vertex below seven-eighths

At the published balanced-surplus scales `(lx, ly, ℓ) = (17/48, 23/48, 1/6)` the cubic compensated
probe has low boundary `7/8` (`θ = 9/10`). Moving along the dual-length edge `lx + ly + ℓ = 1` to
`(lx, ly, ℓ) = (17/48, 479/1000, 1001/6000)` lowers the low boundary in both Gram regimes to
`20999/24000 = 7/8 − 1/24000` (`θ = 4499/5000 = 9/10 − 1/5000`) while preserving strict negativity
of every high-side nonprincipal exponent:

* **Exact sum-of-squares certificate (`endpoint_certificate_subSevenEighths`).** Across every bin
  `0 ≤ δ ≤ 5/6` and every prime-amplitude ratio `0 ≤ x ≤ 1/2`, clearing `rowJ δ x > 0` expresses
  `−endpointExponent` at `(17/48, 479/1000, 1001/6000)` and `σ₀ = 20999/24000` as
  `((6 A₀(y) δ − B₀(y))² + 58 A₀(y) + R₀(y)) / (7776000 A₀(y) rowJ δ x)` in `y = 1/2 − x ≥ 0`,
  where every coefficient of `A₀` and `R₀` is positive. Hence `endpointExponent ≤ −29/9720000`
  uniformly. High bins `5/6 ≤ δ ≤ 1` satisfy `endpointExponent ≤ −109/1500`, and the floor bin
  `δ = 1/50` satisfies `rowExponent ≤ −5083/900000`.
* **Sharp unconstrained `ℝ³` Farkas barrier (`endpointExponent_three_bin_pos_of_lowBoundaryGen_le`).**
  Over **all** `(lx, ly, ℓ) ∈ ℝ³` with no sign or upper-bound hypothesis on the scales, a strictly
  positive convex combination of `lowBoundary` and the two full-amplitude bins `δ₁ = 5/13` and
  `δ₂ = 16/41` cancels `lx`, `ly`, and `ℓ` identically at `40535/46328 = 7/8 − 1/23164`. Any point
  in `ℝ³` with `lowBoundaryGen lx ly ℓ < 40535/46328` has `max(E(5/13), E(16/41)) > 0`, and equality
  at `40535/46328` uniquely pins `(lx, ly, ℓ) = (49255/138984, 66541/138984, 5797/34746)`, where
  the bin `δ₃ = 79/204` has `E(79/204) = 4625/3019566384 > 0`. Thus the true unconstrained `ℝ³`
  vertex of the cubic-probe exponent budget lies in `(40535/46328, 20999/24000]`.
-/

namespace GaloisForLFunctions.FamilyContinuationTheory.Budget

noncomputable section

/-! ### The sub-`7/8` edge geometry `(17/48, 479/1000, 1001/6000)` -/

theorem lowBoundary_subSevenEighths :
    lowBoundary (17 / 48) (479 / 1000) (1001 / 6000) = 20999 / 24000 := by
  unfold lowBoundary
  rw [show (17 : ℝ) / 48 + 479 / 1000 + 1001 / 6000 - 1 = 0 by ring, max_self]
  norm_num

theorem lowBoundaryGen_subSevenEighths :
    lowBoundaryGen (17 / 48) (479 / 1000) (1001 / 6000) = 20999 / 24000 := by
  rw [lowBoundaryGen_eq_of_le (1001 / 6000) (by norm_num), lowBoundary_subSevenEighths]

theorem probeThetaGen_subSevenEighths :
    probeThetaGen 6 (17 / 48) (479 / 1000) (1001 / 6000) = 4499 / 5000 := by
  have hb := positiveFormTheta_probeThetaGen_iff (n := 6)
  norm_num [probeThetaGen, lowBoundaryGenOrder, positiveFormTheta] at *

/-- On `(M, ℓ) = (4999/6000, 1001/6000)` we have `1 + 3ℓ = 3001/2000 ≤ 4999/3000 = 2M`, so the
reflected allowance of unselected slots costs nothing. -/
theorem tupleExponent_reflectedAllowance_subSevenEighths {d : ℝ} (hd : 0 ≤ d) :
    tupleExponent d (reflectedAllowance (4999 / 6000) (1001 / 6000) d) ≤ 0 :=
  tupleExponent_reflectedAllowance_nonpos hd (by norm_num)

/-! ### Exact sum-of-squares certificate across `0 ≤ δ ≤ 5/6`, `0 ≤ x ≤ 1/2` -/

/-- Positive cubic polynomial in `y = 1/2 − x` scaling the quadratic form in `δ`. -/
def subA0 (y : ℝ) : ℝ := 32032 * y ^ 3 + 94004 * y ^ 2 + 130988 * y + 51037

/-- Linear shift of the square in `δ`, as a quadratic in `y = 1/2 − x`. -/
def subB0 (y : ℝ) : ℝ := 12974 * y ^ 2 + 188503 * y + 118478

/-- Positive quartic remainder in `y = 1/2 − x` after extracting `58 · subA0 y`. -/
def subR0 (y : ℝ) : ℝ :=
  7929044604 * y ^ 4 + 27681980500 * y ^ 3 + 20359386515 * y ^ 2 + 4261272918 * y + 26885

/-- Cleared-denominator numerator of `−endpointExponent` at `(17/48, 479/1000, 1001/6000)` and
`σ₀ = 20999/24000`. -/
def subSevenEighthsNumerator (δ x : ℝ) : ℝ :=
  rowJ δ x * (-(1 + δ) * (1 - 479 / 1000) / 2 + 20999 / 24000 + (1001 / 6000) / 2
      - (x * δ) * (1001 / 6000) - (1 - 17 / 48 + 1001 / 6000) * (1 - δ / 2 - 1 / 6))
    - (1 - 17 / 48 + 1001 / 6000) * ((5 / 6 - δ) * δ * rowP x / 2)

theorem subA0_pos {y : ℝ} (hy : 0 ≤ y) : 0 < subA0 y := by
  unfold subA0
  positivity

theorem subR0_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ subR0 y := by
  unfold subR0
  positivity

/-- Exact algebraic sum-of-squares identity for `subSevenEighthsNumerator`. -/
theorem subSevenEighthsNumerator_sos (δ x : ℝ) :
    7776000 * subA0 (1 / 2 - x) * subSevenEighthsNumerator δ x =
      (6 * subA0 (1 / 2 - x) * δ - subB0 (1 / 2 - x)) ^ 2 +
        58 * subA0 (1 / 2 - x) + subR0 (1 / 2 - x) := by
  unfold subSevenEighthsNumerator rowJ rowD rowP subA0 subB0 subR0
  ring

theorem subSevenEighthsNumerator_ge {δ x : ℝ} (hx : x ≤ 1 / 2) :
    29 / 3888000 ≤ subSevenEighthsNumerator δ x := by
  have hy : 0 ≤ 1 / 2 - x := by linarith
  have hA : 0 < subA0 (1 / 2 - x) := subA0_pos hy
  have hR : 0 ≤ subR0 (1 / 2 - x) := subR0_nonneg hy
  have hsq : 0 ≤ (6 * subA0 (1 / 2 - x) * δ - subB0 (1 / 2 - x)) ^ 2 := sq_nonneg _
  have hid := subSevenEighthsNumerator_sos δ x
  have hmul : 58 * subA0 (1 / 2 - x) ≤
      7776000 * subA0 (1 / 2 - x) * subSevenEighthsNumerator δ x := by
    linarith
  nlinarith

/-- **Sub-`7/8` balanced endpoint certificate.** Across all `0 ≤ δ ≤ 5/6` and `0 ≤ x ≤ 1/2`,
`endpointExponent` at `(17/48, 479/1000, 1001/6000)` and `σ₀ = 20999/24000` is at most
`−29/9720000`. -/
theorem endpoint_certificate_subSevenEighths {δ x : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6)
    (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    endpointExponent (17 / 48) (479 / 1000) (1001 / 6000) (20999 / 24000)
      δ (x * δ) (rowCount δ x) ≤ -(29 / 9720000) := by
  have hJ := rowJ_pos hδ0 hδ hx
  have hJ0 : 0 < rowJ δ x := by linarith
  have hJle := rowJ_le hδ0 hδ hx0 hx
  have hN := subSevenEighthsNumerator_ge (δ := δ) hx
  have hE : endpointExponent (17 / 48) (479 / 1000) (1001 / 6000) (20999 / 24000)
      δ (x * δ) (rowCount δ x) = -(subSevenEighthsNumerator δ x / rowJ δ x) := by
    unfold endpointExponent rowCount subSevenEighthsNumerator
    field_simp
    ring
  rw [hE, neg_le_neg_iff, le_div_iff₀ hJ0]
  nlinarith

/-- Positive row-length slope of `rowCount δ x` relative to `z₀ = 17/50`. -/
theorem rowCount_slope_bounds {δ x : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / 2) :
    73 / 300 ≤ rowCount δ x + δ / 2 - 17 / 50 ∧ rowCount δ x + δ / 2 - 17 / 50 ≤ 2 := by
  have hJ := rowJ_pos hδ0 hδ hx
  have hJ0 : 0 < rowJ δ x := by linarith
  have hP0 : 0 ≤ rowP x := by unfold rowP; exact mul_nonneg (by linarith) (by linarith)
  have hD0 : 0 ≤ rowD x := by unfold rowD; linarith
  have hge : 1 - δ ≤ rowCount δ x := by
    unfold rowCount
    have hq : 0 ≤ (5 / 6 - δ) * δ * rowP x / (2 * rowJ δ x) :=
      div_nonneg (mul_nonneg (mul_nonneg (by linarith) hδ0) hP0) (by linarith)
    linarith
  have hle : rowCount δ x ≤ 1 := by
    unfold rowCount
    have hnum : (5 / 6 - δ) * δ * rowP x ≤ 2 * rowJ δ x * δ := by
      unfold rowJ
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hδ) hD0) hδ0,
        mul_nonneg (mul_nonneg hδ0 hP0) hδ0]
    have hdiv : (5 / 6 - δ) * δ * rowP x / (2 * rowJ δ x) ≤ δ := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith
  exact ⟨by linarith, by linarith⟩

/-- Balanced-bin certificate across all row lengths `d ≤ 1219/1500 + ζ` (`ζ ≥ 0`). -/
theorem rowExponent_balanced_subSevenEighths {δ x d ζ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6)
    (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (hζ : 0 ≤ ζ) (hd : d ≤ 1219 / 1500 + ζ) :
    rowExponent (17 / 48) (479 / 1000) (1001 / 6000) (20999 / 24000) (17 / 50)
      δ (x * δ) (rowCount δ x) d ≤ -(29 / 9720000) + 2 * ζ := by
  have htop := endpoint_certificate_subSevenEighths hδ0 hδ hx0 hx
  have hsl := rowCount_slope_bounds hδ0 hδ hx0 hx
  have hrel : rowExponent (17 / 48) (479 / 1000) (1001 / 6000) (20999 / 24000) (17 / 50)
      δ (x * δ) (rowCount δ x) d =
      endpointExponent (17 / 48) (479 / 1000) (1001 / 6000) (20999 / 24000)
        δ (x * δ) (rowCount δ x) +
      (d - 1219 / 1500) * (rowCount δ x + δ / 2 - 17 / 50) := by
    unfold rowExponent endpointExponent
    ring
  rw [hrel]
  rcases le_total d (1219 / 1500) with hd0 | hd0
  · have hnonpos : (d - 1219 / 1500) * (rowCount δ x + δ / 2 - 17 / 50) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hsl.1])
    linarith
  · have hbd : (d - 1219 / 1500) * (rowCount δ x + δ / 2 - 17 / 50) ≤ 2 * ζ := by
      nlinarith [hsl.1, hsl.2]
    linarith

/-- High-`δ` certificate (`5/6 ≤ δ ≤ 1`, `q ≤ δ/2`, `R = 1 − δ`). -/
theorem endpoint_high_delta_subSevenEighths {δ q : ℝ} (hδ0 : 5 / 6 ≤ δ) (hδ1 : δ ≤ 1)
    (hq : q ≤ δ / 2) :
    endpointExponent (17 / 48) (479 / 1000) (1001 / 6000) (20999 / 24000) δ q (1 - δ) ≤
      -(109 / 1500) := by
  have hmono : endpointExponent (17 / 48) (479 / 1000) (1001 / 6000) (20999 / 24000) δ q (1 - δ) ≤
      endpointExponent (17 / 48) (479 / 1000) (1001 / 6000) (20999 / 24000) δ (δ / 2) (1 - δ) := by
    unfold endpointExponent
    linarith
  have hlin : endpointExponent (17 / 48) (479 / 1000) (1001 / 6000) (20999 / 24000)
      δ (δ / 2) (1 - δ) = -(599 / 1000) + (261 / 4000) * δ := by
    unfold endpointExponent
    ring
  linarith

/-- High-`δ` certificate across all row lengths `d ≤ 1219/1500 + ζ` (`ζ ≥ 0`). -/
theorem rowExponent_high_delta_subSevenEighths {δ q d ζ : ℝ} (hδ0 : 5 / 6 ≤ δ) (hδ1 : δ ≤ 1)
    (hq : q ≤ δ / 2) (hζ : 0 ≤ ζ) (hd : d ≤ 1219 / 1500 + ζ) :
    rowExponent (17 / 48) (479 / 1000) (1001 / 6000) (20999 / 24000) (17 / 50)
      δ q (1 - δ) d ≤ -(109 / 1500) + ζ := by
  have htop := endpoint_high_delta_subSevenEighths hδ0 hδ1 hq
  have hrel : rowExponent (17 / 48) (479 / 1000) (1001 / 6000) (20999 / 24000) (17 / 50)
      δ q (1 - δ) d =
      endpointExponent (17 / 48) (479 / 1000) (1001 / 6000) (20999 / 24000) δ q (1 - δ) +
      (d - 1219 / 1500) * (33 / 50 - δ / 2) := by
    unfold rowExponent endpointExponent
    ring
  rw [hrel]
  rcases le_total d (1219 / 1500) with hd0 | hd0
  · have hnonpos : (d - 1219 / 1500) * (33 / 50 - δ / 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  · have hbd : (d - 1219 / 1500) * (33 / 50 - δ / 2) ≤ ζ := by nlinarith
    linarith

/-- Floor-bin certificate (`δ = 1/50`, `q ≤ 1/100`, `R = 1`, `d ≤ 1219/1500 + ζ`). -/
theorem rowExponent_floor_bin_subSevenEighths {q d ζ : ℝ} (hq : q ≤ 1 / 100)
    (hd : d ≤ 1219 / 1500 + ζ) :
    rowExponent (17 / 48) (479 / 1000) (1001 / 6000) (20999 / 24000) (17 / 50)
      (1 / 50) q 1 d ≤ -(5083 / 900000) + (67 / 100) * ζ := by
  have hrel : rowExponent (17 / 48) (479 / 1000) (1001 / 6000) (20999 / 24000) (17 / 50)
      (1 / 50) q 1 d =
      -(52331 / 900000) + (1001 / 6000) * (q - 1 / 100) + (67 / 100) * (d - 1219 / 1500) := by
    unfold rowExponent
    ring
  -- Check exact constant via linear arithmetic
  unfold rowExponent
  linarith

/-! ### Sharp unconstrained `ℝ³` Farkas barrier at `40535/46328 = 7/8 − 1/23164` -/

theorem rowCount_five_thirteenths : rowCount (5 / 13) (1 / 2) = 61 / 91 := by
  norm_num [rowCount, rowJ, rowD, rowP]

theorem rowCount_sixteen_fortyfirsts : rowCount (16 / 41) (1 / 2) = 146633 / 220457 := by
  norm_num [rowCount, rowJ, rowD, rowP]

/-- Exact unconstrained `ℝ³` Farkas identity cancelling `lx`, `ly`, and `ℓ` between the linear part
of `lowBoundary` and the two full-amplitude bins `δ₁ = 5/13` and `δ₂ = 16/41`. -/
theorem farkas_two_bin_identity (lx ly ℓ σ₀ : ℝ) :
    (75277 / 92656 : ℝ) * (5 / 6 + (lx + ly) / 12 - ℓ / 6) +
      (5793 / 92656 : ℝ) * (lx + ly + ℓ - 1) +
      (92365 / 1667808 : ℝ) *
        (endpointExponent lx ly ℓ σ₀ (5 / 13) (5 / 26) (rowCount (5 / 13) (1 / 2)) + σ₀) +
      (220457 / 1667808 : ℝ) *
        (endpointExponent lx ly ℓ σ₀ (16 / 41) (8 / 41) (rowCount (16 / 41) (1 / 2)) + σ₀) =
      40535 / 46328 := by
  rw [rowCount_five_thirteenths, rowCount_sixteen_fortyfirsts]
  unfold endpointExponent
  ring

theorem lowBoundary_le_lowBoundaryGen (lx ly ℓ : ℝ) :
    lowBoundary lx ly ℓ ≤ lowBoundaryGen lx ly ℓ := by
  unfold lowBoundary lowBoundaryGen
  have h : ly - lx ≤ max 0 (ly - lx) := le_max_right _ _
  linarith

/-- Nonnegative decomposition of the Farkas slack at `σ₀ = lowBoundaryGen lx ly ℓ`. -/
theorem farkas_two_bin_slack_gen (lx ly ℓ : ℝ) :
    (92365 / 1667808 : ℝ) *
        endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ)
          (5 / 13) (5 / 26) (rowCount (5 / 13) (1 / 2)) +
      (220457 / 1667808 : ℝ) *
        endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ)
          (16 / 41) (8 / 41) (rowCount (16 / 41) (1 / 2)) =
      (40535 / 46328 - lowBoundaryGen lx ly ℓ) +
        (75277 / 92656) * (lowBoundaryGen lx ly ℓ - lowBoundary lx ly ℓ) +
        ((75277 / 185312) * max 0 (lx + ly + ℓ - 1) - (5793 / 92656) * (lx + ly + ℓ - 1)) := by
  have hid := farkas_two_bin_identity lx ly ℓ (lowBoundaryGen lx ly ℓ)
  have hlb : 5 / 6 + (lx + ly) / 12 - ℓ / 6 =
      lowBoundary lx ly ℓ - max 0 (lx + ly + ℓ - 1) / 2 := by
    unfold lowBoundary
    ring
  linarith

/-- **Unconstrained `ℝ³` two-bin barrier (`< 40535/46328`).** For every `(lx, ly, ℓ) ∈ ℝ³` with no
sign or upper-bound hypothesis, `lowBoundaryGen lx ly ℓ < 40535/46328` forces one of the two bins
`δ = 5/13` or `δ = 16/41` to have strictly positive high exponent. -/
theorem endpointExponent_two_bin_pos_of_lowBoundaryGen_lt {lx ly ℓ : ℝ}
    (hσ : lowBoundaryGen lx ly ℓ < 40535 / 46328) :
    0 < max
      (endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ)
        (5 / 13) (5 / 26) (rowCount (5 / 13) (1 / 2)))
      (endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ)
        (16 / 41) (8 / 41) (rowCount (16 / 41) (1 / 2))) := by
  have hslack := farkas_two_bin_slack_gen lx ly ℓ
  have hgen := lowBoundary_le_lowBoundaryGen lx ly ℓ
  have hmax0 : 0 ≤ max 0 (lx + ly + ℓ - 1) := le_max_left _ _
  have hmax1 : lx + ly + ℓ - 1 ≤ max 0 (lx + ly + ℓ - 1) := le_max_right _ _
  have hpen : 0 ≤ (75277 / 185312 : ℝ) * max 0 (lx + ly + ℓ - 1) -
      (5793 / 92656) * (lx + ly + ℓ - 1) := by
    linarith
  have hpos : 0 < (92365 / 1667808 : ℝ) *
      endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ)
        (5 / 13) (5 / 26) (rowCount (5 / 13) (1 / 2)) +
      (220457 / 1667808 : ℝ) *
      endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ)
        (16 / 41) (8 / 41) (rowCount (16 / 41) (1 / 2)) := by
    linarith
  by_contra hle
  rw [not_lt, max_le_iff] at hle
  linarith [hle.1, hle.2]

theorem endpointExponent_two_bin_pos_of_lowBoundary_lt {lx ly ℓ : ℝ}
    (hσ : lowBoundary lx ly ℓ < 40535 / 46328) :
    0 < max
      (endpointExponent lx ly ℓ (lowBoundary lx ly ℓ)
        (5 / 13) (5 / 26) (rowCount (5 / 13) (1 / 2)))
      (endpointExponent lx ly ℓ (lowBoundary lx ly ℓ)
        (16 / 41) (8 / 41) (rowCount (16 / 41) (1 / 2))) := by
  have hid := farkas_two_bin_identity lx ly ℓ (lowBoundary lx ly ℓ)
  have hlb : 5 / 6 + (lx + ly) / 12 - ℓ / 6 =
      lowBoundary lx ly ℓ - max 0 (lx + ly + ℓ - 1) / 2 := by
    unfold lowBoundary
    ring
  have hmax0 : 0 ≤ max 0 (lx + ly + ℓ - 1) := le_max_left _ _
  have hmax1 : lx + ly + ℓ - 1 ≤ max 0 (lx + ly + ℓ - 1) := le_max_right _ _
  by_contra hle
  rw [not_lt, max_le_iff] at hle
  linarith [hle.1, hle.2]

/-- Attainment of the two-bin LP value `40535/46328` at `(49255/138984, 66541/138984, 5797/34746)`,
where the third bin `δ = 79/204` is strictly positive (`4625/3019566384`). -/
theorem farkas_two_bin_vertex_attained :
    lowBoundary (49255 / 138984) (66541 / 138984) (5797 / 34746) = 40535 / 46328 ∧
    lowBoundaryGen (49255 / 138984) (66541 / 138984) (5797 / 34746) = 40535 / 46328 ∧
    endpointExponent (49255 / 138984) (66541 / 138984) (5797 / 34746) (40535 / 46328)
      (5 / 13) (5 / 26) (rowCount (5 / 13) (1 / 2)) = 0 ∧
    endpointExponent (49255 / 138984) (66541 / 138984) (5797 / 34746) (40535 / 46328)
      (16 / 41) (8 / 41) (rowCount (16 / 41) (1 / 2)) = 0 ∧
    endpointExponent (49255 / 138984) (66541 / 138984) (5797 / 34746) (40535 / 46328)
      (79 / 204) (79 / 408) (rowCount (79 / 204) (1 / 2)) = 4625 / 3019566384 := by
  have hlb : lowBoundary (49255 / 138984) (66541 / 138984) (5797 / 34746) = 40535 / 46328 := by
    unfold lowBoundary
    rw [show (49255 : ℝ) / 138984 + 66541 / 138984 + 5797 / 34746 - 1 = 0 by ring, max_self]
    norm_num
  refine ⟨hlb, ?_, ?_, ?_, ?_⟩
  · rw [lowBoundaryGen_eq_of_le (5797 / 34746) (by norm_num), hlb]
  · rw [rowCount_five_thirteenths]; norm_num [endpointExponent]
  · rw [rowCount_sixteen_fortyfirsts]; norm_num [endpointExponent]
  · rw [rowCount_binding]; norm_num [endpointExponent]

/-- **Sharp unconstrained `ℝ³` three-bin barrier (`≤ 40535/46328`).** Over **all**
`(lx, ly, ℓ) ∈ ℝ³` with no sign or upper-bound hypothesis on the scales, if
`lowBoundaryGen lx ly ℓ ≤ 40535/46328`, then at least one of the three bins `5/13`, `79/204`, or
`16/41` has strictly positive high exponent. -/
theorem endpointExponent_three_bin_pos_of_lowBoundaryGen_le {lx ly ℓ : ℝ}
    (hσ : lowBoundaryGen lx ly ℓ ≤ 40535 / 46328) :
    0 < max
      (endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ)
        (5 / 13) (5 / 26) (rowCount (5 / 13) (1 / 2)))
      (max
        (endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ)
          (79 / 204) (79 / 408) (rowCount (79 / 204) (1 / 2)))
        (endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ)
          (16 / 41) (8 / 41) (rowCount (16 / 41) (1 / 2)))) := by
  by_contra hle
  rw [not_lt, max_le_iff, max_le_iff] at hle
  rcases hle with ⟨hE1, hE3, hE2⟩
  have hslack := farkas_two_bin_slack_gen lx ly ℓ
  have hgen := lowBoundary_le_lowBoundaryGen lx ly ℓ
  have hmax0 : 0 ≤ max 0 (lx + ly + ℓ - 1) := le_max_left _ _
  have hmax1 : lx + ly + ℓ - 1 ≤ max 0 (lx + ly + ℓ - 1) := le_max_right _ _
  have hpen : 0 ≤ (75277 / 185312 : ℝ) * max 0 (lx + ly + ℓ - 1) -
      (5793 / 92656) * (lx + ly + ℓ - 1) := by linarith
  have hσ_eq : lowBoundaryGen lx ly ℓ = 40535 / 46328 := by linarith
  have hE1_eq : endpointExponent lx ly ℓ (40535 / 46328)
      (5 / 13) (5 / 26) (rowCount (5 / 13) (1 / 2)) = 0 := by
    rw [← hσ_eq]; linarith
  have hE2_eq : endpointExponent lx ly ℓ (40535 / 46328)
      (16 / 41) (8 / 41) (rowCount (16 / 41) (1 / 2)) = 0 := by
    rw [← hσ_eq]; linarith
  have hpen_eq : (75277 / 185312 : ℝ) * max 0 (lx + ly + ℓ - 1) -
      (5793 / 92656) * (lx + ly + ℓ - 1) = 0 := by linarith
  have hu_eq : lx + ly + ℓ - 1 = 0 := by
    rcases le_total 0 (lx + ly + ℓ - 1) with hu | hu
    · rw [max_eq_right hu] at hpen_eq; linarith
    · rw [max_eq_left hu] at hpen_eq; linarith
  rw [rowCount_five_thirteenths] at hE1_eq
  rw [rowCount_sixteen_fortyfirsts] at hE2_eq
  rw [hσ_eq, rowCount_binding] at hE3
  unfold endpointExponent at hE1_eq hE2_eq hE3
  linarith

/-- Unconstrained `ℝ³` three-bin barrier for `lowBoundary`. -/
theorem endpointExponent_three_bin_pos_of_lowBoundary_le {lx ly ℓ : ℝ}
    (hσ : lowBoundary lx ly ℓ ≤ 40535 / 46328) :
    0 < max
      (endpointExponent lx ly ℓ (lowBoundary lx ly ℓ)
        (5 / 13) (5 / 26) (rowCount (5 / 13) (1 / 2)))
      (max
        (endpointExponent lx ly ℓ (lowBoundary lx ly ℓ)
          (79 / 204) (79 / 408) (rowCount (79 / 204) (1 / 2)))
        (endpointExponent lx ly ℓ (lowBoundary lx ly ℓ)
          (16 / 41) (8 / 41) (rowCount (16 / 41) (1 / 2)))) := by
  by_contra hle
  rw [not_lt, max_le_iff, max_le_iff] at hle
  rcases hle with ⟨hE1, hE3, hE2⟩
  have hid := farkas_two_bin_identity lx ly ℓ (lowBoundary lx ly ℓ)
  have hlb : 5 / 6 + (lx + ly) / 12 - ℓ / 6 =
      lowBoundary lx ly ℓ - max 0 (lx + ly + ℓ - 1) / 2 := by
    unfold lowBoundary; ring
  have hmax0 : 0 ≤ max 0 (lx + ly + ℓ - 1) := le_max_left _ _
  have hmax1 : lx + ly + ℓ - 1 ≤ max 0 (lx + ly + ℓ - 1) := le_max_right _ _
  have hpen : 0 ≤ (75277 / 185312 : ℝ) * max 0 (lx + ly + ℓ - 1) -
      (5793 / 92656) * (lx + ly + ℓ - 1) := by linarith
  have hσ_eq : lowBoundary lx ly ℓ = 40535 / 46328 := by linarith
  have hE1_eq : endpointExponent lx ly ℓ (40535 / 46328)
      (5 / 13) (5 / 26) (rowCount (5 / 13) (1 / 2)) = 0 := by
    rw [← hσ_eq]; linarith
  have hE2_eq : endpointExponent lx ly ℓ (40535 / 46328)
      (16 / 41) (8 / 41) (rowCount (16 / 41) (1 / 2)) = 0 := by
    rw [← hσ_eq]; linarith
  have hpen_eq : (75277 / 185312 : ℝ) * max 0 (lx + ly + ℓ - 1) -
      (5793 / 92656) * (lx + ly + ℓ - 1) = 0 := by linarith
  have hu_eq : lx + ly + ℓ - 1 = 0 := by
    rcases le_total 0 (lx + ly + ℓ - 1) with hu | hu
    · rw [max_eq_right hu] at hpen_eq; linarith
    · rw [max_eq_left hu] at hpen_eq; linarith
  rw [rowCount_five_thirteenths] at hE1_eq
  rw [rowCount_sixteen_fortyfirsts] at hE2_eq
  rw [hσ_eq, rowCount_binding] at hE3
  unfold endpointExponent at hE1_eq hE2_eq hE3
  linarith

/-- Twist-exponent form of the sharp unconstrained `ℝ³` barrier (`θ ≤ 52113/57910 = 9/10 − 3/28955`). -/
theorem probeThetaGen_three_bin_pos_of_le {lx ly ℓ : ℝ}
    (hθ : probeThetaGen 6 lx ly ℓ ≤ 52113 / 57910) :
    0 < max
      (endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ)
        (5 / 13) (5 / 26) (rowCount (5 / 13) (1 / 2)))
      (max
        (endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ)
          (79 / 204) (79 / 408) (rowCount (79 / 204) (1 / 2)))
        (endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ)
          (16 / 41) (8 / 41) (rowCount (16 / 41) (1 / 2)))) := by
  refine endpointExponent_three_bin_pos_of_lowBoundaryGen_le ?_
  have hmon := (positiveFormBoundary_strictMono (by norm_num : (1 : ℝ) < 6)).monotone hθ
  rw [positiveFormBoundary_probeThetaGen (by norm_num) (by norm_num),
    lowBoundaryGenOrder_six] at hmon
  have hval : positiveFormBoundary 6 (52113 / 57910) = 40535 / 46328 := by
    norm_num [positiveFormBoundary]
  linarith

end

end GaloisForLFunctions.FamilyContinuationTheory.Budget
