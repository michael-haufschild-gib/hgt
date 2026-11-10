import GaloisForLFunctions.RHTower.QuasiRHDetectorScaleBudget
import Mathlib

/-!
# The seven-eighths geometry is a vertex

Exponent budget of the compensated probe with scales `X = Z^{lx}`, `Y = Z^{ly}` and total slot
length `ℓ`; `M = lx + ly` is the row length. All statements are identities and inequalities
between exponents of the published estimates, not bounds for arithmetic sums.

**Low side.** The low exponent minus the principal shift is `5/6 + M/12 − ℓ/6`
(`lowGram_sub_principalShift`). A term with rescaled slot length `d` carries the factor `Z^{−d}`
(count `Z^d`, coefficient `Z^{−3d/2}`, row scale `Z^{−d/2}`) and half the excess of its reflected
energy. With this factor
* the face of zero retained length, at `d = 1/6 − h/5` for slot length `1/6 + h`, with excess
  `6h/5`, has total exponent `−1/6 + 4h/5 ≤ 0` (`tupleExponent_zero_retained_face`);
* the allowance `(3ℓ + 1 − 2M + d)₊/4` costs nothing when `1 + 3ℓ ≤ 2M`
  (`tupleExponent_reflectedAllowance_nonpos`).
Past `M + ℓ = 1` the dual sum is longer than the row sum and the reflected exponent exceeds the
row length by `M + ℓ − 1` (`reflectedExponent_dual_length_face`). The low boundary is
`lowBoundary = 5/6 + M/12 − ℓ/6 + (M + ℓ − 1)₊/2`.

**High side.** The exponent of the nonprincipal rows of the top length, relative to the signal at
`σ₀`, in a bin `δ = 2a − 1` with prime amplitude `q` and row count `R`, is `endpointExponent`.
At the published geometry and the published row count it is at most `−49/440640` in every bin
(`endpoint_certificate`), and it equals `−7/30672` in the bin `δ = 79/204` with full prime
amplitude (`endpoint_binding_bin`).

**The vertex** (`endpointExponent_pos_of_lowBoundary_le`). For every geometry with `lx ≤ 1` whose
low boundary is at most `7/8 − 1/4000`, the high exponent of that bin is positive. With the
published row count the boundary of the probe lies in `(7/8 − 1/4000, 7/8]`; the three estimates
that meet at the published point are the low bound, the row count in the bin `δ = 79/204`, and
the dual length of the reflected rows.

**The floor** (`endpointExponent_floor_bin_pos_of_lowBoundary_lt`, `endpointExponent_balanced`).
In the bin `δ = 0` with the trivial count `R = 1`, every geometry with `lx ≤ ly` and low boundary
below `13/15` has a positive high exponent; with the count `U^{1−δ}` in every bin the balanced
geometry `lx = ly = 2/5`, `ℓ = 1/5` reaches `13/15`. The room inside the probe is `[13/15, 7/8]`.
-/

namespace GaloisForLFunctions.FamilyContinuationTheory.Budget

open _root_.RHTower.QuasiRHDetectorScaleBudget

noncomputable section

/-! ### The low side -/

/-- Exponent of a term with rescaled slot length `d`, relative to the fully marked term: the
factor `Z^{−d}` and half the excess of the reflected energy. -/
def tupleExponent (d excess : ℝ) : ℝ := -d + excess / 2

/-- The face of zero retained length is paid by the tuple factor. -/
theorem tupleExponent_zero_retained_face {h : ℝ} (hh : h ≤ 5 / 24) :
    tupleExponent (1 / 6 - h / 5) (6 * h / 5) ≤ 0 := by
  unfold tupleExponent
  linarith

/-- The reflected allowance of a term with rescaled length `d`, row length `M`, slot length `ℓ`. -/
def reflectedAllowance (M ℓ d : ℝ) : ℝ := max 0 ((3 * ℓ + 1 - 2 * M + d) / 4)

/-- The allowance costs nothing when `1 + 3ℓ ≤ 2M`. -/
theorem tupleExponent_reflectedAllowance_nonpos {M ℓ d : ℝ} (hd : 0 ≤ d)
    (h : 1 + 3 * ℓ ≤ 2 * M) : tupleExponent d (reflectedAllowance M ℓ d) ≤ 0 := by
  unfold tupleExponent reflectedAllowance
  have hmax : max 0 ((3 * ℓ + 1 - 2 * M + d) / 4) ≤ d / 4 :=
    max_le (by linarith) (by linarith)
  linarith

/-- On the edge `M + ℓ = 1` the allowance costs nothing up to slot length `1/5`. -/
theorem tupleExponent_reflectedAllowance_edge {ℓ d : ℝ} (hd : 0 ≤ d) (hℓ : ℓ ≤ 1 / 5) :
    tupleExponent d (reflectedAllowance (1 - ℓ) ℓ d) ≤ 0 :=
  tupleExponent_reflectedAllowance_nonpos hd (by linarith)

/-- The low exponent minus the principal shift. -/
theorem lowGram_sub_principalShift (lx ly ℓ : ℝ) :
    lowGramExponent lx ly - principalShift lx ℓ = 5 / 6 + (lx + ly) / 12 - ℓ / 6 := by
  unfold lowGramExponent principalShift
  ring

/-- **The dual-length face.** With all slots marked and dual length `2M + ℓ − 1` at least the row
length `M`, the reflected exponent is `M + (M + ℓ − 1)`. -/
theorem reflectedExponent_dual_length_face {M ℓ : ℝ} (h1 : 1 ≤ M + ℓ) (h2 : 1 + ℓ ≤ 2 * M) :
    reflectedExponent 0 M 0 0 ℓ (2 * M + ℓ - 1) 0 0 (2 * M + ℓ - 1) = M + (M + ℓ - 1) := by
  have hs : hybridSaving (2 * M + ℓ - 1) ℓ = ℓ := by
    unfold hybridSaving
    rw [min_eq_left (by linarith : ℓ ≤ (2 * M + ℓ - 1 + ℓ) / 3), min_eq_right (by linarith)]
  unfold reflectedExponent
  rw [hs, max_eq_right (by linarith : M ≤ 2 * M + ℓ - 1 + 0)]
  simp
  ring

/-- The low boundary of a geometry: Gram bound, principal shift, and half the excess of the dual
length over the row length. -/
def lowBoundary (lx ly ℓ : ℝ) : ℝ :=
  5 / 6 + (lx + ly) / 12 - ℓ / 6 + max 0 (lx + ly + ℓ - 1) / 2

theorem lowBoundary_published : lowBoundary (17 / 48) (23 / 48) (1 / 6) = 7 / 8 := by
  norm_num [lowBoundary]

/-! ### The high side -/

/-- Crossing weight of the inverse and plain counts at amplitude ratio `x`. -/
def rowD (x : ℝ) : ℝ := 3 - 17 * x / 9

/-- Slope of the short count at amplitude ratio `x`. -/
def rowP (x : ℝ) : ℝ := (2 - 8 * x / 9) * (1 - x)

def rowJ (δ x : ℝ) : ℝ := (5 / 6 - δ) * rowD x + δ * rowP x

/-- The balanced row count exponent of a bin `δ` at amplitude ratio `x`. -/
def rowCount (δ x : ℝ) : ℝ := 1 - δ + (5 / 6 - δ) * δ * rowP x / (2 * rowJ δ x)

/-- Exponent of the nonprincipal rows of the top length `1 − lx + ℓ`, relative to the signal at
`σ₀`: bin `δ = 2a − 1`, prime amplitude `q`, row count `R`. -/
def endpointExponent (lx ly ℓ σ₀ δ q R : ℝ) : ℝ :=
  (1 + δ) * (1 - ly) / 2 - σ₀ - ℓ / 2 + q * ℓ + (1 - lx + ℓ) * (R + δ / 2 - 1 / 6)

theorem endpointExponent_published (δ q R : ℝ) :
    endpointExponent (17 / 48) (23 / 48) (1 / 6) (7 / 8) δ q R =
      -1 / 48 + 2 * δ / 3 + q / 6 - 13 / 16 * (1 - R) := by
  unfold endpointExponent
  ring

theorem rowJ_pos {δ x : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6) (hx : x ≤ 1 / 2) :
    35 / 54 ≤ rowJ δ x := by
  unfold rowJ rowD rowP
  have hD : 7 / 9 ≤ 3 - 17 * x / 9 := by linarith
  have hP : 7 / 9 ≤ (2 - 8 * x / 9) * (1 - x) := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hδ) (sub_nonneg.2 hD), mul_nonneg hδ0 (sub_nonneg.2 hP)]

theorem rowJ_le {δ x : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    rowJ δ x ≤ 5 / 2 := by
  have hx1 : 0 ≤ 1 - x := by linarith
  unfold rowJ rowD rowP
  have hD : 3 - 17 * x / 9 ≤ 3 := by linarith
  have hP : (2 - 8 * x / 9) * (1 - x) ≤ 2 := by nlinarith [mul_nonneg hx0 hx1]
  nlinarith [mul_nonneg (sub_nonneg.2 hδ) (sub_nonneg.2 hD), mul_nonneg hδ0 (sub_nonneg.2 hP)]

/-- Numerator of the negative endpoint exponent at the published geometry. -/
def endpointNumerator (δ x : ℝ) : ℝ :=
  rowJ δ x * (1 + (7 - 8 * x) * δ) / 48 - 13 / 32 * (5 / 6 - δ) * δ * rowP x

/-- The numerator is a sum of squares plus `49/176256`. -/
theorem endpointNumerator_ge {δ x : ℝ} (hδ0 : 0 ≤ δ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    49 / 176256 ≤ endpointNumerator δ x := by
  -- `y = 1/2 − x`, `v = 51 + 41y`
  have hy0 : 0 ≤ 1 / 2 - x := by linarith
  have hv : 0 < 51 + 41 * (1 / 2 - x) := by linarith
  have hid : 10368 * (51 + 41 * (1 / 2 - x)) * endpointNumerator δ x =
      (3 + 5 * (1 / 2 - x)) * ((4 * (51 + 41 * (1 / 2 - x)) * δ - 79) ^ 2 + 49) +
        4 * (1 / 2 - x) * (4 * (51 + 41 * (1 / 2 - x)) * δ *
          ((1 + 3 * (1 / 2 - x)) * (15 + 32 * (1 / 2 - x)) * δ + 9 - 13 * (1 / 2 - x))
            + 265 + 3485 * (1 / 2 - x)) := by
    unfold endpointNumerator rowJ rowD rowP
    ring
  have h1 : 0 ≤ (3 + 5 * (1 / 2 - x)) * (4 * (51 + 41 * (1 / 2 - x)) * δ - 79) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hin : 0 ≤ (1 + 3 * (1 / 2 - x)) * (15 + 32 * (1 / 2 - x)) * δ + 9 - 13 * (1 / 2 - x) := by
    have : 0 ≤ (1 + 3 * (1 / 2 - x)) * (15 + 32 * (1 / 2 - x)) * δ :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) hδ0
    linarith
  have h2 : 0 ≤ 4 * (1 / 2 - x) * (4 * (51 + 41 * (1 / 2 - x)) * δ *
      ((1 + 3 * (1 / 2 - x)) * (15 + 32 * (1 / 2 - x)) * δ + 9 - 13 * (1 / 2 - x))
        + 265 + 3485 * (1 / 2 - x)) := by
    have h3 : 0 ≤ 4 * (51 + 41 * (1 / 2 - x)) * δ *
        ((1 + 3 * (1 / 2 - x)) * (15 + 32 * (1 / 2 - x)) * δ + 9 - 13 * (1 / 2 - x)) :=
      mul_nonneg (mul_nonneg (by linarith) hδ0) hin
    exact mul_nonneg (by linarith) (by linarith)
  -- `10368 v N ≥ 49 (3 + 5y) ≥ 49 v / 17`
  have hlow : 49 * (51 + 41 * (1 / 2 - x)) / 17 ≤
      10368 * (51 + 41 * (1 / 2 - x)) * endpointNumerator δ x := by
    rw [hid]
    nlinarith
  by_contra hcon
  rw [not_le] at hcon
  nlinarith

/-- **The endpoint certificate.** At the published geometry and row count the high exponent is at
most `−49/440640` in every bin `0 ≤ δ ≤ 5/6` and at every amplitude ratio `0 ≤ x ≤ 1/2`. -/
theorem endpoint_certificate {δ x : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / 2) :
    endpointExponent (17 / 48) (23 / 48) (1 / 6) (7 / 8) δ (x * δ) (rowCount δ x)
      ≤ -(49 / 440640) := by
  have hJ := rowJ_pos hδ0 hδ hx
  have hJ0 : 0 < rowJ δ x := by linarith
  have hJle := rowJ_le hδ0 hδ hx0 hx
  have hN := endpointNumerator_ge hδ0 hx0 hx
  have hE : endpointExponent (17 / 48) (23 / 48) (1 / 6) (7 / 8) δ (x * δ) (rowCount δ x)
      = -(endpointNumerator δ x / rowJ δ x) := by
    rw [endpointExponent_published]
    unfold rowCount endpointNumerator
    field_simp
    ring
  rw [hE, neg_le_neg_iff, le_div_iff₀ hJ0]
  nlinarith

theorem rowCount_binding : rowCount (79 / 204) (1 / 2) = 21766 / 32589 := by
  norm_num [rowCount, rowJ, rowD, rowP]

/-- The bin `δ = 79/204` with full prime amplitude is within `1/4000` of equality. -/
theorem endpoint_binding_bin :
    endpointExponent (17 / 48) (23 / 48) (1 / 6) (7 / 8) (79 / 204) (79 / 408)
      (rowCount (79 / 204) (1 / 2)) = -(7 / 30672) := by
  rw [rowCount_binding]
  norm_num [endpointExponent]

/-! ### The vertex -/

/-- **The published geometry is a vertex.** For every geometry with `lx ≤ 1` whose low boundary
is at most `7/8 − 1/4000`, the high exponent of the bin `δ = 79/204` with full prime amplitude
and the published row count is positive: the rows of that bin exceed the signal. -/
theorem endpointExponent_pos_of_lowBoundary_le {lx ly ℓ : ℝ} (hlx : lx ≤ 1)
    (hσ : lowBoundary lx ly ℓ ≤ 7 / 8 - 1 / 4000) :
    0 < endpointExponent lx ly ℓ (lowBoundary lx ly ℓ) (79 / 204) (79 / 408)
      (rowCount (79 / 204) (1 / 2)) := by
  rw [rowCount_binding]
  unfold lowBoundary at hσ ⊢
  have hμ0 : (0 : ℝ) ≤ max 0 (lx + ly + ℓ - 1) := le_max_left _ _
  have hμ1 : lx + ly + ℓ - 1 ≤ max 0 (lx + ly + ℓ - 1) := le_max_right _ _
  generalize max 0 (lx + ly + ℓ - 1) = μ at hσ hμ0 hμ1 ⊢
  unfold endpointExponent
  nlinarith

/-- On the edge `M + ℓ = 1` the low boundary is `11/12 − ℓ/4`, and a slot length above
`1/6 + 1/1000` makes the high exponent of the binding bin positive for every choice of the
remaining scale. -/
theorem endpointExponent_pos_on_edge {lx ℓ : ℝ} (hlx : lx ≤ 1) (hℓ : 1 / 6 + 1 / 1000 ≤ ℓ) :
    0 < endpointExponent lx (1 - ℓ - lx) ℓ (11 / 12 - ℓ / 4) (79 / 204) (79 / 408)
      (rowCount (79 / 204) (1 / 2)) := by
  have hb : lowBoundary lx (1 - ℓ - lx) ℓ = 11 / 12 - ℓ / 4 := by
    unfold lowBoundary
    rw [show lx + (1 - ℓ - lx) + ℓ - 1 = 0 by ring, max_self]
    ring
  rw [← hb]
  exact endpointExponent_pos_of_lowBoundary_le hlx (by rw [hb]; linarith)

/-! ### The floor of the probe -/

/-- **The floor bin.** Rows whose characters have no zero to the right of the critical line
(`δ = 0`), summed trivially (`R = 1`): for every geometry with `lx ≤ ly` whose low boundary is
below `13/15`, their exponent is positive. Bounds of Riemann-hypothesis quality for every
nonprincipal row do not bring the probe below `13/15` without cancellation across the rows. -/
theorem endpointExponent_floor_bin_pos_of_lowBoundary_lt {lx ly ℓ : ℝ} (hb : lx ≤ ly)
    (hσ : lowBoundary lx ly ℓ < 13 / 15) :
    0 < endpointExponent lx ly ℓ (lowBoundary lx ly ℓ) 0 0 1 := by
  unfold lowBoundary at hσ ⊢
  have hμ0 : (0 : ℝ) ≤ max 0 (lx + ly + ℓ - 1) := le_max_left _ _
  have hμ1 : lx + ly + ℓ - 1 ≤ max 0 (lx + ly + ℓ - 1) := le_max_right _ _
  generalize max 0 (lx + ly + ℓ - 1) = μ at hσ hμ0 hμ1 ⊢
  unfold endpointExponent
  nlinarith

theorem lowBoundary_balanced : lowBoundary (2 / 5) (2 / 5) (1 / 5) = 13 / 15 := by
  norm_num [lowBoundary]

/-- With the count `U^{1−δ}` in every bin, the balanced geometry `lx = ly = 2/5`, `ℓ = 1/5`
has high exponent `(q − δ/2)/5 ≤ 0` at the boundary `13/15`. -/
theorem endpointExponent_balanced (δ q : ℝ) :
    endpointExponent (2 / 5) (2 / 5) (1 / 5) (13 / 15) δ q (1 - δ) = (q - δ / 2) / 5 := by
  unfold endpointExponent
  ring

end

end GaloisForLFunctions.FamilyContinuationTheory.Budget
