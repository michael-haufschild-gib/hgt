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
the dual length of the reflected rows. The row count depends on the top `β` of the zeros through
`κ = 2β − 1`; for `κ ∈ [11/15, 3/4]` it changes by less than `10⁻⁴` in that bin, and the vertex
holds with `1/2500` (`endpointExponent_pos_of_lowBoundary_le_at`).

**The floor** (`endpointExponent_floor_bin_pos_of_lowBoundary_lt`, `endpointExponent_balanced`).
In the bin `δ = 0` with the trivial count `R = 1`, every geometry with low boundary below `13/15`
has a positive high exponent, in both regimes of the Gram bound
(`endpointExponent_floor_bin_pos_of_lowBoundaryGen_lt`); with the count `U^{1−δ}` in every bin the
balanced geometry `lx = ly = 2/5`, `ℓ = 1/5` reaches `13/15`. The room inside the probe is
`[13/15, 7/8]`.

**The order of the row twist** (`lowBoundaryOrder_lt_floorBinOrder`). With principal frequencies
the `n`-th powers in the place of the sixth powers, the balanced budget has the floor
`1 − 4/(5n)`.

**The number of row variables** (`one_le_lowBoundaryDesign`). The cube identity `γ₃³ = μ ε` of the
normalized cubic Gauss sum can be realized with `k` row variables whose twists have order `n`:
`(1, 6)` (cubic theta row and one sextic twist, the published design), `(2, 3)` (cubic theta row
and two cubic twists), `(3, 3)` (three cubic twists, no theta row). Every design with two or more
row variables has balanced low boundary at least `1`.

**The conductor of the rows** (`corner_two_six`, `corner_three_four`, `corner_four_three`). With
rows of conductor `q_m^κ` and principal frequencies of order `n`, the corner of the low boundary
and the floor bin without slots is `8/9` for `(κ, n) = (2, 6)`, `25/28` for `(3, 4)` and `49/54`
for `(4, 3)`: a lower order of the frequencies is paid by the conductor.

**The reflected mean square through the twists** (`dualExcess_nonpos_of_density`,
`budget_half_density`). The dual-length term of the low boundary belongs to the unconditional
bound for the reflected rows. Expressed through the Möbius sums of the twists of norm up to
`Z^{2 − M}`, the mean square of the rows has the excess `dualExcess` in a bin; with the count
`U^{1 − δ}` it is `(1 − M)(1 − δ)` at full prime amplitude, so rows at least as long as the
completed index are generic. Without the dual-length term the low boundary is at least `5/6` for
rescaled row length `lx + ly − 2ℓ ≥ 0` (`five_sixths_le_lowBoundaryFree`), and the budget closes
at `5/6` at `lx = ly = ℓ = 1/2`.
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

/-- The short count: inverse and plain witnesses with selected prime slots, at witness length
`t ∈ [1, 3/2]`. -/
def rowShort (δ x t : ℝ) : ℝ := 1 - δ + δ * rowP x / rowD x * (3 / 2 - t)

/-- The long count: an inverse witness longer than the rows, with sixth-power amplification. -/
def rowLong (δ t : ℝ) : ℝ := 1 - δ + (5 / 6 - δ) * (t - 1)

/-- The two counts agree at `t = 1 + δP/(2J)`, with common value `rowCount`. -/
theorem rowShort_eq_rowCount {δ x : ℝ} (hD : rowD x ≠ 0) (hJ : rowJ δ x ≠ 0) :
    rowShort δ x (1 + δ * rowP x / (2 * rowJ δ x)) = rowCount δ x := by
  unfold rowShort rowCount
  have hJ' : rowJ δ x = (5 / 6 - δ) * rowD x + δ * rowP x := rfl
  field_simp
  rw [hJ']
  ring

theorem rowLong_eq_rowCount {δ x : ℝ} (hJ : rowJ δ x ≠ 0) :
    rowLong δ (1 + δ * rowP x / (2 * rowJ δ x)) = rowCount δ x := by
  unfold rowLong rowCount
  field_simp
  ring

/-- **The balanced count is the best of the two.** For `0 ≤ δ ≤ 5/6` and `x ≤ 1/2`, at every
witness length one of the two counts is at least `rowCount`. -/
theorem rowCount_le_max {δ x : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6) (hx : x ≤ 1 / 2) (t : ℝ) :
    rowCount δ x ≤ max (rowShort δ x t) (rowLong δ t) := by
  have hD : 0 < rowD x := by unfold rowD; linarith
  have hP : 0 ≤ rowP x := by
    unfold rowP
    exact mul_nonneg (by linarith) (by linarith)
  have hJ : 0 < rowJ δ x := by
    have := rowJ_pos hδ0 hδ hx
    linarith
  rcases le_total t (1 + δ * rowP x / (2 * rowJ δ x)) with ht | ht
  · -- the short count decreases with `t`
    refine le_trans ?_ (le_max_left _ _)
    rw [← rowShort_eq_rowCount hD.ne' hJ.ne']
    unfold rowShort
    have hc : 0 ≤ δ * rowP x / rowD x := div_nonneg (mul_nonneg hδ0 hP) hD.le
    nlinarith
  · -- the long count increases with `t`
    refine le_trans ?_ (le_max_right _ _)
    rw [← rowLong_eq_rowCount (x := x) hJ.ne']
    unfold rowLong
    nlinarith [mul_nonneg (sub_nonneg.2 hδ) (sub_nonneg.2 ht)]

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

/-! ### The other row lengths at the published geometry -/

/-- Exponent of the nonprincipal rows of length `d`, relative to the signal at `σ₀`, on the
contours `Re s = a`, `Re w = 1 − a`, `Re z = z₀` with `a = (1 + δ)/2`. -/
def rowExponent (lx ly ℓ σ₀ z₀ δ q R d : ℝ) : ℝ :=
  (1 + δ) / 2 - σ₀ + (1 - lx + ℓ) * (z₀ - 1 / 6) - (1 + δ) / 2 * ly - ℓ / 2 + q * ℓ
    + d * (R + δ / 2 - z₀)

/-- At the top row length the contour `z₀` cancels. -/
theorem rowExponent_top (lx ly ℓ σ₀ z₀ δ q R : ℝ) :
    rowExponent lx ly ℓ σ₀ z₀ δ q R (1 - lx + ℓ) = endpointExponent lx ly ℓ σ₀ δ q R := by
  unfold rowExponent endpointExponent
  ring

theorem rowExponent_published (δ q R d : ℝ) :
    rowExponent (17 / 48) (23 / 48) (1 / 6) (7 / 8) (17 / 50) δ q R d =
      -1 / 48 + 2 * δ / 3 + q / 6 - 13 / 16 * (1 - R)
        + (d - 13 / 16) * (R + δ / 2 - 17 / 50) := by
  unfold rowExponent
  ring

/-- The floor bin `δ = 1/50` with the trivial count: at most `−7/1200` at the top length. -/
theorem rowExponent_floor_bin {q : ℝ} (hq : q ≤ 1 / 100) :
    rowExponent (17 / 48) (23 / 48) (1 / 6) (7 / 8) (17 / 50) (1 / 50) q 1 (13 / 16)
      ≤ -(7 / 1200) := by
  rw [rowExponent_published]
  linarith

/-- Rows of length `Z^{1/2}` with the count `76/75 − 2δ/3` and full prime amplitude: at most
`−49/14400` for `δ ≤ 5/6`. -/
theorem rowExponent_short_rows {δ : ℝ} (hδ : δ ≤ 5 / 6) :
    rowExponent (17 / 48) (23 / 48) (1 / 6) (7 / 8) (17 / 50) δ (δ / 2) (76 / 75 - 2 * δ / 3)
      (1 / 2) ≤ -(49 / 14400) := by
  have h : rowExponent (17 / 48) (23 / 48) (1 / 6) (7 / 8) (17 / 50) δ (δ / 2)
      (76 / 75 - 2 * δ / 3) (1 / 2) = -(529 / 2400) + 25 / 96 * δ := by
    rw [rowExponent_published]
    ring
  rw [h]
  linarith

/-- The part of the exponent of the small rows that does not depend on their length. -/
theorem smallRows_published : (13 / 16 : ℝ) * (17 / 50 - 1 / 6) - 23 / 48 / 2 = -(79 / 800) := by
  norm_num

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

/-! ### The row count at a lower target

The plain capacity of the row count is `(1 − 2m)/(6κ)` with `κ = 2β − 1` for the top `β` of the
zeros of the family; the published count is its value at `κ = 3/4`. For a target below `7/8` the
capacity is larger. In the binding bin the effect is below `10⁻⁴` down to `κ = 11/15`, the value
at the floor `13/15`. -/

/-- Count from an inverse witness of length `r` with the selected slot length `(1 − r)/2`, at
amplitude ratio `x`. -/
def inverseCount (δ x r : ℝ) : ℝ := 1 - δ * (x + (1 - x) * r)

/-- Count from two plain witnesses of length `t − r` with the selected slot length
`(1 − 2(t − r))/(6κ)`. -/
def plainCount (κ δ x t r : ℝ) : ℝ :=
  1 - δ * (x / (3 * κ) + (2 - 2 * x / (3 * κ)) * (t - r))

theorem inverseCount_eq (δ x r : ℝ) :
    inverseCount δ x r = 1 - δ * r - 2 * (x * δ) * ((1 - r) / 2) := by
  unfold inverseCount
  ring

theorem plainCount_eq {κ : ℝ} (hκ : κ ≠ 0) (δ x t r : ℝ) :
    plainCount κ δ x t r =
      1 - 2 * δ * (t - r) - 2 * (x * δ) * ((1 - 2 * (t - r)) / (6 * κ)) := by
  unfold plainCount
  field_simp
  ring

/-- **The crossing of the two counts.** With weights `2 − 2x/(3κ)` and `1 − x` the average of the
inverse and the plain count does not depend on the split `r`: it is the short count
`1 − δ + δP(3/2 − t)/D` with `D = 3 − x − 2x/(3κ)`, `P = (1 − x)(2 − 2x/(3κ))`. -/
theorem weighted_inverse_plain (κ δ x t r : ℝ) :
    (2 - 2 * x / (3 * κ)) * inverseCount δ x r + (1 - x) * plainCount κ δ x t r =
      (3 - x - 2 * x / (3 * κ)) * (1 - δ) +
        δ * ((1 - x) * (2 - 2 * x / (3 * κ))) * (3 / 2 - t) := by
  unfold inverseCount plainCount
  ring

/-- For every split the smaller of the two counts is at most the short count. -/
theorem min_inverse_plain_le {κ δ x t r : ℝ} (hw₁ : 0 ≤ 2 - 2 * x / (3 * κ)) (hw₂ : 0 ≤ 1 - x)
    (hD : 0 < 3 - x - 2 * x / (3 * κ)) :
    min (inverseCount δ x r) (plainCount κ δ x t r) ≤
      1 - δ + δ * ((1 - x) * (2 - 2 * x / (3 * κ))) / (3 - x - 2 * x / (3 * κ)) * (3 / 2 - t) := by
  have h := weighted_inverse_plain κ δ x t r
  have hmin₁ := min_le_left (inverseCount δ x r) (plainCount κ δ x t r)
  have hmin₂ := min_le_right (inverseCount δ x r) (plainCount κ δ x t r)
  have hsum : (3 - x - 2 * x / (3 * κ)) * min (inverseCount δ x r) (plainCount κ δ x t r) ≤
      (3 - x - 2 * x / (3 * κ)) * (1 - δ) +
        δ * ((1 - x) * (2 - 2 * x / (3 * κ))) * (3 / 2 - t) := by
    rw [← h]
    nlinarith [mul_le_mul_of_nonneg_left hmin₁ hw₁, mul_le_mul_of_nonneg_left hmin₂ hw₂]
  generalize 3 - x - 2 * x / (3 * κ) = D at hD hsum ⊢
  generalize (1 - x) * (2 - 2 * x / (3 * κ)) = P at hsum ⊢
  generalize min (inverseCount δ x r) (plainCount κ δ x t r) = m at hsum ⊢
  have hDne : D ≠ 0 := hD.ne'
  rw [show 1 - δ + δ * P / D * (3 / 2 - t) = (D * (1 - δ) + δ * P * (3 / 2 - t)) / D by
    field_simp, le_div_iff₀ hD]
  linarith

/-- At `κ = 3/4` the weights of the crossing are `rowD` and `rowP`. -/
theorem crossing_three_quarters (x : ℝ) :
    3 - x - 2 * x / (3 * (3 / 4 : ℝ)) = rowD x ∧
      (1 - x) * (2 - 2 * x / (3 * (3 / 4 : ℝ))) = rowP x := by
  unfold rowD rowP
  constructor <;> ring

/-- The balanced row count of the bin `δ` at full prime amplitude, with plain capacity
`(1 − 2m)/(6κ)`. -/
def rowCountAt (κ δ : ℝ) : ℝ :=
  1 - δ + (5 / 6 - δ) * δ * (1 - 1 / (6 * κ)) /
    (2 * ((5 / 6 - δ) * (5 / 2 - 1 / (3 * κ)) + δ * (1 - 1 / (6 * κ))))

theorem rowCountAt_three_quarters (δ : ℝ) : rowCountAt (3 / 4) δ = rowCount δ (1 / 2) := by
  unfold rowCountAt rowCount rowJ rowD rowP
  norm_num

/-- In the binding bin the count stays within `10⁻⁴` of the published one for
`11/15 ≤ κ ≤ 3/4`. -/
theorem rowCountAt_binding_ge {κ : ℝ} (hκ : 11 / 15 ≤ κ) (hκ' : κ ≤ 3 / 4) :
    21766 / 32589 - 1 / 10000 ≤ rowCountAt κ (79 / 204) := by
  have hκ0 : 0 < κ := by linarith
  -- with `c = 1/(6κ) ∈ [2/9, 5/22]` the count is `125/204 + (91·79/204²)(1−c)/(2J)`
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / (6 * κ) := ⟨_, rfl⟩
  have hc1 : c ≤ 5 / 22 := by
    rw [hc, div_le_iff₀ (by positivity)]
    nlinarith
  have hc0 : 2 / 9 ≤ c := by
    rw [hc, le_div_iff₀ (by positivity)]
    nlinarith
  have h3 : 1 / (3 * κ) = 2 * c := by rw [hc]; field_simp; ring
  unfold rowCountAt
  rw [h3, ← hc]
  have hJ : 0 < (5 / 6 - 79 / 204) * (5 / 2 - 2 * c) + 79 / 204 * (1 - c) := by nlinarith
  rw [show (1 : ℝ) - 79 / 204 + (5 / 6 - 79 / 204) * (79 / 204) * (1 - c) /
      (2 * ((5 / 6 - 79 / 204) * (5 / 2 - 2 * c) + 79 / 204 * (1 - c)))
      = 1 - 79 / 204 + ((5 / 6 - 79 / 204) * (79 / 204) * (1 - c) / 2) /
        ((5 / 6 - 79 / 204) * (5 / 2 - 2 * c) + 79 / 204 * (1 - c)) by
    field_simp]
  have hfrac : 21766 / 32589 - 1 / 10000 - (1 - 79 / 204) ≤
      ((5 / 6 - 79 / 204) * (79 / 204) * (1 - c) / 2) /
        ((5 / 6 - 79 / 204) * (5 / 2 - 2 * c) + 79 / 204 * (1 - c)) := by
    rw [le_div_iff₀ hJ]
    nlinarith
  linarith

/-- **The vertex for every admissible row count.** For a geometry with `lx ≤ 1`, `0 ≤ ly`,
`0 ≤ ℓ` whose low boundary is at most `7/8 − 1/2500`, the high exponent of the binding bin is
positive for every row count within `10⁻⁴` of the published one. -/
theorem endpointExponent_pos_of_lowBoundary_le_of_rowCount {lx ly ℓ R : ℝ} (hlx : lx ≤ 1)
    (hly : 0 ≤ ly) (hℓ : 0 ≤ ℓ) (hR : 21766 / 32589 - 1 / 10000 ≤ R)
    (hσ : lowBoundary lx ly ℓ ≤ 7 / 8 - 1 / 2500) :
    0 < endpointExponent lx ly ℓ (lowBoundary lx ly ℓ) (79 / 204) (79 / 408) R := by
  have hh : 0 ≤ 1 - lx + ℓ := by linarith
  have hmono : endpointExponent lx ly ℓ (lowBoundary lx ly ℓ) (79 / 204) (79 / 408)
      (21766 / 32589 - 1 / 10000) ≤
      endpointExponent lx ly ℓ (lowBoundary lx ly ℓ) (79 / 204) (79 / 408) R := by
    unfold endpointExponent
    nlinarith [mul_nonneg hh (sub_nonneg.2 hR)]
  refine lt_of_lt_of_le ?_ hmono
  unfold lowBoundary at hσ ⊢
  have hμ0 : (0 : ℝ) ≤ max 0 (lx + ly + ℓ - 1) := le_max_left _ _
  have hμ1 : lx + ly + ℓ - 1 ≤ max 0 (lx + ly + ℓ - 1) := le_max_right _ _
  generalize max 0 (lx + ly + ℓ - 1) = μ at hσ hμ0 hμ1 ⊢
  unfold endpointExponent
  nlinarith

/-- The same with the row count at the plain capacity of any `κ ∈ [11/15, 3/4]`. -/
theorem endpointExponent_pos_of_lowBoundary_le_at {lx ly ℓ κ : ℝ} (hlx : lx ≤ 1) (hly : 0 ≤ ly)
    (hℓ : 0 ≤ ℓ) (hκ : 11 / 15 ≤ κ) (hκ' : κ ≤ 3 / 4)
    (hσ : lowBoundary lx ly ℓ ≤ 7 / 8 - 1 / 2500) :
    0 < endpointExponent lx ly ℓ (lowBoundary lx ly ℓ) (79 / 204) (79 / 408)
      (rowCountAt κ (79 / 204)) :=
  endpointExponent_pos_of_lowBoundary_le_of_rowCount hlx hly hℓ
    (rowCountAt_binding_ge hκ hκ') hσ

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

/-- The low boundary in both regimes of the Gram bound: the exceptional term is present only for
`lx ≤ ly`, and for `ly < lx` the low exponent is `lx/2`. -/
def lowBoundaryGen (lx ly ℓ : ℝ) : ℝ :=
  5 / 6 + lx / 6 + max 0 (ly - lx) / 12 - ℓ / 6 + max 0 (lx + ly + ℓ - 1) / 2

theorem lowBoundaryGen_eq_of_le {lx ly : ℝ} (ℓ : ℝ) (h : lx ≤ ly) :
    lowBoundaryGen lx ly ℓ = lowBoundary lx ly ℓ := by
  unfold lowBoundaryGen lowBoundary
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ ly - lx)]
  ring

/-- **The floor in both regimes.** Every geometry whose low boundary is below `13/15` has a
positive exponent in the floor bin: `E = 5(13/15 − σ) + ⅙(ν − ly + lx) + ⅙ν + (5/3)μ +
⅓(μ − lx − ly − ℓ + 1)` with `ν = (ly − lx)₊`, `μ = (lx + ly + ℓ − 1)₊`. -/
theorem endpointExponent_floor_bin_pos_of_lowBoundaryGen_lt {lx ly ℓ : ℝ}
    (hσ : lowBoundaryGen lx ly ℓ < 13 / 15) :
    0 < endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ) 0 0 1 := by
  unfold lowBoundaryGen at hσ ⊢
  have hν0 : (0 : ℝ) ≤ max 0 (ly - lx) := le_max_left _ _
  have hν1 : ly - lx ≤ max 0 (ly - lx) := le_max_right _ _
  have hμ0 : (0 : ℝ) ≤ max 0 (lx + ly + ℓ - 1) := le_max_left _ _
  have hμ1 : lx + ly + ℓ - 1 ≤ max 0 (lx + ly + ℓ - 1) := le_max_right _ _
  generalize max 0 (ly - lx) = ν at hσ hν0 hν1 ⊢
  generalize max 0 (lx + ly + ℓ - 1) = μ at hσ hμ0 hμ1 ⊢
  unfold endpointExponent
  linarith

theorem lowBoundary_balanced : lowBoundary (2 / 5) (2 / 5) (1 / 5) = 13 / 15 := by
  norm_num [lowBoundary]

/-- With the count `U^{1−δ}` in every bin, the balanced geometry `lx = ly = 2/5`, `ℓ = 1/5`
has high exponent `(q − δ/2)/5 ≤ 0` at the boundary `13/15`. -/
theorem endpointExponent_balanced (δ q : ℝ) :
    endpointExponent (2 / 5) (2 / 5) (1 / 5) (13 / 15) δ q (1 - δ) = (q - δ / 2) / 5 := by
  unfold endpointExponent
  ring

/-! ### The order of the row twist

In the published probe the row twist is the sextic symbol and the principal frequencies of the
Poisson side are the sixth powers, with residue point `z = 1/6`. For a probe of the same shape
whose principal frequencies are the `n`-th powers, the balanced budget (`lx = ly = M/2`) has the
same form with `1/n` in the place of `1/6`. -/

/-- Low boundary of the balanced geometry at principal frequencies of order `n`. -/
def lowBoundaryOrder (n M ℓ : ℝ) : ℝ :=
  1 - (1 - M / 2 + ℓ) / n + max 0 (M + ℓ - 1) / 2

/-- The boundary forced by the floor bin (rows without zeros right of the line, summed
trivially) at principal frequencies of order `n`. -/
def floorBinOrder (n M ℓ : ℝ) : ℝ :=
  (1 - M / 2) / 2 - ℓ / 2 + (1 - M / 2 + ℓ) * (1 - 1 / n)

theorem lowBoundaryOrder_six (M ℓ : ℝ) :
    lowBoundaryOrder 6 M ℓ = lowBoundary (M / 2) (M / 2) ℓ := by
  unfold lowBoundaryOrder lowBoundary
  rw [show M / 2 + M / 2 + ℓ - 1 = M + ℓ - 1 by ring]
  ring

theorem floorBinOrder_six (M ℓ σ₀ : ℝ) :
    floorBinOrder 6 M ℓ - σ₀ = endpointExponent (M / 2) (M / 2) ℓ σ₀ 0 0 1 := by
  unfold floorBinOrder endpointExponent
  ring

/-- **The floor at order `n`.** For `n ≥ 2`, a balanced geometry whose low boundary is below
`1 − 4/(5n)` has a larger floor-bin boundary: the probe does not go below `1 − 4/(5n)`, which is
`13/15` at `n = 6`, `11/15` at `n = 3` and `3/5` at `n = 2`. -/
theorem lowBoundaryOrder_lt_floorBinOrder {n M ℓ : ℝ} (hn : 2 ≤ n)
    (h : lowBoundaryOrder n M ℓ < 1 - 4 / (5 * n)) :
    lowBoundaryOrder n M ℓ < floorBinOrder n M ℓ := by
  have hn0 : 0 < n := by linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 1 / n := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr2 : r ≤ 1 / 2 := by
    rw [hr, div_le_iff₀ hn0]
    linarith
  have e1 : (1 - M / 2 + ℓ) / n = (1 - M / 2 + ℓ) * r := by rw [hr]; ring
  have e2 : 4 / (5 * n) = 4 / 5 * r := by rw [hr]; field_simp
  unfold lowBoundaryOrder floorBinOrder at *
  rw [e1, e2] at h
  rw [e1, ← hr]
  have hμ0 : (0 : ℝ) ≤ max 0 (M + ℓ - 1) := le_max_left _ _
  have hμ1 : M + ℓ - 1 ≤ max 0 (M + ℓ - 1) := le_max_right _ _
  generalize max 0 (M + ℓ - 1) = μ at h hμ0 hμ1 ⊢
  -- `t = 1 − M/2 + ℓ` exceeds `4/5 + μ`
  have h1 : μ / 2 < (1 - M / 2 + ℓ - 4 / 5) * r := by linarith
  have ht : 0 < 1 - M / 2 + ℓ - 4 / 5 := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith [mul_nonneg (sub_nonneg.2 hc) hr0.le]
  have h2 : (1 - M / 2 + ℓ - 4 / 5) * r ≤ (1 - M / 2 + ℓ - 4 / 5) / 2 := by nlinarith
  linarith

/-! ### The number of row variables

Each Poisson summation in a row variable of order `n` contributes `N(A)^{−1/2+1/n}` to the
principal row (its Gauss sum, and the count of the `n`-th powers among the dual frequencies) and
loses `x_i/n` against Cauchy–Schwarz. -/

/-- Low boundary of the balanced geometry (`X_i = Y_i`, row ball `Q = Z`, `∑ x_i = 1/2`) of a
design with `k` row variables of order `n`: the principal row
`Z^{β − 1/2 − k(1/2 − 1/n)} ∏ X_i^{1−1/n} Y_i^{1/2}` against the direct bound
`Q^{1/2} ∏ X_i Y_i^{1/2}`. -/
def lowBoundaryDesign (k n : ℝ) : ℝ := 1 / 2 + k * (1 / 2 - 1 / n) + 1 / (2 * n)

/-- One row variable: the balanced budget of order `n` at row length `1` without slots. -/
theorem lowBoundaryDesign_one (n : ℝ) : lowBoundaryDesign 1 n = lowBoundaryOrder n 1 0 := by
  unfold lowBoundaryDesign lowBoundaryOrder
  rw [show (1 : ℝ) + 0 - 1 = 0 by ring, max_self]
  ring

/-- The published design: `11/12`, the balanced low estimate of the uncompensated probe. -/
theorem lowBoundaryDesign_one_six : lowBoundaryDesign 1 6 = 11 / 12 := by
  norm_num [lowBoundaryDesign]

/-- The cubic theta row with two cubic row variables. -/
theorem lowBoundaryDesign_two_three : lowBoundaryDesign 2 3 = 1 := by
  norm_num [lowBoundaryDesign]

/-- Three cubic row variables without a theta row. -/
theorem lowBoundaryDesign_three_three : lowBoundaryDesign 3 3 = 7 / 6 := by
  norm_num [lowBoundaryDesign]

/-- **Two or more row variables give no information.** For `k ≥ 2` and order `n ≥ 3` the balanced
low boundary is at least `1`. -/
theorem one_le_lowBoundaryDesign {k n : ℝ} (hk : 2 ≤ k) (hn : 3 ≤ n) :
    1 ≤ lowBoundaryDesign k n := by
  have hn0 : 0 < n := by linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 1 / n := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr3 : r ≤ 1 / 3 := by
    rw [hr, div_le_iff₀ hn0]
    linarith
  have e : 1 / (2 * n) = r / 2 := by rw [hr]; field_simp
  unfold lowBoundaryDesign
  rw [e, ← hr]
  nlinarith [mul_nonneg (sub_nonneg.2 hk) (by linarith : (0 : ℝ) ≤ 1 / 2 - r)]

/-! ### The conductor of the rows

A probe whose row coefficient is the Gauss sum of a character `χ` and whose row twist is `φ`, with
`χ φ` quadratic, has principal frequencies of the order `n` of `φ`. If a row has conductor
`q_m^κ`, the reflected rows of a row ball `Z^M` have length `Z^{κM − 1}`, and with an optimal
large sieve their mean square exceeds `Z^M` by the exponent `((κ − 1)M − 1)₊`. The cubic
coefficient with sextic twist has `(κ, n) = (2, 6)`; the coefficient of order four with itself as
twist has `(3, 4)`; the sextic coefficient with cubic twist has `(4, 3)`. -/

/-- Low boundary without slots at balanced scales, for rows of conductor exponent `κ` and
principal frequencies of order `n`. -/
def lowUnslotted (κ n M : ℝ) : ℝ := 1 - (1 - M / 2) / n + max 0 ((κ - 1) * M - 1) / 2

/-- Boundary of the floor bin without slots at balanced scales. -/
def floorUnslotted (n M : ℝ) : ℝ := (3 / 2 - 1 / n) * (1 - M / 2)

theorem lowUnslotted_two (n M : ℝ) : lowUnslotted 2 n M = lowBoundaryOrder n M 0 := by
  unfold lowUnslotted lowBoundaryOrder
  have e1 : ((2 : ℝ) - 1) * M - 1 = M + 0 - 1 := by ring
  have e2 : (1 : ℝ) - M / 2 + 0 = 1 - M / 2 := by ring
  rw [e1, e2]

theorem floorUnslotted_eq (n M : ℝ) : floorUnslotted n M = floorBinOrder n M 0 := by
  unfold floorUnslotted floorBinOrder
  ring

/-- Cubic coefficient, sextic twist: the corner is `8/9`, at row length `2/3`. -/
theorem corner_two_six (M : ℝ) : 8 / 9 ≤ max (lowUnslotted 2 6 M) (floorUnslotted 6 M) := by
  rcases le_total M (2 / 3) with h | h
  · refine le_max_of_le_right ?_
    unfold floorUnslotted
    linarith
  · refine le_max_of_le_left ?_
    unfold lowUnslotted
    have hm : (0 : ℝ) ≤ max 0 ((2 - 1) * M - 1) := le_max_left _ _
    generalize max 0 (((2 : ℝ) - 1) * M - 1) = m at hm ⊢
    linarith

theorem corner_two_six_attained :
    max (lowUnslotted 2 6 (2 / 3)) (floorUnslotted 6 (2 / 3)) = 8 / 9 := by
  have h1 : lowUnslotted 2 6 (2 / 3) = 8 / 9 := by
    unfold lowUnslotted
    rw [max_eq_left (by norm_num)]
    norm_num
  have h2 : floorUnslotted 6 (2 / 3) = 8 / 9 := by
    unfold floorUnslotted
    norm_num
  rw [h1, h2, max_self]

/-- Coefficient of order four with itself as twist: the corner is at least `25/28`. -/
theorem corner_three_four (M : ℝ) :
    25 / 28 ≤ max (lowUnslotted 3 4 M) (floorUnslotted 4 M) := by
  rcases le_total M (4 / 7) with h | h
  · refine le_max_of_le_right ?_
    unfold floorUnslotted
    linarith
  · refine le_max_of_le_left ?_
    unfold lowUnslotted
    have hm : ((3 : ℝ) - 1) * M - 1 ≤ max 0 ((3 - 1) * M - 1) := le_max_right _ _
    generalize max 0 (((3 : ℝ) - 1) * M - 1) = m at hm ⊢
    have e : ((3 : ℝ) - 1) * M - 1 = 2 * M - 1 := by ring
    rw [e] at hm
    linarith

/-- Sextic coefficient, cubic twist: the corner is at least `49/54`. -/
theorem corner_four_three (M : ℝ) :
    49 / 54 ≤ max (lowUnslotted 4 3 M) (floorUnslotted 3 M) := by
  rcases le_total M (4 / 9) with h | h
  · refine le_max_of_le_right ?_
    unfold floorUnslotted
    linarith
  · refine le_max_of_le_left ?_
    unfold lowUnslotted
    have hm : ((4 : ℝ) - 1) * M - 1 ≤ max 0 ((4 - 1) * M - 1) := le_max_right _ _
    generalize max 0 (((4 : ℝ) - 1) * M - 1) = m at hm ⊢
    have e : ((4 : ℝ) - 1) * M - 1 = 3 * M - 1 := by ring
    rw [e] at hm
    linarith

/-! ### The reflected mean square through the twists

Poisson summation in the row index turns the mean square of the rows of length `Z^M`, with
completed index of length `Z`, into the mean square of the Möbius sums of the twists of norm up
to `Z^{2 − M}`. A bin of twists with count exponent `R`, zeros at real part `(1 + δ)/2` and prime
amplitude `q` then contributes `Z^{dualExcess}` times the generic value, the Möbius sums having
length `Z^{1 − ℓ}`. Where every bin has `dualExcess ≤ 0`, the reflected mean square is generic and
the low boundary has no dual-length term. -/

/-- Exponent of a bin of twists in the mean square of the marked rows of length `M`, relative to
its generic value. -/
def dualExcess (M ℓ δ q R : ℝ) : ℝ := (2 - M) * R + 2 * q * ℓ + δ * (1 - ℓ) - 1

/-- With the count `U^{1 − δ}` and full prime amplitude the excess is `(1 − M)(1 − δ)`. -/
theorem dualExcess_density (M ℓ δ : ℝ) :
    dualExcess M ℓ δ (δ / 2) (1 - δ) = (1 - M) * (1 - δ) := by
  unfold dualExcess
  ring

/-- **Rows at least as long as the completed index are generic under the count `U^{1 − δ}`.** -/
theorem dualExcess_nonpos_of_density {M ℓ δ q : ℝ} (hM : 1 ≤ M) (hδ : δ ≤ 1) (hℓ : 0 ≤ ℓ)
    (hq : q ≤ δ / 2) : dualExcess M ℓ δ q (1 - δ) ≤ 0 := by
  have h1 : dualExcess M ℓ δ q (1 - δ) ≤ dualExcess M ℓ δ (δ / 2) (1 - δ) := by
    unfold dualExcess
    nlinarith [mul_nonneg hℓ (sub_nonneg.2 hq)]
  rw [dualExcess_density] at h1
  nlinarith [mul_nonneg (sub_nonneg.2 hM) (sub_nonneg.2 hδ)]

/-- Between the dual length `1 − ℓ` and the length `1` of the completed index the excess of the
floor bin is `1 − M`: it meets the unconditional excess `M + ℓ − 1` at `M = 1 − ℓ/2`. -/
theorem dualExcess_floor_bin (M ℓ : ℝ) : dualExcess M ℓ 0 0 1 = 1 - M := by
  unfold dualExcess
  ring

/-- The low boundary with a generic reflected mean square. -/
def lowBoundaryFree (lx ly ℓ : ℝ) : ℝ := 5 / 6 + lx / 6 + max 0 (ly - lx) / 12 - ℓ / 6

theorem lowBoundaryFree_le_lowBoundaryGen (lx ly ℓ : ℝ) :
    lowBoundaryFree lx ly ℓ ≤ lowBoundaryGen lx ly ℓ := by
  unfold lowBoundaryFree lowBoundaryGen
  linarith [le_max_left (0 : ℝ) (lx + ly + ℓ - 1)]

/-- **The barrier.** With rescaled row length `lx + ly − 2ℓ ≥ 0` the low boundary is at least
`5/6`, whatever the reflected mean square. -/
theorem five_sixths_le_lowBoundaryFree {lx ly ℓ : ℝ} (h : 2 * ℓ ≤ lx + ly) :
    5 / 6 ≤ lowBoundaryFree lx ly ℓ := by
  unfold lowBoundaryFree
  have h1 : ly - lx ≤ max 0 (ly - lx) := le_max_right _ _
  have h0 : (0 : ℝ) ≤ max 0 (ly - lx) := le_max_left _ _
  generalize max 0 (ly - lx) = ν at h0 h1 ⊢
  linarith

theorem lowBoundaryFree_half : lowBoundaryFree (1 / 2) (1 / 2) (1 / 2) = 5 / 6 := by
  norm_num [lowBoundaryFree]

/-- At `lx = ly = ℓ = 1/2` and `σ₀ = 5/6`, with the count `U^{1 − δ}`, the high exponent of a
bin is `q/2 − δ/4`. -/
theorem endpointExponent_half_density (δ q : ℝ) :
    endpointExponent (1 / 2) (1 / 2) (1 / 2) (5 / 6) δ q (1 - δ) = q / 2 - δ / 4 := by
  unfold endpointExponent
  ring

/-- **With generic reflected rows and the count `U^{1 − δ}` the budget closes at `5/6`.** The
geometry `lx = ly = ℓ = 1/2` has free low boundary `5/6`, rows of the length of the completed
index, no excess in any bin, and a nonpositive high exponent in every bin. -/
theorem budget_half_density {δ q : ℝ} (hδ : δ ≤ 1) (hq : q ≤ δ / 2) :
    lowBoundaryFree (1 / 2) (1 / 2) (1 / 2) = 5 / 6 ∧
      dualExcess (1 / 2 + 1 / 2) (1 / 2) δ q (1 - δ) ≤ 0 ∧
      endpointExponent (1 / 2) (1 / 2) (1 / 2) (5 / 6) δ q (1 - δ) ≤ 0 := by
  refine ⟨lowBoundaryFree_half, dualExcess_nonpos_of_density (by norm_num) hδ (by norm_num) hq, ?_⟩
  rw [endpointExponent_half_density]
  linarith

end

end GaloisForLFunctions.FamilyContinuationTheory.Budget
