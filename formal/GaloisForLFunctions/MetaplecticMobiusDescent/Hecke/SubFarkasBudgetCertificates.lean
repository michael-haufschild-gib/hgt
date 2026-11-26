import GaloisForLFunctions.FamilyContinuationTheory.TheTrueVertexBelowSevenEighths
import GaloisForLFunctions.JointMarkedMoments.Induction.TheLargeValueExponents

/-!
# Sub-`16799/19200` detector and Stage-1 complete-factor selection certificates

Algebraic sum-of-squares, Bernstein, and subset-sum certificates for the Stage-1 complete-factor
upgrade of `source_batch_inverse_marked` on `69/100 ≤ r ≤ 19/26` and for the compensated physical
detector at the edge geometry `(lx, ly, ℓ) = (17/48, 2299/4800, 801/4800)`:

* **Low boundary below the Farkas vertex (`lowBoundary_sub16799`, `sub16799_lt_farkas_wall`).**
  At `(17/48, 2299/4800, 801/4800)` we have `lowBoundary = lowBoundaryGen = 16799/19200 <
  40535/46328 < 20999/24000` and `1 - 16799/19200 = 2401/19200 > 3001/24000`, while
  `1 + 3ℓ = 7203/4800 ≤ 7998/4800 = 2M` keeps `tupleExponent d (reflectedAllowance M ℓ d) ≤ 0`.
* **Upgraded balanced endpoint certificate (`endpoint_certificate_sub16799`).** Inside the critical
  box `B = [17/50, 41/100] × [12/25, 1/2]`, combining the Stage-1 inverse-marked line
  `269/500 - (69/125) r` with the `9/2` plain-marked line places the balanced crossing strictly inside
  `[139/200, 364/500] ⊂ (69/100, 19/26)` and certifies `endpointExponent ≤ -1/20000`. Outside `B`,
  the existing balanced count `rowCount δ x` already satisfies `endpointExponent ≤ -1/20000`.
* **Stage-1 complete-factor large-value and slot-supply certificates
  (`stage1_large_value_certificate`, `stage1_slot_supply_certificate`).** Across all
  `r ∈ [17/25, 19/26]`, `ν ∈ [11/25, 3/4]`, and `x ∈ [0, 1/2]`, with selection width
  `u = (11/3) (269/500 - 69 r / 125 - (1 - r)/2)` and dual row exponent `H₀ = 1 - 6 u`, the dual
  large-value exponent saves `1/2000` below `H₀ + u` while `z_rem` exceeds both the inverse and
  plain witness slot requirements at `H₀` by at least `1/1000`.
-/

namespace GaloisForLFunctions.FamilyContinuationTheory.Budget

open scoped BigOperators Classical

noncomputable section

/-! ### The sub-`16799/19200` edge geometry `(17/48, 2299/4800, 801/4800)` -/

theorem lowBoundary_sub16799 :
    lowBoundary (17 / 48) (2299 / 4800) (801 / 4800) = 16799 / 19200 := by
  unfold lowBoundary
  rw [show (17 : ℝ) / 48 + 2299 / 4800 + 801 / 4800 - 1 = 0 by ring, max_self]
  norm_num

theorem lowBoundaryGen_sub16799 :
    lowBoundaryGen (17 / 48) (2299 / 4800) (801 / 4800) = 16799 / 19200 := by
  rw [lowBoundaryGen_eq_of_le (801 / 4800) (by norm_num), lowBoundary_sub16799]

theorem sub16799_lt_farkas_wall : (16799 / 19200 : ℝ) < 40535 / 46328 := by norm_num

theorem sub16799_lt_subSevenEighths : (16799 / 19200 : ℝ) < 20999 / 24000 := by norm_num

theorem one_sub_sub16799_gt_wall : (3001 / 24000 : ℝ) < 1 - 16799 / 19200 := by norm_num

/-- On `(M, ℓ) = (3999/4800, 801/4800)` we have `1 + 3ℓ = 7203/4800 ≤ 7998/4800 = 2M`, so the
reflected allowance of unselected slots is nonpositive. -/
theorem tupleExponent_reflectedAllowance_sub16799 {d : ℝ} (hd : 0 ≤ d) :
    tupleExponent d (reflectedAllowance (3999 / 4800) (801 / 4800) d) ≤ 0 :=
  tupleExponent_reflectedAllowance_nonpos hd (by norm_num)

/-! ### Reusable degree-`(2, 3)` Bernstein nonnegativity helper -/

/-- A degree-`(2, 3)` bivariate Bernstein polynomial on `[0, 1]²` with nonnegative coefficients is
nonnegative. -/
def bernstein23 (u v : ℝ)
    (c00 c01 c02 c03 c10 c11 c12 c13 c20 c21 c22 c23 : ℝ) : ℝ :=
  (1 - u) ^ 2 * (c00 * (1 - v) ^ 3 + 3 * c01 * v * (1 - v) ^ 2 +
      3 * c02 * v ^ 2 * (1 - v) + c03 * v ^ 3) +
    2 * u * (1 - u) * (c10 * (1 - v) ^ 3 + 3 * c11 * v * (1 - v) ^ 2 +
      3 * c12 * v ^ 2 * (1 - v) + c13 * v ^ 3) +
    u ^ 2 * (c20 * (1 - v) ^ 3 + 3 * c21 * v * (1 - v) ^ 2 +
      3 * c22 * v ^ 2 * (1 - v) + c23 * v ^ 3)

theorem bernstein23_nonneg {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    {c00 c01 c02 c03 c10 c11 c12 c13 c20 c21 c22 c23 : ℝ}
    (h00 : 0 ≤ c00) (h01 : 0 ≤ c01) (h02 : 0 ≤ c02) (h03 : 0 ≤ c03)
    (h10 : 0 ≤ c10) (h11 : 0 ≤ c11) (h12 : 0 ≤ c12) (h13 : 0 ≤ c13)
    (h20 : 0 ≤ c20) (h21 : 0 ≤ c21) (h22 : 0 ≤ c22) (h23 : 0 ≤ c23) :
    0 ≤ bernstein23 u v c00 c01 c02 c03 c10 c11 c12 c13 c20 c21 c22 c23 := by
  have hu' : 0 ≤ 1 - u := by linarith
  have hv' : 0 ≤ 1 - v := by linarith
  unfold bernstein23
  positivity

/-! ### Critical-box `B = [17/50, 41/100] × [12/25, 1/2]` upgraded row-count functions -/

/-- Critical box `B = [17/50, 41/100] × [12/25, 1/2]` where the Stage-1 inverse-marked line
`269/500 - (69/125) r` is invoked. -/
def inBoxB (δ x : ℝ) : Prop :=
  17 / 50 ≤ δ ∧ δ ≤ 41 / 100 ∧ 12 / 25 ≤ x ∧ x ≤ 1 / 2

/-- Crossing denominator of the upgraded `269/500 - (69/125) r` inverse count and `9/2` plain count. -/
def rowD_B (x : ℝ) : ℝ := 3 - 2242 * x / 1125

/-- Short-count slope weight for the upgraded `B`-box crossing. -/
def rowP_B (x : ℝ) : ℝ := (2 - 8 * x / 9) * (1 - 138 * x / 125)

/-- Numerator quadratic of `t_bal_B - 1` for the upgraded `B`-box crossing. -/
def rowN_B (x : ℝ) : ℝ := 1 - 1679 * x / 1125 + 524 * x ^ 2 / 1125

/-- Balance denominator in the critical box `B`. -/
def rowJ_B (δ x : ℝ) : ℝ := (5 / 6 - δ) * rowD_B x + δ * rowP_B x

/-- Balanced cutoff `t ∈ [1, 3/2]` in the critical box `B`. -/
def balancedCutoff_B (δ x : ℝ) : ℝ := 1 + δ * rowN_B x / rowJ_B δ x

/-- Crossing point `r = crossing_B x t` of the upgraded inverse and `9/2` plain counts. -/
def crossing_B (x t : ℝ) : ℝ := ((2 - 8 * x / 9) * t - 1421 * x / 2250) / rowD_B x

/-- Upgraded balanced row-count exponent inside `B`. -/
def rowCount_B (δ x : ℝ) : ℝ := 1 - δ + (5 / 6 - δ) * δ * rowN_B x / rowJ_B δ x

/-- Combined sub-`16799/19200` balanced row-count exponent across `[0, 5/6] × [0, 1/2]`. -/
def rowCountSub16799 (δ x : ℝ) : ℝ :=
  if inBoxB δ x then rowCount_B δ x else rowCount δ x

theorem rowD_B_pos {x : ℝ} (hx : x ≤ 1 / 2) : 2254 / 1125 ≤ rowD_B x := by
  unfold rowD_B
  linarith

theorem rowN_B_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    833 / 2250 ≤ rowN_B x ∧ rowN_B x ≤ 1 := by
  unfold rowN_B
  constructor
  · nlinarith [sq_nonneg (1 / 2 - x)]
  · have hx1 : x * (1679 - 524 * x) ≥ 0 := mul_nonneg hx0 (by linarith)
    nlinarith

theorem rowJ_B_pos {δ x : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6) (hx : x ≤ 1 / 2) :
    392 / 675 ≤ rowJ_B δ x := by
  unfold rowJ_B rowD_B rowP_B
  have hD : 2254 / 1125 ≤ 3 - 2242 * x / 1125 := by linarith
  have hP : 784 / 1125 ≤ (2 - 8 * x / 9) * (1 - 138 * x / 125) := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hδ) (sub_nonneg.mpr hD),
    mul_nonneg hδ0 (sub_nonneg.mpr hP)]

theorem rowJ_B_le {δ x : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    rowJ_B δ x ≤ 5 / 2 := by
  unfold rowJ_B rowD_B rowP_B
  have hD : 3 - 2242 * x / 1125 ≤ 3 := by linarith
  have hP : (2 - 8 * x / 9) * (1 - 138 * x / 125) ≤ 2 := by
    nlinarith [mul_nonneg hx0 (show 0 ≤ 1 - 138 * x / 125 by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hδ) (sub_nonneg.mpr hD),
    mul_nonneg hδ0 (sub_nonneg.mpr hP)]

/-- Inside `B = [17/50, 41/100] × [12/25, 1/2]`, the balanced crossing `crossing_B x (balancedCutoff_B δ x)`
lies strictly inside `[139/200, 364/500] ⊂ (69/100, 19/26)`. -/
theorem crossing_B_mem_box {δ x : ℝ} (hB : inBoxB δ x) :
    139 / 200 ≤ crossing_B x (balancedCutoff_B δ x) ∧
      crossing_B x (balancedCutoff_B δ x) ≤ 364 / 500 := by
  rcases hB with ⟨hδ0, hδ1, hx0, hx1⟩
  have hD := rowD_B_pos hx1
  have hD0 : 0 < rowD_B x := by linarith
  have hJ := rowJ_B_pos (δ := δ) (x := x) (by linarith) (by linarith) hx1
  have hJ0 : 0 < rowJ_B δ x := by linarith
  have hDJ : 0 < rowD_B x * rowJ_B δ x := mul_pos hD0 hJ0
  set u := (δ - 17 / 50) / (41 / 100 - 17 / 50)
  set v := (x - 12 / 25) / (1 / 2 - 12 / 25)
  have hu0 : 0 ≤ u := div_nonneg (by linarith) (by norm_num)
  have hu1 : u ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 41 / 100 - 17 / 50)).mpr (by linarith)
  have hv0 : 0 ≤ v := div_nonneg (by linarith) (by norm_num)
  have hv1 : v ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 2 - 12 / 25)).mpr (by linarith)
  have hcr : crossing_B x (balancedCutoff_B δ x) =
      ((2 - 8 * x / 9) * (rowJ_B δ x + δ * rowN_B x) - 1421 * x / 2250 * rowJ_B δ x) /
        (rowD_B x * rowJ_B δ x) := by
    unfold crossing_B balancedCutoff_B
    field_simp [hD0.ne', hJ0.ne']
  rw [hcr, le_div_iff₀ hDJ, div_le_iff₀ hDJ]
  constructor
  · have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
      (c00 := 111039738257 / 5493164062500) (c01 := 32189429653 / 1977539062500)
      (c02 := 984064081 / 79101562500) (c03 := 2753261 / 316406250)
      (c10 := 56937228509 / 1171875000000) (c11 := 55980892763 / 1265625000000)
      (c12 := 3036285959 / 75937500000) (c13 := 181447 / 5062500)
      (c20 := 3381974232119 / 43945312500000) (c21 := 126889653539 / 1757812500000)
      (c22 := 64098380003 / 949218750000) (c23 := 3321269 / 52734375)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hid : ((2 - 8 * x / 9) * (rowJ_B δ x + δ * rowN_B x) - 1421 * x / 2250 * rowJ_B δ x) -
        (139 / 200) * (rowD_B x * rowJ_B δ x) =
        bernstein23 u v
          (111039738257 / 5493164062500) (32189429653 / 1977539062500)
          (984064081 / 79101562500) (2753261 / 316406250)
          (56937228509 / 1171875000000) (55980892763 / 1265625000000)
          (3036285959 / 75937500000) (181447 / 5062500)
          (3381974232119 / 43945312500000) (126889653539 / 1757812500000)
          (64098380003 / 949218750000) (3321269 / 52734375) := by
      dsimp [u, v]
      unfold bernstein23 rowJ_B rowD_B rowP_B rowN_B
      ring
    linarith
  · have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
      (c00 := 148133015903 / 2288818359375) (c01 := 166442997836 / 2471923828125)
      (c02 := 41448152207 / 593261718750) (c03 := 19067713 / 263671875)
      (c10 := 73104855287 / 2197265625000) (c11 := 38305558229 / 1054687500000)
      (c12 := 14913914407 / 379687500000) (c13 := 4267949 / 101250000)
      (c20 := 50025191339 / 27465820312500) (c21 := 209828901799 / 39550781250000)
      (c22 := 13754214173 / 1582031250000) (c23 := 75868513 / 6328125000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hid : (364 / 500) * (rowD_B x * rowJ_B δ x) -
        ((2 - 8 * x / 9) * (rowJ_B δ x + δ * rowN_B x) - 1421 * x / 2250 * rowJ_B δ x) =
        bernstein23 u v
          (148133015903 / 2288818359375) (166442997836 / 2471923828125)
          (41448152207 / 593261718750) (19067713 / 263671875)
          (73104855287 / 2197265625000) (38305558229 / 1054687500000)
          (14913914407 / 379687500000) (4267949 / 101250000)
          (50025191339 / 27465820312500) (209828901799 / 39550781250000)
          (13754214173 / 1582031250000) (75868513 / 6328125000) := by
      dsimp [u, v]
      unfold bernstein23 rowJ_B rowD_B rowP_B rowN_B
      ring
    linarith

/-! ### Sum-of-squares and Bernstein certificates for `endpointExponent` at `16799/19200` -/

/-- Cleared-denominator margin `-(endpointExponent + 1/20000) * rowJ_B` inside `B`. -/
def sub16799MarginB (δ x : ℝ) : ℝ :=
  rowJ_B δ x * (-(1 + δ) * (1 - 2299 / 4800) / 2 + 16799 / 19200 + (801 / 4800) / 2
      - (x * δ) * (801 / 4800) - (1 - 17 / 48 + 801 / 4800) * (1 - δ / 2 - 1 / 6) - 1 / 20000)
    - (1 - 17 / 48 + 801 / 4800) * ((5 / 6 - δ) * δ * rowN_B x)

/-- Cleared-denominator margin `-(endpointExponent + 1/20000) * rowJ` outside `B`. -/
def sub16799MarginOut (δ x : ℝ) : ℝ :=
  rowJ δ x * (-(1 + δ) * (1 - 2299 / 4800) / 2 + 16799 / 19200 + (801 / 4800) / 2
      - (x * δ) * (801 / 4800) - (1 - 17 / 48 + 801 / 4800) * (1 - δ / 2 - 1 / 6) - 1 / 20000)
    - (1 - 17 / 48 + 801 / 4800) * ((5 / 6 - δ) * δ * rowP x / 2)

private def a2_B (y : ℝ) : ℝ :=
  2369003 / 10800000 + 280793 / 450000 * y + 248531 / 540000 * y ^ 2 + 2047 / 12500 * y ^ 3

private def a1_B (y : ℝ) : ℝ :=
  18729319 / 216000000 + 251547643 / 1620000000 * y + 7347197 / 810000000 * y ^ 2

private def rem_B (y : ℝ) : ℝ :=
  4355667235871 / 419904000000000000 + 1038390744838699 / 524880000000000000 * y +
    9987451132196087 / 874800000000000000 * y ^ 2 +
    12149027939762579 / 656100000000000000 * y ^ 3 +
    3614218136337191 / 656100000000000000 * y ^ 4

private def a2_R1 (z : ℝ) : ℝ :=
  55941467 / 225000000 + 4211989 / 6750000 * z + 53293 / 120000 * z ^ 2 + 89 / 600 * z ^ 3

private def a1_R1 (z : ℝ) : ℝ :=
  509193523 / 5400000000 + 94513601 / 648000000 * z + 43321 / 4320000 * z ^ 2

private def rem_R1 (z : ℝ) : ℝ :=
  239830002735157 / 9720000000000000000 + 1700821465080059 / 583200000000000000 * z +
    1813133014431337 / 139968000000000000 * z ^ 2 +
    23465961890329 / 1399680000000000 * z ^ 3 +
    29233989653 / 6220800000000 * z ^ 4

theorem sub16799MarginB_nonneg {δ x : ℝ} (hx : x ≤ 1 / 2) :
    0 ≤ sub16799MarginB δ x := by
  set y := 1 / 2 - x
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have ha2 : 0 < a2_B y := by unfold a2_B; positivity
  have hrem : 0 ≤ rem_B y := by unfold rem_B; positivity
  have hsq : 0 ≤ (a2_B y * δ - a1_B y) ^ 2 := sq_nonneg _
  have hsos : a2_B y * sub16799MarginB δ x = (a2_B y * δ - a1_B y) ^ 2 + rem_B y := by
    dsimp [y]
    unfold sub16799MarginB rowJ_B rowD_B rowP_B rowN_B a2_B a1_B rem_B
    ring
  nlinarith

theorem sub16799MarginOut_nonneg_R1 {δ x : ℝ} (hx : x ≤ 12 / 25) :
    0 ≤ sub16799MarginOut δ x := by
  set z := 12 / 25 - x
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have ha2 : 0 < a2_R1 z := by unfold a2_R1; positivity
  have hrem : 0 ≤ rem_R1 z := by unfold rem_R1; positivity
  have hsq : 0 ≤ (a2_R1 z * δ - a1_R1 z) ^ 2 := sq_nonneg _
  have hsos : a2_R1 z * sub16799MarginOut δ x = (a2_R1 z * δ - a1_R1 z) ^ 2 + rem_R1 z := by
    dsimp [z]
    unfold sub16799MarginOut rowJ rowD rowP a2_R1 a1_R1 rem_R1
    ring
  nlinarith

theorem sub16799MarginOut_nonneg_R2 {δ x : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 17 / 50)
    (hx0 : 12 / 25 ≤ x) (hx1 : x ≤ 1 / 2) :
    0 ≤ sub16799MarginOut δ x := by
  set u := δ / (17 / 50)
  set v := (x - 12 / 25) / (1 / 2 - 12 / 25)
  have hu0 : 0 ≤ u := div_nonneg hδ0 (by norm_num)
  have hu1 : u ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 17 / 50)).mpr (by linarith)
  have hv0 : 0 ≤ v := div_nonneg (by linarith) (by norm_num)
  have hv1 : v ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 2 - 12 / 25)).mpr (by linarith)
  have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
    (c00 := 4647671 / 129600000) (c01 := 83154827 / 2332800000)
    (c02 := 10331447 / 291600000) (c03 := 1095311 / 31104000)
    (c10 := 3079074077 / 810000000000) (c11 := 57098208287 / 14580000000000)
    (c12 := 2350658203 / 583200000000) (c13 := 16114153 / 3888000000)
    (c20 := 305316649 / 632812500000) (c21 := 814764847 / 1822500000000)
    (c22 := 30441443 / 72900000000) (c23 := 382867 / 972000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hid : sub16799MarginOut δ x = bernstein23 u v
      (4647671 / 129600000) (83154827 / 2332800000)
      (10331447 / 291600000) (1095311 / 31104000)
      (3079074077 / 810000000000) (57098208287 / 14580000000000)
      (2350658203 / 583200000000) (16114153 / 3888000000)
      (305316649 / 632812500000) (814764847 / 1822500000000)
      (30441443 / 72900000000) (382867 / 972000000) := by
    dsimp [u, v]
    unfold bernstein23 sub16799MarginOut rowJ rowD rowP
    ring
  linarith

theorem sub16799MarginOut_nonneg_R3 {δ x : ℝ} (hδ0 : 41 / 100 ≤ δ) (hδ1 : δ ≤ 5 / 6)
    (hx0 : 12 / 25 ≤ x) (hx1 : x ≤ 1 / 2) :
    0 ≤ sub16799MarginOut δ x := by
  set u := (δ - 41 / 100) / (5 / 6 - 41 / 100)
  set v := (x - 12 / 25) / (1 / 2 - 12 / 25)
  have hu0 : 0 ≤ u := div_nonneg (by linarith) (by norm_num)
  have hu1 : u ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 5 / 6 - 41 / 100)).mpr (by linarith)
  have hv0 : 0 ≤ v := div_nonneg (by linarith) (by norm_num)
  have hv1 : v ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 2 - 12 / 25)).mpr (by linarith)
  have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
    (c00 := 211467649 / 632812500000) (c01 := 3156359753 / 14580000000000)
    (c02 := 125571839 / 1166400000000) (c03 := 116449 / 15552000000)
    (c10 := 1927570747 / 540000000000) (c11 := 30535261417 / 9720000000000)
    (c12 := 1062189673 / 388800000000) (c13 := 224699 / 96000000)
    (c20 := 27735487 / 540000000) (c21 := 484814227 / 9720000000)
    (c22 := 2092301 / 43200000) (c23 := 121891 / 2592000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hid : sub16799MarginOut δ x = bernstein23 u v
      (211467649 / 632812500000) (3156359753 / 14580000000000)
      (125571839 / 1166400000000) (116449 / 15552000000)
      (1927570747 / 540000000000) (30535261417 / 9720000000000)
      (1062189673 / 388800000000) (224699 / 96000000)
      (27735487 / 540000000) (484814227 / 9720000000)
      (2092301 / 43200000) (121891 / 2592000) := by
    dsimp [u, v]
    unfold bernstein23 sub16799MarginOut rowJ rowD rowP
    ring
  linarith

/-- **Sub-`16799/19200` balanced endpoint certificate.** Across all `0 ≤ δ ≤ 5/6` and `0 ≤ x ≤ 1/2`,
`endpointExponent` at `(17/48, 2299/4800, 801/4800)` and `σ₀ = 16799/19200` with
`rowCountSub16799 δ x` is at most `-1/20000`. -/
theorem endpoint_certificate_sub16799 {δ x : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6)
    (_hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    endpointExponent (17 / 48) (2299 / 4800) (801 / 4800) (16799 / 19200)
      δ (x * δ) (rowCountSub16799 δ x) ≤ -(1 / 20000) := by
  unfold rowCountSub16799
  split_ifs with hB
  · have hJ := rowJ_B_pos hδ0 hδ hx
    have hJ0 : 0 < rowJ_B δ x := by linarith
    have hM := sub16799MarginB_nonneg (δ := δ) hx
    have hid : endpointExponent (17 / 48) (2299 / 4800) (801 / 4800) (16799 / 19200)
        δ (x * δ) (rowCount_B δ x) + 1 / 20000 = -(sub16799MarginB δ x / rowJ_B δ x) := by
      unfold endpointExponent rowCount_B sub16799MarginB
      field_simp [hJ0.ne']
      ring
    have hq : 0 ≤ sub16799MarginB δ x / rowJ_B δ x := div_nonneg hM hJ0.le
    linarith
  · have hJ := rowJ_pos hδ0 hδ hx
    have hJ0 : 0 < rowJ δ x := by linarith
    have hM : 0 ≤ sub16799MarginOut δ x := by
      rcases le_or_gt x (12 / 25) with hx12 | hx12
      · exact sub16799MarginOut_nonneg_R1 hx12
      · rcases le_or_gt δ (17 / 50) with hδ17 | hδ17
        · exact sub16799MarginOut_nonneg_R2 hδ0 hδ17 hx12.le hx
        · have hδ41 : 41 / 100 ≤ δ := by
            by_contra hlt
            exact hB ⟨hδ17.le, le_of_not_ge hlt, hx12.le, hx⟩
          exact sub16799MarginOut_nonneg_R3 hδ41 hδ hx12.le hx
    have hid : endpointExponent (17 / 48) (2299 / 4800) (801 / 4800) (16799 / 19200)
        δ (x * δ) (rowCount δ x) + 1 / 20000 = -(sub16799MarginOut δ x / rowJ δ x) := by
      unfold endpointExponent rowCount sub16799MarginOut
      field_simp [hJ0.ne']
      ring
    have hq : 0 ≤ sub16799MarginOut δ x / rowJ δ x := div_nonneg hM hJ0.le
    linarith

/-- Positive row-length slope of `rowCountSub16799 δ x` relative to `z₀ = 17/50`. -/
theorem rowCountSub16799_slope_bounds {δ x : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6)
    (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    73 / 300 ≤ rowCountSub16799 δ x + δ / 2 - 17 / 50 ∧
      rowCountSub16799 δ x + δ / 2 - 17 / 50 ≤ 3 := by
  unfold rowCountSub16799
  split_ifs with hB
  · have hJ := rowJ_B_pos hδ0 hδ hx
    have hJ0 : 0 < rowJ_B δ x := by linarith
    have hN := rowN_B_bounds hx0 hx
    have hge : 1 - δ ≤ rowCount_B δ x := by
      unfold rowCount_B
      have hq : 0 ≤ (5 / 6 - δ) * δ * rowN_B x / rowJ_B δ x :=
        div_nonneg (mul_nonneg (mul_nonneg (by linarith) hδ0) (by linarith [hN.1])) hJ0.le
      linarith
    have hle : rowCount_B δ x ≤ 5 / 2 := by
      unfold rowCount_B
      have hprod : (5 / 6 - δ) * δ ≤ 25 / 36 := by nlinarith [sq_nonneg (δ - 5 / 12)]
      have hnum : (5 / 6 - δ) * δ * rowN_B x ≤ 25 / 36 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hδ) hδ0, hN.2]
      have hdiv : (5 / 6 - δ) * δ * rowN_B x / rowJ_B δ x ≤ 3 / 2 :=
        (div_le_iff₀ hJ0).mpr (by linarith)
      linarith
    exact ⟨by linarith, by linarith⟩
  · exact rowCount_slope_bounds hδ0 hδ hx0 hx

/-- Balanced-bin certificate across all row lengths `d ≤ 3901/4800 + ζ` (`3901/4800 = 1 - 17/48 + 801/4800`). -/
theorem rowExponent_balanced_sub16799 {δ x d ζ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6)
    (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (_hζ : 0 ≤ ζ) (hd : d ≤ 3901 / 4800 + ζ) :
    rowExponent (17 / 48) (2299 / 4800) (801 / 4800) (16799 / 19200) (17 / 50)
      δ (x * δ) (rowCountSub16799 δ x) d ≤ -(1 / 20000) + 3 * ζ := by
  have htop := endpoint_certificate_sub16799 hδ0 hδ hx0 hx
  have hsl := rowCountSub16799_slope_bounds hδ0 hδ hx0 hx
  have hrel : rowExponent (17 / 48) (2299 / 4800) (801 / 4800) (16799 / 19200) (17 / 50)
      δ (x * δ) (rowCountSub16799 δ x) d =
      endpointExponent (17 / 48) (2299 / 4800) (801 / 4800) (16799 / 19200)
        δ (x * δ) (rowCountSub16799 δ x) +
      (d - 3901 / 4800) * (rowCountSub16799 δ x + δ / 2 - 17 / 50) := by
    unfold rowExponent endpointExponent
    ring
  rw [hrel]
  rcases le_total d (3901 / 4800) with hd0 | hd0
  · have hnonpos : (d - 3901 / 4800) * (rowCountSub16799 δ x + δ / 2 - 17 / 50) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hsl.1])
    linarith
  · have hbd : (d - 3901 / 4800) * (rowCountSub16799 δ x + δ / 2 - 17 / 50) ≤ 3 * ζ := by
      nlinarith [hsl.1, hsl.2]
    linarith

/-- High-`δ` certificate (`5/6 ≤ δ ≤ 1`, `q ≤ δ/2`, `R = 1 - δ`) at `(17/48, 2299/4800, 801/4800)`. -/
theorem endpoint_high_delta_sub16799 {δ q : ℝ} (hδ0 : 5 / 6 ≤ δ) (_hδ1 : δ ≤ 1)
    (hq : q ≤ δ / 2) :
    endpointExponent (17 / 48) (2299 / 4800) (801 / 4800) (16799 / 19200) δ q (1 - δ) ≤
      -(697 / 9600) := by
  unfold endpointExponent
  linarith

/-- High-`δ` certificate across all row lengths `d ≤ 3901/4800 + ζ` (`ζ ≥ 0`). -/
theorem rowExponent_high_delta_sub16799 {δ q d ζ : ℝ} (hδ0 : 5 / 6 ≤ δ) (hδ1 : δ ≤ 1)
    (hq : q ≤ δ / 2) (_hζ : 0 ≤ ζ) (hd : d ≤ 3901 / 4800 + ζ) :
    rowExponent (17 / 48) (2299 / 4800) (801 / 4800) (16799 / 19200) (17 / 50)
      δ q (1 - δ) d ≤ -(697 / 9600) + ζ := by
  have htop := endpoint_high_delta_sub16799 hδ0 hδ1 hq
  have hrel : rowExponent (17 / 48) (2299 / 4800) (801 / 4800) (16799 / 19200) (17 / 50)
      δ q (1 - δ) d =
      endpointExponent (17 / 48) (2299 / 4800) (801 / 4800) (16799 / 19200) δ q (1 - δ) +
      (d - 3901 / 4800) * (33 / 50 - δ / 2) := by
    unfold rowExponent endpointExponent
    ring
  rw [hrel]
  rcases le_total d (3901 / 4800) with hd0 | hd0
  · have hnonpos : (d - 3901 / 4800) * (33 / 50 - δ / 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  · have hbd : (d - 3901 / 4800) * (33 / 50 - δ / 2) ≤ ζ := by nlinarith
    linarith

/-! ### Stage-1 complete-factor selection certificates on `17/25 ≤ r ≤ 19/26` -/

/-- Stage-1 target marked width `269/500 - 69 r / 125`. -/
def stage1Line (r : ℝ) : ℝ := 269 / 500 - 69 * r / 125

/-- Stage-1 complete-factor selection width `u(r) = (11/3) (stage1Line r - (1 - r)/2)`. -/
def stage1Width (r : ℝ) : ℝ := (11 / 3) * (stage1Line r - (1 - r) / 2)

/-- Stage-1 dual row norm exponent `H₀(r) = 1 - 6 u(r)`. -/
def stage1DualScale (r : ℝ) : ℝ := 1 - 6 * stage1Width r

/-- Stage-1 surviving marked width `z_rem(r) = stage1Line r - u(r)`. -/
def stage1RemWidth (r : ℝ) : ℝ := stage1Line r - stage1Width r

/-- Balanced crossing `r = crossing x (balancedCutoff ν x)` of the existing `(9/2, 2)` counts. -/
def stage1Crossing (ν x : ℝ) : ℝ :=
  ((2 - 8 * x / 9) * (1 + ν * rowP x / (2 * rowJ ν x)) - 5 * x / 9) / rowD x

theorem stage1_basic_identities (r : ℝ) :
    stage1Width (19 / 26) = 0 ∧
      stage1Line (19 / 26) = (1 - 19 / 26) / 2 ∧
      stage1RemWidth r - (stage1DualScale r - r) / 2 = (25 / 11) * stage1Width r := by
  unfold stage1RemWidth stage1DualScale stage1Width stage1Line
  refine ⟨by norm_num, by norm_num, by ring⟩

theorem stage1_bounds_on_interval {r : ℝ} (hr0 : 17 / 25 ≤ r) (hr1 : r ≤ 19 / 26) :
    0 ≤ stage1Width r ∧ stage1Width r ≤ 121 / 12500 ∧
      5887 / 6250 ≤ stage1DualScale r ∧ stage1DualScale r ≤ 1 ∧
      r + stage1Line r + 4 * stage1Width r ≤ 9 / 10 := by
  unfold stage1DualScale stage1Width stage1Line
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Pass-1 shift preservation: for `r_eff = rr - G - P + Aslot + δclip` and `z_rem = z_all - G - Aslot`,
nonnegative `G, Aslot ≥ 0`, `P ≥ -2 η`, `rr ≤ r`, and `δclip ≤ η` preserve
`z_rem ≤ stage1Line r_eff + 2 η`. -/
theorem stage1_window_shift {r rr z_all G P Aslot δclip η : ℝ}
    (hz : z_all ≤ stage1Line r) (hG : 0 ≤ G) (hA : 0 ≤ Aslot) (hP : -2 * η ≤ P)
    (hrr1 : rr ≤ r) (hclip1 : δclip ≤ η) (hη : 0 ≤ η) :
    z_all - G - Aslot ≤ stage1Line (rr - G - P + Aslot + δclip) + 2 * η := by
  unfold stage1Line at hz ⊢
  linarith

/-- Left/right `u = 0` capacity discharge outside `(17/25, 19/26)`:
if either `r_eff ≤ 17/25` (with `r ≥ 69/100`) or `19/26 ≤ r_eff`, then `r_eff + 2 z_rem ≤ 1 + 4 η`
and `2 r_eff + 8 z_rem ≤ 3 - 1 / 10`. -/
theorem stage1_outside_window_capacity {r rr z_all G P Aslot δclip η : ℝ}
    (hr69 : 69 / 100 ≤ r) (hz : z_all ≤ stage1Line r) (_hz0 : 0 ≤ z_all - G - Aslot)
    (hG : 0 ≤ G) (hA : 0 ≤ Aslot) (hP : -2 * η ≤ P)
    (hrr0 : r - η ≤ rr) (hrr1 : rr ≤ r)
    (hclip0 : 0 ≤ δclip) (hclip1 : δclip ≤ η) (hη : 0 ≤ η) (hηs : η ≤ 1 / 2000) :
    let r_eff := rr - G - P + Aslot + δclip
    let z_rem := z_all - G - Aslot
    (r_eff ≤ 17 / 25 ∨ 19 / 26 ≤ r_eff) →
      r_eff + 2 * z_rem ≤ 1 + 4 * η ∧ 2 * r_eff + 8 * z_rem ≤ 3 - 1 / 10 := by
  intro r_eff z_rem hout
  have hshift := stage1_window_shift hz hG hA hP hrr1 hclip1 hη
  unfold stage1Line at hz hshift
  rcases hout with hlo | hhi
  · have hGP : 1 / 100 - η ≤ G + P - Aslot := by dsimp [r_eff] at hlo; linarith
    have h3 : 1 / 100 - η ≤ 3 * G + P + Aslot := by linarith
    have hsum1 : r_eff + 2 * z_rem ≤ (r + 2 * z_all) - (3 * G + P + Aslot) + η := by
      dsimp [r_eff, z_rem]; linarith
    constructor
    · linarith
    · dsimp [r_eff, z_rem] at hlo _hz0 ⊢; linarith
  · constructor
    · linarith
    · linarith

/-- Sixth-power cofactor monotonicity on `[11/25, 3/4]`: since `rowCount ν x ≥ 1 - ν ≥ 1/4 > 1/6`,
replacing `H₀` by `M = H₀ - 6 x₆` (`x₆ ≥ 0`) decreases `M · rowCount ν x + x₆` by at least `x₆ / 2`. -/
theorem stage1_sixth_power_monotonicity {H₀ x₆ ν x : ℝ}
    (hx₆ : 0 ≤ x₆) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 3 / 4) (hx : x ≤ 1 / 2) :
    (H₀ - 6 * x₆) * rowCount ν x + x₆ ≤ H₀ * rowCount ν x - x₆ / 2 := by
  have hJ := rowJ_pos (δ := ν) (x := x) hν0 (by linarith) hx
  have hP0 : 0 ≤ rowP x := by unfold rowP; exact mul_nonneg (by linarith) (by linarith)
  have hrc : 1 / 4 ≤ rowCount ν x := by
    unfold rowCount
    have hq : 0 ≤ (5 / 6 - ν) * ν * rowP x / (2 * rowJ ν x) :=
      div_nonneg (mul_nonneg (mul_nonneg (by linarith) hν0) hP0) (by linarith)
    linarith
  nlinarith

/-- **Stage-1 large-value certificate.** Across all `r ∈ [17/25, 19/26]`, `ν ∈ [11/25, 3/4]`, and
`x ∈ [0, 1/2]`, the dual large-value exponent satisfies
`H₀(r) · rowCount ν x + ν r + 2 x ν z_rem(r) ≤ H₀(r) + u(r) - 1/2000`. -/
theorem stage1_large_value_certificate {r ν x : ℝ}
    (hr0 : 17 / 25 ≤ r) (hr1 : r ≤ 19 / 26)
    (hν0 : 11 / 25 ≤ ν) (hν1 : ν ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    stage1DualScale r * rowCount ν x + ν * r + 2 * x * ν * stage1RemWidth r ≤
      stage1DualScale r + stage1Width r - 1 / 2000 := by
  have hJ := rowJ_pos (δ := ν) (x := x) (by linarith) (by linarith) hx1
  have hJ0 : 0 < 2 * rowJ ν x := by linarith
  set u := (ν - 11 / 25) / (3 / 4 - 11 / 25)
  set v := x / (1 / 2)
  have hu0 : 0 ≤ u := div_nonneg (by linarith) (by norm_num)
  have hu1 : u ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 3 / 4 - 11 / 25)).mpr (by linarith)
  have hv0 : 0 ≤ v := div_nonneg hx0 (by norm_num)
  have hv1 : v ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)).mpr (by linarith)
  let F : ℝ → ℝ := fun rc =>
    (stage1DualScale rc + stage1Width rc - 1 / 2000 -
      (stage1DualScale rc * rowCount ν x + ν * rc + 2 * x * ν * stage1RemWidth rc)) * (2 * rowJ ν x)
  have hF_lo : 0 ≤ F (17 / 25) := by
    have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
      (c00 := 699751 / 3750000) (c01 := 150401359 / 1687500000)
      (c02 := 20802239 / 632812500) (c03 := 7891993 / 1687500000)
      (c10 := 4933757 / 15000000) (c11 := 45595849 / 270000000)
      (c12 := 15279023 / 202500000) (c13 := 1415791 / 54000000)
      (c20 := 60193 / 100000) (c21 := 606857 / 1800000)
      (c22 := 121307 / 675000) (c23 := 164527 / 1800000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hid : F (17 / 25) = bernstein23 u v
        (699751 / 3750000) (150401359 / 1687500000)
        (20802239 / 632812500) (7891993 / 1687500000)
        (4933757 / 15000000) (45595849 / 270000000)
        (15279023 / 202500000) (1415791 / 54000000)
        (60193 / 100000) (606857 / 1800000)
        (121307 / 675000) (164527 / 1800000) := by
      dsimp [F, u, v]
      unfold stage1RemWidth stage1DualScale stage1Width stage1Line rowCount
      field_simp [(show rowJ ν x ≠ 0 by linarith)]
      unfold bernstein23 rowJ rowD rowP
      ring
    linarith
  have hF_hi : 0 ≤ F (19 / 26) := by
    have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
      (c00 := 272743 / 1950000) (c01 := 6597949 / 105300000)
      (c02 := 528701 / 26325000) (c03 := 1513 / 2700000)
      (c10 := 2259641 / 7800000) (c11 := 64173883 / 421200000)
      (c12 := 15308419 / 210600000) (c13 := 4344493 / 140400000)
      (c20 := 30159 / 52000) (c21 := 2832521 / 8424000)
      (c22 := 1587691 / 8424000) (c23 := 36157 / 351000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hid : F (19 / 26) = bernstein23 u v
        (272743 / 1950000) (6597949 / 105300000)
        (528701 / 26325000) (1513 / 2700000)
        (2259641 / 7800000) (64173883 / 421200000)
        (15308419 / 210600000) (4344493 / 140400000)
        (30159 / 52000) (2832521 / 8424000)
        (1587691 / 8424000) (36157 / 351000) := by
      dsimp [F, u, v]
      unfold stage1RemWidth stage1DualScale stage1Width stage1Line rowCount
      field_simp [(show rowJ ν x ≠ 0 by linarith)]
      unfold bernstein23 rowJ rowD rowP
      ring
    linarith
  -- `F` is affine linear in `rc`, so convex combination on `[17/25, 19/26]` gives `F r ≥ 0`.
  set θ := (r - 17 / 25) / (19 / 26 - 17 / 25)
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by norm_num)
  have hθ1 : 0 ≤ 1 - θ := by
    have : θ ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 19 / 26 - 17 / 25)).mpr (by linarith)
    linarith
  have haff : F r = (1 - θ) * F (17 / 25) + θ * F (19 / 26) := by
    dsimp [F, θ]
    unfold stage1RemWidth stage1DualScale stage1Width stage1Line
    ring
  have hFr : 0 ≤ F r := by rw [haff]; exact add_nonneg (mul_nonneg hθ1 hF_lo) (mul_nonneg hθ0 hF_hi)
  dsimp [F] at hFr
  nlinarith

/-- **Stage-1 slot-supply certificate.** Across all `r ∈ [17/25, 19/26]`, `ν ∈ [11/25, 3/4]`, and
`x ∈ [0, 1/2]`, `stage1RemWidth r` exceeds both the inverse witness width
`H₀(r) (1 - stage1Crossing ν x) / 2` and the plain witness width
`H₀(r) (1 - 2 (t_bal - stage1Crossing ν x)) · (2/9)` by at least `1/1000`. -/
theorem stage1_slot_supply_certificate {r ν x : ℝ}
    (hr0 : 17 / 25 ≤ r) (hr1 : r ≤ 19 / 26)
    (hν0 : 11 / 25 ≤ ν) (hν1 : ν ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    stage1DualScale r * (1 - stage1Crossing ν x) / 2 + 1 / 1000 ≤ stage1RemWidth r ∧
      stage1DualScale r *
          (1 - 2 * ((1 + ν * rowP x / (2 * rowJ ν x)) - stage1Crossing ν x)) * (2 / 9) +
          1 / 1000 ≤
        stage1RemWidth r := by
  have hD : 7 / 9 ≤ rowD x := by unfold rowD; linarith
  have hD0 : 0 < rowD x := by linarith
  have hJ := rowJ_pos (δ := ν) (x := x) (by linarith) (by linarith) hx1
  have hJ0 : 0 < rowJ ν x := by linarith
  have hDJ : 0 < 2 * rowD x * rowJ ν x := by positivity
  set u := (ν - 11 / 25) / (3 / 4 - 11 / 25)
  set v := x / (1 / 2)
  have hu0 : 0 ≤ u := div_nonneg (by linarith) (by norm_num)
  have hu1 : u ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 3 / 4 - 11 / 25)).mpr (by linarith)
  have hv0 : 0 ≤ v := div_nonneg hx0 (by norm_num)
  have hv1 : v ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)).mpr (by linarith)
  set θ := (r - 17 / 25) / (19 / 26 - 17 / 25)
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by norm_num)
  have hθ1 : 0 ≤ 1 - θ := by
    have : θ ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 19 / 26 - 17 / 25)).mpr (by linarith)
    linarith
  constructor
  · let G : ℝ → ℝ := fun rc =>
      (stage1RemWidth rc - 1 / 1000 - stage1DualScale rc * (1 - stage1Crossing ν x) / 2) *
        (2 * rowD x * rowJ ν x)
    have hG_lo : 0 ≤ G (17 / 25) := by
      have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
        (c00 := 19169 / 25000) (c01 := 23417587 / 50625000)
        (c02 := 157056199 / 607500000) (c03 := 25630751 / 202500000)
        (c10 := 106343 / 100000) (c11 := 136102249 / 202500000)
        (c12 := 993958673 / 2430000000) (c13 := 191368477 / 810000000)
        (c20 := 13601 / 10000) (c21 := 3570683 / 4050000)
        (c22 := 3021539 / 5400000) (c23 := 1868093 / 5400000)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have hid : G (17 / 25) = bernstein23 u v
          (19169 / 25000) (23417587 / 50625000)
          (157056199 / 607500000) (25630751 / 202500000)
          (106343 / 100000) (136102249 / 202500000)
          (993958673 / 2430000000) (191368477 / 810000000)
          (13601 / 10000) (3570683 / 4050000)
          (3021539 / 5400000) (1868093 / 5400000) := by
        dsimp [G, u, v]
        unfold stage1RemWidth stage1DualScale stage1Width stage1Line stage1Crossing
        field_simp [hD0.ne', hJ0.ne']
        unfold bernstein23 rowJ rowD rowP
        ring
      linarith
    have hG_hi : 0 ≤ G (19 / 26) := by
      have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
        (c00 := 153233 / 325000) (c01 := 3163019 / 13162500)
        (c02 := 87621331 / 947700000) (c03 := 79291 / 24300000)
        (c10 := 1055891 / 1300000) (c11 := 12902719 / 26325000)
        (c12 := 1053615637 / 3790800000) (c13 := 179782741 / 1263600000)
        (c20 := 29977 / 26000) (c21 := 97397 / 131625)
        (c22 := 35134919 / 75816000) (c23 := 7108847 / 25272000)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have hid : G (19 / 26) = bernstein23 u v
          (153233 / 325000) (3163019 / 13162500)
          (87621331 / 947700000) (79291 / 24300000)
          (1055891 / 1300000) (12902719 / 26325000)
          (1053615637 / 3790800000) (179782741 / 1263600000)
          (29977 / 26000) (97397 / 131625)
          (35134919 / 75816000) (7108847 / 25272000) := by
        dsimp [G, u, v]
        unfold stage1RemWidth stage1DualScale stage1Width stage1Line stage1Crossing
        field_simp [hD0.ne', hJ0.ne']
        unfold bernstein23 rowJ rowD rowP
        ring
      linarith
    have haff : G r = (1 - θ) * G (17 / 25) + θ * G (19 / 26) := by
      dsimp [G, θ]; unfold stage1RemWidth stage1DualScale stage1Width stage1Line; ring
    have hGr : 0 ≤ G r := by rw [haff]; exact add_nonneg (mul_nonneg hθ1 hG_lo) (mul_nonneg hθ0 hG_hi)
    dsimp [G] at hGr
    nlinarith
  · let P : ℝ → ℝ := fun rc =>
      (stage1RemWidth rc - 1 / 1000 -
        stage1DualScale rc *
          (1 - 2 * ((1 + ν * rowP x / (2 * rowJ ν x)) - stage1Crossing ν x)) * (2 / 9)) *
        (2 * rowD x * rowJ ν x)
    have hP_lo : 0 ≤ P (17 / 25) := by
      have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
        (c00 := 1557271 / 1125000) (c01 := 115643677 / 113906250)
        (c02 := 1360341077 / 1822500000) (c03 := 333918673 / 607500000)
        (c10 := 6469117 / 4500000) (c11 := 917627483 / 911250000)
        (c12 := 5136988979 / 7290000000) (c13 := 1197067771 / 2430000000)
        (c20 := 134183 / 90000) (c21 := 18202111 / 18225000)
        (c22 := 96652273 / 145800000) (c23 := 21169217 / 48600000)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have hid : P (17 / 25) = bernstein23 u v
          (1557271 / 1125000) (115643677 / 113906250)
          (1360341077 / 1822500000) (333918673 / 607500000)
          (6469117 / 4500000) (917627483 / 911250000)
          (5136988979 / 7290000000) (1197067771 / 2430000000)
          (134183 / 90000) (18202111 / 18225000)
          (96652273 / 145800000) (21169217 / 48600000) := by
        dsimp [P, u, v]
        unfold stage1RemWidth stage1DualScale stage1Width stage1Line stage1Crossing
        field_simp [hD0.ne', hJ0.ne']
        unfold bernstein23 rowJ rowD rowP
        ring
      linarith
    have hP_hi : 0 ≤ P (19 / 26) := by
      have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
        (c00 := 3296597 / 2925000) (c01 := 48988273 / 59231250)
        (c02 := 192833777 / 315900000) (c03 := 10994291 / 24300000)
        (c10 := 14150519 / 11700000) (c11 := 400720817 / 473850000)
        (c12 := 747791879 / 1263600000) (c13 := 523697741 / 1263600000)
        (c20 := 302293 / 234000) (c21 := 8190709 / 9477000)
        (c22 := 14484973 / 25272000) (c23 := 9513847 / 25272000)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have hid : P (19 / 26) = bernstein23 u v
          (3296597 / 2925000) (48988273 / 59231250)
          (192833777 / 315900000) (10994291 / 24300000)
          (14150519 / 11700000) (400720817 / 473850000)
          (747791879 / 1263600000) (523697741 / 1263600000)
          (302293 / 234000) (8190709 / 9477000)
          (14484973 / 25272000) (9513847 / 25272000) := by
        dsimp [P, u, v]
        unfold stage1RemWidth stage1DualScale stage1Width stage1Line stage1Crossing
        field_simp [hD0.ne', hJ0.ne']
        unfold bernstein23 rowJ rowD rowP
        ring
      linarith
    have haff : P r = (1 - θ) * P (17 / 25) + θ * P (19 / 26) := by
      dsimp [P, θ]; unfold stage1RemWidth stage1DualScale stage1Width stage1Line; ring
    have hPr : 0 ≤ P r := by rw [haff]; exact add_nonneg (mul_nonneg hθ1 hP_lo) (mul_nonneg hθ0 hP_hi)
    dsimp [P] at hPr
    nlinarith

/-! ### Greedy subset-sum lemma up to `mesh` -/

/-- Any finite set of nonnegative weights bounded by `mesh ≥ 0` whose sum is at least `target ≥ 0`
admits a subset whose sum lies in `[target, target + mesh]`. -/
theorem exists_subset_sum_interval {α : Type*} [DecidableEq α]
    (S : Finset α) (w : α → ℝ) {mesh target : ℝ}
    (hm : 0 ≤ mesh) (hw0 : ∀ i ∈ S, 0 ≤ w i) (hwm : ∀ i ∈ S, w i ≤ mesh)
    (ht0 : 0 ≤ target) (hts : target ≤ ∑ i ∈ S, w i) :
    ∃ U ⊆ S, target ≤ ∑ i ∈ U, w i ∧ ∑ i ∈ U, w i ≤ target + mesh := by
  induction S using Finset.induction_on with
  | empty =>
    have ht_eq : target = 0 := le_antisymm (by simpa using hts) ht0
    exact ⟨∅, Finset.Subset.refl _, by simp [ht_eq], by simp [ht_eq, hm]⟩
  | @insert a s ha ih =>
    have hw0_s : ∀ i ∈ s, 0 ≤ w i := fun i hi => hw0 i (Finset.mem_insert_of_mem hi)
    have hwm_s : ∀ i ∈ s, w i ≤ mesh := fun i hi => hwm i (Finset.mem_insert_of_mem hi)
    have hwa0 : 0 ≤ w a := hw0 a (Finset.mem_insert_self a s)
    have hwam : w a ≤ mesh := hwm a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha] at hts
    rcases le_or_gt target (∑ i ∈ s, w i) with hle | hgt
    · obtain ⟨U, hUs, hUlo, hUhi⟩ := ih hw0_s hwm_s hle
      exact ⟨U, hUs.trans (Finset.subset_insert a s), hUlo, hUhi⟩
    · exact ⟨insert a s, Finset.Subset.refl _, by rw [Finset.sum_insert ha]; exact hts,
        by rw [Finset.sum_insert ha]; linarith⟩

end

end GaloisForLFunctions.FamilyContinuationTheory.Budget
