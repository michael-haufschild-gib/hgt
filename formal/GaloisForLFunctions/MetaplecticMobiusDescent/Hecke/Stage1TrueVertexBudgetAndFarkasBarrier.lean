import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.SubFarkasBudgetCertificates

/-!
# Stage-1 True-Vertex Certificates Below `139989 / 160000` and Unconstrained `ℝ³` Farkas Barrier

Under the Stage-1 complete-factor inverse-marked line `269/500 - (69/125) r` (`rowCountSub16799`),
the full-amplitude `lx`-slope `∂(endpointExponent)/∂lx = 2/3 - R(δ, 1/2)` changes sign at
`δ_* ≈ 0.38838578` rather than the Stage-0 root between `5/13` and `16/41`. Freezing `lx = 17/48`
therefore leaves most of the Stage-1 saddle-point gain unused. Moving along the edge `lx + ly + ℓ = 1`
toward the Stage-1 saddle point while preserving positive Gram slack yields both a sharper
unconditional Gram-admissible certificate and the matching unconstrained `ℝ³` Farkas dual barrier:

* **Positive Gram-admissible Stage-1 vertex (`endpoint_certificate_stage1_vertex`).**
  At `(lx, ly, ℓ) = (2111/6000, 19249/40000, 20033/120000)` (`M = 99967/120000 > 4/5`,
  `1 + 3ℓ = 60033/40000 ≤ 99967/60000 = 2M`, Gram gap `2 lx - ly - ℓ = 111/2000 > 0`), we have
  `lowBoundary = lowBoundaryGen = 139989/160000 < 3281/3750 < 16799/19200 < 40535/46328 < 20999/24000`
  and `1 - 139989/160000 = 20011/160000 > 469/3750 > 2401/19200 > 3001/24000`. Exact rational
  sum-of-squares identities in `y = 1/2 - x` (inside `B = [17/50, 41/100] × [12/25, 1/2]`) and
  `z = 12/25 - x` (on `[0, 5/6] × [0, 12/25]`), together with degree-`(2, 3)` Bernstein certificates
  on `[0, 17/50] × [12/25, 1/2]` and `[41/100, 5/6] × [12/25, 1/2]`, certify
  `endpointExponent ≤ -1/100000` across all `[0, 5/6] × [0, 1/2]`. High bins `5/6 ≤ δ ≤ 1` satisfy
  `endpointExponent ≤ -7/100`.
* **Sharp unconstrained `ℝ³` Stage-1 Farkas barrier
  (`stage1_endpointExponent_three_bin_pos_of_lowBoundaryGen_le`).**
  Over **all** `(lx, ly, ℓ) ∈ ℝ³` with no sign, simplex, or Gram hypothesis, a strictly positive
  convex combination of the linear part of `lowBoundary` and the two full-amplitude Stage-1 bins
  `δ₁ = 40/103` (`rowCountSub16799 = 6661/9991`) and `δ₂ = 87/224`
  (`rowCountSub16799 = 5355041/8032640`) cancels `lx`, `ly`, and `ℓ` identically at
  `14925581/17059187` (`1 - 14925581/17059187 = 2133606/17059187`). Any `(lx, ly, ℓ) ∈ ℝ³` with
  `lowBoundaryGen lx ly ℓ ≤ 14925581/17059187` forces at least one of the three Stage-1 bins
  `40/103`, `127/327`, or `87/224` to have strictly positive `endpointExponent`
  (`736/9734227990005 > 0` at the unique two-bin vertex). Thus the true unconstrained `ℝ³` Stage-1
  vertex is confined to `(14925581/17059187, 139989/160000]`, a window of width `< 2.05 × 10⁻⁶`.
-/

namespace GaloisForLFunctions.FamilyContinuationTheory.Budget

open scoped BigOperators Classical

noncomputable section

/-! ### Part 1: The Gram-admissible Stage-1 vertex `(2111/6000, 19249/40000, 20033/120000)` -/

theorem lowBoundary_stage1_vertex :
    lowBoundary (2111 / 6000) (19249 / 40000) (20033 / 120000) = 139989 / 160000 := by
  unfold lowBoundary
  rw [show (2111 : ℝ) / 6000 + 19249 / 40000 + 20033 / 120000 - 1 = 0 by ring, max_self]
  norm_num

theorem lowBoundaryGen_stage1_vertex :
    lowBoundaryGen (2111 / 6000) (19249 / 40000) (20033 / 120000) = 139989 / 160000 := by
  rw [lowBoundaryGen_eq_of_le (20033 / 120000) (by norm_num), lowBoundary_stage1_vertex]

theorem stage1_vertex_lt_benchmarks :
    (139989 / 160000 : ℝ) < 3281 / 3750 ∧
    (3281 / 3750 : ℝ) < 16799 / 19200 ∧
    (16799 / 19200 : ℝ) < 40535 / 46328 ∧
    (40535 / 46328 : ℝ) < 20999 / 24000 := by
  norm_num

theorem one_sub_stage1_vertex_gt_benchmarks :
    (3001 / 24000 : ℝ) < 2401 / 19200 ∧
    (2401 / 19200 : ℝ) < 469 / 3750 ∧
    (469 / 3750 : ℝ) < 20011 / 160000 ∧
    1 - (139989 / 160000 : ℝ) = 20011 / 160000 := by
  norm_num

/-- On `(M, ℓ) = (99967/120000, 20033/120000)` we have `1 + 3ℓ = 60033/40000 ≤ 99967/60000 = 2M`,
so the reflected allowance of unselected prime slots is nonpositive. -/
theorem tupleExponent_reflectedAllowance_stage1_vertex {d : ℝ} (hd : 0 ≤ d) :
    tupleExponent d (reflectedAllowance (99967 / 120000) (20033 / 120000) d) ≤ 0 :=
  tupleExponent_reflectedAllowance_nonpos hd (by norm_num)

/-! ### Part 2: Exact SOS and Bernstein certificates at `139989 / 160000` -/

/-- Cleared-denominator margin `-(endpointExponent + 1/100000) * rowJ_B` inside `B`. -/
def stage1VertexMarginB (δ x : ℝ) : ℝ :=
  rowJ_B δ x * (-(1 + δ) * (1 - 19249 / 40000) / 2 + 139989 / 160000 + (20033 / 120000) / 2
      - (x * δ) * (20033 / 120000) -
      (1 - 2111 / 6000 + 20033 / 120000) * (1 - δ / 2 - 1 / 6) - 1 / 100000)
    - (1 - 2111 / 6000 + 20033 / 120000) * ((5 / 6 - δ) * δ * rowN_B x)

/-- Cleared-denominator margin `-(endpointExponent + 1/100000) * rowJ` outside `B`. -/
def stage1VertexMarginOut (δ x : ℝ) : ℝ :=
  rowJ δ x * (-(1 + δ) * (1 - 19249 / 40000) / 2 + 139989 / 160000 + (20033 / 120000) / 2
      - (x * δ) * (20033 / 120000) -
      (1 - 2111 / 6000 + 20033 / 120000) * (1 - δ / 2 - 1 / 6) - 1 / 100000)
    - (1 - 2111 / 6000 + 20033 / 120000) * ((5 / 6 - δ) * δ * rowP x / 2)

private def s1_a2_B (y : ℝ) : ℝ :=
  58653539 / 270000000 + 2349913 / 3750000 * y + 6258947 / 13500000 * y ^ 2 +
    460759 / 2812500 * y ^ 3

private def s1_a1_B (y : ℝ) : ℝ :=
  10155691 / 120000000 + 46316149 / 300000000 * y + 1481771 / 150000000 * y ^ 2

private def s1_rem_B (y : ℝ) : ℝ :=
  1612286729543 / 10497600000000000000 +
    21701099686958419 / 13122000000000000000 * y +
    677757243292515181 / 65610000000000000000 * y ^ 2 +
    287966263613016259 / 16402500000000000000 * y ^ 3 +
    28842082441579637 / 5467500000000000000 * y ^ 4

private def s1_a2_R1 (z : ℝ) : ℝ :=
  1387551611 / 5625000000 + 105754537 / 168750000 * z + 12075221 / 27000000 * z ^ 2 +
    20033 / 135000 * z ^ 3

private def s1_a1_R1 (z : ℝ) : ℝ :=
  829623901 / 9000000000 + 156667087 / 1080000000 * z + 698543 / 64800000 * z ^ 2

private def s1_rem_R1 (z : ℝ) : ℝ :=
  305918199807991 / 729000000000000000000 +
    109905819916583417 / 43740000000000000000 * z +
    124463317621281331 / 10497600000000000000 * z ^ 2 +
    1667670908611427 / 104976000000000000 * z ^ 3 +
    6293610514117 / 1399680000000000 * z ^ 4

theorem stage1VertexMarginB_nonneg {δ x : ℝ} (hx : x ≤ 1 / 2) :
    0 ≤ stage1VertexMarginB δ x := by
  set y := 1 / 2 - x
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have ha2 : 0 < s1_a2_B y := by unfold s1_a2_B; positivity
  have hrem : 0 ≤ s1_rem_B y := by unfold s1_rem_B; positivity
  have hsq : 0 ≤ (s1_a2_B y * δ - s1_a1_B y) ^ 2 := sq_nonneg _
  have hsos : s1_a2_B y * stage1VertexMarginB δ x =
      (s1_a2_B y * δ - s1_a1_B y) ^ 2 + s1_rem_B y := by
    dsimp [y]
    unfold stage1VertexMarginB rowJ_B rowD_B rowP_B rowN_B s1_a2_B s1_a1_B s1_rem_B
    ring
  nlinarith

theorem stage1VertexMarginOut_nonneg_R1 {δ x : ℝ} (hx : x ≤ 12 / 25) :
    0 ≤ stage1VertexMarginOut δ x := by
  set z := 12 / 25 - x
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have ha2 : 0 < s1_a2_R1 z := by unfold s1_a2_R1; positivity
  have hrem : 0 ≤ s1_rem_R1 z := by unfold s1_rem_R1; positivity
  have hsq : 0 ≤ (s1_a2_R1 z * δ - s1_a1_R1 z) ^ 2 := sq_nonneg _
  have hsos : s1_a2_R1 z * stage1VertexMarginOut δ x =
      (s1_a2_R1 z * δ - s1_a1_R1 z) ^ 2 + s1_rem_R1 z := by
    dsimp [z]
    unfold stage1VertexMarginOut rowJ rowD rowP s1_a2_R1 s1_a1_R1 s1_rem_R1
    ring
  nlinarith

theorem stage1VertexMarginOut_nonneg_R2 {δ x : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 17 / 50)
    (hx0 : 12 / 25 ≤ x) (hx1 : x ≤ 1 / 2) :
    0 ≤ stage1VertexMarginOut δ x := by
  set u := δ / (17 / 50)
  set v := (x - 12 / 25) / (1 / 2 - 12 / 25)
  have hu0 : 0 ≤ u := div_nonneg hδ0 (by norm_num)
  have hu1 : u ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 17 / 50)).mpr (by linarith)
  have hv0 : 0 ≤ v := div_nonneg (by linarith) (by norm_num)
  have hv1 : v ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 2 - 12 / 25)).mpr (by linarith)
  have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
    (c00 := 22322731 / 648000000) (c01 := 399392047 / 11664000000)
    (c02 := 49621867 / 1458000000) (c03 := 5260771 / 155520000)
    (c10 := 12584611897 / 4050000000000) (c11 := 235386134707 / 72900000000000)
    (c12 := 9768545183 / 2916000000000) (c13 := 67468133 / 19440000000)
    (c20 := 4456448167 / 15820312500000) (c21 := 11349907207 / 45562500000000)
    (c22 := 405391523 / 1822500000000) (c23 := 4897579 / 24300000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hid : stage1VertexMarginOut δ x = bernstein23 u v
      (22322731 / 648000000) (399392047 / 11664000000)
      (49621867 / 1458000000) (5260771 / 155520000)
      (12584611897 / 4050000000000) (235386134707 / 72900000000000)
      (9768545183 / 2916000000000) (67468133 / 19440000000)
      (4456448167 / 15820312500000) (11349907207 / 45562500000000)
      (405391523 / 1822500000000) (4897579 / 24300000000) := by
    dsimp [u, v]
    unfold bernstein23 stage1VertexMarginOut rowJ rowD rowP
    ring
  linarith

theorem stage1VertexMarginOut_nonneg_R3 {δ x : ℝ} (hδ0 : 41 / 100 ≤ δ) (hδ1 : δ ≤ 5 / 6)
    (hx0 : 12 / 25 ≤ x) (hx1 : x ≤ 1 / 2) :
    0 ≤ stage1VertexMarginOut δ x := by
  set u := (δ - 41 / 100) / (5 / 6 - 41 / 100)
  set v := (x - 12 / 25) / (1 / 2 - 12 / 25)
  have hu0 : 0 ≤ u := div_nonneg (by linarith) (by norm_num)
  have hu1 : u ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 5 / 6 - 41 / 100)).mpr (by linarith)
  have hv0 : 0 ≤ v := div_nonneg (by linarith) (by norm_num)
  have hv1 : v ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 2 - 12 / 25)).mpr (by linarith)
  have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
    (c00 := 2585929421 / 7910156250000) (c01 := 76682022041 / 364500000000000)
    (c02 := 2994282623 / 29160000000000) (c03 := 1414849 / 388800000000)
    (c10 := 33360384893 / 8100000000000) (c11 := 537458582111 / 145800000000000)
    (c12 := 19085607359 / 5832000000000) (c13 := 37286453 / 12960000000)
    (c20 := 422149897 / 8100000000) (c21 := 7380466741 / 145800000000)
    (c22 := 286716947 / 5832000000) (c23 := 618751 / 12960000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hid : stage1VertexMarginOut δ x = bernstein23 u v
      (2585929421 / 7910156250000) (76682022041 / 364500000000000)
      (2994282623 / 29160000000000) (1414849 / 388800000000)
      (33360384893 / 8100000000000) (537458582111 / 145800000000000)
      (19085607359 / 5832000000000) (37286453 / 12960000000)
      (422149897 / 8100000000) (7380466741 / 145800000000)
      (286716947 / 5832000000) (618751 / 12960000) := by
    dsimp [u, v]
    unfold bernstein23 stage1VertexMarginOut rowJ rowD rowP
    ring
  linarith

/-- **Stage-1 true-vertex balanced endpoint certificate.** Across all `0 ≤ δ ≤ 5/6` and
`0 ≤ x ≤ 1/2`, `endpointExponent` at `(2111/6000, 19249/40000, 20033/120000)` and
`σ₀ = 139989/160000` with `rowCountSub16799 δ x` is at most `-1/100000`. -/
theorem endpoint_certificate_stage1_vertex {δ x : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6)
    (_hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    endpointExponent (2111 / 6000) (19249 / 40000) (20033 / 120000) (139989 / 160000)
      δ (x * δ) (rowCountSub16799 δ x) ≤ -(1 / 100000) := by
  unfold rowCountSub16799
  split_ifs with hB
  · have hJ := rowJ_B_pos hδ0 hδ hx
    have hJ0 : 0 < rowJ_B δ x := by linarith
    have hM := stage1VertexMarginB_nonneg (δ := δ) hx
    have hid : endpointExponent (2111 / 6000) (19249 / 40000) (20033 / 120000) (139989 / 160000)
        δ (x * δ) (rowCount_B δ x) + 1 / 100000 = -(stage1VertexMarginB δ x / rowJ_B δ x) := by
      unfold endpointExponent rowCount_B stage1VertexMarginB
      field_simp [hJ0.ne']
      ring
    have hq : 0 ≤ stage1VertexMarginB δ x / rowJ_B δ x := div_nonneg hM hJ0.le
    linarith
  · have hJ := rowJ_pos hδ0 hδ hx
    have hJ0 : 0 < rowJ δ x := by linarith
    have hM : 0 ≤ stage1VertexMarginOut δ x := by
      rcases le_or_gt x (12 / 25) with hx12 | hx12
      · exact stage1VertexMarginOut_nonneg_R1 hx12
      · rcases le_or_gt δ (17 / 50) with hδ17 | hδ17
        · exact stage1VertexMarginOut_nonneg_R2 hδ0 hδ17 hx12.le hx
        · have hδ41 : 41 / 100 ≤ δ := by
            by_contra hlt
            exact hB ⟨hδ17.le, le_of_not_ge hlt, hx12.le, hx⟩
          exact stage1VertexMarginOut_nonneg_R3 hδ41 hδ hx12.le hx
    have hid : endpointExponent (2111 / 6000) (19249 / 40000) (20033 / 120000) (139989 / 160000)
        δ (x * δ) (rowCount δ x) + 1 / 100000 = -(stage1VertexMarginOut δ x / rowJ δ x) := by
      unfold endpointExponent rowCount stage1VertexMarginOut
      field_simp [hJ0.ne']
      ring
    have hq : 0 ≤ stage1VertexMarginOut δ x / rowJ δ x := div_nonneg hM hJ0.le
    linarith

/-- Balanced-bin certificate across all row lengths `d ≤ 97813/120000 + ζ`
(`97813/120000 = 1 - 2111/6000 + 20033/120000`). -/
theorem rowExponent_balanced_stage1_vertex {δ x d ζ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 5 / 6)
    (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (_hζ : 0 ≤ ζ) (hd : d ≤ 97813 / 120000 + ζ) :
    rowExponent (2111 / 6000) (19249 / 40000) (20033 / 120000) (139989 / 160000) (17 / 50)
      δ (x * δ) (rowCountSub16799 δ x) d ≤ -(1 / 100000) + 3 * ζ := by
  have htop := endpoint_certificate_stage1_vertex hδ0 hδ hx0 hx
  have hsl := rowCountSub16799_slope_bounds hδ0 hδ hx0 hx
  have hrel : rowExponent (2111 / 6000) (19249 / 40000) (20033 / 120000) (139989 / 160000) (17 / 50)
      δ (x * δ) (rowCountSub16799 δ x) d =
      endpointExponent (2111 / 6000) (19249 / 40000) (20033 / 120000) (139989 / 160000)
        δ (x * δ) (rowCountSub16799 δ x) +
      (d - 97813 / 120000) * (rowCountSub16799 δ x + δ / 2 - 17 / 50) := by
    unfold rowExponent endpointExponent
    ring
  rw [hrel]
  rcases le_total d (97813 / 120000) with hd0 | hd0
  · have hnonpos : (d - 97813 / 120000) * (rowCountSub16799 δ x + δ / 2 - 17 / 50) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hsl.1])
    linarith
  · have hbd : (d - 97813 / 120000) * (rowCountSub16799 δ x + δ / 2 - 17 / 50) ≤ 3 * ζ := by
      nlinarith [hsl.1, hsl.2]
    linarith

/-- High-`δ` certificate (`5/6 ≤ δ ≤ 1`, `q ≤ δ/2`, `R = 1 - δ`) at `(2111/6000, 19249/40000, 20033/120000)`. -/
theorem endpoint_high_delta_stage1_vertex {δ q : ℝ} (hδ0 : 5 / 6 ≤ δ) (_hδ1 : δ ≤ 1)
    (hq : q ≤ δ / 2) :
    endpointExponent (2111 / 6000) (19249 / 40000) (20033 / 120000) (139989 / 160000)
      δ q (1 - δ) ≤ -(7 / 100) := by
  unfold endpointExponent
  linarith

/-- High-`δ` row certificate across all `d ≤ 97813/120000 + ζ`. -/
theorem rowExponent_high_delta_stage1_vertex {δ q d ζ : ℝ} (hδ0 : 5 / 6 ≤ δ) (hδ1 : δ ≤ 1)
    (hq : q ≤ δ / 2) (_hζ : 0 ≤ ζ) (hd : d ≤ 97813 / 120000 + ζ) :
    rowExponent (2111 / 6000) (19249 / 40000) (20033 / 120000) (139989 / 160000) (17 / 50)
      δ q (1 - δ) d ≤ -(7 / 100) + ζ := by
  have htop := endpoint_high_delta_stage1_vertex hδ0 hδ1 hq
  have hrel : rowExponent (2111 / 6000) (19249 / 40000) (20033 / 120000) (139989 / 160000) (17 / 50)
      δ q (1 - δ) d =
      endpointExponent (2111 / 6000) (19249 / 40000) (20033 / 120000) (139989 / 160000)
        δ q (1 - δ) +
      (d - 97813 / 120000) * (33 / 50 - δ / 2) := by
    unfold rowExponent endpointExponent
    ring
  rw [hrel]
  rcases le_total d (97813 / 120000) with hd0 | hd0
  · have hnonpos : (d - 97813 / 120000) * (33 / 50 - δ / 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  · have hbd : (d - 97813 / 120000) * (33 / 50 - δ / 2) ≤ ζ := by nlinarith
    linarith

/-! ### Part 3: Sharp Unconstrained `ℝ³` Stage-1 Farkas Dual Barrier at `14925581 / 17059187` -/

theorem rowCountSub16799_forty_103 :
    rowCountSub16799 (40 / 103) (1 / 2) = 6661 / 9991 := by
  have hB : inBoxB (40 / 103) (1 / 2) := by unfold inBoxB; norm_num
  rw [rowCountSub16799, if_pos hB]
  norm_num [rowCount_B, rowJ_B, rowD_B, rowP_B, rowN_B]

theorem rowCountSub16799_eightyseven_224 :
    rowCountSub16799 (87 / 224) (1 / 2) = 5355041 / 8032640 := by
  have hB : inBoxB (87 / 224) (1 / 2) := by unfold inBoxB; norm_num
  rw [rowCountSub16799, if_pos hB]
  norm_num [rowCount_B, rowJ_B, rowD_B, rowP_B, rowN_B]

theorem rowCountSub16799_binding_127_327 :
    rowCountSub16799 (127 / 327) (1 / 2) = 7608269 / 11412300 := by
  have hB : inBoxB (127 / 327) (1 / 2) := by unfold inBoxB; norm_num
  rw [rowCountSub16799, if_pos hB]
  norm_num [rowCount_B, rowJ_B, rowD_B, rowP_B, rowN_B]

/-- Exact unconstrained `ℝ³` Stage-1 Farkas identity cancelling `lx`, `ly`, and `ℓ` between the
linear part of `lowBoundary` and the two Stage-1 full-amplitude bins `δ₁ = 40/103` and
`δ₂ = 87/224` (`rowCountSub16799`). -/
theorem stage1_farkas_two_bin_identity (lx ly ℓ σ₀ : ℝ) :
    (13858778 / 17059187 : ℝ) * (5 / 6 + (lx + ly) / 12 - ℓ / 6) +
      (1066803 / 17059187 : ℝ) * (lx + ly + ℓ - 1) +
      (1568587 / 51177561 : ℝ) *
        (endpointExponent lx ly ℓ σ₀ (40 / 103) (20 / 103)
          (rowCountSub16799 (40 / 103) (1 / 2)) + σ₀) +
      (8032640 / 51177561 : ℝ) *
        (endpointExponent lx ly ℓ σ₀ (87 / 224) (87 / 448)
          (rowCountSub16799 (87 / 224) (1 / 2)) + σ₀) =
      14925581 / 17059187 := by
  rw [rowCountSub16799_forty_103, rowCountSub16799_eightyseven_224]
  unfold endpointExponent
  ring

/-- Nonnegative decomposition of the Stage-1 Farkas slack at `σ₀ = lowBoundaryGen lx ly ℓ`. -/
theorem stage1_farkas_two_bin_slack_gen (lx ly ℓ : ℝ) :
    (1568587 / 51177561 : ℝ) *
        endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ)
          (40 / 103) (20 / 103) (rowCountSub16799 (40 / 103) (1 / 2)) +
      (8032640 / 51177561 : ℝ) *
        endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ)
          (87 / 224) (87 / 448) (rowCountSub16799 (87 / 224) (1 / 2)) =
      (14925581 / 17059187 - lowBoundaryGen lx ly ℓ) +
        (13858778 / 17059187) * (lowBoundaryGen lx ly ℓ - lowBoundary lx ly ℓ) +
        ((6929389 / 17059187) * max 0 (lx + ly + ℓ - 1) -
          (1066803 / 17059187) * (lx + ly + ℓ - 1)) := by
  have hid := stage1_farkas_two_bin_identity lx ly ℓ (lowBoundaryGen lx ly ℓ)
  have hlb : 5 / 6 + (lx + ly) / 12 - ℓ / 6 =
      lowBoundary lx ly ℓ - max 0 (lx + ly + ℓ - 1) / 2 := by
    unfold lowBoundary
    ring
  linarith

/-- **Unconstrained `ℝ³` Stage-1 two-bin barrier (`< 14925581 / 17059187`).** Over all
`(lx, ly, ℓ) ∈ ℝ³` with no sign or upper-bound hypothesis, `lowBoundaryGen lx ly ℓ <
14925581 / 17059187` forces at least one of the Stage-1 bins `δ = 40/103` or `δ = 87/224` to have
strictly positive `endpointExponent`. -/
theorem stage1_endpointExponent_two_bin_pos_of_lowBoundaryGen_lt {lx ly ℓ : ℝ}
    (hσ : lowBoundaryGen lx ly ℓ < 14925581 / 17059187) :
    0 < max
      (endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ)
        (40 / 103) (20 / 103) (rowCountSub16799 (40 / 103) (1 / 2)))
      (endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ)
        (87 / 224) (87 / 448) (rowCountSub16799 (87 / 224) (1 / 2))) := by
  have hslack := stage1_farkas_two_bin_slack_gen lx ly ℓ
  have hgen := lowBoundary_le_lowBoundaryGen lx ly ℓ
  have hmax0 : 0 ≤ max 0 (lx + ly + ℓ - 1) := le_max_left _ _
  have hmax1 : lx + ly + ℓ - 1 ≤ max 0 (lx + ly + ℓ - 1) := le_max_right _ _
  have hpen : 0 ≤ (6929389 / 17059187 : ℝ) * max 0 (lx + ly + ℓ - 1) -
      (1066803 / 17059187) * (lx + ly + ℓ - 1) := by linarith
  by_contra hle
  rw [not_lt, max_le_iff] at hle
  linarith [hle.1, hle.2]

/-- Attainment of the two-bin Stage-1 LP value `14925581 / 17059187` at
`(17980606 / 51177561, 24652870 / 51177561, 8544085 / 51177561)`, where the third Stage-1 bin
`δ = 127 / 327` has strictly positive `endpointExponent` (`736 / 9734227990005 > 0`). -/
theorem stage1_farkas_two_bin_vertex_attained :
    lowBoundary (17980606 / 51177561) (24652870 / 51177561) (8544085 / 51177561) =
      14925581 / 17059187 ∧
    lowBoundaryGen (17980606 / 51177561) (24652870 / 51177561) (8544085 / 51177561) =
      14925581 / 17059187 ∧
    endpointExponent (17980606 / 51177561) (24652870 / 51177561) (8544085 / 51177561)
      (14925581 / 17059187) (40 / 103) (20 / 103) (rowCountSub16799 (40 / 103) (1 / 2)) = 0 ∧
    endpointExponent (17980606 / 51177561) (24652870 / 51177561) (8544085 / 51177561)
      (14925581 / 17059187) (87 / 224) (87 / 448) (rowCountSub16799 (87 / 224) (1 / 2)) = 0 ∧
    endpointExponent (17980606 / 51177561) (24652870 / 51177561) (8544085 / 51177561)
      (14925581 / 17059187) (127 / 327) (127 / 654) (rowCountSub16799 (127 / 327) (1 / 2)) =
      736 / 9734227990005 := by
  have hlb : lowBoundary (17980606 / 51177561) (24652870 / 51177561) (8544085 / 51177561) =
      14925581 / 17059187 := by
    unfold lowBoundary
    rw [show (17980606 : ℝ) / 51177561 + 24652870 / 51177561 + 8544085 / 51177561 - 1 = 0 by ring,
      max_self]
    norm_num
  refine ⟨hlb, ?_, ?_, ?_, ?_⟩
  · rw [lowBoundaryGen_eq_of_le (8544085 / 51177561) (by norm_num), hlb]
  · rw [rowCountSub16799_forty_103]; norm_num [endpointExponent]
  · rw [rowCountSub16799_eightyseven_224]; norm_num [endpointExponent]
  · rw [rowCountSub16799_binding_127_327]; norm_num [endpointExponent]

/-- **Sharp unconstrained `ℝ³` Stage-1 three-bin barrier (`≤ 14925581 / 17059187`).** Over **all**
`(lx, ly, ℓ) ∈ ℝ³` with no sign, simplex, or Gram hypothesis, if
`lowBoundaryGen lx ly ℓ ≤ 14925581 / 17059187`, then at least one of the three Stage-1 bins
`40/103`, `127/327`, or `87/224` has strictly positive `endpointExponent`. -/
theorem stage1_endpointExponent_three_bin_pos_of_lowBoundaryGen_le {lx ly ℓ : ℝ}
    (hσ : lowBoundaryGen lx ly ℓ ≤ 14925581 / 17059187) :
    0 < max
      (endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ)
        (40 / 103) (20 / 103) (rowCountSub16799 (40 / 103) (1 / 2)))
      (max
        (endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ)
          (127 / 327) (127 / 654) (rowCountSub16799 (127 / 327) (1 / 2)))
        (endpointExponent lx ly ℓ (lowBoundaryGen lx ly ℓ)
          (87 / 224) (87 / 448) (rowCountSub16799 (87 / 224) (1 / 2)))) := by
  by_contra hle
  rw [not_lt, max_le_iff, max_le_iff] at hle
  rcases hle with ⟨hE1, hE3, hE2⟩
  have hslack := stage1_farkas_two_bin_slack_gen lx ly ℓ
  have hgen := lowBoundary_le_lowBoundaryGen lx ly ℓ
  have hmax0 : 0 ≤ max 0 (lx + ly + ℓ - 1) := le_max_left _ _
  have hmax1 : lx + ly + ℓ - 1 ≤ max 0 (lx + ly + ℓ - 1) := le_max_right _ _
  have hpen : 0 ≤ (6929389 / 17059187 : ℝ) * max 0 (lx + ly + ℓ - 1) -
      (1066803 / 17059187) * (lx + ly + ℓ - 1) := by linarith
  have hσ_eq : lowBoundaryGen lx ly ℓ = 14925581 / 17059187 := by linarith
  have hE1_eq : endpointExponent lx ly ℓ (14925581 / 17059187)
      (40 / 103) (20 / 103) (rowCountSub16799 (40 / 103) (1 / 2)) = 0 := by
    rw [← hσ_eq]; linarith
  have hE2_eq : endpointExponent lx ly ℓ (14925581 / 17059187)
      (87 / 224) (87 / 448) (rowCountSub16799 (87 / 224) (1 / 2)) = 0 := by
    rw [← hσ_eq]; linarith
  have hpen_eq : (6929389 / 17059187 : ℝ) * max 0 (lx + ly + ℓ - 1) -
      (1066803 / 17059187) * (lx + ly + ℓ - 1) = 0 := by linarith
  have hu_eq : lx + ly + ℓ - 1 = 0 := by
    rcases le_total 0 (lx + ly + ℓ - 1) with hu | hu
    · rw [max_eq_right hu] at hpen_eq; linarith
    · rw [max_eq_left hu] at hpen_eq; linarith
  rw [rowCountSub16799_forty_103] at hE1_eq
  rw [rowCountSub16799_eightyseven_224] at hE2_eq
  rw [hσ_eq, rowCountSub16799_binding_127_327] at hE3
  unfold endpointExponent at hE1_eq hE2_eq hE3
  linarith

/-- Unconstrained `ℝ³` Stage-1 three-bin barrier for `lowBoundary`. -/
theorem stage1_endpointExponent_three_bin_pos_of_lowBoundary_le {lx ly ℓ : ℝ}
    (hσ : lowBoundary lx ly ℓ ≤ 14925581 / 17059187) :
    0 < max
      (endpointExponent lx ly ℓ (lowBoundary lx ly ℓ)
        (40 / 103) (20 / 103) (rowCountSub16799 (40 / 103) (1 / 2)))
      (max
        (endpointExponent lx ly ℓ (lowBoundary lx ly ℓ)
          (127 / 327) (127 / 654) (rowCountSub16799 (127 / 327) (1 / 2)))
        (endpointExponent lx ly ℓ (lowBoundary lx ly ℓ)
          (87 / 224) (87 / 448) (rowCountSub16799 (87 / 224) (1 / 2)))) := by
  by_contra hle
  rw [not_lt, max_le_iff, max_le_iff] at hle
  rcases hle with ⟨hE1, hE3, hE2⟩
  have hid := stage1_farkas_two_bin_identity lx ly ℓ (lowBoundary lx ly ℓ)
  have hlb : 5 / 6 + (lx + ly) / 12 - ℓ / 6 =
      lowBoundary lx ly ℓ - max 0 (lx + ly + ℓ - 1) / 2 := by
    unfold lowBoundary; ring
  have hmax0 : 0 ≤ max 0 (lx + ly + ℓ - 1) := le_max_left _ _
  have hmax1 : lx + ly + ℓ - 1 ≤ max 0 (lx + ly + ℓ - 1) := le_max_right _ _
  have hpen : 0 ≤ (6929389 / 17059187 : ℝ) * max 0 (lx + ly + ℓ - 1) -
      (1066803 / 17059187) * (lx + ly + ℓ - 1) := by linarith
  have hσ_eq : lowBoundary lx ly ℓ = 14925581 / 17059187 := by linarith
  have hE1_eq : endpointExponent lx ly ℓ (14925581 / 17059187)
      (40 / 103) (20 / 103) (rowCountSub16799 (40 / 103) (1 / 2)) = 0 := by
    rw [← hσ_eq]; linarith
  have hE2_eq : endpointExponent lx ly ℓ (14925581 / 17059187)
      (87 / 224) (87 / 448) (rowCountSub16799 (87 / 224) (1 / 2)) = 0 := by
    rw [← hσ_eq]; linarith
  have hpen_eq : (6929389 / 17059187 : ℝ) * max 0 (lx + ly + ℓ - 1) -
      (1066803 / 17059187) * (lx + ly + ℓ - 1) = 0 := by linarith
  have hu_eq : lx + ly + ℓ - 1 = 0 := by
    rcases le_total 0 (lx + ly + ℓ - 1) with hu | hu
    · rw [max_eq_right hu] at hpen_eq; linarith
    · rw [max_eq_left hu] at hpen_eq; linarith
  rw [rowCountSub16799_forty_103] at hE1_eq
  rw [rowCountSub16799_eightyseven_224] at hE2_eq
  rw [hσ_eq, rowCountSub16799_binding_127_327] at hE3
  unfold endpointExponent at hE1_eq hE2_eq hE3
  linarith

/-- **Tightness bracket for the Stage-1 vertex.** The unconstrained `ℝ³` Stage-1 Farkas lower
barrier `14925581 / 17059187` and our Gram-admissible Stage-1 vertex `139989 / 160000` bracket
the optimal Stage-1 exponent within `< 2.05 × 10⁻⁶` (`1 - 14925581/17059187 = 2133606/17059187`). -/
theorem stage1_vertex_within_two_millionths_of_farkas_barrier :
    (14925581 / 17059187 : ℝ) < 139989 / 160000 ∧
    (139989 / 160000 : ℝ) - 14925581 / 17059187 < 205 / 100000000 ∧
    1 - (14925581 / 17059187 : ℝ) = 2133606 / 17059187 := by
  norm_num

end

end GaloisForLFunctions.FamilyContinuationTheory.Budget
