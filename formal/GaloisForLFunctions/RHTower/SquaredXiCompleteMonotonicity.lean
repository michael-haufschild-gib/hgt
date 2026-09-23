import GaloisForLFunctions.RHTower.XiShiftedReciprocalHankelDisproof
import GaloisForLFunctions.RHTower.XiRelativeResolventTrace
import GaloisForLFunctions.RHTower.XiOffLineQuartetThermalOrientationBound
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap
import GaloisForLFunctions.RHTower.XiHeatShellMinimum
import GaloisForLFunctions.RHTower.XiWeilPolarization
import GaloisForLFunctions.RHTower.XiGaussianHeatTraceCriterion
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion
import GaloisForLFunctions.RHTower.XiCenteredOrdersSeventeenEighteenSourcePositivity
import GaloisForLFunctions.HTGeometry.SectorPowerPositivity

/-!
# Squared-variable complete monotonicity of the centered Xi logarithmic derivative

Write

`g y = xi' (1/2 + sqrt y) / (2 * sqrt y * xi (1/2 + sqrt y))`.

Pairing every centered Xi zero with its functional-equation reflection turns the Hadamard
logarithmic derivative into the absolutely convergent shifted reciprocal-square sum

`g y = (1/2) * sum_q (y + alpha_q ^ (2 : ℕ))⁻¹`,

where `alpha_q` is the centered spectral coordinate of one Xi multiplicity copy.  In the zero
coordinates `u = (Re rho - 1/2) ^ (2 : ℕ)`, `v = (Im rho) ^ (2 : ℕ)` each summand is `(A - B i)⁻¹` with

`A = y + v - u > 0`,   `B = 2 (Re rho - 1/2) (Im rho)`,   `84 * B ^ (2 : ℕ) < A ^ (2 : ℕ)`,

the sector bound coming from the open critical strip and the off-line quartet height gap
`85 < v`.  A sector of tangent `1/9` therefore carries fourteen powers, since `14 / 9 < pi / 2`.

Consequently every summand of the `n`-th alternating derivative is strictly positive for
`n + 1 <= 14`, and termwise differentiation of the tsum (uniform reciprocal-square majorant on
`(0, infinity)`) gives

`(-1) ^ n * g^(n) y > 0`   for `0 <= n <= 13`, `y > 0`.

Conjugation of the divisor makes the field real, so the statement is one about a genuine
real-valued function of the squared radial coordinate.
-/

open Complex

namespace RHTower

noncomputable section

/-! ### The squared centered spectral coordinate -/

/-- The squared centered spectral coordinate of one Xi multiplicity copy. -/
def xiSquaredNode (q : XiZeroCopy) : ℂ := xiSpectralPoint q ^ (2 : ℕ)

theorem xiSquaredNode_re (q : XiZeroCopy) :
    (xiSquaredNode q).re = (q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) := by
  rw [xiSquaredNode, pow_two, Complex.mul_re, xiSpectralPoint_re_eq, xiSpectralPoint_im_eq]
  ring

theorem xiSquaredNode_im (q : XiZeroCopy) :
    (xiSquaredNode q).im = -(2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) := by
  rw [xiSquaredNode, pow_two, Complex.mul_im, xiSpectralPoint_re_eq, xiSpectralPoint_im_eq]
  ring

/-- The open critical strip and the endpoint height gap put every squared centered node in the
right half-plane. -/
theorem xiSquaredNode_re_pos (q : XiZeroCopy) : 0 < (xiSquaredNode q).re := by
  rw [xiSquaredNode_re]
  have h1 := xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have h2 := xi_divisor_support_centered_re_sq_lt_quarter q.1
  linarith

theorem xiSquaredNode_ne_zero (q : XiZeroCopy) : xiSquaredNode q ≠ 0 := by
  intro h
  have hpos := xiSquaredNode_re_pos q
  rw [h, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

theorem xiZeroCopyReciprocalSquare_eq_inv_node (q : XiZeroCopy) :
    xiZeroCopyReciprocalSquare q = (xiSquaredNode q)⁻¹ := by
  rw [xiZeroCopyReciprocalSquare, xiSquaredNode, inv_pow]

theorem ofReal_add_xiSquaredNode_re {v : ℝ} (q : XiZeroCopy) :
    ((v : ℂ) + xiSquaredNode q).re = v + (xiSquaredNode q).re := by
  simp

theorem ofReal_add_xiSquaredNode_im {v : ℝ} (q : XiZeroCopy) :
    ((v : ℂ) + xiSquaredNode q).im = (xiSquaredNode q).im := by
  simp

theorem ofReal_add_xiSquaredNode_ne_zero {v : ℝ} (hv : 0 ≤ v) (q : XiZeroCopy) :
    (v : ℂ) + xiSquaredNode q ≠ 0 := by
  intro h
  have hre : ((v : ℂ) + xiSquaredNode q).re = 0 := by rw [h, Complex.zero_re]
  rw [ofReal_add_xiSquaredNode_re] at hre
  linarith [xiSquaredNode_re_pos q]

/-- The Möbius-translated reciprocal-square atom is the shifted resolvent kernel of the squared
centered node. -/
theorem xiShiftedReciprocalSquare_eq_inv {v : ℝ} (hv : 0 ≤ v) (q : XiZeroCopy) :
    xiShiftedReciprocalSquare v q = ((v : ℂ) + xiSquaredNode q)⁻¹ := by
  have hnode := xiSquaredNode_ne_zero q
  have hden := ofReal_add_xiSquaredNode_ne_zero hv q
  have hone : (1 : ℂ) + (v : ℂ) * (xiSquaredNode q)⁻¹ ≠ 0 := by
    have := one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hv q
    rwa [xiZeroCopyReciprocalSquare_eq_inv_node] at this
  rw [xiShiftedReciprocalSquare, xiZeroCopyReciprocalSquare_eq_inv_node, eq_comm,
    eq_div_iff hone]
  field_simp
  ring

/-! ### The shifted sector bound -/

/-- **Shifted reciprocal-square sector bound.**  At every positive squared base point the
transverse square of a centered node is below one eighty-fourth of the shifted longitudinal
square.  On-line copies are transversally trivial; off-line copies use the open critical strip
`u < 1/4` together with the four-copy endpoint height gap `85 < v`. -/
theorem eightyFour_mul_xiSquaredNode_im_sq_lt {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    84 * (xiSquaredNode q).im ^ (2 : ℕ) < (y + (xiSquaredNode q).re) ^ (2 : ℕ) := by
  have hnodere : (xiSquaredNode q).re =
      (q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) := xiSquaredNode_re q
  have hnodeim2 : (xiSquaredNode q).im ^ (2 : ℕ) =
      4 * ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) * (q.1 : ℂ).im ^ (2 : ℕ) := by
    rw [xiSquaredNode_im]; ring
  have hpos : 0 < (xiSquaredNode q).re := xiSquaredNode_re_pos q
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have hzero : (xiSquaredNode q).im ^ (2 : ℕ) = 0 := by
      rw [hnodeim2, hon]; ring
    rw [hzero]
    nlinarith
  · set u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) with hu
    set v : ℝ := (q.1 : ℂ).im ^ (2 : ℕ) with hv
    have hu0 : 0 ≤ u := by rw [hu]; positivity
    have hu4 : u < 1 / 4 := xi_divisor_support_centered_re_sq_lt_quarter q.1
    have hv85 : 85 < v := xiZeroCopy_offLine_eightyFive_lt_im_sq q hon
    have h340 : 340 * u < v := by linarith
    have hcore : 336 * u * v ≤ (v - u) ^ (2 : ℕ) := by nlinarith [mul_nonneg hu0 (by linarith : (0:ℝ) ≤ v)]
    rw [hnodeim2, hnodere]
    rw [hnodere] at hpos
    nlinarith [hcore, hpos]

/-- **Atomwise positivity of the shifted reciprocal-square powers.**  A tangent-`1/9` sector
carries fourteen powers because `14 / 9 < pi / 2`. -/
theorem re_xiShiftedReciprocalSquare_pow_pos {y : ℝ} (hy : 0 < y) (q : XiZeroCopy)
    {m : ℕ} (hm : m ≤ 14) :
    0 < ((xiShiftedReciprocalSquare y q) ^ m).re := by
  have hArepr : ((y + (xiSquaredNode q).re : ℝ) : ℂ) -
      ((-(xiSquaredNode q).im : ℝ) : ℂ) * I = (y : ℂ) + xiSquaredNode q := by
    apply Complex.ext
    · simp
    · simp
  rw [xiShiftedReciprocalSquare_eq_inv hy.le, ← hArepr]
  refine GaloisForLFunctions.HTGeometry.re_inv_sub_mul_I_pow_pos_of_sq_lt
    (N := 84) (t := 1 / 9) ?_ (by norm_num) (by norm_num) ?_ ?_
  · linarith [xiSquaredNode_re_pos q]
  · have h := eightyFour_mul_xiSquaredNode_im_sq_lt hy q
    nlinarith [h]
  · have hmR : (m : ℝ) ≤ 14 := by exact_mod_cast hm
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith [Real.pi_gt_d20]

/-! ### Higher sector orders through the corner exclusions -/

/-- The shifted reciprocal-square atom in the real zero coordinates
`A = y + im^(2 : ℕ) - (re - 1/2)^(2 : ℕ)`, `B = 2 (re - 1/2) im`. -/
theorem xiShiftedReciprocalSquare_eq_coordinate {y : ℝ} (hy : 0 ≤ y) (q : XiZeroCopy) :
    xiShiftedReciprocalSquare y q =
      ((((y + ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) : ℝ) : ℂ) -
        ((2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im : ℝ) : ℂ) * I)⁻¹) := by
  rw [xiShiftedReciprocalSquare_eq_inv hy]
  congr 1
  apply Complex.ext
  · rw [ofReal_add_xiSquaredNode_re, xiSquaredNode_re]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero]
  · rw [ofReal_add_xiSquaredNode_im, xiSquaredNode_im]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_sub]

/-- **A strict unshifted sector ratio survives every positive shift.**  The shifted longitudinal
coordinate only grows, so a power positivity criterion valid at the unshifted ratio is valid at
every positive squared base point. -/
theorem re_xiShiftedReciprocalSquare_pow_pos_of_sector
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) {n : ℕ} {N : ℝ}
    (hcrit : ∀ A B : ℝ, 0 < A → N * B ^ (2 : ℕ) < A ^ (2 : ℕ) →
      0 < ((((A : ℂ) - B * I)⁻¹) ^ n).re)
    (hsector : N * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ)) :
    0 < ((xiShiftedReciprocalSquare y q) ^ n).re := by
  have ht : 0 < (q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) := by
    have h := xiSquaredNode_re_pos q
    rwa [xiSquaredNode_re] at h
  rw [xiShiftedReciprocalSquare_eq_coordinate hy.le]
  exact hcrit _ _ (by linarith) (by nlinarith)

/-- **An empty sector-failure window gives the strict unshifted sector ratio.**  On the critical
line the transverse coordinate vanishes and the ratio is trivial; off it a failure would place the
zero in the excluded window. -/
theorem xiCenteredSectorRatio_of_window_empty {N : ℝ} {W : Prop} (q : XiZeroCopy)
    (hcorner : (q.1 : ℂ).re ≠ 1 / 2 →
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) ≤
        N * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) → W)
    (hempty : ¬ W) :
    N * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  have ht : 0 < (q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) := by
    have h := xiSquaredNode_re_pos q
    rwa [xiSquaredNode_re] at h
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have hB : 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im = 0 := by rw [hon]; ring
    rw [hB]
    simpa using pow_pos ht 2
  · by_contra hnot
    exact hempty (hcorner hon (not_lt.mp hnot))

theorem re_xiShiftedReciprocalSquare_pow_fifteen_pos {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    0 < ((xiShiftedReciprocalSquare y q) ^ (15 : ℕ)).re :=
  re_xiShiftedReciprocalSquare_pow_pos_of_sector hy q
    (fun _ _ hA h => orderFifteenReciprocalPower_re_pos_of_sectorRatio hA h)
    (xiCenteredSectorRatio_of_window_empty q
      (fun hoff hfail => xiCenteredOrderFifteenSectorFailure_mem_edgeCorner q hoff hfail)
      (fun hc => not_exists_xiZeroCopy_mem_centeredOrderFourteen_edgeCorner ⟨q, hc⟩))

theorem re_xiShiftedReciprocalSquare_pow_sixteen_pos {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    0 < ((xiShiftedReciprocalSquare y q) ^ (16 : ℕ)).re :=
  re_xiShiftedReciprocalSquare_pow_pos_of_sector hy q
    (fun _ _ hA h => orderSixteenReciprocalPower_re_pos_of_sectorRatio hA h)
    (xiCenteredSectorRatio_of_window_empty q
      (fun hoff hfail => xiCenteredOrderSixteenSectorFailure_mem_edgeCorner q hoff hfail)
      (fun hc => not_exists_xiZeroCopy_mem_centeredOrderSeventeen_sourceCorner
        ⟨q, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.trans (by norm_num)⟩))

theorem re_xiShiftedReciprocalSquare_pow_seventeen_pos {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    0 < ((xiShiftedReciprocalSquare y q) ^ (17 : ℕ)).re :=
  re_xiShiftedReciprocalSquare_pow_pos_of_sector hy q
    (fun _ _ hA h => orderSeventeenReciprocalPower_re_pos_of_sectorRatio hA h)
    (xiCenteredSectorRatio_of_window_empty q
      (fun hoff hfail => xiCenteredOrderSeventeenSectorFailure_mem_edgeCorner q hoff hfail)
      (fun hc => not_exists_xiZeroCopy_mem_centeredOrderSeventeen_sourceCorner ⟨q, hc⟩))

theorem re_xiShiftedReciprocalSquare_pow_eighteen_pos {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    0 < ((xiShiftedReciprocalSquare y q) ^ (18 : ℕ)).re :=
  re_xiShiftedReciprocalSquare_pow_pos_of_sector hy q
    (fun _ _ hA h => orderEighteenReciprocalPower_re_pos_of_sectorRatio hA h)
    (xiCenteredSectorRatio_of_window_empty q
      (fun hoff hfail => xiCenteredOrderEighteenSectorFailure_mem_edgeCorner q hoff hfail)
      (fun hc => not_exists_xiZeroCopy_mem_centeredOrderNineteen_sourceCorner
        ⟨q, by linarith [hc.1], hc.2.1, hc.2.2.1, hc.2.2.2.trans (by norm_num)⟩))

theorem re_xiShiftedReciprocalSquare_pow_nineteen_pos {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    0 < ((xiShiftedReciprocalSquare y q) ^ (19 : ℕ)).re :=
  re_xiShiftedReciprocalSquare_pow_pos_of_sector hy q
    (fun _ _ hA h => orderNineteenReciprocalPower_re_pos_of_sectorRatio hA h)
    (xiCenteredSectorRatio_of_window_empty q
      (fun hoff hfail => xiCenteredOrderNineteenSectorFailure_mem_edgeCorner q hoff hfail)
      (fun hc => not_exists_xiZeroCopy_mem_centeredOrderNineteen_sourceCorner ⟨q, hc⟩))

/-- **Complete atomwise sector range.**  Every shifted reciprocal-square Xi atom has strictly
positive real part in all nineteen powers, at every positive squared base point. -/
theorem re_xiShiftedReciprocalSquare_pow_pos_of_le_nineteen {y : ℝ} (hy : 0 < y)
    (q : XiZeroCopy) {m : ℕ} (hm : m ≤ 19) :
    0 < ((xiShiftedReciprocalSquare y q) ^ m).re := by
  rcases Nat.lt_or_ge m 15 with hlt | hge
  · exact re_xiShiftedReciprocalSquare_pow_pos hy q (by omega)
  · interval_cases m
    · exact re_xiShiftedReciprocalSquare_pow_fifteen_pos hy q
    · exact re_xiShiftedReciprocalSquare_pow_sixteen_pos hy q
    · exact re_xiShiftedReciprocalSquare_pow_seventeen_pos hy q
    · exact re_xiShiftedReciprocalSquare_pow_eighteen_pos hy q
    · exact re_xiShiftedReciprocalSquare_pow_nineteen_pos hy q

/-! ### Reality of the shifted reciprocal-square moments -/

theorem xiSquaredNode_copyConj (q : XiZeroCopy) :
    xiSquaredNode (xiZeroCopyConjEquiv q) = (starRingEnd ℂ) (xiSquaredNode q) := by
  rw [xiSquaredNode, xiSquaredNode, xiSpectralPoint_copyConj, neg_sq, ← map_pow]

theorem xiShiftedReciprocalSquare_copyConj {v : ℝ} (hv : 0 ≤ v) (q : XiZeroCopy) :
    xiShiftedReciprocalSquare v (xiZeroCopyConjEquiv q) =
      (starRingEnd ℂ) (xiShiftedReciprocalSquare v q) := by
  rw [xiShiftedReciprocalSquare_eq_inv hv, xiShiftedReciprocalSquare_eq_inv hv,
    xiSquaredNode_copyConj, map_inv₀]
  congr 1
  rw [map_add, Complex.conj_ofReal]

/-- The shifted reciprocal-square moments are real: the Xi divisor is conjugation invariant, and
conjugation acts on the squared centered nodes by complex conjugation. -/
theorem xiShiftedReciprocalMoment_im_eq_zero {v : ℝ} (hv : 0 ≤ v) (n : ℕ) :
    (xiShiftedReciprocalMoment v n).im = 0 := by
  rw [← Complex.conj_eq_iff_im, xiShiftedReciprocalMoment]
  calc
    (starRingEnd ℂ) (∑' q : XiZeroCopy, xiShiftedReciprocalSquare v q ^ (n + 1))
        = ∑' q : XiZeroCopy, (starRingEnd ℂ) (xiShiftedReciprocalSquare v q ^ (n + 1)) := by
      simpa only [Complex.star_def] using
        (tsum_star (f := fun q : XiZeroCopy => xiShiftedReciprocalSquare v q ^ (n + 1)))
    _ = ∑' q : XiZeroCopy,
          xiShiftedReciprocalSquare v (xiZeroCopyConjEquiv q) ^ (n + 1) := by
      refine tsum_congr fun q => ?_
      rw [xiShiftedReciprocalSquare_copyConj hv, map_pow]
    _ = ∑' q : XiZeroCopy, xiShiftedReciprocalSquare v q ^ (n + 1) :=
      xiZeroCopyConjEquiv.tsum_eq
        (fun q => xiShiftedReciprocalSquare v q ^ (n + 1))

/-! ### Termwise differentiation of the shifted moment tower -/

/-- The squared-base-point derivative of one shifted reciprocal-square power. -/
theorem hasDerivAt_xiShiftedReciprocalSquare_pow {v : ℝ} (hv : 0 < v) (q : XiZeroCopy) (m : ℕ) :
    HasDerivAt (fun t : ℝ => xiShiftedReciprocalSquare t q ^ (m + 1))
      (-((m : ℂ) + 1) * xiShiftedReciprocalSquare v q ^ (m + 2)) v := by
  have hne : (v : ℂ) + xiSquaredNode q ≠ 0 :=
    ofReal_add_xiSquaredNode_ne_zero hv.le q
  have hbase : HasDerivAt (fun t : ℝ => (t : ℂ) + xiSquaredNode q) 1 v := by
    have h0 : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) (1 : ℂ) v := by
      simpa using (hasDerivAt_id v).ofReal_comp
    simpa using h0.add_const (xiSquaredNode q)
  have hinv := hbase.inv hne
  have key : HasDerivAt (fun t : ℝ => (((t : ℂ) + xiSquaredNode q)⁻¹) ^ (m + 1))
      (-((m : ℂ) + 1) * (((v : ℂ) + xiSquaredNode q)⁻¹) ^ (m + 2)) v := by
    have hpow := hinv.pow (m + 1)
    have hval : -((m : ℂ) + 1) * (((v : ℂ) + xiSquaredNode q)⁻¹) ^ (m + 2)
        = ((m + 1 : ℕ) : ℂ) * (((v : ℂ) + xiSquaredNode q)⁻¹) ^ (m + 1 - 1) *
          (-1 / ((v : ℂ) + xiSquaredNode q) ^ (2 : ℕ)) := by
      have hX : (-1 : ℂ) / ((v : ℂ) + xiSquaredNode q) ^ (2 : ℕ)
          = -((((v : ℂ) + xiSquaredNode q)⁻¹) ^ (2 : ℕ)) := by
        rw [inv_pow, neg_div, one_div]
      rw [hX]
      simp only [Nat.add_sub_cancel]
      push_cast
      ring
    rw [hval]
    exact hpow
  have heq : (fun t : ℝ => xiShiftedReciprocalSquare t q ^ (m + 1))
      =ᶠ[nhds v] (fun t : ℝ => (((t : ℂ) + xiSquaredNode q)⁻¹) ^ (m + 1)) := by
    filter_upwards [Ioi_mem_nhds hv] with t ht
    rw [xiShiftedReciprocalSquare_eq_inv (le_of_lt ht)]
  rw [xiShiftedReciprocalSquare_eq_inv hv.le]
  exact key.congr_of_eventuallyEq heq

/-- **Termwise differentiation of the shifted moment tower.**  The reciprocal-square atoms are a
uniform majorant on the whole positive base ray, so the moment tower differentiates term by
term. -/
theorem hasDerivAt_xiShiftedReciprocalMoment {y : ℝ} (hy : 0 < y) (n : ℕ) :
    HasDerivAt (fun v : ℝ => xiShiftedReciprocalMoment v n)
      (-((n : ℂ) + 1) * xiShiftedReciprocalMoment y (n + 1)) y := by
  have hu : Summable (fun q : XiZeroCopy =>
      ((n : ℝ) + 1) * ‖xiZeroCopyReciprocalSquare q‖ ^ (n + 2)) := by
    have h := (summable_xiZeroCopyReciprocalSquare_pow (n + 1)).norm
    simp only [norm_pow] at h
    exact h.mul_left _
  have hderiv : ∀ q : XiZeroCopy, ∀ v ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun t : ℝ => xiShiftedReciprocalSquare t q ^ (n + 1))
        (-((n : ℂ) + 1) * xiShiftedReciprocalSquare v q ^ (n + 2)) v :=
    fun q v hv => hasDerivAt_xiShiftedReciprocalSquare_pow hv q n
  have hbound : ∀ q : XiZeroCopy, ∀ v ∈ Set.Ioi (0 : ℝ),
      ‖-((n : ℂ) + 1) * xiShiftedReciprocalSquare v q ^ (n + 2)‖ ≤
        ((n : ℝ) + 1) * ‖xiZeroCopyReciprocalSquare q‖ ^ (n + 2) := by
    intro q v hv
    rw [norm_mul, norm_neg, norm_pow]
    have hcast : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    have hc : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      rw [hcast, Complex.norm_natCast]
      push_cast
      ring
    rw [hc]
    refine mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _)
        (norm_xiShiftedReciprocalSquare_le (le_of_lt hv) q) _) (by positivity)
  have hsum0 : Summable (fun q : XiZeroCopy => xiShiftedReciprocalSquare y q ^ (n + 1)) :=
    summable_xiShiftedReciprocalSquare_pow hy.le n
  have hmain := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi isPreconnected_Ioi hderiv hbound
    (Set.mem_Ioi.mpr hy) hsum0 (Set.mem_Ioi.mpr hy)
  simpa only [xiShiftedReciprocalMoment, tsum_mul_left] using hmain

theorem hasDerivAt_re_xiShiftedReciprocalMoment {y : ℝ} (hy : 0 < y) (n : ℕ) :
    HasDerivAt (fun v : ℝ => (xiShiftedReciprocalMoment v n).re)
      (-((n : ℝ) + 1) * (xiShiftedReciprocalMoment y (n + 1)).re) y := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (hasDerivAt_xiShiftedReciprocalMoment hy n)
  have hval : (Complex.reCLM (-((n : ℂ) + 1) * xiShiftedReciprocalMoment y (n + 1)))
      = -((n : ℝ) + 1) * (xiShiftedReciprocalMoment y (n + 1)).re := by
    simp [Complex.mul_re]
  rw [hval] at h
  exact h

/-! ### The squared radial field and its alternating derivatives -/

/-- The squared-variable logarithmic derivative field of centered Xi, written through the shifted
reciprocal-square moment tower. -/
def squaredXiRadialField (y : ℝ) : ℝ := (xiShiftedReciprocalMoment y 0).re / 2

theorem iteratedDeriv_squaredXiRadialField (n : ℕ) :
    ∀ {y : ℝ}, 0 < y →
      iteratedDeriv n squaredXiRadialField y =
        (-1 : ℝ) ^ n * (n.factorial : ℝ) / 2 * (xiShiftedReciprocalMoment y n).re := by
  induction n with
  | zero =>
    intro y _
    simp only [iteratedDeriv_zero, squaredXiRadialField, pow_zero, Nat.factorial_zero,
      Nat.cast_one, one_mul]
    ring
  | succ n ih =>
    intro y hy
    have hEq : iteratedDeriv n squaredXiRadialField =ᶠ[nhds y]
        (fun v : ℝ => (-1 : ℝ) ^ n * (n.factorial : ℝ) / 2 *
          (xiShiftedReciprocalMoment v n).re) := by
      filter_upwards [Ioi_mem_nhds hy] with v hv using ih hv
    rw [iteratedDeriv_succ, hEq.deriv_eq]
    have hd := (hasDerivAt_re_xiShiftedReciprocalMoment hy n).const_mul
      ((-1 : ℝ) ^ n * (n.factorial : ℝ) / 2)
    rw [hd.deriv]
    push_cast [Nat.factorial_succ]
    ring

theorem re_xiShiftedReciprocalMoment_pos {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : n ≤ 18) :
    0 < (xiShiftedReciprocalMoment y n).re := by
  have hsumC := summable_xiShiftedReciprocalSquare_pow hy.le n
  have hsum : Summable (fun q : XiZeroCopy =>
      (xiShiftedReciprocalSquare y q ^ (n + 1)).re) := Complex.reCLM.summable hsumC
  obtain ⟨q0⟩ := nonempty_xiZeroCopy
  rw [xiShiftedReciprocalMoment, re_tsum hsumC]
  exact hsum.tsum_pos
    (fun q => (re_xiShiftedReciprocalSquare_pow_pos_of_le_nineteen hy q (by omega)).le) q0
    (re_xiShiftedReciprocalSquare_pow_pos_of_le_nineteen hy q0 (by omega))

/-- **Squared-Xi complete monotonicity through order eighteen.**  Every alternating
squared-coordinate derivative of the centered Xi logarithmic derivative through order eighteen is
strictly positive on the whole positive squared ray, unconditionally. -/
theorem alternating_iteratedDeriv_squaredXiRadialField_pos {y : ℝ} (hy : 0 < y)
    {n : ℕ} (hn : n ≤ 18) :
    0 < (-1 : ℝ) ^ n * iteratedDeriv n squaredXiRadialField y := by
  have hsq : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [iteratedDeriv_squaredXiRadialField n hy,
    show (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * (n.factorial : ℝ) / 2 *
        (xiShiftedReciprocalMoment y n).re)
      = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
        ((n.factorial : ℝ) / 2 * (xiShiftedReciprocalMoment y n).re) by ring,
    hsq, one_mul]
  exact mul_pos (by positivity) (re_xiShiftedReciprocalMoment_pos hy hn)

/-- **Low-order complete monotonicity.**  The alternating signs through derivative order thirteen,
the range protected by the eighty-four sector alone. -/
theorem alternating_iteratedDeriv_squaredXiRadialField_pos_of_le_thirteen {y : ℝ} (hy : 0 < y)
    {n : ℕ} (hn : n ≤ 13) :
    0 < (-1 : ℝ) ^ n * iteratedDeriv n squaredXiRadialField y :=
  alternating_iteratedDeriv_squaredXiRadialField_pos hy (by omega)

/-- **The first order beyond the eighty-four sector.**  Derivative order fourteen has the
RH-compatible strict sign at every positive squared base point, with no far-right restriction. -/
theorem alternating_iteratedDeriv_squaredXiRadialField_pos_orderFourteen {y : ℝ} (hy : 0 < y) :
    0 < iteratedDeriv 14 squaredXiRadialField y := by
  have h := alternating_iteratedDeriv_squaredXiRadialField_pos hy (n := 14) (by norm_num)
  rw [show ((-1 : ℝ) ^ (14 : ℕ)) = 1 by norm_num, one_mul] at h
  exact h

/-! ### Identification with the Xi logarithmic derivative -/

/-- The source-pure zero-free band keeps `xi` away from zero on the whole real axis shifted from
the centre. -/
theorem xi_ofReal_shift_ne_zero (w : ℝ) : xi (1 / 2 + (w : ℂ)) ≠ 0 := by
  have hre : (((w : ℂ) * (-I)).re) = 0 := by simp
  have hXi : XiC ((w : ℂ) * (-I)) ≠ 0 :=
    XiC_ne_zero_of_abs_re_le_nine_halves (by rw [hre]; norm_num)
  have hmul : (1 : ℂ) / 2 + ((w : ℂ) * (-I)) * I = 1 / 2 + (w : ℂ) := by
    have hII : (-I) * I = (1 : ℂ) := by rw [neg_mul, Complex.I_mul_I]; ring
    calc (1 : ℂ) / 2 + ((w : ℂ) * (-I)) * I = 1 / 2 + (w : ℂ) * ((-I) * I) := by ring
      _ = 1 / 2 + (w : ℂ) := by rw [hII, mul_one]
  rwa [XiC, hmul] at hXi

/-- **Exact Hadamard identity in the squared coordinate.**  On the positive real ray the shifted
reciprocal-square moment of order zero is exactly the radial logarithmic derivative of `xi`. -/
theorem xiShiftedReciprocalMoment_zero_eq {w : ℝ} (hw : 0 < w) :
    xiShiftedReciprocalMoment (w ^ (2 : ℕ)) 0 =
      deriv xi (1 / 2 + (w : ℂ)) / ((w : ℂ) * xi (1 / 2 + (w : ℂ))) := by
  have hII : (-I) * I = (1 : ℂ) := by rw [neg_mul, Complex.I_mul_I]; ring
  have hmul : (1 : ℂ) / 2 + ((w : ℂ) * (-I)) * I = 1 / 2 + (w : ℂ) := by
    calc (1 : ℂ) / 2 + ((w : ℂ) * (-I)) * I = 1 / 2 + (w : ℂ) * ((-I) * I) := by ring
      _ = 1 / 2 + (w : ℂ) := by rw [hII, mul_one]
  have hre : (((w : ℂ) * (-I)).re) = 0 := by simp
  have hXi : XiC ((w : ℂ) * (-I)) ≠ 0 :=
    XiC_ne_zero_of_abs_re_le_nine_halves (by rw [hre]; norm_num)
  have hxine : xi (1 / 2 + (w : ℂ)) ≠ 0 := xi_ofReal_shift_ne_zero w
  have hwne : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  have hz2 : ((w : ℂ) * (-I)) ^ (2 : ℕ) = -((w : ℂ) ^ (2 : ℕ)) := by
    rw [mul_pow, neg_sq, Complex.I_sq]; ring
  have hterm : ∀ q : XiZeroCopy,
      xiReciprocalSquareResolventTerm ((w : ℂ) * (-I)) q =
        xiShiftedReciprocalSquare (w ^ (2 : ℕ)) q := by
    intro q
    rw [xiReciprocalSquareResolventTerm, xiShiftedReciprocalSquare, hz2]
    congr 2
    push_cast
    ring
  have htrace : logDeriv XiC ((w : ℂ) * (-I)) =
      (w : ℂ) * I * xiShiftedReciprocalMoment (w ^ (2 : ℕ)) 0 := by
    rw [logDeriv_XiC_eq_relativeResolventTrace hXi,
      xiRelativeResolventTrace_eq_reciprocalSquareResolvent hXi]
    rw [tsum_congr hterm, xiShiftedReciprocalMoment]
    simp only [zero_add, pow_one]
    ring
  -- the Xi side
  have hinner : HasDerivAt (fun z : ℂ => 1 / 2 + z * I) I ((w : ℂ) * (-I)) := by
    simpa using ((hasDerivAt_id ((w : ℂ) * (-I))).mul_const I).const_add (1 / 2 : ℂ)
  have hXiC : HasDerivAt XiC (deriv xi (1 / 2 + (w : ℂ)) * I) ((w : ℂ) * (-I)) := by
    have hxi : HasDerivAt xi (deriv xi (1 / 2 + ((w : ℂ) * (-I)) * I))
        (1 / 2 + ((w : ℂ) * (-I)) * I) := (xi_differentiable _).hasDerivAt
    have := hxi.comp ((w : ℂ) * (-I)) hinner
    rw [hmul] at this
    exact this
  have hlog : logDeriv XiC ((w : ℂ) * (-I)) =
      deriv xi (1 / 2 + (w : ℂ)) * I / xi (1 / 2 + (w : ℂ)) := by
    rw [logDeriv_apply, hXiC.deriv, XiC, hmul]
  rw [hlog, div_eq_iff hxine] at htrace
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h2 : deriv xi (1 / 2 + (w : ℂ)) =
      (w : ℂ) * xiShiftedReciprocalMoment (w ^ (2 : ℕ)) 0 * xi (1 / 2 + (w : ℂ)) := by
    refine mul_right_cancel₀ hI ?_
    linear_combination htrace
  rw [eq_div_iff (mul_ne_zero hwne hxine)]
  linear_combination -h2

/-- **The squared radial field is the card's `g`.**  For `y > 0`,
`squaredXiRadialField y = xi' (1/2 + sqrt y) / (2 sqrt y xi (1/2 + sqrt y))`. -/
theorem squaredXiRadialField_eq {y : ℝ} (hy : 0 < y) :
    ((squaredXiRadialField y : ℝ) : ℂ) =
      deriv xi (1 / 2 + (Real.sqrt y : ℂ)) /
        (2 * (Real.sqrt y : ℂ) * xi (1 / 2 + (Real.sqrt y : ℂ))) := by
  have hw : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hsq : Real.sqrt y ^ (2 : ℕ) = y := Real.sq_sqrt hy.le
  have hmom := xiShiftedReciprocalMoment_zero_eq hw
  rw [hsq] at hmom
  have him : (xiShiftedReciprocalMoment y 0).im = 0 :=
    xiShiftedReciprocalMoment_im_eq_zero hy.le 0
  have hreal : ((xiShiftedReciprocalMoment y 0).re : ℂ) = xiShiftedReciprocalMoment y 0 := by
    apply Complex.ext <;> simp [him]
  rw [squaredXiRadialField, Complex.ofReal_div, hreal, hmom]
  have hwne : ((Real.sqrt y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  have hxine : xi (1 / 2 + (Real.sqrt y : ℂ)) ≠ 0 := xi_ofReal_shift_ne_zero (Real.sqrt y)
  push_cast
  field_simp

/-! ### The first-gate consequence -/

/-- The logarithmic derivative of `xi` along the shifted real ray. -/
def xiRealLogDeriv (w : ℝ) : ℝ := (logDeriv xi (1 / 2 + (w : ℂ))).re

theorem differentiableAt_logDeriv_xi {z : ℂ} (hz : xi z ≠ 0) :
    DifferentiableAt ℂ (logDeriv xi) z := by
  have h1 : DifferentiableAt ℂ (deriv xi) z := xi_differentiable.deriv z
  have h2 : DifferentiableAt ℂ xi z := xi_differentiable z
  simpa [logDeriv] using h1.div h2 hz

theorem hasDerivAt_xiRealLogDeriv (w : ℝ) :
    HasDerivAt xiRealLogDeriv ((deriv (logDeriv xi) (1 / 2 + (w : ℂ))).re) w := by
  have hxi : xi (1 / 2 + (w : ℂ)) ≠ 0 := xi_ofReal_shift_ne_zero w
  have hg : HasDerivAt (logDeriv xi) (deriv (logDeriv xi) (1 / 2 + (w : ℂ)))
      (1 / 2 + (w : ℂ)) := (differentiableAt_logDeriv_xi hxi).hasDerivAt
  have hf : HasDerivAt (fun z : ℂ => 1 / 2 + z) 1 ((w : ℂ)) := by
    simpa using (hasDerivAt_id ((w : ℂ))).const_add (1 / 2 : ℂ)
  have hcomp := hg.comp ((w : ℂ)) hf
  rw [mul_one] at hcomp
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt w hcomp.comp_ofReal

/-- On the positive ray the squared radial field is the halved radial logarithmic derivative. -/
theorem squaredXiRadialField_sq_eq {w : ℝ} (hw : 0 < w) :
    squaredXiRadialField (w ^ (2 : ℕ)) = xiRealLogDeriv w / (2 * w) := by
  have hy : (0 : ℝ) < w ^ (2 : ℕ) := by positivity
  have h := squaredXiRadialField_eq hy
  rw [Real.sqrt_sq hw.le] at h
  have hxi : xi (1 / 2 + (w : ℂ)) ≠ 0 := xi_ofReal_shift_ne_zero w
  have hwne : ((w : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  have hmul : ((squaredXiRadialField (w ^ (2 : ℕ)) * (2 * w) : ℝ) : ℂ) =
      logDeriv xi (1 / 2 + (w : ℂ)) := by
    push_cast
    rw [h, logDeriv_apply]
    field_simp
  have hre := congrArg Complex.re hmul
  rw [Complex.ofReal_re] at hre
  rw [xiRealLogDeriv, ← hre]
  field_simp

/-- **First-gate consequence.**  On the absolute Euler ray the radial logarithmic derivative of
`xi` obeys `w L'(1/2+w) - L(1/2+w) < 0`; this is the order-one case of the alternating sign law,
transported through the squared coordinate. -/
theorem hasDerivAt_squaredXiRadialField {y : ℝ} (hy : 0 < y) :
    HasDerivAt squaredXiRadialField (-(xiShiftedReciprocalMoment y 1).re / 2) y := by
  have hval : -(xiShiftedReciprocalMoment y 1).re / 2
      = -(((0 : ℕ) : ℝ) + 1) * (xiShiftedReciprocalMoment y (0 + 1)).re / 2 := by
    norm_num
  rw [hval]
  exact (hasDerivAt_re_xiShiftedReciprocalMoment hy 0).div_const 2

theorem xiRealLogDeriv_radial_gap_neg {w : ℝ} (hw : 0 < w) :
    w * deriv xiRealLogDeriv w - xiRealLogDeriv w < 0 := by
  have hy : (0 : ℝ) < w ^ (2 : ℕ) := by positivity
  have hS := hasDerivAt_squaredXiRadialField hy
  have hpow : HasDerivAt (fun v : ℝ => v ^ (2 : ℕ)) (2 * w) w := by
    simpa using hasDerivAt_pow 2 w
  have hG1 : HasDerivAt (fun v : ℝ => squaredXiRadialField (v ^ (2 : ℕ)))
      (-(xiShiftedReciprocalMoment (w ^ (2 : ℕ)) 1).re / 2 * (2 * w)) w :=
    HasDerivAt.comp (h := fun v : ℝ => v ^ (2 : ℕ)) w hS hpow
  have hnum : HasDerivAt xiRealLogDeriv
      ((deriv (logDeriv xi) (1 / 2 + (w : ℂ))).re) w := hasDerivAt_xiRealLogDeriv w
  have hden : HasDerivAt (fun v : ℝ => 2 * v) 2 w := by
    have h := (hasDerivAt_id w).const_mul (2 : ℝ)
    rw [mul_one] at h
    exact h
  have hdenne : (2 : ℝ) * w ≠ 0 := by positivity
  have hG2 := hnum.div hden hdenne
  have heq : (fun v : ℝ => xiRealLogDeriv v / (2 * v))
      =ᶠ[nhds w] (fun v : ℝ => squaredXiRadialField (v ^ (2 : ℕ))) := by
    filter_upwards [Ioi_mem_nhds hw] with v hv
    exact (squaredXiRadialField_sq_eq hv).symm
  have hu := HasDerivAt.unique (hG1.congr_of_eventuallyEq heq) hG2
  have hsq : (0 : ℝ) < (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) 1).re :=
    re_xiShiftedReciprocalMoment_pos hy (by norm_num)
  have hdenpow : ((2 : ℝ) * w) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hdenne
  rw [eq_div_iff hdenpow] at hu
  norm_num at hu
  rw [hnum.deriv]
  nlinarith [hu, mul_pos hsq (pow_pos hw 3)]

end

end RHTower
