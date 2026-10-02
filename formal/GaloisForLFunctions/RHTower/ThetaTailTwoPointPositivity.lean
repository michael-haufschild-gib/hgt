import GaloisForLFunctions.RHTower.ThetaCuspLogFourthNegative
import GaloisForLFunctions.RHTower.ThetaCuspGlobalReflectedRiccati
import GaloisForLFunctions.RHTower.ThetaPrimeGammaCutEnergy
import GaloisForLFunctions.RHTower.ThetaGeometricBoundaryEnergy
import GaloisForLFunctions.RHTower.ThetaTailCommonTranslationLoewnerNoGo

/-!
# Complete theta tail positivity on any two real nodes

The complete source's negative fourth logarithmic derivative controls its
squared-coordinate decay slope and the normalized diagonal tail. These retain
the full first-moment kernel in the two-point comparison.
-/

open Filter Topology MeasureTheory Set
noncomputable section
namespace RHTower.ThetaTailTwoPoint
open ThetaGeometricBoundaryAudit ThetaSourceWard

private theorem logThird_neg {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 3 thetaCuspLogSource x < 0 := by
  have hanti : StrictAnti (iteratedDeriv 3 thetaCuspLogSource) := by
    apply strictAnti_of_deriv_neg
    intro y
    rw [(hasDerivAt_iteratedDeriv_thetaCuspLogSource 3 y).deriv]
    exact iteratedDeriv_four_thetaCuspLogSource_neg_all y
  have hz := iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 3) ⟨1, rfl⟩
  simpa only [hz] using hanti hx

private def slopeDefect (x : ℝ) : ℝ :=
  x*iteratedDeriv 2 thetaCuspLogSource x-iteratedDeriv 1 thetaCuspLogSource x

private theorem slopeDefect_hasDerivAt (x : ℝ) :
    HasDerivAt slopeDefect (x*iteratedDeriv 3 thetaCuspLogSource x) x := by
  convert! ((hasDerivAt_id x).mul
    (hasDerivAt_iteratedDeriv_thetaCuspLogSource 2 x)).sub
    (hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 x) using 1
  simp only [id_eq]
  ring

private theorem slopeDefect_neg {x : ℝ} (hx : 0 < x) : slopeDefect x < 0 := by
  have hc : Continuous slopeDefect := continuous_iff_continuousAt.mpr
    fun y => (slopeDefect_hasDerivAt y).continuousAt
  have ha : StrictAntiOn slopeDefect (Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0) hc.continuousOn
    intro y hy
    have hy' : 0 < y := by simpa only [interior_Ici, mem_Ioi] using hy
    rw [(slopeDefect_hasDerivAt y).deriv]
    exact mul_neg_of_pos_of_neg hy' (logThird_neg hy')
  have hz : slopeDefect 0 = 0 := by
    simp only [slopeDefect, zero_mul, zero_sub,
      iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0, rfl⟩, neg_zero]
  simpa only [hz] using ha (by simp : (0:ℝ) ∈ Ici 0) hx.le hx

private theorem decaySlope_div_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t => thetaCuspLogDecaySlope t/t) (-slopeDefect x/x^2) x := by
  convert! ((hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 x).neg).div
    (hasDerivAt_id x) hx using 1
  simp only [slopeDefect, id_eq, Pi.neg_apply]
  ring

/-- The literal source's logarithmic decay per squared coordinate is strictly increasing. -/
theorem strictMonoOn_decaySlope_div :
    StrictMonoOn (fun x : ℝ => thetaCuspLogDecaySlope x/x) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun x hx => (decaySlope_div_hasDerivAt (ne_of_gt hx)).continuousAt.continuousWithinAt)
  intro x hx
  have hx' : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using hx
  rw [(decaySlope_div_hasDerivAt hx'.ne').deriv]
  exact div_pos (neg_pos.mpr (slopeDefect_neg hx')) (sq_pos_of_pos hx')

private theorem source_deriv_eq (x : ℝ) :
    deriv thetaCuspFullSource x = -thetaCuspLogDecaySlope x*thetaCuspFullSource x := by
  have h : iteratedDeriv 1 thetaCuspLogSource x =
      deriv thetaCuspFullSource x/thetaCuspFullSource x := by
    simpa only [iteratedDeriv_one] using (hasDerivAt_thetaCuspLogSource x).deriv
  dsimp only [thetaCuspLogDecaySlope]
  rw [h]
  field_simp [(thetaCuspFullSource_pos_all x).ne']

/-- Strict diagonal tail comparison supplied by squared-coordinate source curvature. -/
theorem diagonal_tail_lt_source_square {x : ℝ} (hx : 0 < x) :
    (thetaCuspLogDecaySlope x/x)*thetaPrimeGammaCutEnergy x < thetaCuspFullSource x^2 := by
  let g : ℝ → ℝ := fun t => -2*(thetaCuspFullSource t*deriv thetaCuspFullSource t)-
    (thetaCuspLogDecaySlope x/x)*(2*t*thetaCuspFullSource t^2)
  have hi : Integrable g :=
    (source_times_derivative_integrable.const_mul (-2)).sub
      (integrable_thetaCutMoment.const_mul (thetaCuspLogDecaySlope x/x))
  have hp (t : ℝ) (ht : t ∈ Ioi x) : 0 < g t := by
    have ht0 : 0 < t := lt_trans hx ht
    have hq := strictMonoOn_decaySlope_div hx ht0 ht
    have hq' := (lt_div_iff₀ ht0).mp hq
    dsimp only [g]
    rw [source_deriv_eq]
    have h := mul_pos (mul_pos (by norm_num : (0:ℝ)<2)
      (sq_pos_of_pos (thetaCuspFullSource_pos_all t))) (sub_pos.mpr hq')
    nlinarith only [h]
  have hnn : ∀ᵐ t ∂volume.restrict (Ioi x), 0 ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hp t ht).le
  have hsupport : 0 < (volume.restrict (Ioi x)) (Function.support g) := by
    have hm : 0 < (volume.restrict (Ioi x)) (Ioi x) := by
      simp only [Measure.restrict_apply measurableSet_Ioi, inter_self, Real.volume_Ioi,
        ENNReal.zero_lt_top]
    exact lt_of_lt_of_le hm (measure_mono fun t ht => (hp t ht).ne')
  have hpos := (integral_pos_iff_support_of_nonneg_ae hnn hi.integrableOn).mpr hsupport
  have heq : (∫ t in Ioi x, g t) = thetaCuspFullSource x^2-
      (thetaCuspLogDecaySlope x/x)*thetaPrimeGammaCutEnergy x := by
    dsimp only [g]
    rw [integral_sub (source_times_derivative_integrable.const_mul (-2)).integrableOn
      (integrable_thetaCutMoment.const_mul (thetaCuspLogDecaySlope x/x)).integrableOn,
      integral_const_mul, integral_const_mul, source_times_derivative_tail,
      ← thetaPrimeGammaCutEnergy_eq_tail]
    ring
  rw [heq] at hpos
  linarith

/-- The source normalized by its full diagonal tail current. -/
def normalizedSource (x : ℝ) : ℝ :=
  thetaCuspFullSource x/Real.sqrt (thetaPrimeGammaCutEnergy x)

theorem normalizedSource_pos (x : ℝ) : 0 < normalizedSource x :=
  div_pos (thetaCuspFullSource_pos_all x) (Real.sqrt_pos.mpr (thetaPrimeGammaCutEnergy_pos x))

private theorem normalizedSource_neg (x : ℝ) : normalizedSource (-x) = normalizedSource x := by
  simp only [normalizedSource, thetaCuspFullSource_neg, thetaPrimeGammaCutEnergy_neg]

private theorem normalizedSource_abs (x : ℝ) : normalizedSource |x| = normalizedSource x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, normalizedSource_neg]

private theorem sqrt_cut_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t => Real.sqrt (thetaPrimeGammaCutEnergy t))
      (-x*thetaCuspFullSource x^2/Real.sqrt (thetaPrimeGammaCutEnergy x)) x := by
  convert! (Real.hasDerivAt_sqrt (thetaPrimeGammaCutEnergy_pos x).ne').comp x
    (hasDerivAt_thetaPrimeGammaCutEnergy x) using 1
  ring

private theorem normalizedSource_hasDerivAt (x : ℝ) :
    HasDerivAt normalizedSource
      (thetaCuspFullSource x*(x*thetaCuspFullSource x^2-
        thetaCuspLogDecaySlope x*thetaPrimeGammaCutEnergy x)/
        (thetaPrimeGammaCutEnergy x*Real.sqrt (thetaPrimeGammaCutEnergy x))) x := by
  have hk := thetaCuspSchwartzReal.hasDerivAt x
  change HasDerivAt thetaCuspFullSource (deriv thetaCuspFullSource x) x at hk
  rw [source_deriv_eq] at hk
  have hj := thetaPrimeGammaCutEnergy_pos x
  have hs := (Real.sqrt_pos.mpr hj).ne'
  convert! hk.div (sqrt_cut_hasDerivAt x) hs using 1
  field_simp [hs, hj.ne']
  ring_nf
  simp only [Real.sq_sqrt hj.le]

/-- The completed source's normalized diagonal tail increases on the whole positive ray. -/
theorem strictMonoOn_normalizedSource : StrictMonoOn normalizedSource (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    (fun x _ => (normalizedSource_hasDerivAt x).continuousAt.continuousWithinAt)
  intro x hx
  have hx' : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  have ht := diagonal_tail_lt_source_square hx'
  have hgap : thetaCuspLogDecaySlope x*thetaPrimeGammaCutEnergy x <
      x*thetaCuspFullSource x^2 := by
    convert! mul_lt_mul_of_pos_left ht hx' using 1
    field_simp [hx'.ne']
  rw [(normalizedSource_hasDerivAt x).deriv]
  exact div_pos (mul_pos (thetaCuspFullSource_pos_all x) (sub_pos.mpr hgap))
    (mul_pos (thetaPrimeGammaCutEnergy_pos x)
      (Real.sqrt_pos.mpr (thetaPrimeGammaCutEnergy_pos x)))

private def diagonalGap (x y s : ℝ) : ℝ :=
  Real.sqrt (thetaPrimeGammaCutEnergy (x+s))*Real.sqrt (thetaPrimeGammaCutEnergy (y+s))-
    thetaTailFirstMomentKernel (x+s) (y+s)

private theorem diagonalGap_hasDerivAt (x y s : ℝ) :
    HasDerivAt (diagonalGap x y)
      (-Real.sqrt (thetaPrimeGammaCutEnergy (x+s))*Real.sqrt (thetaPrimeGammaCutEnergy (y+s))*
        (normalizedSource (y+s)-normalizedSource (x+s))*
        ((y+s)*normalizedSource (y+s)-(x+s)*normalizedSource (x+s))) s := by
  have hx := (sqrt_cut_hasDerivAt (x+s)).comp s ((hasDerivAt_id s).const_add x)
  have hy := (sqrt_cut_hasDerivAt (y+s)).comp s ((hasDerivAt_id s).const_add y)
  convert! (hx.mul hy).sub
    (hasDerivAt_thetaTailFirstMomentKernel_commonShift s x y) using 1
  simp only [thetaTailCommonTranslationGenerator, normalizedSource, Function.comp_apply]
  field_simp [(Real.sqrt_pos.mpr (thetaPrimeGammaCutEnergy_pos (x+s))).ne',
    (Real.sqrt_pos.mpr (thetaPrimeGammaCutEnergy_pos (y+s))).ne']
  ring

private theorem diagonalGap_strictAntiOn {x y : ℝ} (hsum : 0 ≤ x+y) (hxy : x < y) :
    StrictAntiOn (diagonalGap x y) (Ici 0) := by
  have hc : Continuous (diagonalGap x y) := continuous_iff_continuousAt.mpr
    fun s => (diagonalGap_hasDerivAt x y s).continuousAt
  apply strictAntiOn_of_deriv_neg (convex_Ici 0) hc.continuousOn
  intro s hs
  have hs' : 0 < s := by simpa only [interior_Ici, mem_Ioi] using hs
  have hb : 0 < y+s := by linarith
  have hab : x+s < y+s := by linarith
  have habs : |x+s| < y+s := abs_lt.mpr ⟨by linarith, hab⟩
  have hR := strictMonoOn_normalizedSource (abs_nonneg (x+s)) hb.le habs
  rw [normalizedSource_abs] at hR
  have hprod : (x+s)*normalizedSource (x+s) < (y+s)*normalizedSource (y+s) := by
    by_cases ha : 0 ≤ x+s
    · exact (mul_le_mul_of_nonneg_left hR.le ha).trans_lt
        (mul_lt_mul_of_pos_right hab (normalizedSource_pos (y+s)))
    · exact (mul_neg_of_neg_of_pos (lt_of_not_ge ha) (normalizedSource_pos (x+s))).trans
        (mul_pos hb (normalizedSource_pos (y+s)))
  have hpos := mul_pos (mul_pos
    (mul_pos (Real.sqrt_pos.mpr (thetaPrimeGammaCutEnergy_pos (x+s)))
      (Real.sqrt_pos.mpr (thetaPrimeGammaCutEnergy_pos (y+s))))
    (sub_pos.mpr hR)) (sub_pos.mpr hprod)
  rw [(diagonalGap_hasDerivAt x y s).deriv]
  nlinarith only [hpos]

private theorem diagonalGap_limit (x y : ℝ) :
    Tendsto (diagonalGap x y) atTop (𝓝 0) := by
  have hcut (a : ℝ) := tendsto_thetaPrimeGammaCutEnergy_atTop.comp
    (tendsto_atTop_add_const_left atTop a tendsto_id)
  have hsqrt (a : ℝ) :
      Tendsto (fun s => Real.sqrt (thetaPrimeGammaCutEnergy (a+s))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def, id_eq] using
      (Real.continuous_sqrt.tendsto 0).comp (hcut a)
  have htail : Tendsto (fun s => thetaTailFirstMomentKernel (x+s) (y+s)) atTop (𝓝 0) := by
    simpa only [thetaTailFirstMomentKernel_commonShift_eq_tail, id_eq] using
      (tendsto_integral_Ioi_zero (f := thetaTailCommonTranslationIntegrand x y) tendsto_id)
  unfold diagonalGap
  simpa only [mul_zero, sub_zero] using ((hsqrt x).mul (hsqrt y)).sub htail

theorem kernel_diag_eq_cut (x : ℝ) :
    thetaTailFirstMomentKernel x x = thetaPrimeGammaCutEnergy x := by
  rw [thetaPrimeGammaCutEnergy_eq_tail]
  simpa only [thetaTailCommonTranslationIntegrand, zero_add, pow_two, mul_assoc] using
    thetaTailFirstMomentKernel_commonShift_eq_tail x 0 0

/-- Strict full-kernel comparison, with no far-tail or separation assumption. -/
theorem kernel_lt_sqrt_cut {x y : ℝ} (hsum : 0 ≤ x+y) (hxy : x < y) :
    thetaTailFirstMomentKernel x y <
      Real.sqrt (thetaPrimeGammaCutEnergy x)*Real.sqrt (thetaPrimeGammaCutEnergy y) := by
  have ha := diagonalGap_strictAntiOn hsum hxy
  have h1 : 0 ≤ diagonalGap x y 1 := by
    apply le_of_tendsto (diagonalGap_limit x y)
    filter_upwards [eventually_gt_atTop (1:ℝ)] with s hs
    exact (ha (by norm_num) (show 0 ≤ s by linarith) hs).le
  have h0 := lt_of_le_of_lt h1 (ha (by norm_num) (by norm_num) (by norm_num : (0:ℝ)<1))
  simpa only [diagonalGap, add_zero, sub_pos] using h0

/-- Every ordered pair of distinct real nodes has a strictly positive full-kernel minor. -/
theorem kernel_two_point_strict {x y : ℝ} (hxy : x < y) :
    thetaTailFirstMomentKernel x y^2 <
      thetaTailFirstMomentKernel x x*thetaTailFirstMomentKernel y y := by
  have hlt : thetaTailFirstMomentKernel x y <
      Real.sqrt (thetaPrimeGammaCutEnergy x)*Real.sqrt (thetaPrimeGammaCutEnergy y) := by
    by_cases hsum : 0 ≤ x+y
    · exact kernel_lt_sqrt_cut hsum hxy
    · have h := kernel_lt_sqrt_cut (x := -y) (y := -x) (by linarith) (by linarith)
      simpa only [thetaTailFirstMomentKernel_neg_neg, thetaTailFirstMomentKernel_comm y x,
        thetaPrimeGammaCutEnergy_neg, mul_comm] using h
  have h := mul_self_lt_mul_self (thetaTailFirstMomentKernel_nonneg x y) hlt
  rw [← sq, ← sq, mul_pow, Real.sq_sqrt (thetaPrimeGammaCutEnergy_pos x).le,
    Real.sq_sqrt (thetaPrimeGammaCutEnergy_pos y).le] at h
  simpa only [kernel_diag_eq_cut] using h

/-- Strict positivity of every two-node minor of the complete real theta tail kernel. -/
theorem kernel_two_point_det_pos {x y : ℝ} (hxy : x ≠ y) :
    0 < thetaTailFirstMomentKernel x x*thetaTailFirstMomentKernel y y-
      thetaTailFirstMomentKernel x y^2 := by
  rcases lt_or_gt_of_ne hxy with h | h
  · exact sub_pos.mpr (kernel_two_point_strict h)
  · have hp := kernel_two_point_strict h
    rw [thetaTailFirstMomentKernel_comm y x, mul_comm] at hp
    exact sub_pos.mpr hp

/-- Every real two-node packet has nonnegative complete tail energy. -/
theorem kernel_two_point_quadratic_nonneg (x y a b : ℝ) :
    0 ≤ thetaTailFirstMomentKernel x x*a^2+
      2*thetaTailFirstMomentKernel x y*a*b+thetaTailFirstMomentKernel y y*b^2 := by
  by_cases hxy : x = y
  · subst y
    have h := mul_nonneg (thetaTailFirstMomentKernel_nonneg x x) (sq_nonneg (a+b))
    nlinarith only [h]
  · have hA : 0 < thetaTailFirstMomentKernel x x := by
      rw [kernel_diag_eq_cut]
      exact thetaPrimeGammaCutEnergy_pos x
    have hdet := kernel_two_point_det_pos hxy
    have hsq := sq_nonneg (thetaTailFirstMomentKernel x x*a+thetaTailFirstMomentKernel x y*b)
    have hrest := mul_nonneg hdet.le (sq_nonneg b)
    have hprod : 0 ≤ thetaTailFirstMomentKernel x x*
        (thetaTailFirstMomentKernel x x*a^2+2*thetaTailFirstMomentKernel x y*a*b+
          thetaTailFirstMomentKernel y y*b^2) := by
      nlinarith only [hsq, hrest]
    by_contra hn
    exact (not_lt_of_ge hprod) (mul_neg_of_pos_of_neg hA (lt_of_not_ge hn))

/-- The complete kernel evaluated on any two real nodes, allowing repetitions. -/
def twoNodeMatrix (x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => thetaTailFirstMomentKernel (![x,y] i) (![x,y] j)

/-- Unconditional two-node positivity of the literal completed theta tail kernel. -/
theorem twoNodeMatrix_posSemidef (x y : ℝ) : (twoNodeMatrix x y).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, twoNodeMatrix]
    exact thetaTailFirstMomentKernel_comm _ _
  · intro v
    have h := kernel_two_point_quadratic_nonneg x y (v 0) (v 1)
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, twoNodeMatrix,
      Matrix.cons_val_zero, Matrix.cons_val_one, star_trivial,
      thetaTailFirstMomentKernel_comm y x]
    nlinarith only [h]

end RHTower.ThetaTailTwoPoint
