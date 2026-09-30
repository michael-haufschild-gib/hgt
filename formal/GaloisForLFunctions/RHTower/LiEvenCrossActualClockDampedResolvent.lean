import GaloisForLFunctions.RHTower.ThetaZeroDivisionCausalKernel
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockSineSource
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The full-copy damped actual clock resolvent

The critical-strip width and actual reciprocal-square radius give the frequency bound
`|Im(alpha⁻¹)| < 1/300`. Squared-weight source mass then controls the literal sine response
by `A t exp(t/300)` on the positive half-line. This supplies absolute atom-integral interchange
for damping `p > 1/300` and identifies the complete Laplace transform with its reciprocal-square
resolvent. The source sector gives absolute convergence and a strictly positive quantitative
resolvent floor for every `p > 0`, without a zero-location hypothesis.
-/

open Complex Set MeasureTheory Filter
open scoped BigOperators


namespace RHTower
noncomputable section

/-- The actual spectral strip and radial gap bound every reciprocal transverse frequency. -/
theorem abs_im_inv_xiSpectralPoint_lt_one_div_threeHundred (q : XiZeroCopy) :
    |((xiSpectralPoint q)⁻¹).im| < (1/300:ℝ) := by
  simp only [Complex.inv_im, abs_div, abs_neg]
  rw [abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  have hs := xiSpectralPoint_im_mem_openHalf q
  have hi : |(xiSpectralPoint q).im| < (1/2:ℝ) :=
    abs_lt.mpr ⟨by linarith [hs.1], hs.2⟩
  have hrad := oneHundredFifty_lt_norm_xiSpectralPoint_sq q
  rw [div_lt_iff₀ (by positivity : 0 < ‖xiSpectralPoint q‖^2)]
  nlinarith

private theorem norm_complex_cos_le_exp_abs_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  rw [Complex.cos, norm_div, norm_ofNat]
  have h₁ : ‖Complex.exp (z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (by simpa using neg_le_abs z.im)
  have h₂ : ‖Complex.exp (-z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (by simpa using le_abs_self z.im)
  have := norm_add_le (Complex.exp (z * I)) (Complex.exp (-z * I))
  linarith

/-- Each literal sine atom has a squared-weight exponential envelope. -/
theorem norm_liEvenCrossActualClockSineAtom_le_mass_mul_exp (q : XiZeroCopy) {t : ℝ} (ht : 0 ≤ t) :
    ‖liEvenCrossActualClockSineAtom t q‖ ≤
      ‖xiZeroCopyReciprocalSquare q‖ * t * Real.exp (t/300) := by
  let w := (xiSpectralPoint q)⁻¹
  have hw : |w.im| ≤ (1/300:ℝ) := (abs_im_inv_xiSpectralPoint_lt_one_div_threeHundred q).le
  have hderiv (x : ℝ) : HasDerivAt (fun x : ℝ => Complex.sin ((x:ℂ)*w))
      (Complex.cos ((x:ℂ)*w)*w) x := by
    convert! (Complex.hasDerivAt_sin ((x:ℂ)*w)).comp x
      ((Complex.ofRealCLM.hasDerivAt (x:=x)).mul_const w) using 1; simp
  have hsin := norm_image_sub_le_of_norm_deriv_le_segment'
    (a:=0) (b:=t) (C:=‖w‖*Real.exp (t/300))
    (fun x _ => (hderiv x).hasDerivWithinAt) (by
      intro x hx
      rw [norm_mul]
      have hi : |((x:ℂ)*w).im| ≤ t/300 := by
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, add_zero, abs_mul, abs_of_nonneg hx.1]
        calc
          x * |w.im| ≤ x * (1/300) := mul_le_mul_of_nonneg_left hw hx.1
          _ ≤ t/300 := by nlinarith [hx.2.le]
      have hc := (norm_complex_cos_le_exp_abs_im ((x:ℂ)*w)).trans (Real.exp_le_exp.mpr hi)
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hc (norm_nonneg w))
    t ⟨ht,le_rfl⟩
  simp only [Complex.ofReal_zero, zero_mul, Complex.sin_zero, sub_zero] at hsin
  have hnorm : ‖xiZeroCopyReciprocalSquare q‖ = ‖w‖^2 := by
    simp [xiZeroCopyReciprocalSquare, w, norm_pow]
  rw [liEvenCrossActualClockSineAtom, norm_mul, hnorm]
  have h := mul_le_mul_of_nonneg_left hsin (norm_nonneg w)
  nlinarith

/-- Complete multiplicity-copy summation preserves the squared-weight response envelope. -/
theorem norm_liEvenCrossActualClockResponse_le_mass_mul_exp {t : ℝ} (ht : 0 ≤ t) :
    ‖liEvenCrossActualClockResponse t‖ ≤
      xiShiftAbsoluteMass 0 * t * Real.exp (t/300) := by
  rw [← Complex.norm_real, liEvenCrossActualClockResponse_ofReal_eq_tsum_sine]
  refine (norm_tsum_le_tsum_norm (summable_norm_liEvenCrossActualClockSineAtom t)).trans ?_
  have hm : Summable (fun q : XiZeroCopy => ‖xiZeroCopyReciprocalSquare q‖) := by
    simpa using summable_xiShiftAbsoluteMass 0
  calc
    ∑' q : XiZeroCopy, ‖liEvenCrossActualClockSineAtom t q‖ ≤
        ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ * t * Real.exp (t/300) :=
      (summable_norm_liEvenCrossActualClockSineAtom t).tsum_le_tsum
        (fun q => norm_liEvenCrossActualClockSineAtom_le_mass_mul_exp q ht) ((hm.mul_right t).mul_right _)
    _ = xiShiftAbsoluteMass 0 * t * Real.exp (t/300) := by
      rw [tsum_mul_right, tsum_mul_right]
      simp [xiShiftAbsoluteMass]


/-- The signed real resolvent of every actual reciprocal-square multiplicity copy. -/
def liEvenCrossActualClockDampedResolvent (p : ℝ) : ℝ :=
  (∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q /
    ((p : ℂ)^2 + xiZeroCopyReciprocalSquare q)).re

private theorem liEvenCrossActualClockDampedResolvent_denominator_norm_ge (q : XiZeroCopy) {p : ℝ} (_hp : 0 < p) :
    p^2 ≤ ‖(p : ℂ)^2 + xiZeroCopyReciprocalSquare q‖ := by
  have hre : 0 < (xiZeroCopyReciprocalSquare q).re := by
    simpa only [xiThermalNode] using xiThermalNode_pos q
  calc
    p^2 ≤ ((p : ℂ)^2 + xiZeroCopyReciprocalSquare q).re := by
      simp only [← Complex.ofReal_pow, Complex.add_re, Complex.ofReal_re]
      linarith
    _ ≤ ‖(p : ℂ)^2 + xiZeroCopyReciprocalSquare q‖ := Complex.re_le_norm _

theorem summable_liEvenCrossActualClockDampedResolvent {p : ℝ} (hp : 0 < p) :
    Summable (fun q : XiZeroCopy => xiZeroCopyReciprocalSquare q /
      ((p : ℂ)^2 + xiZeroCopyReciprocalSquare q)) := by
  have hm : Summable (fun q : XiZeroCopy => ‖xiZeroCopyReciprocalSquare q‖) := by
    simpa using summable_xiShiftAbsoluteMass 0
  apply Summable.of_norm_bounded (hm.div_const (p^2))
  intro q
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hp)
    (liEvenCrossActualClockDampedResolvent_denominator_norm_ge q hp)

private theorem liEvenCrossActualClockDampedResolvent_atom_ge_margin (q : XiZeroCopy) {p : ℝ} (hp : 0 < p) :
    (167/168:ℝ)*p^2*‖xiZeroCopyReciprocalSquare q‖ / (p^2+1/150)^2 ≤
      (xiZeroCopyReciprocalSquare q /
        ((p : ℂ)^2 + xiZeroCopyReciprocalSquare q)).re := by
  let z := xiZeroCopyReciprocalSquare q
  have hzre : (167/168:ℝ)*‖z‖ ≤ z.re := by
    have h := sectorFactor_mul_norm_xiZeroCopyReciprocalSquare_pow_le_re q 1
    norm_num at h
    exact h
  have hn : ‖z‖ ≤ (1/150:ℝ) :=
    (norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty q).le
  have hd : 0 < ‖(p : ℂ)^2+z‖ :=
    (sq_pos_of_pos hp).trans_le (liEvenCrossActualClockDampedResolvent_denominator_norm_ge q hp)
  have hdU : ‖(p : ℂ)^2+z‖^2 ≤ (p^2+1/150)^2 := by
    have hb := (norm_add_le ((p:ℂ)^2) z).trans
      (add_le_add le_rfl hn)
    simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hb
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hformula : (z / ((p : ℂ)^2+z)).re =
      (p^2*z.re+‖z‖^2)/‖(p : ℂ)^2+z‖^2 := by
    rw [Complex.div_re, Complex.normSq_eq_norm_sq]
    simp only [Complex.add_re, Complex.add_im, ← Complex.ofReal_pow,
      Complex.ofReal_re, Complex.ofReal_im, zero_add]
    rw [Complex.sq_norm z, Complex.normSq_apply z]
    ring
  change (167/168:ℝ)*p^2*‖z‖ / (p^2+1/150)^2 ≤ _
  rw [hformula, le_div_iff₀ (sq_pos_of_pos hd)]
  calc
    ((167/168:ℝ)*p^2*‖z‖ / (p^2+1/150)^2)*‖(p : ℂ)^2+z‖^2 ≤
      ((167/168:ℝ)*p^2*‖z‖ / (p^2+1/150)^2)*(p^2+1/150)^2 :=
        mul_le_mul_of_nonneg_left hdU (by positivity)
    _ = (167/168:ℝ)*p^2*‖z‖ := by
      exact div_mul_cancel₀ _ (by positivity)
    _ ≤ p^2*z.re+‖z‖^2 := by
      nlinarith [mul_le_mul_of_nonneg_left hzre (sq_nonneg p), sq_nonneg ‖z‖]

/-- The actual sector and radius give a positive full-copy resolvent floor for every positive damping. -/
theorem liEvenCrossActualClockDampedResolvent_ge_positive_margin {p : ℝ}
    (hp : 0 < p) :
    (167/168:ℝ)*p^2*xiShiftAbsoluteMass 0/(p^2+1/150)^2 ≤
      liEvenCrossActualClockDampedResolvent p := by
  have hm : Summable (fun q : XiZeroCopy => ‖xiZeroCopyReciprocalSquare q‖) := by
    simpa using summable_xiShiftAbsoluteMass 0
  have hrs := summable_liEvenCrossActualClockDampedResolvent hp
  rw [liEvenCrossActualClockDampedResolvent, Complex.re_tsum hrs]
  have hs : Summable (fun q : XiZeroCopy =>
      (167/168:ℝ)*p^2*‖xiZeroCopyReciprocalSquare q‖/(p^2+1/150)^2) :=
    (hm.mul_left ((167/168:ℝ)*p^2)).div_const _
  have h := hs.tsum_le_tsum (fun q => liEvenCrossActualClockDampedResolvent_atom_ge_margin q hp) (Complex.reCLM.summable hrs)
  simpa [tsum_div_const, tsum_mul_left, xiShiftAbsoluteMass] using h

theorem liEvenCrossActualClockDampedResolvent_pos {p : ℝ} (hp : 0 < p) :
    0 < liEvenCrossActualClockDampedResolvent p := by
  have hm := xiShiftAbsoluteMass_pos 0
  have hl : 0 < (167/168:ℝ)*p^2*xiShiftAbsoluteMass 0/(p^2+1/150)^2 := by positivity
  exact hl.trans_le (liEvenCrossActualClockDampedResolvent_ge_positive_margin hp)


private theorem integrableOn_dampedMajorant {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t*Real.exp (-c*t)) (Ioi 0) := by
  simpa only [Real.rpow_one] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (s:=1) (p:=1) (b:=c)
      (by norm_num) (by norm_num) hc

theorem norm_liEvenCrossActualClockDampedSineAtom_le (q : XiZeroCopy)
    (p : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖(Real.exp (-p*t) : ℂ) * liEvenCrossActualClockSineAtom t q‖ ≤
      ‖xiZeroCopyReciprocalSquare q‖ * t * Real.exp (-(p-1/300)*t) := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    Real.exp (-p*t)*‖liEvenCrossActualClockSineAtom t q‖ ≤
        Real.exp (-p*t)*(‖xiZeroCopyReciprocalSquare q‖*t*Real.exp (t/300)) :=
      mul_le_mul_of_nonneg_left (norm_liEvenCrossActualClockSineAtom_le_mass_mul_exp q ht) (Real.exp_pos _).le
    _ = ‖xiZeroCopyReciprocalSquare q‖*t*Real.exp (-(p-1/300)*t) := by
      rw [show Real.exp (-p*t)*(‖xiZeroCopyReciprocalSquare q‖*t*Real.exp (t/300)) =
        (‖xiZeroCopyReciprocalSquare q‖*t)*(Real.exp (-p*t)*Real.exp (t/300)) by ring,
        ← Real.exp_add]
      congr 2
      ring

theorem integrableOn_liEvenCrossActualClockDampedResponse {p : ℝ}
    (hp : 1/300 < p) :
    IntegrableOn (fun t : ℝ => Real.exp (-p*t)*liEvenCrossActualClockResponse t)
      (Ioi 0) := by
  have hmaj := (integrableOn_dampedMajorant (by linarith : 0 < p-1/300)).const_mul
    (xiShiftAbsoluteMass 0)
  refine hmaj.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioi ?_)
  · exact ((show Continuous (fun t : ℝ => Real.exp (-p*t)) by fun_prop).mul
      continuous_liEvenCrossActualClockResponse).aestronglyMeasurable
  · intro t ht
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hb := mul_le_mul_of_nonneg_left (norm_liEvenCrossActualClockResponse_le_mass_mul_exp ht.le)
      (Real.exp_pos (-p*t)).le
    refine hb.trans_eq ?_
    rw [show Real.exp (-p*t)*(xiShiftAbsoluteMass 0*t*Real.exp (t/300)) =
        xiShiftAbsoluteMass 0*(t*(Real.exp (-p*t)*Real.exp (t/300))) by ring,
      ← Real.exp_add]
    congr 3
    ring

private theorem dampedSineAtom_laplace (q : XiZeroCopy) {p : ℝ}
    (hp : 1/300 < p) :
    IntegrableOn (fun t : ℝ => (Real.exp (-p*t):ℂ)*liEvenCrossActualClockSineAtom t q)
      (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, (Real.exp (-p*t):ℂ)*liEvenCrossActualClockSineAtom t q) =
      xiZeroCopyReciprocalSquare q/((p:ℂ)^2+xiZeroCopyReciprocalSquare q) := by
  let w := (xiSpectralPoint q)⁻¹
  have hw : |w.im| < (p:ℂ).re := by
    change |((xiSpectralPoint q)⁻¹).im| < p
    exact (abs_im_inv_xiSpectralPoint_lt_one_div_threeHundred q).trans hp
  have hs : ∀ μ ∈ (sineKernel w).support, μ.re < (p:ℂ).re := by
    intro μ hμ
    have h := support_sineKernel_subset w hμ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl
    · simp only [Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, one_mul,
        zero_sub]
      linarith [neg_abs_le w.im]
    · simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, zero_mul,
        Complex.I_im, one_mul, zero_sub, neg_neg]
      linarith [le_abs_self w.im]
  have hbase := GaloisForLFunctions.HTGeometry.QuasiPolynomial.integral_eval_mul_cexp
    (sineKernel w) hs
  have heq : (fun t : ℝ => (sineKernel w).eval t*Complex.exp (-((p:ℂ)*(t:ℂ)))) =
      (fun t : ℝ => (Real.exp (-p*t):ℂ)*liEvenCrossActualClockSineAtom t q) := by
    funext t
    rw [sineKernel_eval]
    simp only [liEvenCrossActualClockSineAtom, w]
    rw [show -((p:ℂ)*(t:ℂ)) = ((-p*t:ℝ):ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
    rw [mul_comm ((xiSpectralPoint q)⁻¹) (t:ℂ)]
    ring
  rw [heq] at hbase
  refine ⟨hbase.1, ?_⟩
  rw [hbase.2, laplace_sineKernel w hw]
  rfl

theorem integrableOn_liEvenCrossActualClockDampedSineAtom (q : XiZeroCopy)
    {p : ℝ} (hp : 1/300 < p) :
    IntegrableOn (fun t : ℝ => (Real.exp (-p*t):ℂ)*liEvenCrossActualClockSineAtom t q)
      (Ioi 0) := (dampedSineAtom_laplace q hp).1

theorem liEvenCrossActualClockDampedSineAtom_integral (q : XiZeroCopy)
    {p : ℝ} (hp : 1/300 < p) :
    (∫ t : ℝ in Ioi 0, (Real.exp (-p*t):ℂ)*liEvenCrossActualClockSineAtom t q) =
      xiZeroCopyReciprocalSquare q/((p:ℂ)^2+xiZeroCopyReciprocalSquare q) :=
    (dampedSineAtom_laplace q hp).2

theorem summable_integral_norm_liEvenCrossActualClockDampedSineAtom {p : ℝ}
    (hp : 1/300 < p) :
    Summable (fun q : XiZeroCopy =>
      ∫ t : ℝ in Ioi 0, ‖(Real.exp (-p*t):ℂ)*liEvenCrossActualClockSineAtom t q‖) := by
  have hm : Summable (fun q : XiZeroCopy => ‖xiZeroCopyReciprocalSquare q‖) := by
    simpa using summable_xiShiftAbsoluteMass 0
  have hmaj := integrableOn_dampedMajorant (by linarith : 0 < p-1/300)
  apply Summable.of_nonneg_of_le
    (fun q => integral_nonneg (fun _ => norm_nonneg _))
    (fun q => ?_)
    (hm.mul_right (∫ t : ℝ in Ioi 0, t*Real.exp (-(p-1/300)*t)))
  rw [← integral_const_mul]
  exact integral_mono_ae (integrableOn_liEvenCrossActualClockDampedSineAtom q hp).norm
    (hmaj.const_mul _) (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => by simpa [mul_assoc] using
        norm_liEvenCrossActualClockDampedSineAtom_le q p ht.le))

/-- Absolute squared-weight atom-integral interchange identifies the literal damped response. -/
theorem liEvenCrossActualClockDampedResponse_integral_eq_resolvent {p : ℝ}
    (hp : 1/300 < p) :
    (∫ t : ℝ in Ioi 0, Real.exp (-p*t)*liEvenCrossActualClockResponse t) =
      liEvenCrossActualClockDampedResolvent p := by
  have hswap := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Ioi (0:ℝ)))
    (fun q : XiZeroCopy => integrableOn_liEvenCrossActualClockDampedSineAtom q hp)
    (summable_integral_norm_liEvenCrossActualClockDampedSineAtom hp)
  simp_rw [liEvenCrossActualClockDampedSineAtom_integral _ hp] at hswap
  have heq : (fun t : ℝ => ∑' q : XiZeroCopy,
      (Real.exp (-p*t):ℂ)*liEvenCrossActualClockSineAtom t q) =
      (fun t : ℝ => ((Real.exp (-p*t)*liEvenCrossActualClockResponse t:ℝ):ℂ)) := by
    funext t
    rw [tsum_mul_left, ← liEvenCrossActualClockResponse_ofReal_eq_tsum_sine,
      Complex.ofReal_mul]
  rw [heq, integral_complex_ofReal] at hswap
  have h := congrArg Complex.re hswap
  simpa [liEvenCrossActualClockDampedResolvent] using h.symm


/-- The full-copy resolvent is absolutely summable for every positive damping. -/
theorem summable_norm_liEvenCrossActualClockDampedResolvent {p : ℝ} (hp : 0 < p) :
    Summable (fun q : XiZeroCopy => ‖xiZeroCopyReciprocalSquare q /
      ((p : ℂ)^2 + xiZeroCopyReciprocalSquare q)‖) :=
  (summable_liEvenCrossActualClockDampedResolvent hp).norm

/-- Every absolutely convergent literal damped actual clock area is strictly positive. -/
theorem liEvenCrossActualClockDampedResponse_integral_pos {p : ℝ} (hp : 1/300 < p) :
    0 < (∫ t : ℝ in Ioi 0, Real.exp (-p*t)*liEvenCrossActualClockResponse t) := by
  rw [liEvenCrossActualClockDampedResponse_integral_eq_resolvent hp]
  exact liEvenCrossActualClockDampedResolvent_pos (by linarith)

end
end RHTower
