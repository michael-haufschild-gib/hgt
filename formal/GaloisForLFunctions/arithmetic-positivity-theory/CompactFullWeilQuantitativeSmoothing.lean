import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialRampFullWeilSmoothingLimit
import GaloisForLFunctions.BiScaleUncertainty.CompactLipschitzLevyEnergy

/-! Quantitative full Weil continuity under compact Lipschitz approximation.
One source L¹ error controls the Gamma, complete prime, and polar channels. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology CompactlySupported
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.WeilMarkovPole
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false


def compactSourceL1Gap (f g : C_c(ℝ, ℝ)) : ℝ := ∫ x, |f x - g x|

private theorem cross_integrable (f g : C_c(ℝ, ℝ)) (t : ℝ) :
    Integrable (fun x => f x * g (x + t)) :=
  (f.continuous.mul (g.continuous.comp (continuous_id.add_const t))).integrable_of_hasCompactSupport
    f.hasCompactSupport.mul_right

private theorem gap_integrable (f g : C_c(ℝ, ℝ)) : Integrable (fun x => |f x - g x|) :=
  ((f-g).continuous.integrable_of_hasCompactSupport (f-g).hasCompactSupport).abs

private theorem autocorr_sub_identity (f g : C_c(ℝ, ℝ)) (t : ℝ) :
    autocorr f t - autocorr g t =
      ∫ x, (f x - g x) * (f (x+t) + g (x-t)) := by
  have hs : (∫ x, g x * (f (x+t) - g (x+t))) =
      ∫ x, (f x-g x)*g (x-t) := by
    calc
      _ = ∫ x, g (x-t) * (f ((x-t)+t)-g ((x-t)+t)) :=
        (integral_sub_right_eq_self _ t).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [sub_add_cancel]
        ring
  have hi₁ : Integrable (fun x => (f x-g x)*f (x+t)) := by
    simpa only [CompactlySupportedContinuousMap.sub_apply] using cross_integrable (f-g) f t
  have hi₃ : Integrable (fun x => g x*(f (x+t)-g (x+t))) := by
    simpa only [CompactlySupportedContinuousMap.sub_apply] using cross_integrable g (f-g) t
  have hi₂ : Integrable (fun x => (f x-g x)*g (x-t)) := by
    have h := cross_integrable (f-g) g (-t)
    simp only [CompactlySupportedContinuousMap.sub_apply] at h
    exact h.congr (Filter.Eventually.of_forall fun x => by dsimp only; simp only [sub_eq_add_neg])
  unfold autocorr
  rw [← integral_sub (cross_integrable f f t) (cross_integrable g g t)]
  calc
    _ = (∫ x, (f x-g x)*f (x+t)) + ∫ x, g x*(f (x+t)-g (x+t)) := by
      rw [← integral_add hi₁ hi₃]
      apply integral_congr_ae
      filter_upwards with x
      change f x*f (x+t)-g x*g (x+t) = (f x-g x)*f (x+t)+g x*(f (x+t)-g (x+t))
      ring
    _ = _ := by
      rw [hs, ← integral_add hi₁ hi₂]
      apply integral_congr_ae
      filter_upwards with x
      ring

theorem autocorr_sub_le_L1 (f g : C_c(ℝ, ℝ)) {Mf Mg : ℝ}
    (hf : ∀ x, |f x| ≤ Mf) (hg : ∀ x, |g x| ≤ Mg) (t : ℝ) :
    |autocorr f t-autocorr g t| ≤ (Mf+Mg)*compactSourceL1Gap f g := by
  rw [autocorr_sub_identity]
  have h := norm_integral_le_of_norm_le ((gap_integrable f g).mul_const (Mf+Mg))
    (f := fun x => (f x-g x)*(f (x+t)+g (x-t))) ?_
  · simp only [integral_mul_const] at h
    simpa only [Real.norm_eq_abs, compactSourceL1Gap, mul_comm] using h
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left
      ((abs_add_le _ _).trans (add_le_add (hf _) (hg _))) (abs_nonneg _)

private theorem autocorr_increment_sub_identity (f g : C_c(ℝ, ℝ)) (t : ℝ) :
    (autocorr f 0-autocorr f t)-(autocorr g 0-autocorr g t) =
      ∫ x, (f x-g x)*((f x-f (x+t))+(g x-g (x-t))) := by
  have hi (s : ℝ) : Integrable (fun x => (f x-g x)*(f (x+s)+g (x-s))) := by
    have h := (cross_integrable (f-g) f s).add (cross_integrable (f-g) g (-s))
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, CompactlySupportedContinuousMap.sub_apply]
    rw [sub_eq_add_neg]
    ring
  rw [show (autocorr f 0-autocorr f t)-(autocorr g 0-autocorr g t) =
    (autocorr f 0-autocorr g 0)-(autocorr f t-autocorr g t) by ring,
    autocorr_sub_identity, autocorr_sub_identity, ← integral_sub (hi 0) (hi t)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [add_zero, sub_zero]
  ring

theorem autocorr_increment_sub_le_L1 (f g : C_c(ℝ, ℝ)) {Kf Kg : ℝ}
    (hf : ∀ x y, |f x-f y| ≤ Kf*|x-y|)
    (hg : ∀ x y, |g x-g y| ≤ Kg*|x-y|) (t : ℝ) :
    |(autocorr f 0-autocorr f t)-(autocorr g 0-autocorr g t)| ≤
      (Kf+Kg)*compactSourceL1Gap f g*|t| := by
  rw [autocorr_increment_sub_identity]
  have h := norm_integral_le_of_norm_le ((gap_integrable f g).mul_const ((Kf+Kg)*|t|))
    (f := fun x => (f x-g x)*((f x-f (x+t))+(g x-g (x-t)))) ?_
  · simp only [integral_mul_const] at h
    simpa only [Real.norm_eq_abs, compactSourceL1Gap, mul_comm, mul_left_comm, mul_assoc] using h
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have hf' : |f x-f (x+t)| ≤ Kf*|t| := by
      simpa only [show x-(x+t) = -t by ring, abs_neg] using hf x (x+t)
    have hg' : |g x-g (x-t)| ≤ Kg*|t| := by
      simpa only [show x-(x-t) = t by ring] using hg x (x-t)
    exact (abs_add_le _ _).trans ((add_le_add hf' hg').trans_eq (by ring))

theorem biScaleLevyEnergy_sub_le_L1 (f g : C_c(ℝ, ℝ)) {Kf Kg : ℝ}
    (hf : ∀ x y, |f x-f y| ≤ Kf*|x-y|)
    (hg : ∀ x y, |g x-g y| ≤ Kg*|x-y|) :
    |biScaleLevyEnergy f-biScaleLevyEnergy g| ≤
      (Kf+Kg)*compactSourceL1Gap f g*archWeightFirstMoment := by
  have hfi := integrableOn_levy_of_lipschitz f hf
  have hgi := integrableOn_levy_of_lipschitz g hg
  unfold biScaleLevyEnergy
  rw [← integral_sub hfi hgi]
  have hi := norm_integral_le_of_norm_le
    (integrableOn_mul_archLevySinhWeight.const_mul ((Kf+Kg)*compactSourceL1Gap f g))
    (f := fun t => (autocorr f 0-autocorr f t)*archLevySinhWeight t -
      (autocorr g 0-autocorr g t)*archLevySinhWeight t) ?_
  · simpa only [Real.norm_eq_abs, integral_const_mul, archWeightFirstMoment] using hi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [← sub_mul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (archLevySinhWeight_pos ht).le]
    have h := mul_le_mul_of_nonneg_right (autocorr_increment_sub_le_L1 f g hf hg t)
      (archLevySinhWeight_pos ht).le
    simpa only [abs_of_pos (show 0 < t from ht), mul_assoc] using h

theorem fullPairing_autocorr_sub_le_L1 (f g : C_c(ℝ, ℝ)) {Mf Mg : ℝ}
    (hf : ∀ x, |f x| ≤ Mf) (hg : ∀ x, |g x| ≤ Mg) (N : ℕ)
    (hft : ∀ x, SignedPrimePolar.cutoff N ≤ x → autocorr f x = 0)
    (hgt : ∀ x, SignedPrimePolar.cutoff N ≤ x → autocorr g x = 0) :
    |fullPairing (autocorr f)-fullPairing (autocorr g)| ≤
      mass N*((Mf+Mg)*compactSourceL1Gap f g) := by
  have he : pairing N (fun x => autocorr f x-autocorr g x) =
      pairing N (autocorr f)-pairing N (autocorr g) := by
    have hfi : IntegrableOn (fun x => polarDensity x*autocorr f x) (Icc 0 (SignedPrimePolar.cutoff N)) :=
      (continuous_polarDensity.mul (continuous_autocorr_compact f)).integrableOn_Icc
    have hgi : IntegrableOn (fun x => polarDensity x*autocorr g x) (Icc 0 (SignedPrimePolar.cutoff N)) :=
      (continuous_polarDensity.mul (continuous_autocorr_compact g)).integrableOn_Icc
    simp only [pairing, mul_sub, Finset.sum_sub_distrib, integral_sub hfi hgi]
    ring
  rw [fullPairing_eq_pairing_of_tail _ N hft, fullPairing_eq_pairing_of_tail _ N hgt, ← he]
  exact abs_pairing_le_mass_mul N _ _ (autocorr_sub_le_L1 f g hf hg)

def compactFullWeilEnergy (f : C_c(ℝ, ℝ)) : ℝ :=
  (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (EF.weilTest (fun x => (f x : ℂ)) (fun x => (f x : ℂ)))).re

/-- Every signed channel is controlled by the same physical source error. -/
theorem compactFullWeilEnergy_sub_le_L1 (f g : C_c(ℝ, ℝ)) {Mf Mg Kf Kg : ℝ}
    (hf : ∀ x, |f x| ≤ Mf) (hg : ∀ x, |g x| ≤ Mg)
    (hfL : ∀ x y, |f x-f y| ≤ Kf*|x-y|)
    (hgL : ∀ x y, |g x-g y| ≤ Kg*|x-y|) (N : ℕ)
    (hft : ∀ x, SignedPrimePolar.cutoff N ≤ x → autocorr f x = 0)
    (hgt : ∀ x, SignedPrimePolar.cutoff N ≤ x → autocorr g x = 0) :
    |compactFullWeilEnergy f-compactFullWeilEnergy g| ≤
      compactSourceL1Gap f g*((Mf+Mg)*(|EF.gammaBracket 0|+2*mass N)+
        (Kf+Kg)*archWeightFirstMoment) := by
  have hmass := autocorr_sub_le_L1 f g hf hg 0
  have hJ := biScaleLevyEnergy_sub_le_L1 f g hfL hgL
  have hP := fullPairing_autocorr_sub_le_L1 f g hf hg N hft hgt
  unfold compactFullWeilEnergy
  rw [re_weilFullFunctional_eq_of_compact_finite_jump f (integrableOn_levy_of_lipschitz f hfL),
    re_weilFullFunctional_eq_of_compact_finite_jump g (integrableOn_levy_of_lipschitz g hgL)]
  have he : EF.gammaBracket 0*autocorr f 0+biScaleLevyEnergy f-2*fullPairing (autocorr f) -
      (EF.gammaBracket 0*autocorr g 0+biScaleLevyEnergy g-2*fullPairing (autocorr g)) =
      EF.gammaBracket 0*(autocorr f 0-autocorr g 0)+(biScaleLevyEnergy f-biScaleLevyEnergy g)-
        2*(fullPairing (autocorr f)-fullPairing (autocorr g)) := by ring
  rw [he]
  calc
    _ ≤ |EF.gammaBracket 0*(autocorr f 0-autocorr g 0)|+
        |biScaleLevyEnergy f-biScaleLevyEnergy g|+
        |2*(fullPairing (autocorr f)-fullPairing (autocorr g))| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |EF.gammaBracket 0| *((Mf+Mg)*compactSourceL1Gap f g)+
        (Kf+Kg)*compactSourceL1Gap f g*archWeightFirstMoment+
        2*(mass N*((Mf+Mg)*compactSourceL1Gap f g)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hmass (abs_nonneg _)) hJ)
        (mul_le_mul_of_nonneg_left hP (by norm_num))
    _ = _ := by ring


open _root_.RHTower.CHMDDoobGraph


private theorem smooth_lipschitz_bound (f : C_c(ℝ, ℝ)) {M K : ℝ}
    (hM : ∀ x, |f x| ≤ M) (hK : ∀ x y, |f x-f y| ≤ K*|x-y|)
    (k : ℕ) (x y : ℝ) : |smooth f k x-smooth f k y| ≤ K*|x-y| := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hK0 : 0 ≤ K := by simpa using (abs_nonneg _).trans (hK 1 0)
  have he := difference_smooth (v := (f : ℝ → ℝ)) f.continuous.measurable hM0 hM k (y-x) x
  rw [show x+(y-x) = y by ring] at he
  rw [he]
  exact smooth_bound (mul_nonneg hK0 (abs_nonneg _))
    (fun z => by simpa only [show z-(z+(y-x)) = x-y by ring] using hK z (z+(y-x))) k x

private theorem smooth_sub_le_radius (f : C_c(ℝ, ℝ)) {M K : ℝ}
    (hM : ∀ x, |f x| ≤ M) (hK : ∀ x y, |f x-f y| ≤ K*|x-y|)
    (k : ℕ) (x : ℝ) :
    |smooth f k x-f x| ≤ K*(WeilOneSided.narrowBump k).rOut := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hK0 : 0 ≤ K := by simpa using (abs_nonneg _).trans (hK 1 0)
  have he : smooth f k x-f x = ∫ y, CHMDDoobGraph.mollifier k y*(f (x-y)-f x) := by
    change (∫ y, CHMDDoobGraph.mollifier k y*f (x-y))-f x = _
    have hc : (∫ y, CHMDDoobGraph.mollifier k y*f x) = f x := by
      rw [integral_mul_const, mollifier_integral, one_mul]
    calc
      _ = (∫ y, CHMDDoobGraph.mollifier k y*f (x-y))-(∫ y, CHMDDoobGraph.mollifier k y*f x) := by rw [hc]
      _ = _ := by
        rw [← integral_sub (integrable_mollifier_mul (v := (f : ℝ → ℝ)) f.continuous.measurable hM0 hM k x)
          ((mollifier_integrable k).mul_const (f x))]
        apply integral_congr_ae
        filter_upwards with y
        ring
  rw [he]
  have hb : ∀ y, ‖CHMDDoobGraph.mollifier k y*(f (x-y)-f x)‖ ≤
      CHMDDoobGraph.mollifier k y*(K*(WeilOneSided.narrowBump k).rOut) := by
    intro y
    by_cases hy : CHMDDoobGraph.mollifier k y = 0
    · simp [hy]
    have hyr : |y| ≤ (WeilOneSided.narrowBump k).rOut := by
      have hm : y ∈ Function.support (CHMDDoobGraph.mollifier k) := hy
      rw [CHMDDoobGraph.mollifier, ContDiffBump.support_normed_eq, Metric.mem_ball,
        dist_zero_right, Real.norm_eq_abs] at hm
      exact hm.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mollifier_nonneg k y)]
    apply mul_le_mul_of_nonneg_left _ (mollifier_nonneg k y)
    have hd : |f (x-y)-f x| ≤ K*|y| := by
      simpa only [show x-y-x = -y by ring, abs_neg] using hK (x-y) x
    exact hd.trans (mul_le_mul_of_nonneg_left hyr hK0)
  have h := norm_integral_le_of_norm_le
    ((mollifier_integrable k).mul_const (K*(WeilOneSided.narrowBump k).rOut))
    (Filter.Eventually.of_forall hb)
  simpa only [Real.norm_eq_abs, integral_mul_const, mollifier_integral, one_mul] using h

private theorem smooth_source_L1Gap_le (f : C_c(ℝ, ℝ)) {M K R : ℝ}
    (hM : ∀ x, |f x| ≤ M) (hK : ∀ x y, |f x-f y| ≤ K*|x-y|)
    (hR0 : 0 ≤ R) (hR : ∀ x, R < |x| → f x = 0) (k : ℕ) :
    compactSourceL1Gap (smoothCompactSource f k) f ≤
      2*(R+1)*K*(WeilOneSided.narrowBump k).rOut := by
  have ht : (∫ x in Icc (-(R+1)) (R+1), |smooth f k x-f x|) =
      compactSourceL1Gap (smoothCompactSource f k) f := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxa : R+1 < |x| := not_le.mp fun h => hx (abs_le.mp h)
    rw [smooth_eq_zero_of_far hR k hxa, hR x (by linarith), sub_self, abs_zero]
  rw [← ht]
  calc
    _ ≤ ∫ x in Icc (-(R+1)) (R+1), K*(WeilOneSided.narrowBump k).rOut := by
      apply setIntegral_mono_on (gap_integrable (smoothCompactSource f k) f).integrableOn
        (integrableOn_const (by simp)) measurableSet_Icc
      intro x _
      exact smooth_sub_le_radius f hM hK k x
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : -(R+1) ≤ R+1), intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

/-- A finite prime aperture covering the complete autocorrelation. -/
def compactFullWeilPrimeCutoff (R : ℝ) : ℕ := ⌈Real.exp (2*(R+1)+1)⌉₊

private theorem compactFullWeilPrimeCutoff_large (R : ℝ) :
    2*(R+1) < SignedPrimePolar.cutoff (compactFullWeilPrimeCutoff R) := by
  have he : Real.exp (2*(R+1)+1) ≤ (compactFullWeilPrimeCutoff R : ℝ) := Nat.le_ceil _
  have he' : Real.exp (2*(R+1)+1) ≤ ((compactFullWeilPrimeCutoff R+2 : ℕ) : ℝ) := by
    push_cast
    linarith
  have h := Real.log_le_log (Real.exp_pos _) he'
  rw [Real.log_exp] at h
  exact lt_of_lt_of_le (by linarith) h

/-- Explicit dependence on value, slope, and aperture. The prime–polar mass is literal. -/
def compactFullWeilApproximationCost (R M K : ℝ) : ℝ :=
  (R+1)*K*(M*(|EF.gammaBracket 0|+2*mass (compactFullWeilPrimeCutoff R))+
    K*archWeightFirstMoment)

theorem compactFullWeilEnergy_smoothing_error (f : C_c(ℝ, ℝ)) {M K R : ℝ}
    (hM : ∀ x, |f x| ≤ M) (hK : ∀ x y, |f x-f y| ≤ K*|x-y|)
    (hR0 : 0 ≤ R) (hR : ∀ x, R < |x| → f x = 0) (k : ℕ) :
    |compactFullWeilEnergy (smoothCompactSource f k)-compactFullWeilEnergy f| ≤
      compactFullWeilApproximationCost R M K/((k : ℝ)+1) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hK0 : 0 ≤ K := by simpa using (abs_nonneg _).trans (hK 1 0)
  let N := compactFullWeilPrimeCutoff R
  have hcut : 2*(R+1) < SignedPrimePolar.cutoff N := compactFullWeilPrimeCutoff_large R
  have hft : ∀ x, SignedPrimePolar.cutoff N ≤ x → autocorr (smoothCompactSource f k) x = 0 := by
    intro x hx
    exact autocorr_eq_zero_of_far (fun x hx => smooth_eq_zero_of_far hR k hx)
      (hcut.trans_le (hx.trans (le_abs_self _)))
  have hgt : ∀ x, SignedPrimePolar.cutoff N ≤ x → autocorr f x = 0 := by
    intro x hx
    exact autocorr_eq_zero_of_far hR
      ((show 2*R < 2*(R+1) by linarith).trans (hcut.trans_le (hx.trans (le_abs_self _))))
  have h := compactFullWeilEnergy_sub_le_L1 (smoothCompactSource f k) f
    (smooth_bound hM0 hM k) hM (smooth_lipschitz_bound f hM hK k) hK N hft hgt
  have hfactor : 0 ≤ (M+M)*(|EF.gammaBracket 0|+2*mass N)+(K+K)*archWeightFirstMoment := by
    exact add_nonneg (mul_nonneg (by positivity)
      (add_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) (mass_nonneg N))))
      (mul_nonneg (by positivity) archWeightFirstMoment_nonneg)
  refine h.trans ((mul_le_mul_of_nonneg_right (smooth_source_L1Gap_le f hM hK hR0 hR k)
    hfactor).trans_eq ?_)
  change 2*(R+1)*K*(1/(4*((k : ℝ)+1)))*
    ((M+M)*(|EF.gammaBracket 0|+2*mass N)+(K+K)*archWeightFirstMoment) = _
  dsimp [compactFullWeilApproximationCost, N]
  field_simp
  ring

end GaloisForLFunctions.ArithmeticPositivityTheory
