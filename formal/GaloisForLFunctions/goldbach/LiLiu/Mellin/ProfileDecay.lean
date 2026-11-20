import GaloisForLFunctions.goldbach.LiLiu.Mellin.SignedMellin
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Mellin decay at a nonvanishing endpoint

For a smooth profile on [0,2], the factor xˢ kills the lower boundary
when Re s > 0. Three integrations by parts give three powers of vertical
decay without requiring the profile itself to vanish at zero.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Set Filter
open scoped ContDiff Topology
noncomputable section

private def truncatedMellin (f : ℝ → ℂ) (s : ℂ) :=
  ∫ x in (0:ℝ)..2, (x:ℂ)^(s-1) * f x

private theorem truncatedMellin_step (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (h2 : f 2 = 0)
    {s : ℂ} (hs : 0 < s.re) :
    s * truncatedMellin f s = -truncatedMellin (deriv f) (s+1) := by
  have hs0 : s ≠ 0 := by intro he; simp [he] at hs
  have hc : Continuous (fun x : ℝ => (x:ℂ)^s) :=
    continuous_iff_continuousAt.mpr fun x => continuousAt_ofReal_cpow_const x s (Or.inl hs)
  have hd := (contDiff_infty_iff_deriv.mp hf).1
  have hdc := (contDiff_infty_iff_deriv.mp hf).2.continuous
  have hp : IntervalIntegrable (fun x : ℝ => (x:ℂ)^(s-1)) volume 0 2 :=
    intervalIntegral.intervalIntegrable_cpow' (by simp only [Complex.sub_re, Complex.one_re]; linarith only [hs])
  have H := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0:ℝ)) (b := 2) hc.continuousOn hf.continuous.continuousOn
    (u' := fun x : ℝ => s * (x:ℂ)^(s-1)) (v' := deriv f)
    (fun x hx => hasDerivAt_ofReal_cpow_const (by simpa using hx.1.ne') hs0)
    (fun x _ => (hd x).hasDerivAt) (hp.const_mul s) (hdc.intervalIntegrable ..)
  simp only [h2, mul_zero, ofReal_zero, zero_cpow hs0, zero_mul, sub_zero, zero_sub,
    mul_assoc, intervalIntegral.integral_const_mul] at H
  simpa only [truncatedMellin, add_sub_cancel_right, neg_neg] using congrArg Neg.neg H.symm

private def profile (φ : TestWeight) (x : ℝ) : ℂ := signedProfile φ x

private theorem profile_smooth (φ : TestWeight) : ContDiff ℝ ∞ (profile φ) := by
  have hc := sumProfile_smooth φ
  exact ofRealCLM.contDiff.comp ((contDiff_const.mul (hc.comp (contDiff_const.sub contDiff_id))).sub hc)

private theorem profile_zero_above (φ : TestWeight) {x : ℝ} (hx : 3/2 < x) : profile φ x = 0 := by
  simp only [profile, signedProfile,
    sumProfile_zero φ (show 1-x ∉ Icc (2/3 : ℝ) (4/3) from fun h => by linarith only [h.1,hx]),
    sumProfile_zero φ (show x ∉ Icc (2/3 : ℝ) (4/3) from fun h => by linarith only [h.2,hx]),
    mul_zero, sub_zero, Complex.ofReal_zero]

private theorem profileMellin_eq_interval (φ : TestWeight) (s : ℂ) :
    profileMellin φ s = truncatedMellin (profile φ) s := by
  rw [profileMellin, mellin, truncatedMellin, intervalIntegral.integral_of_le (by norm_num)]
  simp_rw [smul_eq_mul]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (fun _ h => h.1)
  intro x hx
  have h2 : 2 < x := lt_of_not_ge fun h => hx.2 ⟨hx.1,h⟩
  rw [profile_zero_above φ (by linarith only [h2] : 3/2 < x), mul_zero]

/-- The cubic integration-by-parts identity includes the lower endpoint exactly. -/
theorem profileMellin_third_derivative (φ : TestWeight) {s : ℂ} (hs : 0 < s.re) :
    s*(s+1)*(s+2)*profileMellin φ s =
      -∫ x in (0:ℝ)..2, (x:ℂ)^(s+2) * iteratedDeriv 3 (profile φ) x := by
  have he : profile φ =ᶠ[𝓝 (2:ℝ)] (fun _ => 0) := by
    filter_upwards [lt_mem_nhds (by norm_num : (3/2 : ℝ)<2)] with x hx
    exact profile_zero_above φ hx
  have he1 := he.deriv
  have he2 := he1.deriv
  have hf := profile_smooth φ
  have hf1 := (contDiff_infty_iff_deriv.mp hf).2
  have hf2 := (contDiff_infty_iff_deriv.mp hf1).2
  have h0 := truncatedMellin_step _ hf he.eq_of_nhds hs
  have h1 := truncatedMellin_step _ hf1 (by simpa using he1.eq_of_nhds) (s := s+1)
    (by simpa using show 0 < s.re+1 by linarith only [hs])
  have h2 := truncatedMellin_step _ hf2 (by simpa using he2.eq_of_nhds) (s := s+2)
    (by simpa using show 0 < s.re+2 by linarith only [hs])
  rw [show s+1+1 = s+2 by ring] at h1
  rw [profileMellin_eq_interval]
  calc
    _ = (s+2) * ((s+1)*(s*truncatedMellin (profile φ) s)) := by ring
    _ = (s+2)*truncatedMellin (deriv (deriv (profile φ))) (s+2) := by rw [h0, mul_neg, h1, neg_neg]
    _ = _ := by
      rw [h2]
      simp only [truncatedMellin, iteratedDeriv_succ, iteratedDeriv_zero, add_sub_cancel_right]

/-- A common O(|t|⁻³) bound on any bounded range of positive real parts. -/
theorem profileMellin_height_bound (φ : TestWeight) {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 0 < s.re → s.re ≤ b → 1 ≤ |s.im| →
      |s.im| ^ 3 * ‖profileMellin φ s‖ ≤ C := by
  have hf := (profile_smooth φ).continuous_iteratedDeriv 3 (by simp)
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0:ℝ) 2) hf.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by norm_num))
  refine ⟨2*(2^(b+2)*M), by positivity, ?_⟩
  intro s hs hs' ht
  have hpo : 0 < (s+2).re := by simp; linarith only [hs]
  have hp (x : ℝ) (hx : x ∈ Ioc (0:ℝ) 2) : ‖(x:ℂ)^(s+2)‖ ≤ (2:ℝ)^(b+2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
    exact (Real.rpow_le_rpow hx.1.le hx.2 hpo.le).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by simpa using hs'))
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 2)
    (C := (2:ℝ)^(b+2)*M) (f := fun x : ℝ => (x:ℂ)^(s+2) * iteratedDeriv 3 (profile φ) x)
    (fun x hx => by
      rw [uIoc_of_le (by norm_num : (0:ℝ)≤2)] at hx
      rw [norm_mul]
      exact mul_le_mul (hp x hx) (hM x ⟨hx.1.le,hx.2⟩) (norm_nonneg _) (by positivity))
  have he := congrArg norm (profileMellin_third_derivative φ hs)
  simp only [norm_mul,norm_neg] at he
  have him (k : ℝ) : |s.im| ≤ ‖s+k‖ := by simpa using abs_im_le_norm (s+(k:ℂ))
  calc
    _ ≤ ‖s‖ * ‖s+1‖ * ‖s+2‖ * ‖profileMellin φ s‖ := by
      rw [pow_succ, sq]
      gcongr
      · exact abs_im_le_norm s
      · simpa using him 1
      · simpa using him 2
    _ ≤ _ := by rw [he]; simpa [mul_comm] using hI

#print axioms profileMellin_height_bound
end
end GaloisForLFunctions.Goldbach.LiLiu
