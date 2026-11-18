import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.ThetaLogMoment
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PositiveKernelLeakage
import GaloisForLFunctions.RHTower.ThetaPrimeDeletionSpectralEscape

/-!
# Logarithmic windows of a function with zero translated theta mean

A fixed deficit throughout the window cannot be paid by the tail of theta.
For a continuous function both signs give a single bounded value in the window.
-/

noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

open MeasureTheory Filter Topology _root_.RHTower
private abbrev phi := thetaCuspFullSource

/-- A zero translated mean forces the function above minus one in each late logarithmic window. -/
theorem exists_ge_neg_one_in_window_of_thetaMean_zero {G : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (habs : ∀ u, |G u| ≤ A*Real.exp (1/2*|u|))
    (hmean : ∀ t : ℝ, Integrable (fun x => phi x*G (t+x)) ∧ (∫ x, phi x*G (t+x))=0) :
    ∀ᶠ T : ℝ in atTop, ∃ u : ℝ, |u-T| ≤ 8*Real.log (T+2) ∧ -1 ≤ G u := by
  obtain ⟨C,hC,hθ⟩ := exists_theta_logarithmic_moment_bound
  let F := fun u => -G u-1
  have hF (u : ℝ) : |F u| ≤ (A+1)*Real.exp (1/2*|u|) := by
    have hh := abs_sub_le (-G u) 0 1
    simp only [sub_zero,zero_sub,abs_neg,abs_one] at hh
    dsimp only [F]
    linarith only [hh,habs u,Real.one_le_exp (show 0 ≤ 1/2*|u| by positivity)]
  have hi : Integrable phi := by
    simpa only [zero_mul,Real.exp_zero,one_mul] using HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource 0
  have hlim := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul ((A+1)*C)
  rw [mul_zero] at hlim
  filter_upwards [eventually_ge_atTop 6,eventually_ge_atTop (Real.exp 2),
    hlim.eventually_lt_const integral_thetaCuspFullSource_pos] with T hT hlate hsmall
  by_contra! hbad
  have hlog : (2:ℝ) ≤ Real.log (T+2) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) (hlate.trans (show T ≤ T+2 by linarith))
  have he (x : ℝ) : phi x*F (T+x) = -(phi x*G (T+x))-phi x := by
    dsimp only [F]; ring
  have hneg : Integrable (fun x => -(phi x*G (T+x))) := by
    simpa only [neg_one_mul] using (hmean T).1.const_mul (-1:ℝ)
  have hFi : Integrable fun x => phi x*F (T+x) := by
    simp_rw [he]
    exact hneg.sub hi
  have hlocal (x : ℝ) (hx : |x| ≤ 8*Real.log (T+2)) : -(0:ℝ) ≤ F (T+x) := by
    have h := hbad (T+x) (by simpa only [add_sub_cancel_left] using hx)
    dsimp only [F]; linarith only [h]
  have ht := positive_kernel_logarithmic_floor (A := A+1) (C := C) (b := 1/2) (D := 1/2)
    (K := 0) (B := 0) (t := T) (by positivity) hC.le (by norm_num) (by linarith only [hT])
    (by norm_num) le_rfl hT (by linarith only [hlog]) (by rw [abs_of_nonneg (by linarith only [hT] : 0 ≤ T),add_zero])
    (fun x => (thetaCuspFullSource_pos x).le) hi (HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource _)
    hFi hF (hθ _ (by linarith only [hT])) hlocal
  simp_rw [he] at ht
  rw [integral_sub hneg hi,integral_neg,(hmean T).2] at ht
  simp only [neg_zero,zero_mul,mul_zero,zero_sub] at ht
  linarith only [ht,hsmall]

/-- Every late logarithmic window contains a bounded value of a continuous
strip-bounded function annihilated by all theta translates. -/
theorem exists_abs_le_one_in_window_of_thetaMean_zero {G : ℝ → ℝ} {A : ℝ} (hG : Continuous G)
    (hA : 0 ≤ A) (h : ∀ u, |G u| ≤ A*Real.exp (1/2*|u|))
    (hmean : ∀ t : ℝ, Integrable (fun x => phi x*G (t+x)) ∧ (∫ x, phi x*G (t+x))=0) :
    ∀ᶠ T : ℝ in atTop, ∃ u : ℝ, |u-T| ≤ 8*Real.log (T+2) ∧ |G u| ≤ 1 := by
  have neg (t : ℝ) : Integrable (fun x => phi x*(-G (t+x))) ∧
      (∫ x, phi x*(-G (t+x)))=0 := by
    refine ⟨by simpa only [mul_neg] using (hmean t).1.neg,?_⟩
    simp only [mul_neg,integral_neg,(hmean t).2,neg_zero]
  have hneg := exists_ge_neg_one_in_window_of_thetaMean_zero (G := fun t => -G t) hA
    (fun t => (abs_neg _).trans_le (h t)) neg
  filter_upwards [exists_ge_neg_one_in_window_of_thetaMean_zero hA h hmean,hneg] with T ⟨a,ha,ha'⟩ ⟨b,hb,hb'⟩
  by_cases h₁ : G a ≤ 1
  · exact ⟨a,ha,abs_le.mpr ⟨ha',h₁⟩⟩
  by_cases h₂ : -1 ≤ G b
  · exact ⟨b,hb,abs_le.mpr ⟨h₂,by linarith only [hb']⟩⟩
  have hz : 0 ∈ Set.uIcc (G a) (G b) := by
    exact ⟨(min_le_right _ _).trans (by linarith only [lt_of_not_ge h₂]),
      (show 0 ≤ G a by linarith only [lt_of_not_ge h₁]).trans (le_max_left _ _)⟩
  obtain ⟨u,hu,he⟩ := intermediate_value_uIcc hG.continuousOn hz
  have hab : Set.uIcc a b ⊆ Set.Icc (T-8*Real.log (T+2)) (T+8*Real.log (T+2)) := by
    apply Set.uIcc_subset_Icc <;> constructor <;>
      linarith only [(abs_le.mp ha).1,(abs_le.mp ha).2,(abs_le.mp hb).1,(abs_le.mp hb).2]
  obtain ⟨hl,hr⟩ := hab hu
  exact ⟨u,abs_le.mpr ⟨by linarith only [hl],by linarith only [hr]⟩,by rw [he,abs_zero]; exact zero_le_one⟩

#print axioms exists_abs_le_one_in_window_of_thetaMean_zero

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
