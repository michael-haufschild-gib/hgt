import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.FractionalFourierEnergyFromSquareIncrements
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheModulusOfContinuityOfTheStateIsCarriedByTheWall
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateDecaysPastTheBarrierAtTheRateOfTheZeros

/-!
# Fractional Fourier energy of the tilted critical state

The wall modulus bounds square increments linearly in the lag. Multiplication
by a bounded Lipschitz tilt preserves that bound and hence every fractional
Fourier energy strictly below half a derivative.
-/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped FourierTransform
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory

private theorem critical_increments_le_linear {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) : ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, 0 < h →
      (∫ u : ℝ, (F u-F (u+h))^2) ≤ K*h := by
  let L := 8*criticalAliasCoefficient W₀*(∫ u, F u^2*Real.exp (-(8*u)))+1
  have hL : 0 ≤ L := by
    have ha := criticalAliasCoefficient_positive hW
    have hm := criticalState_exponentialMass_pos hW hF
    dsimp only [L]; positivity
  have hl : Tendsto (fun h : ℝ => Real.log (1/h)) (𝓝[>] 0) atTop := by
    simpa only [one_div,Function.comp_def] using Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have he : ∀ᶠ h : ℝ in 𝓝[>] 0, (∫ u, (F u-F (u+h))^2) ≤ L*h := by
    filter_upwards [criticalState_eventually_log_mul_sq_increment_le hW ht hF zero_lt_one,
      hl.eventually_ge_atTop 1] with h hu hv
    exact (le_mul_of_one_le_left (integral_nonneg fun _ => sq_nonneg _) hv).trans hu
  obtain ⟨r,hr,hloc⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 he
  refine ⟨L+4/r,by positivity,fun h hh => ?_⟩
  by_cases hhr : h < r
  · exact (hloc (show h ∈ Ioo 0 r from ⟨hh,hhr⟩)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hh.le)
  have hhi := hF.2.2.1
  have hsum := (hhi.const_mul 2).add ((hhi.comp_add_right h).const_mul 2)
  have hbound : (∫ u, (F u-F (u+h))^2) ≤ 4 := by
    calc _ ≤ ∫ u, (2*(F u)^2+2*(F (u+h))^2) := by
             apply integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) hsum
             exact Eventually.of_forall fun u => by nlinarith only [sq_nonneg (F u+F (u+h))]
      _ = _ := by rw [integral_add (hhi.const_mul 2) ((hhi.comp_add_right h).const_mul 2),
                    integral_const_mul,integral_const_mul,integral_add_right_eq_self (fun u => F u^2),
                    hF.2.2.2.1]; norm_num
  have hrh : 4 ≤ (4/r)*h := by
    rw [div_mul_eq_mul_div,le_div_iff₀ hr]; linarith only [le_of_not_gt hhr]
  exact hbound.trans (by rw [add_mul]; linarith only [hrh,mul_nonneg hL hh.le])

/-- The square-increment bound survives every nonnegative exponential tilt of
a half-line profile. -/
private theorem square_increment_of_tilt {F : ℝ → ℝ} (hd : CriticalHalfLineEnergyDomain F)
    (hunit : (∫ u, F u^2)=1) {K : ℝ} (hK : ∀ h : ℝ, 0<h → (∫ u, (F u-F (u+h))^2) ≤ K*h)
    {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    (∫ u, (Real.exp (β*u)*F u-Real.exp (β*(u+h))*F (u+h))^2) ≤ (2*K+2*β^2)*h := by
  let w := fun u : ℝ => Real.exp (β*min u 0)
  have hnon (u : ℝ) : β*min u 0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ (min_le_right _ _)
  have hclip (u : ℝ) : Real.exp (β*u)*F u=w u*F u := by
    rcases le_total u 0 with hu | hu
    · simp only [w,min_eq_left hu]
    · simp only [hd.support _ hu,mul_zero]
  have hw (u : ℝ) : |w u| ≤ 1 := (abs_of_pos (Real.exp_pos _)).trans_le (Real.exp_le_one_iff.2 (hnon u))
  have hdiff (u : ℝ) : |w u-w (u+h)| ≤ β*h := by
    have hx := abs_exp_sub_exp_le (hnon u) (hnon (u+h))
    rw [Real.exp_zero,one_mul,← mul_sub,abs_mul,abs_of_nonneg hβ] at hx
    apply hx.trans (mul_le_mul_of_nonneg_left _ hβ)
    have hm := abs_min_sub_min_le_max u 0 (u+h) 0
    simpa only [sub_self,abs_zero,max_eq_left (abs_nonneg _),show u-(u+h)=-h by ring,abs_neg,abs_of_pos hh] using hm
  have hpoint (u : ℝ) :
      (Real.exp (β*u)*F u-Real.exp (β*(u+h))*F (u+h))^2 ≤
      2*(F u-F (u+h))^2+2*(β*h)^2*(F (u+h))^2 := by
    rw [hclip,hclip,show w u*F u-w (u+h)*F (u+h) =
      w u*(F u-F (u+h))+(w u-w (u+h))*F (u+h) by ring]
    have ha := pow_le_pow_left₀ (abs_nonneg _) (hw u) 2
    have hb := pow_le_pow_left₀ (abs_nonneg _) (hdiff u) 2
    simp only [sq_abs,one_pow] at ha hb
    have hA := mul_le_mul_of_nonneg_right ha (sq_nonneg (F u-F (u+h)))
    have hB := mul_le_mul_of_nonneg_right hb (sq_nonneg (F (u+h)))
    nlinarith only [hA,hB,sq_nonneg (w u*(F u-F (u+h))-(w u-w (u+h))*F (u+h))]
  have hI := integrable_sq_increment hd hh.le
  have hT := hd.sq.comp_add_right h
  calc _ ≤ ∫ u, (2*(F u-F (u+h))^2+2*(β*h)^2*(F (u+h))^2) :=
           integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
             ((hI.const_mul 2).add (hT.const_mul _)) (Eventually.of_forall hpoint)
    _ ≤ _ := by
             rw [integral_add (hI.const_mul 2) (hT.const_mul _),integral_const_mul,integral_const_mul,
               integral_add_right_eq_self (fun u => F u^2),hunit,mul_one]
             have hsq : h^2 ≤ h := by nlinarith only [mul_nonneg hh.le (sub_nonneg.2 hh1)]
             nlinarith only [hK h hh,mul_le_mul_of_nonneg_left hsq (sq_nonneg β)]

/-- Every continuous representative of the actual state has a tilted Fourier
density integrable against |ξ|ˢ for every 0 ≤ s < 1. -/
theorem criticalState_tilted_fractional_fourier_energy {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (he : F =ᵐ[volume] Φ)
    {β s : ℝ} (hβ : 0 ≤ β) (hs : 0 ≤ s) (hs1 : s < 1) :
    Integrable fun ξ : ℝ => |ξ|^s*‖𝓕 (fun u : ℝ => ((Real.exp (β*u)*Φ u:ℝ):ℂ)) ξ‖^2 := by
  let f := fun u : ℝ => Real.exp (β*u)*F u
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hclip : f = (fun u : ℝ => Real.exp (β*min u 0)*F u) := by
    funext u
    rcases le_total u 0 with hu | hu
    · simp [f,min_eq_left hu]
    · simp [f,hd.support u hu]
  have hfd : CriticalHalfLineEnergyDomain f := by
    rw [hclip]; exact criticalHalfLineEnergyDomain_exp_min_mul hd hβ
  have hi : Integrable (fun u => (f u:ℂ)) := hfd.integrable.ofReal
  have h2 : MemLp (fun u => (f u:ℂ)) 2 := (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).2
    (by simpa only [Complex.norm_real,Real.norm_eq_abs,sq_abs] using hfd.sq)
  obtain ⟨K,hK,hbound⟩ := critical_increments_le_linear hW ht hF
  have hinc (h : ℝ) (hh : 0<h) (hh1 : h≤1) :
      (∫ u, ‖(f u:ℂ)-(f (u+h):ℂ)‖^2) ≤ (2*K+2*β^2)*h := by
    simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs,f] using
      square_increment_of_tilt hd hF.2.2.2.1 hbound hβ hh hh1
  have h := integrable_fractional_fourier_energy_of_square_increments hi h2 (by positivity) hinc hs hs1
  have hrep : (fun u : ℝ => (f u:ℂ)) =ᵐ[volume] (fun u : ℝ => ((Real.exp (β*u)*Φ u:ℝ):ℂ)) :=
    he.mono fun u hu => by simp [f,hu]
  exact h.congr (Eventually.of_forall fun ξ => by rw [Real.fourier_congr_ae hrep ξ])

#print axioms criticalState_tilted_fractional_fourier_energy
end GaloisForLFunctions.ExclusionOfTheCriticalState
