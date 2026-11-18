import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheLogarithmicLocationsOfThePrimeMassBins
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePrimeNumberTheoremOnTheState
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheFirstAbsoluteMomentOfStateIncrements

/-!
# Integrated error of the prime-square layer

A displacement of a Chebyshev mass bin costs the translation modulus of the
profile in the time integral. The reciprocal weight costs its first absolute
moment. Both errors are integrable on the logarithmic mass axis.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry

private def translationCost (g : ℝ → ℝ) (d : ℝ) : ℝ := ∫ u : ℝ, |g u-g (u+d)|

private theorem translationCost_neg (g : ℝ → ℝ) (d : ℝ) :
    translationCost g (-d) = translationCost g d := by
  change (∫ u, |g u-g (u+-d)|) = _
  rw [← integral_add_right_eq_self (fun u : ℝ => |g u-g (u+-d)|) d]
  simp only [add_neg_cancel_right,translationCost]
  exact integral_congr_ae (Eventually.of_forall fun u => abs_sub_comm _ _)

private theorem state_translationCost {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (he : F =ᵐ[volume] Φ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ d : ℝ, |d| < ε → translationCost Φ d ≤ Real.sqrt |d| := by
  have eq (d : ℝ) : translationCost F d = translationCost Φ d := by
    apply integral_congr_ae
    filter_upwards [he,(measurePreserving_add_right volume d).quasiMeasurePreserving.ae_eq_comp he]
      with u hu hv
    change F (u+d) = Φ (u+d) at hv
    rw [hu,hv]
  obtain ⟨ε,hε,h⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    ((criticalState_tendsto_L1_increment_div_sqrt hW ht hF).eventually_lt_const zero_lt_one)
  refine ⟨ε,hε,fun d hd => ?_⟩
  by_cases hz : d=0
  · simp [translationCost,hz]
  have hp := abs_pos.mpr hz
  have hc := (div_lt_iff₀ (Real.sqrt_pos.mpr hp)).mp (h ⟨hp,hd⟩)
  rw [one_mul] at hc
  have ha : translationCost Φ d = translationCost F |d| := by
    rw [eq]
    rcases le_or_gt 0 d with hd | hd
    · rw [abs_of_nonneg hd]
    · rw [abs_of_neg hd,translationCost_neg]
  exact ha.le.trans hc.le

private theorem bin_slice_bound {g : ℝ → ℝ} (hg : Integrable g) (v l w : ℝ) :
    (∫ t : ℝ, |w*g (t-l)-g (t-v)|) ≤
      |w-1|*(∫ u, |g u|)+translationCost g (l-v) := by
  have h1 : Integrable (fun t : ℝ => g (t-l)) := hg.comp_sub_right l
  have h2 : Integrable (fun t : ℝ => g (t-v)) := hg.comp_sub_right v
  have h := integral_mono ((h1.const_mul w).sub h2).abs
    ((h1.abs.const_mul |w-1|).add (h1.sub h2).abs) (fun t => by
      change |w*g (t-l)-g (t-v)| ≤ |w-1|*|g (t-l)|+|g (t-l)-g (t-v)|
      rw [← abs_mul,show w*g (t-l)-g (t-v)=(w-1)*g (t-l)+(g (t-l)-g (t-v)) by ring]
      exact abs_add_le ..)
  refine h.trans_eq ?_
  change (∫ t : ℝ, |w-1|*|g (t-l)|+|g (t-l)-g (t-v)|) = _
  rw [integral_add (h1.abs.const_mul _) (h1.sub h2).abs,integral_const_mul]
  have tr (f : ℝ → ℝ) : (∫ t : ℝ, f (t-l)) = ∫ t, f t := by
    simpa only [sub_eq_add_neg] using integral_add_right_eq_self f (-l)
  rw [tr (fun t => |g t|)]
  congr 1
  change _ = ∫ u : ℝ, |g u-g (u+(l-v))|
  rw [← tr (fun u => |g u-g (u+(l-v))|)]
  exact integral_congr_ae (Eventually.of_forall fun t => by rw [show t-l+(l-v)=t-v by ring])

private theorem squareLayer_mass_coordinates {g : ℝ → ℝ} (hg : Continuous g)
    (hs : ∀ u, 0 ≤ u → g u=0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |g u| ≤ C*Real.exp (2*u))
    {t : ℝ} (ht : 0 ≤ t) :
    primePowerLayer g 2 t = (∫ v, squareBinWeight v*g (t-squareBinLocation v))/2 := by
  let f := fun v : ℝ => squareBinWeight v*g (t-squareBinLocation v)
  rw [primeSquareLayer_eq_bin_integral hg hs hC hb ht]
  calc _ = ∫ r : ℝ, f (2*r) := by
             refine integral_congr_ae (Eventually.of_forall fun r => ?_)
             simp only [f,squareBinWeight,squareBinLocation,show 2*r/2=r by ring]
    _ = _ := by
             rw [Measure.integral_comp_mul_left,smul_eq_mul,abs_of_pos (by norm_num : (0:ℝ)<2⁻¹)]
             ring

end GaloisForLFunctions.ExclusionOfTheCriticalState
