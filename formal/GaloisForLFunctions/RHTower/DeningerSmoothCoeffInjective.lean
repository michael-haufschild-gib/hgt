import GaloisForLFunctions.RHTower.DeningerSmoothCoeffMap

/-!
# A periodic function is determined by its Fourier coefficients

A continuous periodic function descends to the circle, where its coefficients are the interval
coefficients, and a continuous function on the circle is bounded by the sum of the moduli of its
coefficients.  If all of them vanish the function vanishes, so the coefficient map of the smooth
periodic test space is injective.

* `deningerSmoothPeriodic_eq_zero_of_coeff` : vanishing coefficients force a vanishing function.
* `deningerSmoothCoeff_injective` : **the coefficient map is injective.**
-/

namespace RHTower

section Injective

variable {T : ℝ} [Fact (0 < T)]

/-- **A continuous periodic function with vanishing Fourier coefficients vanishes.** -/
theorem deningerSmoothPeriodic_eq_zero_of_coeff {f : ℝ → ℂ} (hcont : Continuous f)
    (hper : Function.Periodic f T) (h : ∀ n : ℤ, deningerFourierCoeff T f n = 0) : f = 0 := by
  set F : C(AddCircle T, ℂ) := ⟨hper.lift, continuous_coinduced_dom.mpr hcont⟩ with hF
  have hcoe : ∀ x : ℝ, F (x : AddCircle T) = f x := fun x => hper.lift_coe x
  have hzero : ∀ n : ℤ, fourierCoeff (F : AddCircle T → ℂ) n = 0 := by
    intro n
    rw [← deningerFourierCoeff_eq_fourierCoeff]
    have hfun : (fun x : ℝ => F (x : AddCircle T)) = f := funext hcoe
    rw [hfun, h n]
  have hsummable : Summable fun n : ℤ => ‖fourierCoeff (F : AddCircle T → ℂ) n‖ := by
    have hfun : (fun n : ℤ => ‖fourierCoeff (F : AddCircle T → ℂ) n‖) = fun _ : ℤ => (0 : ℝ) := by
      funext n
      rw [hzero n, norm_zero]
    rw [hfun]
    exact summable_zero
  funext x
  have hbound := deningerFourier_sup_le F hsummable (x : AddCircle T)
  have htsum : ∑' n : ℤ, ‖fourierCoeff (F : AddCircle T → ℂ) n‖ = 0 := by
    have hfun : ∀ n : ℤ, ‖fourierCoeff (F : AddCircle T → ℂ) n‖ = 0 := by
      intro n
      rw [hzero n, norm_zero]
    rw [tsum_congr hfun, tsum_zero]
  rw [htsum] at hbound
  have hFx : F (x : AddCircle T) = 0 := norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))
  rw [← hcoe x, hFx]
  rfl

/-- **The coefficient map of the smooth periodic test space is injective.** -/
theorem deningerSmoothCoeff_injective (hT : 0 < T) :
    Function.Injective (deningerSmoothCoeff (T := T) hT) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  refine Subtype.ext ?_
  refine deningerSmoothPeriodic_eq_zero_of_coeff (deningerSmoothPeriodic_contDiff f).continuous
    (deningerSmoothPeriodic_periodic f) fun n => ?_
  have hval := congrArg
    (fun w : DeningerKotheCarrier ℂ deningerFourierWeights => (w : ℤ → ℂ) n) hf
  simpa using hval

end Injective

end RHTower
