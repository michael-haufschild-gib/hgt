import GaloisForLFunctions.RHTower.Deninger.DeningerHigherPreimageMass
import GaloisForLFunctions.RHTower.Deninger.DeningerEvenPreimage

/-!
# The even extension of the Möbius preimage is integrable on the line

Each weighted moment of the canonical preimage is finite on the positive ray, and reflection
carries that estimate to the negative ray.  The origin is a null set, so the even extension is
integrable on the whole line, together with all its polynomial moments.

This is the `L¹` datum that turns the even extension into a tempered distribution.

* `deningerMobiusPreimage_integrableOn` : the preimage is integrable on the ray.
* `deningerEvenPreimage_moment_integrable` : **every moment of the even extension is finite.**
* `deningerEvenPreimage_integrable` : **the even extension is integrable on the line.**
-/

namespace RHTower

open MeasureTheory SchwartzMap

noncomputable section

/-- The canonical preimage is integrable on the positive ray. -/
theorem deningerMobiusPreimage_integrableOn {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) :
    IntegrableOn (deningerMobiusPreimage h) (Set.Ioi (0 : ℝ)) := by
  have hint := deningerMobiusPreimage_moment_integrable hh 0
  refine hint.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp

/-- The weighted preimage is integrable on the positive ray, at every order. -/
theorem deningerMobiusPreimagePow_integrableOn {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz)
    (r : ℕ) :
    IntegrableOn (fun x : ℝ => ((x ^ r : ℝ) : ℂ) * deningerMobiusPreimage h x)
      (Set.Ioi (0 : ℝ)) :=
  deningerMobiusPreimage_moment_integrable hh r

/-- The complement of the origin carries the whole Lebesgue measure. -/
theorem deningerCompl_zero_ae_univ : ({(0 : ℝ)}ᶜ : Set ℝ) =ᵐ[volume] Set.univ :=
  ae_eq_univ.mpr (by simp)

/-- Integrability on both open rays is integrability on the line. -/
theorem deningerIntegrable_of_rays {g : ℝ → ℂ} (hpos : IntegrableOn g (Set.Ioi (0 : ℝ)))
    (hneg : IntegrableOn g (Set.Iio (0 : ℝ))) : Integrable g := by
  have hunion : IntegrableOn g (Set.Iio (0 : ℝ) ∪ Set.Ioi (0 : ℝ)) :=
    integrableOn_union.mpr ⟨hneg, hpos⟩
  rw [Set.Iio_union_Ioi] at hunion
  have huniv : IntegrableOn g Set.univ :=
    hunion.congr_set_ae deningerCompl_zero_ae_univ.symm
  rwa [integrableOn_univ] at huniv

/-- **Every moment of the even extension is integrable on the line.** -/
theorem deningerEvenPreimage_moment_integrable {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz)
    (r : ℕ) :
    Integrable (fun x : ℝ => ((x ^ r : ℝ) : ℂ) * deningerEvenPreimage h x) := by
  have hpos : IntegrableOn (fun x : ℝ => ((x ^ r : ℝ) : ℂ) * deningerEvenPreimage h x)
      (Set.Ioi (0 : ℝ)) := by
    refine (deningerMobiusPreimagePow_integrableOn hh r).congr_fun (fun x hx => ?_)
      measurableSet_Ioi
    rw [deningerEvenPreimage_of_pos h hx]
  have hrefl : IntegrableOn
      (fun x : ℝ => ((((-x) ^ r : ℝ)) : ℂ) * deningerMobiusPreimage h (-x))
      (Set.Iio (0 : ℝ)) :=
    deningerEvenPreimage_integrableOn_Iio
      (g := fun y : ℝ => ((y ^ r : ℝ) : ℂ) * deningerMobiusPreimage h y)
      (deningerMobiusPreimagePow_integrableOn hh r)
  have hneg : IntegrableOn (fun x : ℝ => ((x ^ r : ℝ) : ℂ) * deningerEvenPreimage h x)
      (Set.Iio (0 : ℝ)) := by
    refine IntegrableOn.congr_fun (hrefl.const_mul ((-1 : ℂ) ^ r))
      (fun x hx => ?_) measurableSet_Iio
    have hx0 : x < 0 := hx
    have hsign : ((-1 : ℂ) ^ r) * ((((-x) ^ r : ℝ)) : ℂ) = ((x ^ r : ℝ) : ℂ) := by
      have h1 : ((((-x) ^ r : ℝ)) : ℂ) = ((-1 : ℂ) ^ r) * ((x ^ r : ℝ) : ℂ) := by
        push_cast
        rw [neg_pow]
      rw [h1, ← mul_assoc, ← mul_pow]
      norm_num
    rw [deningerEvenPreimage_of_neg h hx0, ← mul_assoc, hsign]
  exact deningerIntegrable_of_rays hpos hneg

/-- **The even extension is integrable on the line.** -/
theorem deningerEvenPreimage_integrable {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) :
    Integrable (deningerEvenPreimage h) := by
  have hint := deningerEvenPreimage_moment_integrable hh 0
  refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
  simp

end

end RHTower
