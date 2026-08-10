import GaloisForLFunctions.RHTower.DeningerPreimageZeroMass

/-!
# The even extension of the canonical Möbius preimage

The commutator of the card is built from the *even* extension `E f_h` of the ray preimage.  Taking
the absolute value of the argument is the extension, and evenness is then definitional.

Reflection of the line carries the negative ray onto the positive one, so the extension inherits
the ray estimates: its mass on each half is the ray mass, which is zero.

* `deningerEvenPreimage` : the even extension `E f_h`.
* `deningerEvenPreimage_even` : it is even.
* `deningerEvenPreimage_of_pos` : on the positive ray it is the preimage itself.
* `deningerEvenPreimage_integrableOn_Iio` : reflection transports integrability to the negative ray.
-/

namespace RHTower

open MeasureTheory SchwartzMap

noncomputable section

/-- **The even extension of the canonical Möbius preimage.** -/
def deningerEvenPreimage (h : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ := deningerMobiusPreimage h |x|

@[simp]
theorem deningerEvenPreimage_even (h : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deningerEvenPreimage h (-x) = deningerEvenPreimage h x := by
  rw [deningerEvenPreimage, deningerEvenPreimage, abs_neg]

theorem deningerEvenPreimage_of_pos (h : 𝓢(ℝ, ℂ)) {x : ℝ} (hx : 0 < x) :
    deningerEvenPreimage h x = deningerMobiusPreimage h x := by
  rw [deningerEvenPreimage, abs_of_pos hx]

theorem deningerEvenPreimage_of_neg (h : 𝓢(ℝ, ℂ)) {x : ℝ} (hx : x < 0) :
    deningerEvenPreimage h x = deningerMobiusPreimage h (-x) := by
  rw [deningerEvenPreimage, abs_of_neg hx]

/-- Reflection carries the negative ray onto the positive one. -/
theorem deningerNeg_preimage_Ioi : (fun x : ℝ => -x) ⁻¹' Set.Ioi 0 = Set.Iio 0 := by
  ext x
  simp [Set.mem_Iio]

/-- **Reflection transports integrability from the positive ray to the negative one.** -/
theorem deningerEvenPreimage_integrableOn_Iio {g : ℝ → ℂ}
    (hg : IntegrableOn g (Set.Ioi 0)) :
    IntegrableOn (fun x : ℝ => g (-x)) (Set.Iio 0) := by
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have hme : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).measurableEmbedding
  have hiff := hmp.integrableOn_comp_preimage hme (f := g) (s := Set.Ioi (0 : ℝ))
  rw [deningerNeg_preimage_Ioi] at hiff
  exact hiff.mpr hg

end

end RHTower
