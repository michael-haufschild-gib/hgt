import GaloisForLFunctions.RHTower.Deninger.DeningerPlaceRestriction
import GaloisForLFunctions.RHTower.Deninger.DeningerKummerPlaceIsometry
import GaloisForLFunctions.RHTower.Deninger.DeningerArchimedeanBaseChange

/-!
# The height and the Kummer norm under base change

The logarithmic height of an element of `K`, computed in an extension `L`, is `[L : K]` times its
height in `K`: the archimedean part scales because the fibres of restriction of complex embeddings
all have size `[L : K]`, and the non-archimedean part scales because the local degrees above a
place add up to `[L : K]`.

By the place isometry the same holds for the Kummer norm.  This is the compatibility that lets the
place models of a tower of number fields glue: the normalized function `f_α / [K : ℚ]` is
independent of the field `K` in which `α` is taken.

* `deningerLogHeight_baseChange` : `h_L(x) = [L : K] · h_K(x)`.
* `deningerKummerL1Norm_baseChange` : the same for the Kummer norm.
* `deningerNormalizedHeight_baseChange` : the `ℚ`-normalized height is independent of the field.
-/

namespace RHTower

open NumberField Module

section HeightBaseChange

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **Base change for the logarithmic height.**  Computing the height of an element of `K` in an
extension `L` multiplies it by the degree `[L : K]`. -/
theorem deningerLogHeight_baseChange (x : K) :
    Height.logHeight₁ (algebraMap K L x) = (finrank K L : ℝ) * Height.logHeight₁ x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [NumberField.logHeight₁_eq, NumberField.logHeight₁_eq, mul_add,
      ← deningerArchPlaceSum_baseChange Real.posLog x,
      ← deningerFinitePlaceFinsum_baseChange Real.posLog (fun n t => Real.posLog_pow n t)
        (by simp [Real.posLog]) hx]

/-- **Base change for the Kummer norm.**  The total variation of `f_α` over the place space
multiplies by `[L : K]` as well, since it is twice the logarithmic height. -/
theorem deningerKummerL1Norm_baseChange {x : K} (hx : x ≠ 0) :
    deningerKummerL1Norm (algebraMap K L x) = (finrank K L : ℝ) * deningerKummerL1Norm x := by
  have hxL : algebraMap K L x ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hx
  rw [deningerKummerL1Norm_eq_two_mul_logHeight hxL, deningerKummerL1Norm_eq_two_mul_logHeight hx,
    deningerLogHeight_baseChange]
  ring

/-- **The normalized height is independent of the field of definition.**  Dividing by the absolute
degree cancels the base-change factor, by the tower law. -/
theorem deningerNormalizedHeight_baseChange (x : K) :
    Height.logHeight₁ (algebraMap K L x) / (finrank ℚ L : ℝ)
      = Height.logHeight₁ x / (finrank ℚ K : ℝ) := by
  have htower : finrank ℚ L = finrank ℚ K * finrank K L :=
    (Module.finrank_mul_finrank ℚ K L).symm
  have hK : (finrank ℚ K : ℝ) ≠ 0 := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    positivity
  have hKL : (finrank K L : ℝ) ≠ 0 := by
    have := Module.finrank_pos (R := K) (M := L)
    positivity
  rw [deningerLogHeight_baseChange, htower]
  push_cast
  field_simp

end HeightBaseChange

end RHTower
