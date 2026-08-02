import GaloisForLFunctions.RHTower.DeningerPoissonMoebius
import GaloisForLFunctions.RHTower.DeningerPoissonSchwartz

/-!
# The Poisson operator is injective

A member of Meyer's space is even and vanishes at the origin, so it is determined by its values on
the positive half line.  Möbius inversion recovers those values from the Poisson sum, which is the
zeroth weight of the image.  Hence the Poisson operator is injective — exactness of the card's
sequence at `ℋ_∩`.

* `deningerPoissonValue_zero` : the Poisson sum of the zero function vanishes.
* `deningerPoissonLM_injective` : **`Z` is injective.**
-/

open scoped Real SchwartzMap FourierTransform ArithmeticFunction ContDiff
open Complex MeasureTheory GaloisForLFunctions GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

theorem deningerPoissonValue_zero (x : ℝ) : deningerPoissonValue (0 : 𝓢(ℝ, ℂ)) x = 0 := by
  rw [deningerPoissonValue]
  have hzero : ∀ n : ℕ, (0 : 𝓢(ℝ, ℂ)) (x * ((n : ℝ) + 1)) = 0 := fun n => rfl
  rw [tsum_congr hzero, tsum_zero]

/-- **The Poisson operator is injective on Meyer's space.** -/
theorem deningerPoissonLM_injective : Function.Injective deningerPoissonLM := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have hzeroth : ∀ t : ℝ, deningerPoissonWeight 0 (f : 𝓢(ℝ, ℂ)) t = 0 := by
    intro t
    have hfam : ((deningerPoissonLM f : deningerRadialCompat) : ∀ _ : ℤ, 𝓢(ℝ, ℂ)) 0 t = 0 := by
      rw [hf]
      rfl
    exact hfam
  have hvalue : ∀ x : ℝ, 0 < x → deningerPoissonValue (f : 𝓢(ℝ, ℂ)) x = 0 := by
    intro x hx
    have ht := hzeroth (Real.log x)
    rw [deningerPoissonWeight, deningerExpWeight] at ht
    have hw : ((Real.exp (((0 : ℤ) : ℝ) * Real.log x) : ℝ) : ℂ) = 1 := by
      norm_num
    rw [hw, one_mul, deningerPoissonLog_eq, Real.exp_log hx] at ht
    exact ht
  have heq : ∀ x : ℝ, 0 < x → (f : 𝓢(ℝ, ℂ)) x = (0 : 𝓢(ℝ, ℂ)) x := by
    refine deningerPoissonValue_injOn (deningerMeyerCap_zero f.2) rfl ?_
    intro x hx
    rw [hvalue x hx, deningerPoissonValue_zero]
  refine Subtype.ext ?_
  refine SchwartzMap.ext fun x => ?_
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hpos : (0 : ℝ) < -x := by linarith
    have hval := heq (-x) hpos
    have heven := deningerMeyerCap_even f.2 (-x)
    show (f : 𝓢(ℝ, ℂ)) x = (0 : 𝓢(ℝ, ℂ)) x
    rw [show x = -(-x) by ring, heven, hval]
    rfl
  · subst hx
    show (f : 𝓢(ℝ, ℂ)) 0 = (0 : 𝓢(ℝ, ℂ)) 0
    rw [deningerMeyerCap_zero f.2]
    rfl
  · exact heq x hx

end RHTower

end
