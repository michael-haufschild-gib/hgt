import GaloisForLFunctions.HTGeometry.HalfPlaneGermShift
import GaloisForLFunctions.HTGeometry.DigammaHypertranscendental

/-!
# The digamma jets as germs on the half-plane

The upper part of a right half-plane misses the poles `−ℕ` of the digamma function, so every jet
`ψ⁽ʲ⁾` has a germ there, and the single-step shift law becomes an identity in the germ ring:

`shift ψ⁽ʲ⁾ = ψ⁽ʲ⁾ + (−1)ʲ j!/s^{j+1}`,

with the increment the germ of the rational pole part `polePart j`.  This is the jet substitution
that the shift elimination reads.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

/-- The upper half-plane filter misses the poles of the digamma function. -/
theorem eventually_off_poles (σ₀ : ℝ) :
    ∀ᶠ s : ℂ in halfPlaneUpper σ₀, ∀ p : ℕ, s ≠ -(p : ℂ) := by
  filter_upwards [eventually_halfPlaneUpper_im (σ₀ := σ₀) 1] with s him p hp
  rw [hp] at him
  simp at him
  linarith

/-- The upper half-plane filter misses the origin. -/
theorem eventually_ne_zero (σ₀ : ℝ) : ∀ᶠ s : ℂ in halfPlaneUpper σ₀, s ≠ 0 := by
  filter_upwards [eventually_one_le_norm σ₀] with s hs
  intro h
  rw [h] at hs
  simp at hs
  linarith

/-- The germ of the rational pole part is the germ of its values. -/
theorem ratGerm_polePart (σ₀ : ℝ) (j : ℕ) :
    ratGerm σ₀ (polePart j)
      = ((fun s : ℂ => (-1) ^ j * (j.factorial : ℂ) / s ^ (j + 1) : ℂ → ℂ) :
          HalfPlaneGerm σ₀) := by
  have hXpoly : ((Polynomial.X : Polynomial ℂ) ^ (j + 1)) ≠ 0 :=
    pow_ne_zero _ Polynomial.X_ne_zero
  have hXrat : ((RatFunc.X : RatFunc ℂ) ^ (j + 1)) ≠ 0 := pow_ne_zero _ ratFuncX_ne_zero
  have hunit : IsUnit (polyGerm σ₀ ((Polynomial.X : Polynomial ℂ) ^ (j + 1))) :=
    isUnit_polyGerm σ₀ hXpoly
  refine hunit.mul_left_cancel ?_
  have hrat : algebraMap (Polynomial ℂ) (RatFunc ℂ) ((Polynomial.X : Polynomial ℂ) ^ (j + 1))
      * polePart j = algebraMap ℂ (RatFunc ℂ) ((-1) ^ j * (j.factorial : ℂ)) := by
    rw [polePart, map_pow, RatFunc.algebraMap_X, mul_comm, div_mul_cancel₀ _ hXrat]
  have hleft : polyGerm σ₀ ((Polynomial.X : Polynomial ℂ) ^ (j + 1)) * ratGerm σ₀ (polePart j)
      = polyGerm σ₀ (Polynomial.C ((-1) ^ j * (j.factorial : ℂ))) := by
    rw [← ratGerm_algebraMap σ₀ ((Polynomial.X : Polynomial ℂ) ^ (j + 1)), ← map_mul, hrat,
      ← algebraMap_polyC ((-1) ^ j * (j.factorial : ℂ)), ratGerm_algebraMap]
  rw [hleft, polyGerm_apply, polyGerm_apply, ← Filter.Germ.coe_mul]
  refine Filter.Germ.coe_eq.mpr ?_
  filter_upwards [eventually_ne_zero σ₀] with s hs
  have hpow : (s : ℂ) ^ (j + 1) ≠ 0 := pow_ne_zero _ hs
  show Polynomial.eval s (Polynomial.C ((-1) ^ j * (j.factorial : ℂ)))
    = Polynomial.eval s ((Polynomial.X : Polynomial ℂ) ^ (j + 1))
      * ((-1) ^ j * (j.factorial : ℂ) / s ^ (j + 1))
  rw [Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  field_simp

/-- The germ of the `j`-th digamma jet. -/
noncomputable def digammaJetGerm (σ₀ : ℝ) (j : ℕ) : HalfPlaneGerm σ₀ :=
  ((fun s : ℂ => iteratedDeriv j Complex.digamma s : ℂ → ℂ) : HalfPlaneGerm σ₀)

/-- **The jet substitution in the germ ring.**  Translating the `j`-th digamma jet adds the germ of
the rational pole part `(−1)ʲ j!/s^{j+1}`. -/
theorem shiftGerm_digammaJetGerm (σ₀ : ℝ) (j : ℕ) :
    shiftGerm σ₀ (digammaJetGerm σ₀ j)
      = digammaJetGerm σ₀ j + ratGerm σ₀ (polePart j) := by
  show shiftGerm σ₀ ((fun s : ℂ => iteratedDeriv j Complex.digamma s : ℂ → ℂ) : HalfPlaneGerm σ₀)
      = ((fun s : ℂ => iteratedDeriv j Complex.digamma s : ℂ → ℂ) : HalfPlaneGerm σ₀)
        + ratGerm σ₀ (polePart j)
  rw [shiftGerm_coe, ratGerm_polePart, ← Filter.Germ.coe_add]
  refine Filter.Germ.coe_eq.mpr ?_
  filter_upwards [eventually_off_poles σ₀] with s hs
  exact digammaJet_shift j hs

end GaloisForLFunctions
