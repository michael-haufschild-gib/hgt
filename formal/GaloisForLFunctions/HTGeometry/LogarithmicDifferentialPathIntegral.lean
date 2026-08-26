import GaloisForLFunctions.HTGeometry.DefectSlopeNormalForm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Path integrals of logarithmic differentials

A logarithm lift along a parametrized path turns `d log Y - dX` into the ordinary derivative of
`L - X`.  The interval integral is therefore the exact endpoint regulator.  When the terminal
point satisfies `Y = exp X`, the existing branch calculation removes that terminal coordinate and
leaves the base-point value plus an integral multiple of `2πi`.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- A differentiable logarithm lift has derivative `Y' / Y` along the path. -/
theorem logarithmLift_deriv_eq_div
    {Y L Y' L' : ℝ → ℂ} {t : ℝ}
    (hY : HasDerivAt Y (Y' t) t)
    (hL : HasDerivAt L (L' t) t)
    (hexp : ∀ s, Complex.exp (L s) = Y s) :
    L' t = Y' t / Y t := by
  have hYexp : HasDerivAt (fun s => Complex.exp (L s)) (Y' t) t := by
    convert hY using 1 <;> exact funext hexp
  have hderiv : Complex.exp (L t) * L' t = Y' t :=
    (hL.cexp).unique hYexp
  rw [← hexp t, eq_div_iff (Complex.exp_ne_zero (L t))]
  rw [mul_comm]
  exact hderiv

/-- The parametrized integral of `d log Y - dX` is its exact endpoint difference. -/
theorem intervalIntegral_logarithmicDifferential_sub_eq
    {a b : ℝ} {X Y L X' Y' L' : ℝ → ℂ}
    (hX : ∀ t ∈ Set.uIcc a b, HasDerivAt X (X' t) t)
    (hY : ∀ t ∈ Set.uIcc a b, HasDerivAt Y (Y' t) t)
    (hL : ∀ t ∈ Set.uIcc a b, HasDerivAt L (L' t) t)
    (hexp : ∀ t, Complex.exp (L t) = Y t)
    (hint : IntervalIntegrable (fun t => Y' t / Y t - X' t)
      MeasureTheory.volume a b) :
    (∫ t in a..b, Y' t / Y t - X' t) =
      (L b - L a) - (X b - X a) := by
  have hd : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun s => L s - X s) (Y' t / Y t - X' t) t := by
    intro t ht
    exact ((hL t ht).sub (hX t ht)).congr_deriv
      (by rw [logarithmLift_deriv_eq_div (hY t ht) (hL t ht) hexp])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  ring

/-- Exact regulator form of the path integral.  The terminal exponential relation cancels the
terminal coordinate; the only remaining ambiguity is the logarithm branch integer. -/
theorem intervalIntegral_logarithmicDifferential_eq_base_add_branch
    {a b : ℝ} {X Y L X' Y' L' : ℝ → ℂ}
    (hX : ∀ t ∈ Set.uIcc a b, HasDerivAt X (X' t) t)
    (hY : ∀ t ∈ Set.uIcc a b, HasDerivAt Y (Y' t) t)
    (hL : ∀ t ∈ Set.uIcc a b, HasDerivAt L (L' t) t)
    (hexp : ∀ t, Complex.exp (L t) = Y t)
    (hend : Y b = Complex.exp (X b))
    (hint : IntervalIntegrable (fun t => Y' t / Y t - X' t)
      MeasureTheory.volume a b) :
    ∃ k : ℤ, (∫ t in a..b, Y' t / Y t - X' t) =
      X a - L a + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  have hbranch : Complex.exp (L b) = Complex.exp (X b) := by
    rw [hexp b, hend]
  obtain ⟨k, hk⟩ := regulator_eq_base_add_branch hbranch
  refine ⟨k, ?_⟩
  rw [intervalIntegral_logarithmicDifferential_sub_eq hX hY hL hexp hint]
  exact hk

end

end GaloisForLFunctions.HTGeometry
