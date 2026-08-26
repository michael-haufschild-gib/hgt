import GaloisForLFunctions.HTGeometry.DefectSlopeNormalForm
import GaloisForLFunctions.HTGeometry.SegmentPolarForm
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

/-- A smooth nowhere-zero path automatically admits the logarithm lift needed by the exact
regulator formula.  Thus the only path hypothesis beyond differentiability is avoidance of the
divisor of `Y`. -/
theorem exists_logarithmLift_intervalIntegral_eq_base_add_branch
    {a b : ℝ} (hab : a ≤ b) {X Y X' Y' : ℝ → ℂ}
    (hX : ∀ t ∈ Icc a b, HasDerivAt X (X' t) t)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y' t) t)
    (hlogCont : ContinuousOn (fun t => Y' t / Y t) (Icc a b))
    (hYne : ∀ t ∈ Icc a b, Y t ≠ 0)
    (hend : Y b = Complex.exp (X b))
    (hint : IntervalIntegrable (fun t => Y' t / Y t - X' t)
      MeasureTheory.volume a b) :
    ∃ (L : ℝ → ℂ) (k : ℤ),
      ContinuousOn L (Icc a b) ∧
      (∀ t ∈ Icc a b, HasDerivAt L (Y' t / Y t) t) ∧
      (∀ t ∈ Icc a b, Complex.exp (L t) = Y t) ∧
      (∫ t in a..b, Y' t / Y t - X' t) =
        X a - L a + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  obtain ⟨L, hLcont, hLderiv, hLexp⟩ :=
    RHTower.exists_continuousOn_log_of_hasDerivAt hab hY hlogCont hYne
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hbranch : Complex.exp (L b) = Complex.exp (X b) := by
    rw [← hLexp b hb, hend]
  obtain ⟨k, hk⟩ := regulator_eq_base_add_branch hbranch
  refine ⟨L, k, hLcont, hLderiv, ?_, ?_⟩
  · intro t ht
    exact (hLexp t ht).symm
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht =>
      (hLderiv t (by simpa [uIcc_of_le hab] using ht)).sub
        (hX t (by simpa [uIcc_of_le hab] using ht))) hint]
    calc
      (L - X) b - (L - X) a = L b - L a - (X b - X a) := by
        change (L b - X b) - (L a - X a) = _
        ring
      _ = X a - L a + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hk

end

end GaloisForLFunctions.HTGeometry
