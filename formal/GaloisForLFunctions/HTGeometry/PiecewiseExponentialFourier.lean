import GaloisForLFunctions.HTGeometry.ExponentialPieceFourierDecay
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fourier decay of a piecewise exponential

A function on the circle that is `e^{αx}` times a piecewise constant with `n` pieces has Fourier
coefficients bounded by `n·M·2e^{|α|}/(1+|j|)`: split the period integral at the breakpoints and
apply the single-piece estimate.

This is the amplitude class of the iterated principal action.  It is closed under multiplication by
`p^{±(1-x)}` (which shifts `α`), under translation (which moves the breakpoints and rescales the
coefficients), and under products (which refines the partition) — so a fixed number of iterations
keeps one decay constant.
-/

open MeasureTheory intervalIntegral

namespace GaloisForLFunctions

/-! ## Two transfer lemmas -/

theorem intervalIntegrable_of_eq_continuous_Ioo {g h : ℝ → ℂ} {a b : ℝ}
    (hc : Continuous h) (hae : ∀ x ∈ Set.Ioo a b, g x = h x) (hab : a ≤ b) :
    IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff]
  have hint : IntegrableOn h (Set.uIoc a b) volume := by
    rw [← intervalIntegrable_iff]
    exact hc.intervalIntegrable a b
  refine hint.congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  have hnull : (volume : Measure ℝ) {b} = 0 := measure_singleton b
  filter_upwards [compl_mem_ae_iff.mpr hnull] with x hx hmem
  rw [Set.uIoc_of_le hab] at hmem
  exact (hae x ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩).symm

theorem intervalIntegral_congr_Ioo {g h : ℝ → ℂ} {a b : ℝ}
    (hae : ∀ x ∈ Set.Ioo a b, g x = h x) (hab : a ≤ b) :
    (∫ x in a..b, g x) = ∫ x in a..b, h x := by
  refine intervalIntegral.integral_congr_ae ?_
  have hnull : (volume : Measure ℝ) {b} = 0 := measure_singleton b
  filter_upwards [compl_mem_ae_iff.mpr hnull] with x hx hmem
  rw [Set.uIoc_of_le hab] at hmem
  exact hae x ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩

/-! ## The piecewise-exponential class -/

/-- `f` is `e^{αx}` times a piecewise constant with `n` pieces on one period. -/
structure IsExpPiecewise (α : ℝ) (n : ℕ) (t : ℕ → ℝ) (c : ℕ → ℂ)
    (f : AddCircle (1 : ℝ) → ℂ) : Prop where
  base : t 0 = 0
  top : t n = 1
  mono : ∀ i, i < n → t i ≤ t (i + 1)
  nonneg : ∀ i, i < n → 0 ≤ t i
  le_one : ∀ i, i < n → t (i + 1) ≤ 1
  eq : ∀ i, i < n → ∀ x ∈ Set.Ioo (t i) (t (i + 1)),
        f ((x : ℝ) : AddCircle (1 : ℝ)) = c i * Complex.exp ((α : ℂ) * (x : ℂ))

/-- **Fourier decay of a piecewise exponential.** -/
theorem norm_fourierCoeff_of_isExpPiecewise {α : ℝ} {n : ℕ} {t : ℕ → ℝ} {c : ℕ → ℂ}
    {f : AddCircle (1 : ℝ) → ℂ} (h : IsExpPiecewise α n t c f)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, ‖c i‖ ≤ M) (j : ℤ) :
    ‖fourierCoeff f j‖ ≤ (n : ℝ) * (M * (2 * Real.exp |α|)) / (1 + (j.natAbs : ℝ)) := by
  set g : ℝ → ℂ := fun x =>
    fourier (-j) ((x : ℝ) : AddCircle (1 : ℝ)) * f ((x : ℝ) : AddCircle (1 : ℝ)) with hg
  have hpiece : ∀ i, i < n → ∀ x ∈ Set.Ioo (t i) (t (i + 1)),
      g x = c i * (Complex.exp ((α : ℂ) * (x : ℂ)) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (x : ℂ)))) := by
    intro i hi x hx
    rw [hg]
    simp only
    rw [h.eq i hi x hx, fourier_coe_apply]
    have hchar : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-j : ℤ) : ℂ) * (x : ℂ) /
        ((1 : ℝ) : ℂ))
        = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (x : ℂ))) := by
      congr 1
      push_cast
      ring
    rw [hchar]
    ring
  have hcont : ∀ i : ℕ, Continuous (fun x : ℝ => c i * (Complex.exp ((α : ℂ) * (x : ℂ)) *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (x : ℂ))))) := by
    intro i
    fun_prop
  have hintegrable : ∀ i, i < n → IntervalIntegrable g volume (t i) (t (i + 1)) := by
    intro i hi
    exact intervalIntegrable_of_eq_continuous_Ioo (hcont i) (hpiece i hi) (h.mono i hi)
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (f := g) (μ := volume) (a := t) (n := n) hintegrable
  have hcoeff : fourierCoeff f j = ∫ x in (0 : ℝ)..1, g x := by
    rw [fourierCoeff_eq_intervalIntegral f j 0]
    simp only [one_div, inv_one, one_smul, zero_add, hg, smul_eq_mul]
  have hpieceInt : ∀ i, i < n →
      (∫ x in (t i)..(t (i + 1)), g x)
        = c i * ∫ x in (t i)..(t (i + 1)),
            Complex.exp ((α : ℂ) * (x : ℂ)) *
              Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (x : ℂ))) := by
    intro i hi
    rw [intervalIntegral_congr_Ioo (hpiece i hi) (h.mono i hi),
      intervalIntegral.integral_const_mul]
  have hsum : fourierCoeff f j
      = ∑ i ∈ Finset.range n, c i * ∫ x in (t i)..(t (i + 1)),
          Complex.exp ((α : ℂ) * (x : ℂ)) *
            Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (x : ℂ))) := by
    rw [hcoeff, ← h.base, ← h.top, ← hsplit]
    exact Finset.sum_congr rfl fun i hi => hpieceInt i (Finset.mem_range.mp hi)
  rw [hsum]
  exact norm_sum_expPieces_fourier_le t c
    (fun i hi => ⟨h.nonneg i hi, h.mono i hi, h.le_one i hi⟩) hM0 hM j

end GaloisForLFunctions
