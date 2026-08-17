import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The ultraviolet multiplicity clock and its parity phase

A band whose points all lie between `a` and `(2M+1)a` converts an energy bound into a probability
bound of order `1/a` on both sides: the energy is between `a` times the probability and `(2M+1)a`
times it.  That is the whole quantitative content of the linear-aperture band statement.

The parity label carried by the clock is the phase `θ_γ(a) = γa - arctan γ`.  Its two squared
trigonometric weights sum to one at every aperture, so the multiplicity marginal of the moving
parity law is the fixed inverse-square multiplicity law — the parity refinement adds a label without
changing the clock.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## `(350)`: the linear-aperture band has probability of order `1/a` -/

/-- The energy of a band is at least its lower endpoint times its probability. -/
theorem band_energy_ge {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hint : IntegrableOn (fun t : ℝ => t) (Set.Icc a b) μ) :
    a * μ.real (Set.Icc a b) ≤ ∫ t in Set.Icc a b, t ∂μ := by
  have h := setIntegral_ge_of_const_le (μ := μ) (s := Set.Icc a b) (f := fun t : ℝ => t)
    (c := a) measurableSet_Icc (measure_ne_top μ _) (fun t ht => ht.1) hint
  rw [smul_eq_mul] at h
  linarith [h]

/-- The energy of a band is at most its upper endpoint times its probability. -/
theorem band_energy_le {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hint : IntegrableOn (fun t : ℝ => t) (Set.Icc a b) μ) :
    (∫ t in Set.Icc a b, t ∂μ) ≤ b * μ.real (Set.Icc a b) := by
  have hle : (∫ t in Set.Icc a b, t ∂μ) ≤ ∫ _t in Set.Icc a b, b ∂μ := by
    refine setIntegral_mono_on hint (integrableOn_const (by exact measure_ne_top μ _))
      measurableSet_Icc ?_
    intro t ht
    exact ht.2
  rw [setIntegral_const, smul_eq_mul] at hle
  linarith [hle]

/-- **`(350)`, lower half: an order-one energy in a linear-aperture band forces probability at
least of order `1/a`.** -/
theorem le_measureReal_band {μ : Measure ℝ} [IsFiniteMeasure μ] {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hint : IntegrableOn (fun t : ℝ => t) (Set.Icc a b) μ)
    (hlow : c ≤ ∫ t in Set.Icc a b, t ∂μ) :
    c / b ≤ μ.real (Set.Icc a b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [div_le_iff₀ hb]
  have := band_energy_le (μ := μ) (a := a) (b := b) hint
  linarith

/-- **`(350)`, upper half: a bounded energy in a band forces probability at most of order `1/a`.** -/
theorem measureReal_band_le {μ : Measure ℝ} [IsFiniteMeasure μ] {a b C : ℝ} (ha : 0 < a)
    (hint : IntegrableOn (fun t : ℝ => t) (Set.Icc a b) μ)
    (hhigh : (∫ t in Set.Icc a b, t ∂μ) ≤ C) :
    μ.real (Set.Icc a b) ≤ C / a := by
  rw [le_div_iff₀ ha]
  have := band_energy_ge (μ := μ) (a := a) (b := b) hint
  linarith

/-! ## `(355)`–`(356)`: the parity phase and its multiplicity marginal -/

/-- **`(355)`: the ultraviolet parity phase.** -/
def parityPhase (γ a : ℝ) : ℝ := γ * a - Real.arctan γ

/-- **`(356)`: the two parity weights sum to one at every aperture.** -/
theorem parityWeights_sum (γ a : ℝ) :
    Real.cos (parityPhase γ a) ^ 2 + Real.sin (parityPhase γ a) ^ 2 = 1 := by
  rw [add_comm]
  exact Real.sin_sq_add_cos_sq _

/-- **`(354)`: the two parity coefficients of one ordinate sum to the multiplicity weight.** -/
theorem parityCoefficient_sum (m γ a : ℝ) :
    4 * m * Real.cos (parityPhase γ a) ^ 2 / (1 + γ ^ 2)
        + 4 * m * Real.sin (parityPhase γ a) ^ 2 / (1 + γ ^ 2)
      = 4 * m / (1 + γ ^ 2) := by
  have hden : (0 : ℝ) < 1 + γ ^ 2 := by positivity
  have h := parityWeights_sum γ a
  field_simp
  rw [h, mul_one]

end GaloisForLFunctions.RHTower
