import GaloisForLFunctions.HTGeometry.PerturbedOscillator
import GaloisForLFunctions.RHTower.BesselNormalForm

/-!
# The Bessel normal form as a perturbed oscillator

The normal form `w = √u J₀(u)` solves `w'' + (1 + 1/(4u²)) w = 0`, so it is an instance of the
abstract perturbed oscillator with `κ = 1/4`.  Its energy and its two branch coefficients are
definitionally the abstract ones, so every abstract bound applies verbatim.

Recording the instantiation keeps the two layers honest: the abstract module is a genuine
generalization, not a parallel development.
-/

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

theorem oscEnergy_bessel (u : ℝ) :
    oscEnergy besselNormalForm besselNormalFormDeriv u = besselEnergy u := rfl

theorem oscCosCoeff_bessel (u : ℝ) :
    oscCosCoeff besselNormalForm besselNormalFormDeriv u = besselCosCoeff u := rfl

theorem oscSinCoeff_bessel (u : ℝ) :
    oscSinCoeff besselNormalForm besselNormalFormDeriv u = besselSinCoeff u := rfl

/-- The Bessel perturbation has size `κ/u²` with `κ = 1/4`. -/
theorem bessel_perturbation_le {u : ℝ} (hu : 0 < u) :
    |1 / (4 * u ^ 2)| ≤ (1 / 4 : ℝ) / u ^ 2 := by
  have hq : (0 : ℝ) < 1 / (4 * u ^ 2) := by positivity
  rw [abs_of_pos hq]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  ring_nf
  linarith

/-- **The Bessel normal form is a perturbed oscillator with `κ = 1/4`.**  Every hypothesis of the
abstract layer is discharged. -/
theorem bessel_isPerturbedOscillator :
    (∀ v : ℝ, 0 < v → HasDerivAt besselNormalForm (besselNormalFormDeriv v) v)
      ∧ (∀ v : ℝ, 0 < v → HasDerivAt besselNormalFormDeriv (besselNormalFormSecond v) v)
      ∧ (∀ v : ℝ, 0 < v → besselNormalFormSecond v
          + (1 + 1 / (4 * v ^ 2)) * besselNormalForm v = 0)
      ∧ ∀ v : ℝ, 0 < v → |1 / (4 * v ^ 2)| ≤ (1 / 4 : ℝ) / v ^ 2 :=
  ⟨fun _ hv => hasDerivAt_besselNormalForm hv, fun _ hv => hasDerivAt_besselNormalFormDeriv hv,
    fun _ hv => besselNormalForm_ode hv, fun _ hv => bessel_perturbation_le hv⟩

/-- The abstract Grönwall bound, read back on the Bessel energy. -/
theorem besselEnergy_le_exp_of_abstract {a u : ℝ} (ha : 0 < a) (hau : a ≤ u) :
    besselEnergy u ≤ besselEnergy a * Real.exp (1 / 4 / a - 1 / 4 / u) := by
  obtain ⟨hw, hDw, hode, hq⟩ := bessel_isPerturbedOscillator
  have h := oscEnergy_le_exp (w := besselNormalForm) (Dw := besselNormalFormDeriv)
    (DDw := besselNormalFormSecond) (q := fun v => 1 / (4 * v ^ 2)) (κ := 1 / 4)
    ha hau (by norm_num) hw hDw hode hq
  rw [oscEnergy_bessel, oscEnergy_bessel] at h
  exact h

/-- The abstract lower Grönwall bound, read back on the Bessel energy.  The normal form's energy
cannot decay past a fixed multiple of its value at the base point, so `√u J₀(u)` retains a definite
amplitude on every exterior ray. -/
theorem exp_mul_besselEnergy_le_of_abstract {a u : ℝ} (ha : 0 < a) (hau : a ≤ u) :
    besselEnergy a * Real.exp (-(1 / 4 / a - 1 / 4 / u)) ≤ besselEnergy u := by
  obtain ⟨hw, hDw, hode, hq⟩ := bessel_isPerturbedOscillator
  have h := exp_mul_oscEnergy_le (w := besselNormalForm) (Dw := besselNormalFormDeriv)
    (DDw := besselNormalFormSecond) (q := fun v => 1 / (4 * v ^ 2)) (κ := 1 / 4)
    ha hau (by norm_num) hw hDw hode hq
  rw [oscEnergy_bessel, oscEnergy_bessel] at h
  exact h

/-- **The Bessel normal form carries mass.**  On an interval long compared with the energy ratio,
`∫ u J₀(u)² du` is bounded below by the energy at the left endpoint.  This is what a pointwise
envelope cannot give. -/
theorem besselMass_lower {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ((β - α) * (besselEnergy α * Real.exp (1 / 4 / β - 1 / 4 / α))
        - besselEnergy α * Real.exp (1 / 4 / α)) / (2 + (1 / 4 : ℝ) / α ^ 2)
      ≤ ∫ u in α..β, besselNormalForm u ^ 2 := by
  obtain ⟨hw, hDw, hode, hq⟩ := bessel_isPerturbedOscillator
  have hE0 : 0 ≤ besselEnergy α := by
    rw [← oscEnergy_bessel]
    exact oscEnergy_nonneg _ _ _
  have hmem : ∀ v ∈ Set.Icc α β, 0 < v := fun v hv => lt_of_lt_of_le hα hv.1
  have hqc : ContinuousOn (fun v : ℝ => 1 / (4 * v ^ 2)) (Set.Icc α β) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun v hv => ?_
    have := hmem v hv
    positivity
  have hElow : ∀ v ∈ Set.Icc α β,
      besselEnergy α * Real.exp (1 / 4 / β - 1 / 4 / α)
        ≤ oscEnergy besselNormalForm besselNormalFormDeriv v := by
    intro v hv
    have hv0 : 0 < v := hmem v hv
    have hmain := exp_mul_besselEnergy_le_of_abstract hα hv.1
    have hstep : Real.exp (1 / 4 / β - 1 / 4 / α) ≤ Real.exp (-(1 / 4 / α - 1 / 4 / v)) := by
      rw [Real.exp_le_exp]
      have : (1 : ℝ) / 4 / β ≤ 1 / 4 / v := by
        refine div_le_div_of_nonneg_left (by norm_num) hv0 hv.2
      linarith
    rw [oscEnergy_bessel]
    nlinarith [hmain, hstep, hE0]
  have hEhigh : ∀ v ∈ Set.Icc α β,
      oscEnergy besselNormalForm besselNormalFormDeriv v
        ≤ besselEnergy α * Real.exp (1 / 4 / α) := by
    intro v hv
    have hv0 : 0 < v := hmem v hv
    have hmain := besselEnergy_le_exp_of_abstract hα hv.1
    have hstep : Real.exp (1 / 4 / α - 1 / 4 / v) ≤ Real.exp (1 / 4 / α) := by
      rw [Real.exp_le_exp]
      have : (0 : ℝ) < 1 / 4 / v := by positivity
      linarith
    rw [oscEnergy_bessel]
    nlinarith [hmain, hstep, hE0]
  exact mass_lower_of_oscEnergy (w := besselNormalForm) (Dw := besselNormalFormDeriv)
    (DDw := besselNormalFormSecond) (q := fun v => 1 / (4 * v ^ 2)) (κ := 1 / 4)
    hαβ hα (by norm_num) hw hDw hode hqc hq hElow hEhigh

end GaloisForLFunctions.RHTower
