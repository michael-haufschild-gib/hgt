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

end GaloisForLFunctions.RHTower
