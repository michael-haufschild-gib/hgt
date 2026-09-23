import GaloisForLFunctions.RHTower.PhotonicFixedKGeometricFloquetNoGo
import GaloisForLFunctions.HTGeometry.PhotonicTimeCrystalDynamicChirality

/-!
# Source-frequency form of the fixed-wavenumber Floquet obstruction

The frequency in the coefficient-level Maxwell no-go is exactly the corpus's
rotating-photonic Floquet frequency, not an independently inserted clock.
The all-grade coefficient equation is still a fixed-spatial-wavenumber ansatz;
this file does not assert that the full rotating-cylinder Maxwell boundary map
has been derived.
-/

open GaloisForLFunctions.HTGeometry

namespace RHTower

set_option autoImplicit false

/-- Exact complexification of the source's real Floquet frequency. -/
theorem ptr_source_frequency_complex (ω Δ : ℝ) (n : ℤ) :
    ((floquetSidebandFrequency ω Δ n : ℝ) : ℂ) =
      (ω : ℂ) + (n : ℂ) * (Δ : ℂ) := by
  simp only [floquetSidebandFrequency]
  push_cast
  rfl

/-- No nondegenerate geometric sequence solves the fixed-spatial-wavenumber
Maxwell coefficient equation at every *source-defined* Floquet frequency. -/
theorem ptr_no_source_frequency_fixedK_geometric_solution :
    ¬ ∃ ω Δ : ℝ, ∃ k μ d a lam : ℂ,
      Δ ≠ 0 ∧ k ≠ 0 ∧ μ ≠ 0 ∧ lam ≠ 0 ∧
      ∀ n : ℤ,
        (((floquetSidebandFrequency ω Δ n : ℝ) : ℂ) ^ 2) *
          ptrMaterialCoefficient d a (fun j => lam ^ j) n =
        (k ^ 2 / μ) * lam ^ n := by
  rintro ⟨ω, Δ, k, μ, d, a, lam, hΔ, hk, hμ, hlam, hmaxwell⟩
  have hΔc : (Δ : ℂ) ≠ 0 := by exact_mod_cast hΔ
  apply ptr_no_fixedK_geometric_coefficient_solution
    (ω : ℂ) (Δ : ℂ) k μ d a lam hΔc hk hμ hlam
  intro n
  have hn := hmaxwell n
  rw [ptr_source_frequency_complex] at hn
  exact hn

end RHTower
