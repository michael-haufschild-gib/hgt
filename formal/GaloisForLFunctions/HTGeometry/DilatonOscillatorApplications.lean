import GaloisForLFunctions.HTGeometry.DilatonSchwartzHamiltonian

/-!
# Oscillator and quartic applications of the dilaton transformation

The half-density potential from arXiv:2608.21406v1 recovers the corpus's
number operator for a Gaussian log-weight and its shifted number operator
when the weight is reversed. The existing Hermite eigenrelations therefore
become exact dilaton eigenrelations.

A quartic log-weight gives a sextic potential with an explicit negative well
for every positive coupling. Nevertheless, the proved factorization excludes
neutral growing modes on the actual Schwartz domain. This gives a closed
functional example of the paper's distinction between a negative potential
and an instability.
-/

noncomputable section
open Polynomial MeasureTheory
open scoped SchwartzMap
namespace GaloisForLFunctions.HTGeometry

def gaussianDilatonLogWeight : ℝ[X] := C (-2 * Real.pi) * X ^ (2 : ℕ)

def quarticDilatonLogWeight (k : ℝ) : ℝ[X] := C (-Real.exp k) * X ^ (4 : ℕ)

theorem gaussianDilaton_potential (x : ℝ) :
    dilatonPotential gaussianDilatonLogWeight x = 4 * Real.pi ^ (2 : ℕ) * x ^ (2 : ℕ) - 2 * Real.pi := by
  simp [dilatonPotential, gaussianDilatonLogWeight]
  ring

theorem gaussianDilaton_supercharge (ψ : 𝓢(ℝ, ℂ)) :
    dilatonSuperchargeCLM gaussianDilatonLogWeight ψ = annihilationCLM ψ := by
  ext x
  rw [dilatonSuperchargeCLM_apply, annihilationCLM_apply]
  simp [gaussianDilatonLogWeight]
  ring

theorem gaussianDilaton_adjointCharge (ψ : 𝓢(ℝ, ℂ)) :
    dilatonAdjointChargeCLM gaussianDilatonLogWeight ψ = creationCLM ψ := by
  ext x
  rw [dilatonAdjointChargeCLM_apply, creationCLM_apply]
  simp [gaussianDilatonLogWeight]
  ring

theorem gaussianDilaton_numberOperator (ψ : 𝓢(ℝ, ℂ)) :
    dilatonHamiltonianCLM gaussianDilatonLogWeight ψ = numberCLM ψ := by
  rw [dilatonHamiltonianCLM, ContinuousLinearMap.comp_apply, gaussianDilaton_adjointCharge,
    gaussianDilaton_supercharge, numberCLM_apply]

theorem gaussianDilaton_hermite_spectrum (n : ℕ) :
    dilatonHamiltonianCLM gaussianDilatonLogWeight (hermiteSchwartz n) =
      (4 * (Real.pi : ℂ) * n) • hermiteSchwartz n := by
  rw [gaussianDilaton_numberOperator, numberCLM_hermiteSchwartz]

/-- Reversing the log-weight exchanges the first-order factors, up to sign. -/
theorem reverseGaussianDilaton_supercharge (ψ : 𝓢(ℝ, ℂ)) :
    dilatonSuperchargeCLM (-gaussianDilatonLogWeight) ψ = -creationCLM ψ := by
  ext x
  rw [dilatonSuperchargeCLM_apply]
  simp only [_root_.neg_apply, creationCLM_apply]
  simp [gaussianDilatonLogWeight]
  ring_nf
  simp

theorem reverseGaussianDilaton_adjointCharge (ψ : 𝓢(ℝ, ℂ)) :
    dilatonAdjointChargeCLM (-gaussianDilatonLogWeight) ψ = -annihilationCLM ψ := by
  ext x
  rw [dilatonAdjointChargeCLM_apply]
  simp only [_root_.neg_apply, annihilationCLM_apply]
  simp [gaussianDilatonLogWeight]
  ring

theorem reverseGaussianDilaton_shiftedNumber (ψ : 𝓢(ℝ, ℂ)) :
    dilatonHamiltonianCLM (-gaussianDilatonLogWeight) ψ = shiftedNumberCLM ψ := by
  rw [dilatonHamiltonianCLM, ContinuousLinearMap.comp_apply, reverseGaussianDilaton_adjointCharge,
    reverseGaussianDilaton_supercharge, map_neg, neg_neg, shiftedNumberCLM_apply]
  have h := annihilationCLM_creationCLM_sub ψ
  rw [numberCLM_apply]
  simpa only [add_comm] using sub_eq_iff_eq_add.mp h

theorem quarticDilaton_potential (k x : ℝ) :
    dilatonPotential (quarticDilatonLogWeight k) x =
      4 * Real.exp k ^ (2 : ℕ) * x ^ (6 : ℕ) - 6 * Real.exp k * x ^ (2 : ℕ) := by
  simp [dilatonPotential, quarticDilatonLogWeight]
  ring

/-- Every positive quartic coupling has an explicit point of negative effective potential. -/
theorem quarticDilaton_negative_well (t : ℝ) :
    dilatonPotential (quarticDilatonLogWeight (-4 * t)) (Real.exp t) < 0 := by
  rw [quarticDilaton_potential]
  have he : Real.exp (-4 * t) * Real.exp t ^ (4 : ℕ) = 1 := by
    rw [show -4 * t = -(4 * t) by ring, Real.exp_neg, ← Real.exp_nat_mul t 4]
    norm_num
  rw [show 4 * Real.exp (-4 * t) ^ (2 : ℕ) * Real.exp t ^ (6 : ℕ) -
      6 * Real.exp (-4 * t) * Real.exp t ^ (2 : ℕ) =
      (Real.exp (-4 * t) * Real.exp t ^ (2 : ℕ)) *
        (4 * (Real.exp (-4 * t) * Real.exp t ^ (4 : ℕ)) - 6) by ring, he]
  exact mul_neg_of_pos_of_neg (by positivity) (by norm_num)

/-- Negative potential does not imply a neutral growing mode, in the actual Schwartz domain. -/
theorem quarticDilaton_negative_potential_without_growing_modes (t : ℝ) :
    dilatonPotential (quarticDilatonLogWeight (-4 * t)) (Real.exp t) < 0 ∧
      ∀ (ψ : 𝓢(ℝ, ℂ)) (u s : ℝ),
        (∀ x, dilatonRadialOperator (quarticDilatonLogWeight (-4 * t))
          (dilatonUndressed (quarticDilatonLogWeight (-4 * t)) ψ) x +
          growingFrequency u s ^ (2 : ℕ) * dilatonUndressed (quarticDilatonLogWeight (-4 * t)) ψ x = 0) ↔
        ψ = 0 :=
  ⟨quarticDilaton_negative_well t, fun ψ u s => dilaton_neutral_radial_no_growing_mode _ ψ u s⟩

end GaloisForLFunctions.HTGeometry
