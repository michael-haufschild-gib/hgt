import GaloisForLFunctions.HTGeometry.GomesPolynomialHamiltonianFibers

/-!
# Tensor probes recover polynomial connections from Hamiltonian observations

The common-connection tensor composition in arXiv:2509.25276v7 section 5.2 motivates
this exact scalar experiment. Tensoring means addition of profiles on the same real
base. A second Hamiltonian observation after one fixed linear probe recovers the
first-order connection, including the sign lost by opposite affine profiles.
-/

noncomputable section
open Polynomial
open scoped SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- The only obstruction to a common tensor probe separating Hamiltonian fibers is zero probe drift. -/
theorem gomesDilatonHamiltonian_tensor_pair_iff (H K R : ℝ[X]) :
    (dilatonHamiltonianCLM H = dilatonHamiltonianCLM K ∧
      dilatonHamiltonianCLM (H + R) = dilatonHamiltonianCLM (K + R)) ↔
        dilatonHamiltonianCLM H = dilatonHamiltonianCLM K ∧
          (dilatonSuperchargeCLM H = dilatonSuperchargeCLM K ∨ R.derivative = 0) := by
  constructor
  · rintro ⟨hh, ht⟩
    refine ⟨hh, ?_⟩
    have hs := ((gomesDilatonHamiltonian_parts_iff H K).mp hh).2
    have ht := ((gomesDilatonHamiltonian_parts_iff (H + R) (K + R)).mp ht).2
    simp only [derivative_add] at ht
    have hp : 2 * (R.derivative * (H.derivative - K.derivative)) = 0 := by
      linear_combination ht - hs
    have hc : R.derivative * (H.derivative - K.derivative) = 0 :=
      (mul_eq_zero.mp hp).resolve_left two_ne_zero
    rcases mul_eq_zero.mp hc with hz | he
    · exact Or.inr hz
    · exact Or.inl ((gomesDilatonConnection_eq_iff H K).mpr (sub_eq_zero.mp he))
  · rintro ⟨hh, hc | hz⟩
    · refine ⟨hh, (gomesDilatonHamiltonian_derivative_fibers _ _).mpr (Or.inl ?_)⟩
      simp only [derivative_add, (gomesDilatonConnection_eq_iff H K).mp hc]
    · refine ⟨hh, ?_⟩
      rw [gomesDilatonHamiltonian_derivative_fibers] at hh ⊢
      simpa only [derivative_add, hz, derivative_zero, add_zero] using hh

/-- One fixed linear tensor probe removes every remaining Hamiltonian sign ambiguity. -/
theorem gomesDilatonHamiltonian_linear_probe_iff (H K : ℝ[X]) :
    (dilatonHamiltonianCLM H = dilatonHamiltonianCLM K ∧
      dilatonHamiltonianCLM (H + X) = dilatonHamiltonianCLM (K + X)) ↔
        dilatonSuperchargeCLM H = dilatonSuperchargeCLM K := by
  constructor
  · intro h
    have hp := ((gomesDilatonHamiltonian_tensor_pair_iff H K X).mp h).2
    exact hp.resolve_right (by rw [derivative_X]; exact one_ne_zero)
  · intro h
    apply (gomesDilatonHamiltonian_tensor_pair_iff H K X).mpr
    exact ⟨((gomesDilatonHamiltonian_origin_slope_iff H K).mpr h).1, Or.inl h⟩

/-- All tensor-context Hamiltonians contain exactly the first-order connection information. -/
theorem gomesDilatonHamiltonian_all_tensor_contexts_iff (H K : ℝ[X]) :
    (∀ R : ℝ[X], dilatonHamiltonianCLM (H + R) = dilatonHamiltonianCLM (K + R)) ↔
      dilatonSuperchargeCLM H = dilatonSuperchargeCLM K := by
  constructor
  · intro h
    apply (gomesDilatonHamiltonian_linear_probe_iff H K).mp
    exact ⟨by simpa only [add_zero] using h 0, h X⟩
  · intro h R
    apply (gomesDilatonHamiltonian_derivative_fibers _ _).mpr
    left
    simp only [derivative_add, (gomesDilatonConnection_eq_iff H K).mp h]

/-- The two actual Hamiltonians form an observation record on polynomial profiles. -/
def gomesDilatonTensorHamiltonianRecord (H : ℝ[X]) :
    (𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) × (𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) :=
  (dilatonHamiltonianCLM H, dilatonHamiltonianCLM (H + X))

/-- This two-operator record loses exactly constant log-amplitude. -/
theorem gomesDilatonTensorHamiltonianRecord_eq_iff (H K : ℝ[X]) :
    gomesDilatonTensorHamiltonianRecord H = gomesDilatonTensorHamiltonianRecord K ↔
      ∃ c : ℝ, H = K + C c := by
  rw [gomesDilatonTensorHamiltonianRecord, gomesDilatonTensorHamiltonianRecord, Prod.mk.injEq,
    gomesDilatonHamiltonian_linear_probe_iff, gomesDilatonConnection_constant_iff]

/-- Adding one density-origin datum makes the two-operator observation injective. -/
theorem gomesDilatonTensorHamiltonianRecord_origin_iff (H K : ℝ[X]) :
    (gomesDilatonTensorHamiltonianRecord H = gomesDilatonTensorHamiltonianRecord K ∧
      H.eval 0 = K.eval 0) ↔ H = K := by
  rw [gomesDilatonTensorHamiltonianRecord_eq_iff, ← gomesDilatonConnection_constant_iff,
    gomesDilatonConnection_origin_iff]

/-- The augmented observation embeds the entire polynomial profile space into measured operator data. -/
theorem gomesDilatonTensorHamiltonianRecord_augmented_injective :
    Function.Injective (fun H : ℝ[X] => (gomesDilatonTensorHamiltonianRecord H, H.eval 0)) := by
  intro H K h
  exact (gomesDilatonTensorHamiltonianRecord_origin_iff H K).mp (Prod.mk.inj h)

end GaloisForLFunctions.HTGeometry
