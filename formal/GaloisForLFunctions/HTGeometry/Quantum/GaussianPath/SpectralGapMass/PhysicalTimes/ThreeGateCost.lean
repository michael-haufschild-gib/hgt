import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.ThreeGateUpper
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.SeparatedAngles
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.TouchedSpectrum
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-! # Exact bounded-time gate cost after arbitrary unitary conjugation -/
open MeasureTheory Matrix Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
open ClockSpectrum SpectralApproximation
noncomputable section

private theorem spectrum_conjugate {I : Type*} [Fintype I] [DecidableEq I]
    (V : unitaryGroup I ℂ) (M : Matrix I I ℂ) :
    spectrum ℂ (V.val*M*star V.val)=spectrum ℂ M := by
  ext z
  simp only [Matrix.mem_spectrum_iff_isRoot_charpoly]
  rw [Matrix.charpoly_mul_comm (V.val*M),←mul_assoc,show star V.val*V.val=1 from V.property.1,one_mul]

/-- Seventeen separated physical eigenphases exclude two gates in every basis. -/
theorem two_gates_excluded {n : ℕ} (u : PathShell n) (t : ℝ)
    (f : Fin 17 → (Fin (n+2) → Bool)) (hf : ∀ i j, i≠j →
      (21/100:ℝ) ≤ ‖expTurns (physicalTurns u t (f i))-expTurns (physicalTurns u t (f j))‖) :
    ∀ W : unitaryGroup (Fin (n+2) → Bool) ℂ, ¬HasProjectiveCircuitApproximation (n+2) (1/10) 2
      (W.val*unitaryEvolution (pathHamiltonian u) t*star W.val) := by
  let U := unitaryEvolution (pathHamiltonian u) t
  let x := physicalTurns u t
  obtain ⟨V,hV⟩ := sorted_physical_diagonal u t (Equiv.refl _)
  have hspec : spectrum ℂ U=range (fun j => expTurns (x j)) := by
    calc spectrum ℂ U = spectrum ℂ (V.val*U*star V.val) := (spectrum_conjugate V U).symm
         _ = _ := by rw [hV]; exact spectrum_diagonal _
  intro W
  refine circuit_exclusion_of_separated_spectrum _ (fun i => expTurns (x (f i))) ?_
    (by norm_num : (1/10:ℝ) < 21/200) ?_ (by decide)
  · intro i
    rw [spectrum_conjugate,hspec]
    exact ⟨f i,rfl⟩
  · intro i j hij
    have h := hf i j hij
    change 21/100 ≤ ‖expTurns (x (f i))-expTurns (x (f j))‖ at h
    linarith only [h]

/-- On every compact interval separated from zero, the physical
minimum after a free unitary change of basis is eventually exactly
three at operator error 1/10, uniformly in the date. -/
theorem gaussian_exact_three_gates_after_conjugation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a T : ℝ, 0 < a → ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc a T,
      let U := unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t
      (∃ W : unitaryGroup (Fin (n+2) → Bool) ℂ,
        HasProjectiveCircuitApproximation (n+2) (1/10) 3 (W.val*U*star W.val)) ∧
      ∀ W : unitaryGroup (Fin (n+2) → Bool) ℂ,
        ¬HasProjectiveCircuitApproximation (n+2) (1/10) 2 (W.val*U*star W.val) := by
  filter_upwards [gaussian_three_gate_conjugate_upper,gaussian_seventeen_phases] with ω hup hsep
  intro a T ha
  filter_upwards [hup a T ha,hsep a T ha] with n hu hs
  intro t ht U
  refine ⟨hu t ht,?_⟩
  obtain ⟨f,hf⟩ := hs t ht
  exact two_gates_excluded _ t f hf

#print axioms gaussian_exact_three_gates_after_conjugation
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
