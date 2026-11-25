import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.Projection
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.ComplexSystem

/-! # Finite certificates after eliminating every real witness -/

open Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
noncomputable section

theorem finite_exists_fin (n : ℕ) {A X : Type*} [CommRing A] [TopologicalSpace X]
    (ρ : X → A →+* ℝ) (hc : ∀ a, Continuous fun x => ρ x a) (p : MvPolynomial (Fin n) A) :
    FinitelyCertified ρ {x | ∃ w : Fin n → ℝ, MvPolynomial.eval₂Hom (ρ x) w p=0} := by
  classical
  induction n generalizing A X with
  | zero =>
    let a := MvPolynomial.eval (fun i : Fin 0 => i.elim0) p
    refine ⟨{a},?_⟩
    rintro x ⟨w,hw⟩
    exact ⟨a,Finset.mem_singleton_self a,(eval_empty_witness p (ρ x) w).trans hw,
      Eventually.of_forall fun z hz => ⟨w,(eval_empty_witness p (ρ z) w).symm.trans hz⟩⟩
  | succ n ih =>
    rw [←exists_move_head ρ p]
    exact (ih (appendEval ρ) (continuous_appendEval ρ hc) (move_head A n p)).fst_image hc

/-- Split into real residuals, number the witness variables and project
a single real sum of squares. Each elimination preserves finiteness. -/
theorem finite_complex_system {A X ι κ : Type*} [CommRing A] [TopologicalSpace X] [Fintype ι] [Fintype κ]
    (ρ : X → A →+* ℝ) (hc : ∀ a, Continuous fun x => ρ x a)
    (F : κ → X × (ι → ℝ) → ℂ) (hF : ∀ k, ComplexRep (witnessEval ρ) (F k)) :
    FinitelyCertified ρ {x | ∃ w : ι → ℝ, ∀ k, F k (x,w)=0} := by
  obtain ⟨p,hp⟩ := exists_real_residual_system ρ F hF
  obtain ⟨q,hq⟩ := system_eq_single_fin ρ p
  rw [hp,hq]
  exact finite_exists_fin _ ρ hc q

#print axioms finite_complex_system
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
