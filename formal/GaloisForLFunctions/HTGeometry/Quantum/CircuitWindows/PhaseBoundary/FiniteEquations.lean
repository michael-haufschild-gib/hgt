import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.WitnessVariables
import Mathlib.Algebra.MvPolynomial.Rename

/-! # Projected real polynomial equations with arbitrary finite coordinate labels -/
open Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
noncomputable section

/-- A finite system can be represented by the sum of the real squares of
its equations. Relabeling the witnesses allows matrix and gate indices. -/
theorem certified_exists_system {A X ι κ : Type*} [CommRing A] [TopologicalSpace X]
    [Fintype ι] [Fintype κ] (ρ : X → A →+* ℝ) (hc : ∀ a, Continuous fun x => ρ x a)
    (p : κ → MvPolynomial ι A) : LocallyCertified ρ
      {x | ∃ w : ι → ℝ, ∀ k, MvPolynomial.eval₂Hom (ρ x) w (p k) = 0} := by
  classical
  let e := Fintype.equivFin ι
  let q := ∑ k, (MvPolynomial.rename e (p k))^2
  have hev (φ : A →+* ℝ) (w : Fin (Fintype.card ι) → ℝ) (k : κ) :
      MvPolynomial.eval₂Hom φ w (MvPolynomial.rename e (p k)) =
        MvPolynomial.eval₂Hom φ (w ∘ e) (p k) := by
    exact MvPolynomial.eval₂Hom_rename _ _ _ _
  have hzero (x : X) (w : Fin (Fintype.card ι) → ℝ) :
      MvPolynomial.eval₂Hom (ρ x) w q = 0 ↔ ∀ k, MvPolynomial.eval₂Hom (ρ x) (w ∘ e) (p k) = 0 := by
    simp only [q,map_sum,map_pow,hev,Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _),
      Finset.mem_univ,true_implies]
    simp
  have heq : {x | ∃ w : ι → ℝ, ∀ k, MvPolynomial.eval₂Hom (ρ x) w (p k) = 0} =
      {x | ∃ w : Fin (Fintype.card ι) → ℝ, MvPolynomial.eval₂Hom (ρ x) w q = 0} := by
    ext x
    constructor
    · rintro ⟨v,hv⟩
      exact ⟨v ∘ e.symm,(hzero ..).2 (by simpa [Function.comp_def] using hv)⟩
    · rintro ⟨w,hw⟩
      exact ⟨w ∘ e,(hzero ..).1 hw⟩
  rw [heq]
  exact certified_exists_fin _ ρ hc q

end
end GaloisForLFunctions.HTGeometry.PhaseBoundary
