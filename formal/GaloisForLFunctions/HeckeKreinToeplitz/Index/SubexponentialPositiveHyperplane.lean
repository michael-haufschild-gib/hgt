import GaloisForLFunctions.HeckeKreinToeplitz.Index.IndexOneKernelDichotomy
import GaloisForLFunctions.HeckeKreinToeplitz.GrowthReadsTheDepthOfTheDeepestPair

/-!
# Unitary positive hyperplanes under cyclic subexponential growth

The index-one dichotomy leaves a single nonunitary hyperbolic pair as the
only obstruction to a unitary positive hyperplane. Such a pair has an outer
node on some cyclic subgroup. The existing non-cancellation growth theorem
excludes it under subexponential growth on that subgroup alone.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [CommGroup G] {k : G → ℂ}

/-- Cyclic subexponential growth forces a positive unitary-character mass hyperplane
for every abelian kernel of negative index at most one. -/
theorem exists_unitary_positive_hyperplane_of_cyclic_subexponential
    (hk : IsHermKernel k) (hi : negIndex k ≤ 1)
    (hsub : ∀ (g : G) (ε : ℝ), 0 < ε →
      ∃ C : ℝ, ∀ n : ℕ, ‖k (g ^ n)‖ ≤ C * Real.exp (ε * n)) :
    ∃ χ : G →* ℂ, IsUnitaryChar χ ∧ ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
      charEval χ x c = 0 → 0 ≤ hermQuad (gram k x) c := by
  classical
  rcases index_one_unitary_or_hyperbolic hk hi with hunit | ⟨p, χ, ω, hp, hχ, hω, hkdec⟩
  · exact hunit
  · exfalso
    have hnot : ¬ ∀ g, ‖χ g‖ = 1 := hχ
    obtain ⟨g, hg⟩ := not_forall.mp hnot
    have hsep : Function.Injective (nodes (fun _ : Fin 1 => χ) g) := by
      have hne := reflectChar_ne_of_norm_ne_one hg
      intro i j hij
      rcases i with i | i <;> rcases j with j | j <;>
        simp only [nodes, Sum.elim_inl, Sum.elim_inr] at hij <;>
        simp [Subsingleton.elim i j, hne, hne.symm] at hij ⊢
    obtain ⟨m, hm, _⟩ := exists_outer_node (χ := fun _ : Fin 1 => χ)
      (ω := fun _ => ω) (fun _ => hω) (fun _ => hg) 0
    obtain ⟨r, hr, hrm⟩ := exists_between hm
    obtain ⟨C, hC⟩ := hsub g (Real.log r) (Real.log_pos hr)
    have hexp (n : ℕ) : Real.exp (Real.log r * n) = r ^ n := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans hr)]
    apply not_norm_le_of_lt_depth hp (fun _ : Fin 1 => χ) (fun _ => ω)
      (fun _ => hω) g hsep hr.le hrm
    refine ⟨C, fun n => ?_⟩
    simpa only [Fin.sum_univ_one, hkdec, hexp] using hC n

#print axioms exists_unitary_positive_hyperplane_of_cyclic_subexponential

end GaloisForLFunctions.HeckeKreinToeplitz
