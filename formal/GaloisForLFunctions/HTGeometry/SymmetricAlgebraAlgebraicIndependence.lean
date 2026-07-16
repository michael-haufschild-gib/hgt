import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Algebraic independence in a symmetric observable algebra

The canonical degree-one images of a family of state vectors in a symmetric algebra are
algebraically independent exactly when the state vectors are linearly independent.  The forward
direction extracts a linear relation from a polynomial relation.  The reverse direction extends a
linearly independent family to a split linear coordinate system and uses the universal property of
the symmetric algebra to retract it onto an independent polynomial-variable family.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

variable {K : Type u} {M : Type v} {α : Type w}
  [Field K] [AddCommGroup M] [Module K M]

/-- A linearly independent state family becomes algebraically independent after the canonical
embedding into its symmetric observable algebra. -/
theorem symmetricAlgebra_ι_algebraicIndependent_of_linearIndependent
    (q : α → M) (hq : LinearIndependent K q) :
    AlgebraicIndependent K (fun a => SymmetricAlgebra.ι K M (q a)) := by
  let F : (α →₀ K) →ₗ[K] M := Finsupp.linearCombination K q
  have hF : LinearMap.ker F = ⊥ :=
    LinearMap.ker_eq_bot.mpr hq.finsuppLinearCombination_injective
  obtain ⟨g, hg⟩ := F.exists_leftInverse_of_injective hF
  let L : M →ₗ[K] MvPolynomial α K :=
    (Finsupp.linearCombination K (MvPolynomial.X : α → MvPolynomial α K)).comp g
  let Φ : SymmetricAlgebra K M →ₐ[K] MvPolynomial α K := SymmetricAlgebra.lift L
  apply AlgebraicIndependent.of_comp Φ
  have hΦ : Φ ∘ (fun a => SymmetricAlgebra.ι K M (q a)) =
      (MvPolynomial.X : α → MvPolynomial α K) := by
    funext a
    have hga : g (q a) = Finsupp.single a 1 := by
      have hpoint := LinearMap.congr_fun hg (Finsupp.single a 1)
      simpa [F, Finsupp.linearCombination_single] using hpoint
    simp [Φ, L, SymmetricAlgebra.lift_ι_apply, hga,
      Finsupp.linearCombination_single]
  rw [hΦ]
  exact MvPolynomial.algebraicIndependent_X α K

/-- **Symmetric observable criterion.**  A state family is linearly independent if and only if its
canonical degree-one observables are algebraically independent. -/
theorem symmetricAlgebra_ι_algebraicIndependent_iff_linearIndependent
    (q : α → M) :
    AlgebraicIndependent K (fun a => SymmetricAlgebra.ι K M (q a)) ↔
      LinearIndependent K q := by
  constructor
  · intro hAI
    rw [linearIndependent_iff_injective_finsuppLinearCombination]
    intro c e hce
    apply (MvPolynomial.linearIndependent_X (σ := α) (R := K)).finsuppLinearCombination_injective
    apply hAI
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
    simp only [Finsupp.sum, map_sum, map_smul, MvPolynomial.aeval_X]
    have hi := congrArg (SymmetricAlgebra.ι K M) hce
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply] at hi
    simpa only [Finsupp.sum, map_sum, map_smul] using hi
  · exact symmetricAlgebra_ι_algebraicIndependent_of_linearIndependent q

end

end GaloisForLFunctions.HTGeometry
