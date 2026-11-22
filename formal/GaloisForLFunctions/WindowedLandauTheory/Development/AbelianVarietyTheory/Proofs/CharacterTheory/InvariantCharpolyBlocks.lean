import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobius
import Mathlib.LinearAlgebra.Trace

/-! Factor the characteristic polynomial along an invariant subspace and its quotient. -/

namespace GlobalTheory.CuspGL

open Module Module.Basis

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]

/-- Endomorphisms that factor through the quotient by the subspace into the subspace. -/
def nilRad (A : Submodule F V) : Set (Module.End F V) :=
  {h | (∀ x, h x ∈ A) ∧ ∀ x ∈ A, h x = 0}

/-- A primitive class function has zero average over every proper nonzero parabolic nilradical. -/
def IsPrimitive (φ : Module.End F V → ℂ) : Prop :=
  ∀ A : Submodule F V, A ≠ ⊥ → A ≠ ⊤ → ∀ g : Module.End F V, (∀ x ∈ A, g x ∈ A) →
    ∑ᶠ h ∈ nilRad A, φ (g + h) = 0

private theorem invariant_matrix_blocks (A : Submodule F V) (g : Module.End F V)
    (hg : ∀ x ∈ A, g x ∈ A) (bA : Basis (Fin (finrank F A)) F A)
    (bQ : Basis (Fin (finrank F (V ⧸ A))) F (V ⧸ A)) :
    let b := bA.sumQuot bQ
    LinearMap.toMatrix b b g = Matrix.fromBlocks (LinearMap.toMatrix bA bA (g.restrict hg))
      (Matrix.of fun i j => b.repr (g (b (Sum.inr j))) (Sum.inl i)) 0
      (LinearMap.toMatrix bQ bQ (A.mapQ A g (fun x hx => hg x hx))) := by
  dsimp only
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₁, sumQuot_inl]
    rw [sumQuot_repr_inl_of_mem bA bQ _ (hg _ (bA j).2)]
    rfl
  · simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
  · simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₂₁, sumQuot_inl, Matrix.zero_apply]
    exact sumQuot_repr_inr_of_mem bA bQ _ (hg _ (bA j).2) i
  · simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₂₂]
    rw [sumQuot_repr_inr, ← sumQuot_inr bA bQ j, Submodule.mapQ_apply]
    rfl

variable [FiniteDimensional F V]

/-- A basis extending a basis of the invariant subspace gives a block triangular matrix. -/
theorem charpoly_eq_restrict_mul_mapQ (A : Submodule F V) (g : Module.End F V)
    (hg : ∀ x ∈ A, g x ∈ A) :
    g.charpoly = (g.restrict hg).charpoly * (A.mapQ A g (fun x hx => hg x hx)).charpoly := by
  let bA := Module.finBasis F A
  let bQ := Module.finBasis F (V ⧸ A)
  rw [← LinearMap.charpoly_toMatrix g (bA.sumQuot bQ), invariant_matrix_blocks A g hg bA bQ,
    Matrix.charpoly_fromBlocks_zero₂₁,
    LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]

/-- The trace is the sum of the traces on the invariant subspace and its quotient. -/
theorem trace_eq_restrict_add_mapQ (A : Submodule F V) (g : Module.End F V)
    (hg : ∀ x ∈ A, g x ∈ A) :
    LinearMap.trace F V g = LinearMap.trace F A (g.restrict hg) +
      LinearMap.trace F (V ⧸ A) (A.mapQ A g (fun x hx => hg x hx)) := by
  let bA := Module.finBasis F A
  let bQ := Module.finBasis F (V ⧸ A)
  rw [LinearMap.trace_eq_matrix_trace F (bA.sumQuot bQ) g, invariant_matrix_blocks A g hg bA bQ,
    LinearMap.trace_eq_matrix_trace F bA, LinearMap.trace_eq_matrix_trace F bQ]
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

/-- A nilradical translate changes only the off-diagonal block. -/
theorem charpoly_add_nilRad (A : Submodule F V) (g : Module.End F V)
    (hg : ∀ x ∈ A, g x ∈ A) {h : Module.End F V} (hh : h ∈ nilRad A) :
    (g + h).charpoly = g.charpoly := by
  obtain ⟨himg, hker⟩ := hh
  have hgh : ∀ x ∈ A, (g + h) x ∈ A := fun x hx => by
    simpa only [LinearMap.add_apply, hker x hx, add_zero] using hg x hx
  have hres : (g + h).restrict hgh = g.restrict hg := by
    ext x
    simp [LinearMap.restrict_apply, hker x x.2]
  have hquot : A.mapQ A (g + h) (fun x hx => hgh x hx) = A.mapQ A g (fun x hx => hg x hx) := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq]
    simpa [LinearMap.add_apply] using himg x
  rw [charpoly_eq_restrict_mul_mapQ A (g + h) hgh, charpoly_eq_restrict_mul_mapQ A g hg, hres, hquot]

end GlobalTheory.CuspGL
