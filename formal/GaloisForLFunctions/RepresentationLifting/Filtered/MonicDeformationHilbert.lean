import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Hilbert functions under arbitrary monic coefficient deformation

Two independent monic relations have a rectangular power basis. Their
total-degree filtration is spanned by the same rectangle below each
diagonal, regardless of any lower coefficient. This includes multiple-root
and inseparable fibers. Coordinate transport preserves the full filtration,
although it need not preserve multiplication.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.Filtered
open Polynomial
open scoped TensorProduct

variable {K : Type*} [Field K]

/-- All monic degree-(m+1) relations, parametrized by their lower coefficients. -/
def monicRelation (m : ℕ) (a : Fin (m + 1) → K) : K[X] :=
  ((monicEquivDegreeLT (m + 1)).symm ((degreeLTEquiv K (m + 1)).symm a)).val

theorem monicRelation_monic (m : ℕ) (a : Fin (m + 1) → K) :
    (monicRelation m a).Monic :=
  ((monicEquivDegreeLT (m + 1)).symm ((degreeLTEquiv K (m + 1)).symm a)).property.1

theorem monicRelation_natDegree (m : ℕ) (a : Fin (m + 1) → K) :
    (monicRelation m a).natDegree = m + 1 :=
  ((monicEquivDegreeLT (m + 1)).symm ((degreeLTEquiv K (m + 1)).symm a)).property.2

@[simp] theorem monicRelation_zero (m : ℕ) :
    monicRelation m (0 : Fin (m + 1) → K) = X ^ (m + 1) := by
  change X ^ (m + 1) + (((degreeLTEquiv K (m + 1)).symm 0 : degreeLT K (m + 1)) : K[X]) = _
  rw [map_zero]
  exact add_zero _

/-- The actual quotient by a freely chosen monic relation. -/
abbrev MonicFiber (m : ℕ) (a : Fin (m + 1) → K) := AdjoinRoot (monicRelation m a)

/-- The root powers form a basis in every fiber. -/
def monicFiberBasis (m : ℕ) (a : Fin (m + 1) → K) :
    Module.Basis (Fin (m + 1)) K (MonicFiber m a) :=
  (AdjoinRoot.powerBasis' (monicRelation_monic m a)).basis.reindex
    (finCongr (by rw [AdjoinRoot.powerBasis'_dim, monicRelation_natDegree]))

@[simp] theorem monicFiberBasis_apply (m : ℕ) (a : Fin (m + 1) → K) (i : Fin (m + 1)) :
    monicFiberBasis m a i = AdjoinRoot.root (monicRelation m a) ^ (i : ℕ) := by
  simp [monicFiberBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]

/-- Reduction by an arbitrary monic relation never raises a power's degree. -/
theorem monicFiber_power_mem (m : ℕ) (a : Fin (m + 1) → K) (k : ℕ) :
    AdjoinRoot.root (monicRelation m a) ^ k ∈ Submodule.span K
      (Set.range fun i : {i : Fin (m + 1) // (i : ℕ) ≤ k} => monicFiberBasis m a i.val) := by
  by_cases hk : k < m + 1
  · apply Submodule.subset_span
    exact ⟨⟨⟨k, hk⟩, le_rfl⟩, monicFiberBasis_apply m a ⟨k, hk⟩⟩
  · have htop : (⊤ : Submodule K (MonicFiber m a)) ≤ Submodule.span K
        (Set.range fun i : {i : Fin (m + 1) // (i : ℕ) ≤ k} => monicFiberBasis m a i.val) := by
      rw [← (monicFiberBasis m a).span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply Submodule.subset_span
      exact ⟨⟨i, by have := i.isLt; omega⟩, rfl⟩
    exact htop trivial

abbrev MonicBox (m n : ℕ) (a : Fin (m + 1) → K) (b : Fin (n + 1) → K) :=
  MonicFiber m a ⊗[K] MonicFiber n b

def monicBoxBasis (m n : ℕ) (a : Fin (m + 1) → K) (b : Fin (n + 1) → K) :
    Module.Basis (Fin (m + 1) × Fin (n + 1)) K (MonicBox m n a b) :=
  (monicFiberBasis m a).tensorProduct (monicFiberBasis n b)

abbrev MonicBoxDegreeIndex (m n d : ℕ) :=
  {ij : Fin (m + 1) × Fin (n + 1) // (ij.1 : ℕ) + (ij.2 : ℕ) < d}

/-- The rectangle of standard monomials below the total-degree cutoff. -/
def monicBoxFiltered (m n : ℕ) (a : Fin (m + 1) → K) (b : Fin (n + 1) → K)
    (d : ℕ) : Submodule K (MonicBox m n a b) :=
  Submodule.span K (Set.range fun ij : MonicBoxDegreeIndex m n d => monicBoxBasis m n a b ij.val)

/-- Even unreduced tensor monomials belong to the expected filtered piece. -/
theorem monicBox_monomial_mem (m n : ℕ) (a : Fin (m + 1) → K) (b : Fin (n + 1) → K)
    (i j : ℕ) :
    (AdjoinRoot.root (monicRelation m a) ^ i) ⊗ₜ[K]
      (AdjoinRoot.root (monicRelation n b) ^ j) ∈ monicBoxFiltered m n a b (i + j + 1) := by
  let F := monicBoxFiltered m n a b (i + j + 1)
  have hleft := monicFiber_power_mem m a i
  have hright := monicFiber_power_mem n b j
  refine Submodule.span_induction (p := fun u _ =>
    u ⊗ₜ[K] (AdjoinRoot.root (monicRelation n b) ^ j) ∈ F) ?_ ?_ ?_ ?_ hleft
  · rintro _ ⟨u, rfl⟩
    refine Submodule.span_induction (p := fun v _ =>
      monicFiberBasis m a u.val ⊗ₜ[K] v ∈ F) ?_ ?_ ?_ ?_ hright
    · rintro _ ⟨v, rfl⟩
      apply Submodule.subset_span
      refine ⟨⟨(u.val, v.val), ?_⟩, ?_⟩
      · have hu := u.property
        have hv := v.property
        change (u.val : ℕ) + (v.val : ℕ) < i + j + 1
        omega
      · exact Module.Basis.tensorProduct_apply _ _ _ _
    · simpa only [TensorProduct.tmul_zero] using F.zero_mem
    · intro x y hx hy hfx hfy
      simpa only [TensorProduct.tmul_add] using F.add_mem hfx hfy
    · intro c x hx hfx
      simpa only [TensorProduct.tmul_smul] using F.smul_mem c hfx
  · simpa only [TensorProduct.zero_tmul] using F.zero_mem
  · intro x y hx hy hfx hfy
    simpa only [TensorProduct.add_tmul] using F.add_mem hfx hfy
  · intro c x hx hfx
    simpa only [TensorProduct.smul_tmul, TensorProduct.tmul_smul] using F.smul_mem c hfx

theorem monicBoxFiltered_mono (m n : ℕ) (a : Fin (m + 1) → K) (b : Fin (n + 1) → K) :
    Monotone (monicBoxFiltered m n a b) := by
  intro d e hde
  apply Submodule.span_mono
  rintro _ ⟨ij, rfl⟩
  exact ⟨⟨ij.val, lt_of_lt_of_le ij.property hde⟩, rfl⟩

/-- The coordinate filtration equals the image of the actual polynomial degree filtration. -/
theorem monicBoxFiltered_eq_degree_span (m n : ℕ) (a : Fin (m + 1) → K)
    (b : Fin (n + 1) → K) (d : ℕ) :
    monicBoxFiltered m n a b d = Submodule.span K
      (Set.range fun ij : {ij : ℕ × ℕ // ij.1 + ij.2 < d} =>
        (AdjoinRoot.root (monicRelation m a) ^ ij.val.1) ⊗ₜ[K]
          (AdjoinRoot.root (monicRelation n b) ^ ij.val.2)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨ij, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨((ij.val.1 : ℕ), (ij.val.2 : ℕ)), ij.property⟩, ?_⟩
    change _ = ((monicFiberBasis m a).tensorProduct (monicFiberBasis n b)) (ij.val.1, ij.val.2)
    rw [Module.Basis.tensorProduct_apply, monicFiberBasis_apply, monicFiberBasis_apply]
  · apply Submodule.span_le.mpr
    rintro _ ⟨ij, rfl⟩
    exact monicBoxFiltered_mono m n a b (Nat.succ_le_of_lt ij.property)
      (monicBox_monomial_mem m n a b ij.val.1 ij.val.2)

/-- Every Hilbert value is independent of every lower coefficient in both relations. -/
theorem monicBoxFiltered_finrank (m n : ℕ) (a : Fin (m + 1) → K)
    (b : Fin (n + 1) → K) (d : ℕ) :
    Module.finrank K (monicBoxFiltered m n a b d) =
      Fintype.card (MonicBoxDegreeIndex m n d) :=
  finrank_span_eq_card
    ((monicBoxBasis m n a b).linearIndependent.comp Subtype.val Subtype.val_injective)

/-- Transport to the nilpotent fiber preserves the full Hilbert function. -/
theorem monicBoxFiltered_specialization (m n : ℕ) (a : Fin (m + 1) → K)
    (b : Fin (n + 1) → K) (d : ℕ) :
    Module.finrank K (monicBoxFiltered m n a b d) =
      Module.finrank K (monicBoxFiltered m n (0 : Fin (m + 1) → K) 0 d) := by
  rw [monicBoxFiltered_finrank, monicBoxFiltered_finrank]

/-- A basis-preserving transport between arbitrary monic fibers. -/
def monicBoxTransport (m n : ℕ) (a a' : Fin (m + 1) → K) (b b' : Fin (n + 1) → K) :
    MonicBox m n a b ≃ₗ[K] MonicBox m n a' b' :=
  (monicBoxBasis m n a b).equiv (monicBoxBasis m n a' b') (Equiv.refl _)

theorem monicBoxTransport_filtered (m n : ℕ) (a a' : Fin (m + 1) → K)
    (b b' : Fin (n + 1) → K) (d : ℕ) :
    (monicBoxFiltered m n a b d).map (monicBoxTransport m n a a' b b').toLinearMap =
      monicBoxFiltered m n a' b' d := by
  unfold monicBoxFiltered
  rw [Submodule.map_span, ← Set.range_comp]
  apply congrArg (Submodule.span K)
  apply congrArg Set.range
  funext ij
  exact Module.Basis.equiv_apply _ _ _ _

end GaloisForLFunctions.RepresentationLifting.Filtered

#print axioms GaloisForLFunctions.RepresentationLifting.Filtered.monicBoxFiltered_eq_degree_span
#print axioms GaloisForLFunctions.RepresentationLifting.Filtered.monicBoxFiltered_specialization
#print axioms GaloisForLFunctions.RepresentationLifting.Filtered.monicBoxTransport_filtered

