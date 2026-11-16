import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.FieldTheory.KummerPolynomial

/-!
# Filtered dimensions survive scalar specialization

The tensor product of `K[X]/(Xᵐ⁺¹-a)` and `K[Y]/(Yⁿ⁺¹-b)` has a rectangular
monomial basis. Every total-degree piece therefore has the same dimension
for all scalar parameters, including the nilpotent fiber `a=b=0` and
inseparable fibers. A basis-preserving linear equivalence realizes this
filtered invariance explicitly. This is a concrete complete-intersection
instance of the leading-symbol mechanism in Zehavi, Propositions 3.33–3.34,
arXiv:2611.18218.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting.Filtered

open Polynomial
open scoped TensorProduct

variable {K : Type*} [Field K]

/-- A scalar specialization of a monic power relation. -/
abbrev ScalarFiber (m : ℕ) (a : K) := AdjoinRoot (X ^ (m + 1) - C a)

/-- The power basis is present even at singular and inseparable parameters. -/
def scalarFiberBasis (m : ℕ) (a : K) : Module.Basis (Fin (m + 1)) K (ScalarFiber m a) :=
  (AdjoinRoot.powerBasis' (monic_X_pow_sub_C a (Nat.succ_ne_zero m))).basis.reindex
    (finCongr (by simp only [AdjoinRoot.powerBasis'_dim, natDegree_X_pow_sub_C]))

@[simp] theorem scalarFiberBasis_apply (m : ℕ) (a : K) (i : Fin (m + 1)) :
    scalarFiberBasis m a i = AdjoinRoot.root (X ^ (m + 1) - C a) ^ (i : ℕ) := by
  simp [scalarFiberBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]

/-- Reduction by the monic relation never increases a monomial's degree. -/
theorem scalarFiber_power_reduction (m : ℕ) (a : K) (k : ℕ) :
    AdjoinRoot.root (X ^ (m + 1) - C a) ^ k =
      a ^ (k / (m + 1)) • scalarFiberBasis m a
        ⟨k % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩ := by
  rw [scalarFiberBasis_apply]
  conv_lhs => rw [← Nat.mod_add_div k (m + 1), pow_add, pow_mul,
    root_X_pow_sub_C_pow]
  rw [Algebra.smul_def, map_pow]
  exact mul_comm _ _

/-- Two independent scalar power relations, realized as the tensor product of their quotients. -/
abbrev ScalarBox (m n : ℕ) (a b : K) := ScalarFiber m a ⊗[K] ScalarFiber n b

/-- The rectangular monomial basis of the two-relation quotient. -/
def scalarBoxBasis (m n : ℕ) (a b : K) :
    Module.Basis (Fin (m + 1) × Fin (n + 1)) K (ScalarBox m n a b) :=
  (scalarFiberBasis m a).tensorProduct (scalarFiberBasis n b)

@[simp] theorem scalarBoxBasis_apply (m n : ℕ) (a b : K)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    scalarBoxBasis m n a b (i, j) =
      (AdjoinRoot.root (X ^ (m + 1) - C a) ^ (i : ℕ)) ⊗ₜ[K]
        (AdjoinRoot.root (X ^ (n + 1) - C b) ^ (j : ℕ)) := by
  simp [scalarBoxBasis]

/-- The whole quotient has the expected complete-intersection dimension. -/
theorem scalarBox_finrank (m n : ℕ) (a b : K) :
    Module.finrank K (ScalarBox m n a b) = (m + 1) * (n + 1) := by
  rw [Module.finrank_eq_card_basis (scalarBoxBasis m n a b)]
  simp

/-- Monomials of total degree strictly below the cutoff. -/
abbrev ScalarBoxDegreeIndex (m n d : ℕ) :=
  {ij : Fin (m + 1) × Fin (n + 1) // (ij.1 : ℕ) + (ij.2 : ℕ) < d}

/-- The standard monomial filtration on a scalar-specialized quotient. -/
def scalarBoxFiltered (m n : ℕ) (a b : K) (d : ℕ) : Submodule K (ScalarBox m n a b) :=
  Submodule.span K (Set.range fun ij : ScalarBoxDegreeIndex m n d =>
    scalarBoxBasis m n a b ij.val)

/-- All monomials below the cutoff lie in the rectangular filtration, including unreduced powers. -/
theorem scalarBox_monomial_mem (m n : ℕ) (a b : K) (i j : ℕ) :
    (AdjoinRoot.root (X ^ (m + 1) - C a) ^ i) ⊗ₜ[K]
      (AdjoinRoot.root (X ^ (n + 1) - C b) ^ j) ∈ scalarBoxFiltered m n a b (i + j + 1) := by
  rw [scalarFiber_power_reduction, scalarFiber_power_reduction, TensorProduct.smul_tmul_smul]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨⟨(⟨i % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩,
    ⟨j % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩), ?_⟩, ?_⟩
  · have hi := Nat.mod_le i (m + 1)
    have hj := Nat.mod_le j (n + 1)
    change i % (m + 1) + j % (n + 1) < i + j + 1
    omega
  · exact Module.Basis.tensorProduct_apply _ _ _ _

/-- Increasing the cutoff enlarges the filtered space. -/
theorem scalarBoxFiltered_mono (m n : ℕ) (a b : K) :
    Monotone (scalarBoxFiltered m n a b) := by
  intro d e hde
  apply Submodule.span_mono
  rintro _ ⟨ij, rfl⟩
  exact ⟨⟨ij.val, lt_of_lt_of_le ij.property hde⟩, rfl⟩

/-- The standard-monomial filtration equals the actual total-degree monomial filtration. -/
theorem scalarBoxFiltered_eq_degree_span (m n : ℕ) (a b : K) (d : ℕ) :
    scalarBoxFiltered m n a b d = Submodule.span K
      (Set.range fun ij : {ij : ℕ × ℕ // ij.1 + ij.2 < d} =>
        (AdjoinRoot.root (X ^ (m + 1) - C a) ^ ij.val.1) ⊗ₜ[K]
          (AdjoinRoot.root (X ^ (n + 1) - C b) ^ ij.val.2)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨ij, rfl⟩
    apply Submodule.subset_span
    exact ⟨⟨((ij.val.1 : ℕ), (ij.val.2 : ℕ)), ij.property⟩,
      (scalarBoxBasis_apply m n a b ij.val.1 ij.val.2).symm⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨ij, rfl⟩
    exact scalarBoxFiltered_mono m n a b (Nat.succ_le_of_lt ij.property)
      (scalarBox_monomial_mem m n a b ij.val.1 ij.val.2)

/-- Every filtered dimension is an explicit lattice-point count independent of the parameters. -/
theorem scalarBoxFiltered_finrank (m n : ℕ) (a b : K) (d : ℕ) :
    Module.finrank K (scalarBoxFiltered m n a b d) =
      Fintype.card (ScalarBoxDegreeIndex m n d) := by
  exact finrank_span_eq_card
    ((scalarBoxBasis m n a b).linearIndependent.comp Subtype.val Subtype.val_injective)

/-- In particular, specializing both scalar parameters to zero preserves the full Hilbert function. -/
theorem scalarBoxFiltered_specialization (m n : ℕ) (a b : K) (d : ℕ) :
    Module.finrank K (scalarBoxFiltered m n a b d) =
      Module.finrank K (scalarBoxFiltered m n (0 : K) 0 d) := by
  rw [scalarBoxFiltered_finrank, scalarBoxFiltered_finrank]

/-- Coordinate transport between any two scalar fibers. -/
def scalarBoxTransport (m n : ℕ) (a b a' b' : K) :
    ScalarBox m n a b ≃ₗ[K] ScalarBox m n a' b' :=
  (scalarBoxBasis m n a b).equiv (scalarBoxBasis m n a' b') (Equiv.refl _)

/-- Coordinate transport preserves every total-degree filtered piece. -/
theorem scalarBoxTransport_filtered (m n : ℕ) (a b a' b' : K) (d : ℕ) :
    (scalarBoxFiltered m n a b d).map (scalarBoxTransport m n a b a' b').toLinearMap =
      scalarBoxFiltered m n a' b' d := by
  unfold scalarBoxFiltered
  rw [Submodule.map_span, ← Set.range_comp]
  apply congrArg (Submodule.span K)
  apply congrArg Set.range
  funext ij
  exact Module.Basis.equiv_apply _ _ _ _

end GaloisForLFunctions.RepresentationLifting.Filtered

#print axioms GaloisForLFunctions.RepresentationLifting.Filtered.scalarBox_finrank
#print axioms GaloisForLFunctions.RepresentationLifting.Filtered.scalarBoxFiltered_eq_degree_span
#print axioms GaloisForLFunctions.RepresentationLifting.Filtered.scalarBoxFiltered_specialization
#print axioms GaloisForLFunctions.RepresentationLifting.Filtered.scalarBoxTransport_filtered
