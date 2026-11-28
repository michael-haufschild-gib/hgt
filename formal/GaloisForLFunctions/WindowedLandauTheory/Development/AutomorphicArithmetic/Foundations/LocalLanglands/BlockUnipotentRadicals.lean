import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.Tactic.NoncommRing

/-! The unipotent radical in block coordinates consists of invertible
matrices whose difference from the identity has strictly upper
block support. Cuspidality is the vanishing of its coinvariants at
each proper splitting. -/

noncomputable section

open Matrix Representation

namespace GlobalTheory.GLp

section Radical

variable (k : Type) [Field k] {N : ℕ}

def IsStrictBlockUpper {k : Type} [Field k] (b : Fin N → ℕ) (X : Matrix (Fin N) (Fin N) k) : Prop :=
  ∀ i j, b j ≤ b i → X i j = 0

variable {k}

theorem IsStrictBlockUpper.mul_blockTriangular {b : Fin N → ℕ} {X Y : Matrix (Fin N) (Fin N) k}
    (hX : IsStrictBlockUpper b X) (hY : Y.BlockTriangular b) : IsStrictBlockUpper b (X * Y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : b l ≤ b i
  · rw [hX i l hl, zero_mul]
  · rw [hY (lt_of_le_of_lt hij (not_le.mp hl)), mul_zero]

theorem blockTriangular_of_sub_one {b : Fin N → ℕ} {X : Matrix (Fin N) (Fin N) k}
    (hX : IsStrictBlockUpper b (X - 1)) : X.BlockTriangular b := by
  intro i j hij
  have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
  have h := hX i j hij.le
  rwa [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at h

variable (k)

def blockUnipotentRadical (b : Fin N → ℕ) : Subgroup (GL (Fin N) k) where
  carrier := {u | IsStrictBlockUpper b ((u : Matrix (Fin N) (Fin N) k) - 1)}
  one_mem' := by
    intro i j _
    simp
  mul_mem' := by
    intro u v hu hv i j hij
    have e : ((u * v : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1 =
        ((u : Matrix (Fin N) (Fin N) k) - 1) * (v : Matrix (Fin N) (Fin N) k) +
          ((v : Matrix (Fin N) (Fin N) k) - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [e, Matrix.add_apply, (IsStrictBlockUpper.mul_blockTriangular hu (blockTriangular_of_sub_one hv)) i j hij,
      hv i j hij, add_zero]
  inv_mem' := by
    intro u hu i j hij
    letI := u.invertible
    have hi : ((u⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).BlockTriangular b := by
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular (blockTriangular_of_sub_one hu)
    have e : ((u⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1 =
        -(((u : Matrix (Fin N) (Fin N) k) - 1) * ((u⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)) := by
      rw [sub_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul, neg_sub]
    rw [e, Matrix.neg_apply, (IsStrictBlockUpper.mul_blockTriangular hu hi) i j hij, neg_zero]

variable {k}

theorem mem_blockUnipotentRadical {b : Fin N → ℕ} {u : GL (Fin N) k} :
    u ∈ blockUnipotentRadical k b ↔ ∀ i j, b j ≤ b i → ((u : Matrix (Fin N) (Fin N) k) - 1) i j = 0 := Iff.rfl


variable [TopologicalSpace k] {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Smooth representations with zero Jacquet modules for all proper block parabolics. -/
def IsSmoothCuspidal (ρ : Representation ℂ (GL (Fin N) k) V) : Prop :=
  (∀ v : V, IsOpen {g : GL (Fin N) k | ρ g v = v}) ∧
    ∀ b : Fin N → ℕ, (∃ i j, b i < b j) →
      Coinvariants.ker (ρ.comp (blockUnipotentRadical k b).subtype) = ⊤

end Radical

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.blockUnipotentRadical
