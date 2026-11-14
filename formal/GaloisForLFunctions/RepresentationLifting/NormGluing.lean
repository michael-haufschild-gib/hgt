import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Integral gluing of invariants and the norm kernel

For a finite group action, the sum of the invariant module and the norm kernel
contains every multiple by the group order. Membership in this sum is detected
by divisibility of the norm inside the invariant module. These are the
module-theoretic statements in Auel–Shaikh, Lemma 1.1(d,e)
(https://arxiv.org/abs/2611.13468); they need neither a bilinear form nor freeness.
The norm kernel agrees with the orthogonal coinvariant lattice in their setting.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

variable {k G V : Type*} [CommRing k] [Group G] [Fintype G]
  [AddCommGroup V] [Module k V]

/-- The integral sum before dividing by the group order. -/
def normGluingSubmodule (ρ : Representation k G V) : Submodule k V :=
  ρ.invariants ⊔ LinearMap.ker ρ.norm

/-- Applying the norm twice multiplies it by the group order. -/
theorem norm_norm_eq_card_smul (ρ : Representation k G V) (v : V) :
    ρ.norm (ρ.norm v) = (Fintype.card G : k) • ρ.norm v := by
  have happ (x : V) : ρ.norm x = ∑ g : G, ρ g x := by
    simp only [Representation.norm, LinearMap.sum_apply]
  rw [happ (ρ.norm v)]
  simp only [Representation.self_norm_apply]
  simp [Nat.cast_smul_eq_nsmul]

/-- The norm of an invariant vector is its group-order multiple. -/
theorem norm_invariant_eq_card_smul (ρ : Representation k G V) (v : ρ.invariants) :
    ρ.norm v = (Fintype.card G : k) • (v : V) := by
  have hv : ∀ g, ρ g (v : V) = (v : V) := v.property
  simp only [Representation.norm, LinearMap.sum_apply, hv]
  simp [Nat.cast_smul_eq_nsmul]

/-- Group-order multiplication splits explicitly into an invariant and a norm-zero part. -/
theorem card_smul_mem_normGluingSubmodule (ρ : Representation k G V) (v : V) :
    (Fintype.card G : k) • v ∈ normGluingSubmodule ρ := by
  refine Submodule.mem_sup.mpr ⟨ρ.norm v, ?_,
    (Fintype.card G : k) • v - ρ.norm v, ?_, by abel⟩
  · exact fun g => Representation.self_norm_apply ρ g v
  · change ρ.norm ((Fintype.card G : k) • v - ρ.norm v) = 0
    rw [map_sub, map_smul, norm_norm_eq_card_smul, sub_self]

/-- The gluing quotient is annihilated by the group order. -/
theorem normGluingQuotient_card_smul (ρ : Representation k G V)
    (q : V ⧸ normGluingSubmodule ρ) : (Fintype.card G : k) • q = 0 := by
  induction q using Submodule.Quotient.induction_on with
  | H v =>
    change (normGluingSubmodule ρ).mkQ ((Fintype.card G : k) • v) = 0
    change (Fintype.card G : k) • v ∈ LinearMap.ker (normGluingSubmodule ρ).mkQ
    rw [Submodule.ker_mkQ]
    exact card_smul_mem_normGluingSubmodule ρ v

/-- Divisibility of the norm in the invariant module detects the full gluing submodule. -/
theorem mem_normGluingSubmodule_iff (ρ : Representation k G V) (v : V) :
    v ∈ normGluingSubmodule ρ ↔
      ∃ w : ρ.invariants, ρ.norm v = (Fintype.card G : k) • (w : V) := by
  constructor
  · intro hv
    obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
    refine ⟨⟨w, hw⟩, ?_⟩
    rw [map_add, show ρ.norm z = 0 from hz, add_zero]
    exact norm_invariant_eq_card_smul ρ ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    refine Submodule.mem_sup.mpr ⟨w, w.property, v - w, ?_, by abel⟩
    change ρ.norm (v - w) = 0
    rw [map_sub, hw, norm_invariant_eq_card_smul, sub_self]

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.normGluingQuotient_card_smul
#print axioms GaloisForLFunctions.RepresentationLifting.mem_normGluingSubmodule_iff
