import GaloisForLFunctions.HTGeometry.GroupCharacter.FDRepBridge
import GaloisForLFunctions.HTGeometry.GroupCharacter.TrivialSummand

/-!
# Multiplicities in the regular representation

Each simple summand of `ℂ[G]` occurs exactly `finrank ℂ` times.  This is the ingredient that turns
the raw column-orthogonality identity into the classical `1 + ∑_{χ ≠ 1} χ(1) χ(g) = 0`.
-/

namespace GaloisForLFunctions.HTGeometry.GroupCharacter

open MonoidAlgebra CategoryTheory

variable {G : Type} [Group G] [Fintype G]

open scoped Classical in
/-- **The multiplicity of a simple summand of `ℂ[G]` is its dimension.** -/
theorem card_iso_eq_finrank [DecidableEq G] {n : ℕ}
    {N : Fin n → Submodule ℂ (MonoidAlgebra ℂ G)}
    (hN : ∀ i, IsMinimalGStable (N i)) (hint : DirectSum.IsInternal N) (i : Fin n) :
    (Finset.univ.filter
        fun j : Fin n => Nonempty (fdRepOf (hN j).stable ≅ fdRepOf (hN i).stable)).card
      = Module.finrank ℂ ↥(N i) := by
  classical
  have hcard : ((Fintype.card G : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  haveI : Invertible ((Nat.card G : ℂ)) := by
    refine invertibleOfNonzero ?_
    rwa [Nat.card_eq_fintype_card]
  have key : ∀ j : Fin n,
      (if Nonempty (fdRepOf (hN j).stable ≅ fdRepOf (hN i).stable) then (1 : ℂ) else 0)
        = (Nat.card G : ℂ)⁻¹ * ∑ g : G, chi (hN j).stable g * chi (hN i).stable g⁻¹ := by
    intro j
    haveI := simple_fdRepOf (hN i)
    haveI := simple_fdRepOf (hN j)
    have h := FDRep.char_orthonormal (fdRepOf (hN j).stable) (fdRepOf (hN i).stable)
    simp only [character_fdRepOf] at h
    rw [h]
  have hsum : ∑ j : Fin n,
      (if Nonempty (fdRepOf (hN j).stable ≅ fdRepOf (hN i).stable) then (1 : ℂ) else 0)
      = (Module.finrank ℂ ↥(N i) : ℂ) := by
    rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum]
    have hswap : ∑ j : Fin n, ∑ g : G, chi (hN j).stable g * chi (hN i).stable g⁻¹
        = ∑ g : G, (∑ j : Fin n, chi (hN j).stable g) * chi (hN i).stable g⁻¹ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun g _ => (Finset.sum_mul _ _ _).symm
    rw [hswap, Finset.sum_congr rfl
      (fun g _ => by rw [sum_chi (fun j => (hN j).stable) hint g])]
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ (1 : G)
      (fun g => (Fintype.card G : ℂ) * chi (hN i).stable g⁻¹)]
    simp only [Finset.mem_univ, if_pos, inv_one]
    rw [chi_one, Nat.card_eq_fintype_card]
    field_simp
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_zero, add_zero, nsmul_eq_mul,
    mul_one] at hsum
  exact_mod_cast hsum

end GaloisForLFunctions.HTGeometry.GroupCharacter
