import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Reduced residues and additive antidiagonals

For a modulus greater than one, the canonical representatives of a unit
and its negative add to the modulus. This bijection transfers arbitrary
weighted correlations between reduced residues and natural-number pairs.
-/

namespace GaloisForLFunctions.Goldbach

open Finset
open scoped Classical

noncomputable section

/-- Representatives of opposite units add to the modulus when the modulus exceeds one. -/
theorem unit_val_add_neg_val (N : ℕ) (u : (ZMod (N + 2))ˣ) :
    (u : ZMod (N + 2)).val + ((-u : (ZMod (N + 2))ˣ) : ZMod (N + 2)).val = N + 2 := by
  have hu : (u : ZMod (N + 2)) ≠ 0 := by
    intro h
    have hc := ZMod.val_coe_unit_coprime u
    rw [h, ZMod.val_zero, Nat.coprime_zero_left] at hc
    omega
  rw [Units.val_neg, ZMod.neg_val, if_neg hu]
  exact Nat.add_sub_of_le (ZMod.val_le _)

/-- Negation on units enumerates exactly the coprime natural-number antidiagonal. -/
theorem sum_units_eq_coprime_antidiagonal (N : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ u : (ZMod (N + 2))ˣ,
      F (u : ZMod (N + 2)).val ((-u : (ZMod (N + 2))ˣ) : ZMod (N + 2)).val) =
      ∑ p ∈ antidiagonal (N + 2), if p.1.Coprime (N + 2) then F p.1 p.2 else 0 := by
  rw [← sum_filter]
  refine sum_bij (fun u _ =>
    ((u : ZMod (N + 2)).val, ((-u : (ZMod (N + 2))ˣ) : ZMod (N + 2)).val)) ?_ ?_ ?_ ?_
  · intro u _
    exact mem_filter.mpr ⟨mem_antidiagonal.mpr (unit_val_add_neg_val N u),
      ZMod.val_coe_unit_coprime u⟩
  · intro u _ v _ h
    exact Units.ext (ZMod.val_injective (congrArg Prod.fst h))
  · intro p hp
    obtain ⟨hpN, hc⟩ := mem_filter.mp hp
    have hs := mem_antidiagonal.mp hpN
    have hlt : p.1 < N + 2 := by
      have hne : p.1 ≠ N + 2 := by
        intro h
        rw [h, Nat.coprime_self] at hc
        omega
      omega
    let u : (ZMod (N + 2))ˣ := ZMod.unitOfCoprime p.1 hc
    have hu : (u : ZMod (N + 2)).val = p.1 := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_cast_of_lt hlt]
    refine ⟨u, mem_univ _, ?_⟩
    apply Prod.ext
    · exact hu
    · have hsum := unit_val_add_neg_val N u
      dsimp only [Prod.snd]
      omega
  · intro u _
    rfl

end GaloisForLFunctions.Goldbach
