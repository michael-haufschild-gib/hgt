import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic

/-!
# Conjugation and generation in the three-letter symmetric group

The even subgroup has order three. Its nonidentity elements generate it,
and conjugation by an odd permutation acts by inversion. These facts are
proved from the cardinality of A3 and two explicit transpositions, without
an exhaustive enumeration of permutations.
-/

open Equiv.Perm
namespace GaloisForLFunctions.HTGeometry

def cubicPermSwap : Equiv.Perm (Fin 3) := Equiv.swap 0 1
def cubicPermRotation : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem cubicPermSwap_sign : sign cubicPermSwap = -1 := by
  exact sign_swap (by norm_num)

theorem cubicPermRotation_sign : sign cubicPermRotation = 1 := by
  simp [cubicPermRotation]

theorem cubicPermRotation_ne_one : cubicPermRotation ≠ 1 := by
  intro h
  have h0 := congrArg (fun p : Equiv.Perm (Fin 3) => p 0) h
  norm_num [cubicPermRotation, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff] at h0

theorem cubicAlternating_card : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [nat_card_alternatingGroup]
  norm_num

/-- Every even permutation of three letters has cube equal to one. -/
theorem cubic_even_pow_three (p : Equiv.Perm (Fin 3)) (hp : sign p = 1) : p ^ 3 = 1 := by
  let a : alternatingGroup (Fin 3) := ⟨p, mem_alternatingGroup.mpr hp⟩
  have h : a ^ Nat.card (alternatingGroup (Fin 3)) = 1 := pow_card_eq_one'
  rw [cubicAlternating_card] at h
  exact congrArg Subtype.val h

/-- The even permutations of three letters commute. -/
theorem cubic_even_commute (p q : Equiv.Perm (Fin 3))
    (hp : sign p = 1) (hq : sign q = 1) : Commute p q := by
  letI : IsMulCommutative (alternatingGroup (Fin 3)) :=
    alternatingGroup.isMulCommutative_of_card_le_three (by norm_num)
  have h := mul_comm' (⟨p, mem_alternatingGroup.mpr hp⟩ : alternatingGroup (Fin 3))
    (⟨q, mem_alternatingGroup.mpr hq⟩ : alternatingGroup (Fin 3))
  exact congrArg Subtype.val h

/-- Any nonidentity even permutation generates all even permutations on three letters. -/
theorem cubic_even_exists_pow {r p : Equiv.Perm (Fin 3)}
    (hr : sign r = 1) (hr0 : r ≠ 1) (hp : sign p = 1) : ∃ k : ℕ, r ^ k = p := by
  let a : alternatingGroup (Fin 3) := ⟨r, mem_alternatingGroup.mpr hr⟩
  let b : alternatingGroup (Fin 3) := ⟨p, mem_alternatingGroup.mpr hp⟩
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have ha : a ≠ 1 := fun h => hr0 (congrArg Subtype.val h)
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff b a).mp
    (mem_powers_of_prime_card cubicAlternating_card ha)
  exact ⟨k, congrArg Subtype.val hk⟩

theorem cubicPermSwap_conj_rotation :
    (MulAut.conj cubicPermSwap) cubicPermRotation = cubicPermRotation⁻¹ := by
  simp [MulAut.conj_apply, cubicPermSwap, cubicPermRotation]

/-- A fixed transposition inverts every even permutation of three letters. -/
theorem cubicPermSwap_conj_even (p : Equiv.Perm (Fin 3)) (hp : sign p = 1) :
    (MulAut.conj cubicPermSwap) p = p⁻¹ := by
  obtain ⟨k, rfl⟩ := cubic_even_exists_pow cubicPermRotation_sign cubicPermRotation_ne_one hp
  rw [map_pow, cubicPermSwap_conj_rotation, inv_pow]

/-- Odd conjugation is inversion on A3. -/
theorem cubic_odd_conj_even (p q : Equiv.Perm (Fin 3))
    (hp : sign p = -1) (hq : sign q = 1) : p * q * p⁻¹ = q⁻¹ := by
  let e := p * cubicPermSwap
  have he : sign e = 1 := by simp [e, hp, cubicPermSwap_sign]
  have hc := cubic_even_commute e q he hq
  calc
    p * q * p⁻¹ = e * ((MulAut.conj cubicPermSwap) q) * e⁻¹ := by
      simp only [e, MulAut.conj_apply, cubicPermSwap, Equiv.swap_inv]
      group
      rw [mul_assoc p (Equiv.swap (0 : Fin 3) 1) (Equiv.swap 0 1),
        Equiv.swap_mul_self, mul_one]
    _ = e * q⁻¹ * e⁻¹ := by rw [cubicPermSwap_conj_even q hq]
    _ = q⁻¹ := by rw [hc.inv_right.eq]; group

end GaloisForLFunctions.HTGeometry
