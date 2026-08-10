import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import GaloisForLFunctions.Core

/-!
# The normalized exterior two-coproduct

Pulling two chosen letters of a wedge monomial to the front is a permutation, so the signed
two-letter splitting of a decomposable returns the monomial itself.  Summing over all ordered
pairs therefore multiplies a decomposable by the number of pairs:

`μ ∘ Δ_{2,r-2} = binom(r,2) · id`.

Nothing here needs an explicit shuffle sign: the permutation carries its own sign, and the sign
appears twice.

* `deningerPairPerm` : the permutation putting the letters `i` and `j` first.
* `deningerIotaMulti_pairPerm` : the resulting factorisation of a wedge monomial.
* `deningerExteriorPairSum` : **the normalized two-coproduct identity.**
-/

namespace RHTower

open ExteriorAlgebra

noncomputable section

variable (k V : Type*) [CommRing k] [AddCommGroup V] [Module k V]

variable {k V}

/-- The permutation of `Fin (n+2)` that puts `i` first and `j` second. -/
def deningerPairPerm {n : ℕ} (i j : Fin (n + 2)) : Equiv.Perm (Fin (n + 2)) :=
  (Equiv.swap (1 : Fin (n + 2)) (Equiv.swap (0 : Fin (n + 2)) i j)).trans
    (Equiv.swap (0 : Fin (n + 2)) i)

theorem deningerPairPerm_zero {n : ℕ} {i j : Fin (n + 2)} (h : i ≠ j) :
    deningerPairPerm i j 0 = i := by
  have hne : (Equiv.swap (0 : Fin (n + 2)) i) j ≠ 0 := by
    intro hc
    apply h
    have := congrArg (Equiv.swap (0 : Fin (n + 2)) i) hc
    rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    exact this.symm
  have hzeroone : (0 : Fin (n + 2)) ≠ 1 := by
    intro hc
    have : (0 : ℕ) = 1 := congrArg Fin.val hc
    omega
  show (Equiv.swap (0 : Fin (n + 2)) i)
      ((Equiv.swap (1 : Fin (n + 2)) ((Equiv.swap (0 : Fin (n + 2)) i) j)) 0) = i
  rw [Equiv.swap_apply_of_ne_of_ne hzeroone (Ne.symm hne), Equiv.swap_apply_left]

theorem deningerPairPerm_one {n : ℕ} (i j : Fin (n + 2)) :
    deningerPairPerm i j 1 = j := by
  show (Equiv.swap (0 : Fin (n + 2)) i)
      ((Equiv.swap (1 : Fin (n + 2)) ((Equiv.swap (0 : Fin (n + 2)) i) j)) 1) = j
  rw [Equiv.swap_apply_left, Equiv.swap_apply_self]

/-- Putting `i` and `j` first factors a wedge monomial. -/
theorem deningerIotaMulti_pairPerm {n : ℕ} (v : Fin (n + 2) → V) {i j : Fin (n + 2)}
    (h : i ≠ j) :
    ExteriorAlgebra.ιMulti k (n + 2) (v ∘ (deningerPairPerm i j))
      = ExteriorAlgebra.ι k (v i) * (ExteriorAlgebra.ι k (v j) *
          (List.ofFn fun t : Fin n =>
            ExteriorAlgebra.ι k (v (deningerPairPerm i j t.succ.succ))).prod) := by
  rw [ExteriorAlgebra.ιMulti_apply, List.ofFn_succ, List.prod_cons, List.ofFn_succ,
    List.prod_cons]
  have h0 : (v ∘ (deningerPairPerm i j)) 0 = v i := by
    show v (deningerPairPerm i j 0) = v i
    rw [deningerPairPerm_zero h]
  have h1 : (v ∘ (deningerPairPerm i j)) (Fin.succ 0) = v j := by
    show v (deningerPairPerm i j (Fin.succ 0)) = v j
    have hone : (Fin.succ (0 : Fin (n + 1))) = (1 : Fin (n + 2)) := rfl
    rw [hone, deningerPairPerm_one]
  rw [h0, h1]
  rfl

/-- The index set of ordered pairs. -/
def deningerPairIndex (m : ℕ) : Finset (Fin m × Fin m) :=
  Finset.univ.filter fun p => p.1 < p.2

/-- **The normalized exterior two-coproduct identity.**  Summing the signed two-letter splittings
of a wedge monomial over all ordered pairs multiplies it by the number of pairs. -/
theorem deningerExteriorPairSum {n : ℕ} (v : Fin (n + 2) → V) :
    (∑ p ∈ deningerPairIndex (n + 2),
        Equiv.Perm.sign (deningerPairPerm p.1 p.2) •
          (ExteriorAlgebra.ι k (v p.1) * (ExteriorAlgebra.ι k (v p.2) *
            (List.ofFn fun t : Fin n =>
              ExteriorAlgebra.ι k (v (deningerPairPerm p.1 p.2 t.succ.succ))).prod)))
      = (deningerPairIndex (n + 2)).card • ExteriorAlgebra.ιMulti k (n + 2) v := by
  have hterm : ∀ p ∈ deningerPairIndex (n + 2),
      Equiv.Perm.sign (deningerPairPerm p.1 p.2) •
          (ExteriorAlgebra.ι k (v p.1) * (ExteriorAlgebra.ι k (v p.2) *
            (List.ofFn fun t : Fin n =>
              ExteriorAlgebra.ι k (v (deningerPairPerm p.1 p.2 t.succ.succ))).prod))
        = ExteriorAlgebra.ιMulti k (n + 2) v := by
    intro p hp
    have hlt : p.1 < p.2 := by
      rw [deningerPairIndex, Finset.mem_filter] at hp
      exact hp.2
    have hne : p.1 ≠ p.2 := ne_of_lt hlt
    rw [← deningerIotaMulti_pairPerm v hne,
      AlternatingMap.map_perm (ExteriorAlgebra.ιMulti k (n + 2)) v
        (deningerPairPerm p.1 p.2),
      smul_smul, Int.units_mul_self, one_smul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const]

/-- The number of ordered pairs is the binomial coefficient. -/
theorem deningerPairIndex_card (m : ℕ) : (deningerPairIndex m).card = m.choose 2 := by
  classical
  have hinner : ∀ j : Fin m,
      (∑ i : Fin m, if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter]
    have h : (Finset.univ.filter fun i : Fin m => i < j) = Finset.Iio j := by
      ext i; simp
    rw [h, Fin.card_Iio]
  rw [deningerPairIndex, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun j _ => hinner j]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) m, Finset.sum_range_id, Nat.choose_two_right]

end

end RHTower
