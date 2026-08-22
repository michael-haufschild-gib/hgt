import GaloisForLFunctions.HTGeometry.SingleDirectionTransverse

/-!
# The two-local transverse family over an arbitrary commutative ring

The corpus carries the all-qubit two-local Hamiltonian over `ℂ`.  A Galois statement needs it over
a rational function field, so this file records the same family over an arbitrary commutative ring
and the degeneration that switches off every transverse coupling but one.

## Main results

* `transverseFamilyHam` — arbitrary diagonal energies plus one transverse coefficient per direction.
* `transverseFamilyHam_eq_singleDirection` — switching off the other couplings.
* `twoLocalDiagonal`, `twoLocalHam` — the two-local occupation-form Hamiltonian.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Arbitrary diagonal energies plus one transverse coefficient per direction. -/
def transverseFamilyHam (d : (Fin n → Bool) → R) (u : Fin n → R) :
    Matrix (Fin n → Bool) (Fin n → Bool) R :=
  fun x y => if x = y then d x else ∑ i, if y = boolToggle x i then u i else 0

/-- **Switching off every transverse coupling but one.** -/
theorem transverseFamilyHam_eq_singleDirection (d : (Fin n → Bool) → R) (u : Fin n → R)
    (i : Fin n) (hu : ∀ j, j ≠ i → u j = 0) :
    transverseFamilyHam d u = singleDirectionHam d (u i) i := by
  classical
  ext x y
  rw [transverseFamilyHam, singleDirectionHam]
  by_cases hxy : x = y
  · rw [if_pos hxy, if_pos hxy]
  · rw [if_neg hxy, if_neg hxy]
    by_cases hy : y = boolToggle x i
    · rw [if_pos hy]
      rw [Finset.sum_eq_single i]
      · rw [if_pos hy]
      · intro j _ hj
        refine if_neg ?_
        intro hyj
        have : boolToggle x i = boolToggle x j := by rw [← hy, hyj]
        have hi := congrFun this i
        rw [boolToggle, boolToggle, Function.update_self,
          Function.update_of_ne (Ne.symm hj)] at hi
        exact (Bool.not_ne_self (x i)) hi
      · intro hmem
        exact absurd (Finset.mem_univ i) hmem
    · rw [if_neg hy]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : j = i
      · subst hj
        exact if_neg hy
      · rw [hu j hj]
        exact ite_self 0

/-- The occupation-form two-local diagonal energy. -/
def twoLocalDiagonal (c : R) (a : Fin n → R) (b : Fin n → Fin n → R) :
    (Fin n → Bool) → R :=
  fun x => c + ∑ i, a i * (if x i then 1 else 0) +
    ∑ i, ∑ j, b i j * (if x i then 1 else 0) * (if x j then 1 else 0)

/-- The all-qubit two-local Hamiltonian over an arbitrary commutative ring. -/
def twoLocalHam (c : R) (a : Fin n → R) (b : Fin n → Fin n → R) (u : Fin n → R) :
    Matrix (Fin n → Bool) (Fin n → Bool) R :=
  transverseFamilyHam (twoLocalDiagonal c a b) u

theorem twoLocalHam_eq_singleDirection (c : R) (a : Fin n → R) (b : Fin n → Fin n → R)
    (u : Fin n → R) (i : Fin n) (hu : ∀ j, j ≠ i → u j = 0) :
    twoLocalHam c a b u = singleDirectionHam (twoLocalDiagonal c a b) (u i) i :=
  transverseFamilyHam_eq_singleDirection _ u i hu

end GaloisForLFunctions.HTGeometry
