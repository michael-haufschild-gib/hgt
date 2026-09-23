import GaloisForLFunctions.HTGeometry.TwoLocalRationalSpecialisation
import GaloisForLFunctions.HTGeometry.BalancedTernaryKrylovCyclicity
import GaloisForLFunctions.HTGeometry.SymmetricGaloisCyclicity

/-!
# An explicit rational two-local witness with symmetric Galois group

Taking the pair couplings `b_{jk} = 3^{j+k}` makes the two-local diagonal energy the square of the
base-three occupation value, which is injective by uniqueness of balanced ternary expansions.  The
detuning across a hypercube edge in direction `i` is then `2·3^i·(occupation) + 9^i`, an increasing
affine function of the occupation of the edge, hence injective in the edge and never opposite.  So
the explicit two-local family satisfies every hypothesis of the Galois computation.

## Main results

* `occZ`, `occZ_injective` — the base-three occupation value and its injectivity.
* `witnessDiagonal` — the explicit two-local diagonal, and its trace.
* `exists_rational_twoLocal_specialisation` — **an explicit rational two-local Hamiltonian whose
  characteristic polynomial has the full symmetric Galois group.**
-/

open Polynomial Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace TwoLocalWitness

variable {n : ℕ}

/-- The base-three occupation value of a hypercube point. -/
def occZ (x : Fin n → Bool) : ℤ := ∑ j : Fin n, 3 ^ (j : ℕ) * (if x j then 1 else 0)

theorem ternaryValue_eq (x : Fin n → Bool) :
    BalancedTernary.ternaryValue x = 2 * occZ x - ∑ j : Fin n, 3 ^ (j : ℕ) := by
  rw [BalancedTernary.ternaryValue, occZ, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : x j = true
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]
    ring

/-- **The base-three occupation values are pairwise distinct.** -/
theorem occZ_injective : Function.Injective (occZ (n := n)) := by
  intro x y hxy
  refine BalancedTernary.injective_ternaryValue ?_
  rw [ternaryValue_eq, ternaryValue_eq, hxy]

theorem occZ_nonneg (x : Fin n → Bool) : 0 ≤ occZ x := by
  refine Finset.sum_nonneg fun j _ => ?_
  by_cases h : x j
  · rw [if_pos h]
    positivity
  · rw [if_neg h, mul_zero]

/-- The occupation value of a point differing from another only by occupying site `i`. -/
theorem occZ_update (x y : Fin n → Bool) (i : Fin n) (hi : x i = true) (hy : y i = false)
    (hxy : ∀ j, j ≠ i → x j = y j) : occZ x = occZ y + 3 ^ (i : ℕ) := by
  classical
  rw [occZ, occZ, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hi, hy]
  have hsum : ∑ j ∈ Finset.univ.erase i, 3 ^ (j : ℕ) * (if x j then (1 : ℤ) else 0)
      = ∑ j ∈ Finset.univ.erase i, 3 ^ (j : ℕ) * (if y j then (1 : ℤ) else 0) :=
    Finset.sum_congr rfl fun j hj => by rw [hxy j (Finset.mem_erase.mp hj).1]
  rw [hsum]
  simp
  ring

/-- The explicit pair couplings. -/
def witnessCoupling (j k : Fin n) : ℚ := 3 ^ (j : ℕ) * 3 ^ (k : ℕ)

/-- The explicit two-local diagonal energy. -/
def witnessDiagonal (c : ℚ) : (Fin n → Bool) → ℚ :=
  twoLocalDiagonal c 0 witnessCoupling

theorem witnessDiagonal_eq (c : ℚ) (x : Fin n → Bool) :
    witnessDiagonal c x = c + ((occZ x : ℤ) : ℚ) ^ (2 : ℕ) := by
  classical
  rw [witnessDiagonal, twoLocalDiagonal]
  have hzero : ∑ i : Fin n, (0 : Fin n → ℚ) i * (if x i then (1 : ℚ) else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    simp
  have hocc : ((occZ x : ℤ) : ℚ) = ∑ j : Fin n, 3 ^ (j : ℕ) * (if x j then (1 : ℚ) else 0) := by
    rw [occZ]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : x j = true <;> simp [h]
  rw [hzero, add_zero, hocc, sq, Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [witnessCoupling]
  ring

theorem witnessDiagonal_injective (c : ℚ) : Function.Injective (witnessDiagonal (n := n) c) := by
  intro x y hxy
  rw [witnessDiagonal_eq, witnessDiagonal_eq] at hxy
  have hsq : ((occZ x : ℤ) : ℚ) ^ (2 : ℕ) = ((occZ y : ℤ) : ℚ) ^ (2 : ℕ) := by linarith
  have hz : (occZ x) ^ (2 : ℕ) = (occZ y) ^ (2 : ℕ) := by exact_mod_cast hsq
  refine occZ_injective ?_
  have hx := occZ_nonneg x
  have hy := occZ_nonneg y
  nlinarith [hz, hx, hy]


variable {m : ℕ}

/-- The endpoint of a hypercube edge in a chosen direction. -/
def edgePoint (i : Fin (m + 1)) (z : Fin m → Bool) (b : Bool) : Fin (m + 1) → Bool :=
  (cubeRelabel (Equiv.swap 0 i)).symm (Fin.cons b z)

theorem cubeSide_eq_edgePoint {R : Type*} (d : (Fin (m + 1) → Bool) → R) (i : Fin (m + 1))
    (b : Bool) (z : Fin m → Bool) : cubeSide d i b z = d (edgePoint i z b) := rfl

theorem edgePoint_apply (i : Fin (m + 1)) (z : Fin m → Bool) (b : Bool) (j : Fin (m + 1)) :
    edgePoint i z b j = (Fin.cons b z : Fin (m + 1) → Bool) (Equiv.swap 0 i j) := by
  rw [edgePoint, cubeRelabel_symm_apply]
  simp [Equiv.symm_swap]

theorem edgePoint_self (i : Fin (m + 1)) (z : Fin m → Bool) (b : Bool) :
    edgePoint i z b i = b := by
  rw [edgePoint_apply, Equiv.swap_apply_right]
  simp

theorem edgePoint_congr (i : Fin (m + 1)) (z : Fin m → Bool) (b b' : Bool) {j : Fin (m + 1)}
    (h : j ≠ i) : edgePoint i z b j = edgePoint i z b' j := by
  rw [edgePoint_apply, edgePoint_apply]
  have hne : Equiv.swap (0 : Fin (m + 1)) i j ≠ 0 := by
    intro hcon
    have := congrArg (Equiv.swap (0 : Fin (m + 1)) i) hcon
    rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    exact h this
  obtain ⟨k, hk⟩ : ∃ k : Fin m, Equiv.swap (0 : Fin (m + 1)) i j = k.succ := by
    refine ⟨(Equiv.swap (0 : Fin (m + 1)) i j).pred hne, ?_⟩
    rw [Fin.succ_pred]
  rw [hk, Fin.cons_succ, Fin.cons_succ]

theorem edgePoint_injective (i : Fin (m + 1)) (b : Bool) :
    Function.Injective (fun z : Fin m → Bool => edgePoint i z b) := by
  intro z z' hzz
  have h : Fin.cons b z = (Fin.cons b z' : Fin (m + 1) → Bool) :=
    (cubeRelabel (Equiv.swap 0 i)).symm.injective hzz
  have := congrArg Fin.tail h
  rwa [Fin.tail_cons, Fin.tail_cons] at this

/-- **The detuning of a hypercube edge of the witness.** -/
theorem detuning_witnessDiagonal (c : ℚ) (i : Fin (m + 1)) (z : Fin m → Bool) :
    detuning (witnessDiagonal c) i z
      = 2 * 3 ^ (i : ℕ) * ((occZ (edgePoint i z false) : ℤ) : ℚ) + (3 ^ (i : ℕ)) ^ (2 : ℕ) := by
  have hocc : occZ (edgePoint i z true) = occZ (edgePoint i z false) + 3 ^ (i : ℕ) :=
    occZ_update _ _ i (edgePoint_self i z true) (edgePoint_self i z false)
      (fun j hj => edgePoint_congr i z true false hj)
  rw [detuning, cubeSide_eq_edgePoint, cubeSide_eq_edgePoint, witnessDiagonal_eq,
    witnessDiagonal_eq, hocc]
  push_cast
  ring

theorem detuning_witnessDiagonal_injective (c : ℚ) (i : Fin (m + 1)) :
    Function.Injective (detuning (witnessDiagonal c) i) := by
  intro z z' hzz
  rw [detuning_witnessDiagonal, detuning_witnessDiagonal] at hzz
  have h3 : (3 : ℚ) ^ (i : ℕ) ≠ 0 := by positivity
  have hocc : ((occZ (edgePoint i z false) : ℤ) : ℚ)
      = ((occZ (edgePoint i z' false) : ℤ) : ℚ) := by
    have hcancel : (2 : ℚ) * 3 ^ (i : ℕ) ≠ 0 := by positivity
    refine mul_left_cancel₀ hcancel ?_
    linarith
  have hoccZ : occZ (edgePoint i z false) = occZ (edgePoint i z' false) := by exact_mod_cast hocc
  exact edgePoint_injective i false (occZ_injective hoccZ)

theorem detuning_witnessDiagonal_ne_neg (c : ℚ) (i : Fin (m + 1)) (z z' : Fin m → Bool) :
    detuning (witnessDiagonal c) i z ≠ -detuning (witnessDiagonal c) i z' := by
  rw [detuning_witnessDiagonal, detuning_witnessDiagonal]
  have h0 : (0 : ℚ) ≤ ((occZ (edgePoint i z false) : ℤ) : ℚ) := by
    exact_mod_cast occZ_nonneg (edgePoint i z false)
  have h0' : (0 : ℚ) ≤ ((occZ (edgePoint i z' false) : ℤ) : ℚ) := by
    exact_mod_cast occZ_nonneg (edgePoint i z' false)
  have h3 : (0 : ℚ) < 3 ^ (i : ℕ) := by positivity
  nlinarith


/-- The constant making the witness traceless. -/
def witnessConstant (m : ℕ) : ℚ :=
  -(∑ x : Fin (m + 1) → Bool, ((occZ x : ℤ) : ℚ) ^ (2 : ℕ)) / 2 ^ (m + 1)

theorem sum_witnessDiagonal (m : ℕ) :
    ∑ x : Fin (m + 1) → Bool, witnessDiagonal (witnessConstant m) x = 0 := by
  have hcard : (Finset.univ : Finset (Fin (m + 1) → Bool)).card = 2 ^ (m + 1) := by
    simp
  have hpow : ((2 : ℚ)) ^ (m + 1) ≠ 0 := by positivity
  rw [Finset.sum_congr rfl (fun x _ => witnessDiagonal_eq (witnessConstant m) x),
    Finset.sum_add_distrib, Finset.sum_const, hcard, witnessConstant, nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-- **The witness Hamiltonian is traceless.** -/
theorem trace_witnessHam (u : Fin (m + 1) → ℚ) :
    (twoLocalHam (witnessConstant m) 0 witnessCoupling u).trace = 0 := by
  rw [twoLocalHam, trace_transverseFamilyHam]
  exact sum_witnessDiagonal m

/-- **An explicit rational two-local Hamiltonian with the full symmetric Galois group.**  For every
prescribed nonzero polynomial condition on the couplings there are rational couplings satisfying it
at which the characteristic polynomial of the traceless two-local Hamiltonian
`∑_{j,k} 3^{j+k} n_j n_k + ∑_i u_i X_i` (shifted to trace zero) has Galois group of order `(2ⁿ)!`. -/
theorem exists_twoLocal_symmetric_gal (c : ℚ) {g : MvPolynomial (Fin (m + 1)) ℚ} (hg : g ≠ 0) :
    ∃ u : Fin (m + 1) → ℚ, MvPolynomial.eval u g ≠ 0 ∧
      Nat.card ((twoLocalHam c 0 witnessCoupling u).charpoly).Gal = (2 ^ (m + 1)).factorial := by
  obtain ⟨y, hy, hgal⟩ := exists_rational_specialisation (witnessDiagonal_injective c)
    (detuning_witnessDiagonal_injective c) (detuning_witnessDiagonal_ne_neg c) hg
  refine ⟨y, hy, ?_⟩
  rwa [map_universalCharpoly_eval] at hgal


/-- **The explicit witness, with irreducible characteristic polynomial and every nonzero rational
vector cyclic.**  Irreducibility follows from the symmetric Galois group, and cyclicity of an
arbitrary nonzero vector from irreducibility — so no separate nonvanishing witness for the
cyclicity determinant is needed. -/
theorem exists_twoLocal_symmetric_gal_cyclic (c : ℚ) {g : MvPolynomial (Fin (m + 1)) ℚ}
    (hg : g ≠ 0) :
    ∃ u : Fin (m + 1) → ℚ, MvPolynomial.eval u g ≠ 0 ∧
      Nat.card ((twoLocalHam c 0 witnessCoupling u).charpoly).Gal = (2 ^ (m + 1)).factorial ∧
      Irreducible ((twoLocalHam c 0 witnessCoupling u).charpoly) ∧
      ∀ v : (Fin (m + 1) → Bool) → ℚ, v ≠ 0 →
        LinearIndependent ℚ (fun k : Fin (Fintype.card (Fin (m + 1) → Bool)) =>
          (twoLocalHam c 0 witnessCoupling u) ^ (k : ℕ) *ᵥ v) := by
  classical
  obtain ⟨u, hu, hgal⟩ := exists_twoLocal_symmetric_gal c hg
  have hdegcard : ((twoLocalHam c 0 witnessCoupling u).charpoly).natDegree = 2 ^ (m + 1) := by
    rw [Matrix.charpoly_natDegree_eq_dim]
    simp
  have hirr : Irreducible ((twoLocalHam c 0 witnessCoupling u).charpoly) := by
    refine irreducible_of_card_gal_eq_factorial
      ((twoLocalHam c 0 witnessCoupling u).charpoly_monic).ne_zero ?_ ?_
    · rw [hdegcard]
      exact Nat.one_le_two_pow
    · rw [hgal, hdegcard]
  exact ⟨u, hu, hgal, hirr, fun v hv => linearIndependent_krylov_of_irreducible _ hirr hv⟩

end TwoLocalWitness

end

end GaloisForLFunctions.HTGeometry
