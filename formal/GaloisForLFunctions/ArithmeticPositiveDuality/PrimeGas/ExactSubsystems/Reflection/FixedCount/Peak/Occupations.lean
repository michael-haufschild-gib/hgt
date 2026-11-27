import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Outgoing

/-! # Linear energy observables and permutations of unrestricted prime occupations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak

open Finset Real

variable {I : Type*} [Fintype I]

abbrev Boson (I : Type*) [Fintype I] (m : ℕ) := State (fun _ : I => m) m

def read {m : ℕ} (e : I → ℝ) (x : Boson I m) := ∑ i, (count x i : ℝ)*e i

theorem read_const {m : ℕ} (x : Boson I m) (v : ℝ) : read (fun _ => v) x = m*v := by
  rw [read, ← sum_mul, ← Nat.cast_sum, count_sum]

theorem read_add {m : ℕ} (x : Boson I m) (e d : I → ℝ) :
    read (fun i => e i+d i) x = read e x + read d x := by
  simp only [read, mul_add, sum_add_distrib]

theorem read_mono {m : ℕ} (x : Boson I m) {e d : I → ℝ} (h : ∀ i, e i ≤ d i) :
    read e x ≤ read d x :=
  sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (Nat.cast_nonneg _)

private def rearrange {m : ℕ} (R : Equiv.Perm I) (x : Boson I m) : Boson I m :=
  ⟨fun j => x.val (R.symm j), (Equiv.sum_comp R.symm (count x)).trans (count_sum x)⟩

/-- A permutation of prime species transports all particles simultaneously. -/
def move (m : ℕ) (R : Equiv.Perm I) : Equiv.Perm (Boson I m) where
  toFun := rearrange R
  invFun := rearrange R.symm
  left_inv x := state_ext fun i => congrArg (count x) (R.symm_apply_apply i)
  right_inv x := state_ext fun i => congrArg (count x) (R.apply_symm_apply i)

theorem read_move {m : ℕ} (x : Boson I m) (R : Equiv.Perm I) (e : I → ℝ) :
    read e (move m R x) = read (fun i => e (R i)) x := by
  change (∑ j, (count x (R.symm j) : ℝ)*e j) = _
  rw [← Equiv.sum_comp R (fun j => (count x (R.symm j) : ℝ)*e j)]
  simp only [Equiv.symm_apply_apply, read]

def pure [DecidableEq I] (m : ℕ) (i : I) : Boson I m :=
  ⟨fun j => ⟨if i = j then m else 0, by
    change (if i = j then m else 0) < m+1
    split <;> omega⟩, by
    change (∑ j, if i = j then m else 0) = m
    rw [sum_ite_eq, if_pos (mem_univ i)]⟩

theorem count_pure [DecidableEq I] (m : ℕ) (i j : I) :
    count (pure m i) j = if i = j then m else 0 := rfl

theorem read_pure [DecidableEq I] (m : ℕ) (i : I) (e : I → ℝ) : read e (pure m i) = m*e i := by
  simp only [read, count_pure, apply_ite Nat.cast, Nat.cast_zero, ite_mul, zero_mul, sum_ite_eq,
    if_pos (mem_univ i)]

/-- Concatenating occupations adds their total particle numbers. -/
def combine {m n : ℕ} (x : Boson I m) (y : Boson I n) : Boson I (m+n) :=
  ⟨fun i => ⟨count x i + count y i, Nat.lt_succ_of_le (Nat.add_le_add (count_cap x i) (count_cap y i))⟩, by
    change (∑ i, (count x i + count y i)) = m+n
    rw [sum_add_distrib, count_sum, count_sum]⟩

theorem count_combine {m n : ℕ} (x : Boson I m) (y : Boson I n) (i : I) :
    count (combine x y) i = count x i + count y i := rfl

theorem read_combine {m n : ℕ} (x : Boson I m) (y : Boson I n) (e : I → ℝ) :
    read e (combine x y) = read e x + read e y := by
  simp only [read, count_combine, Nat.cast_add, add_mul, sum_add_distrib]

def primeEnergy {S : Finset Nat.Primes} (i : S) : ℝ := log (i.val.val : ℝ)

/-- The original integer Hamiltonian is the linear occupation observable with costs log p. -/
theorem energy_eq_read {S : Finset Nat.Primes} {m : ℕ} (x : Boson S m) :
    energy (level x) = read primeEnergy x := by
  classical
  have h : (level x : ℕ) = ∏ i : S, i.val.val^(count x i) := by
    change (Finsupp.embDomain (_root_.HTGeometry.finsetSubtypeEmbedding S)
      (Finsupp.equivFunOnFinite.symm (count x))).prod (fun p k => (p : ℕ)^k) = _
    rw [Finsupp.prod_embDomain, Finsupp.prod_fintype]
    · rfl
    · intro p; exact pow_zero _
  rw [energy, h, Nat.cast_prod, log_prod]
  · simp only [Nat.cast_pow, log_pow, read, primeEnergy]
  · intro i _
    exact_mod_cast pow_ne_zero (count x i) i.val.property.ne_zero

#print axioms read_move
#print axioms read_pure
#print axioms energy_eq_read

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak
