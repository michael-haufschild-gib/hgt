import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.FinitePrimeClockMultipliers

/-!
# Integer multipliers of the prime-logarithm lattice

The scalar endomorphism ring of a nonempty finite prime-logarithm lattice
is exactly the integers. The determinant trick first forces algebraicity;
Baker independence then makes the exponent matrix scalar.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
variable {P : Finset Nat.Primes}

/-- Two distinct prime logarithms have no nonzero integer relation. -/
theorem primeLog_int_relation (p q : P) (hpq : p ≠ q) (n m : ℤ)
    (h : (Real.log ((q : Nat.Primes) : ℕ) : ℂ) * (n : ℂ) =
      (Real.log ((p : Nat.Primes) : ℕ) : ℂ) * (m : ℂ)) : n = 0 ∧ m = 0 := by
  classical
  let c : P → ℝ := fun r =>
    (if r = p then (m : ℝ) else 0) - (if r = q then (n : ℝ) else 0)
  have hc (r : P) : IsAlgebraic ℤ (c r) := by
    apply IsAlgebraic.sub
    · split_ifs
      · exact isAlgebraic_int m
      · exact isAlgebraic_zero
    · split_ifs
      · exact isAlgebraic_int n
      · exact isAlgebraic_zero
  have hrel : ∑ r, c r * Real.log ((r : Nat.Primes) : ℕ) = 0 := by
    simp only [c, sub_mul, sum_sub_distrib, ite_mul, zero_mul,
      sum_ite_eq', mem_univ, if_true]
    have hr := congrArg Complex.re h
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.intCast_re, Complex.intCast_im, mul_zero, sub_zero] at hr
    linear_combination -hr
  have hp := primeLog_algebraic_relation c hc hrel p
  have hq := primeLog_algebraic_relation c hc hrel q
  simp [c, hpq, hpq.symm] at hp hq
  exact ⟨hq, hp⟩

/-- A scalar preserving the signed prime-logarithm lattice is integral. -/
theorem isIntegral_of_prime_log_lattice_dilation (p : P) (a : ℝ)
    (A : P → P → ℤ)
    (hA : ∀ r, ∑ q, (A r q : ℝ) * Real.log ((q : Nat.Primes) : ℕ) =
      a * Real.log ((r : Nat.Primes) : ℕ)) : IsIntegral ℤ a := by
  classical
  let lp : P → ℝ := fun r => Real.log ((r : Nat.Primes) : ℕ)
  let N := Submodule.span ℤ (Set.range lp)
  have hmem (r : P) : lp r ∈ N := Submodule.subset_span ⟨r, rfl⟩
  have hne : N ≠ ⊥ := by
    intro he
    have hp := hmem p
    rw [he, Submodule.mem_bot] at hp
    exact (ne_of_gt (Real.log_pos (by exact_mod_cast p.val.property.one_lt))) hp
  have hgen (r : P) : a * lp r ∈ N := by
    rw [← hA r]
    apply N.sum_mem
    intro q _
    simpa only [zsmul_eq_mul] using N.smul_mem (A r q) (hmem q)
  apply isIntegral_of_smul_mem_submodule N hne
    (Submodule.fg_span (Set.finite_range lp)) a
  intro x hx
  change a * x ∈ N
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨r, rfl⟩ := hx; exact hgen r
  | zero => simpa only [mul_zero] using N.zero_mem
  | add x y hx hy hx' hy' => rw [mul_add]; exact N.add_mem hx' hy'
  | smul z x hx hx' =>
      rw [mul_smul_comm]
      exact N.smul_mem z hx'

/-- The scalar endomorphism ring of a nonempty finite prime-logarithm
lattice is exactly the integers; its exponent matrix is scalar. -/
theorem prime_log_lattice_dilation_is_int (p : P) (a : ℝ) (A : P → P → ℤ)
    (hA : ∀ r, ∑ q, (A r q : ℝ) * Real.log ((q : Nat.Primes) : ℕ) =
      a * Real.log ((r : Nat.Primes) : ℕ)) :
    ∃ n : ℤ, a = n ∧ ∀ r q, A r q = if q = r then n else 0 := by
  classical
  have ha := (isIntegral_of_prime_log_lattice_dilation p a A hA).isAlgebraic
  have hcoeff (r q : P) : (A r q : ℝ) = if q = r then a else 0 := by
    let c : P → ℝ := fun q => (A r q : ℝ) - if q = r then a else 0
    have hc : ∀ q, IsAlgebraic ℤ (c q) := by
      intro q
      apply (isAlgebraic_int (A r q)).sub
      split_ifs
      · exact ha
      · exact isAlgebraic_zero
    have hrel : ∑ q, c q * Real.log ((q : Nat.Primes) : ℕ) = 0 := by
      simp only [c, sub_mul, sum_sub_distrib, ite_mul, zero_mul,
        sum_ite_eq', mem_univ, if_true]
      exact sub_eq_zero.mpr (hA r)
    exact sub_eq_zero.mp (primeLog_algebraic_relation c hc hrel q)
  have he : a = (A p p : ℝ) := by simpa using (hcoeff p p).symm
  refine ⟨A p p, he, fun r q => ?_⟩
  have h := hcoeff r q
  rw [he] at h
  split_ifs at h ⊢ <;> exact_mod_cast h

#print axioms primeLog_int_relation
#print axioms prime_log_lattice_dilation_is_int
end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
