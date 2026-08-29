import GaloisForLFunctions.HTGeometry.HermitePoulain
import GaloisForLFunctions.HTGeometry.SplitsReflect

/-!
# Jensen polynomials of a real-rooted symbol

For a coefficient sequence `c` the degree-`d` Jensen polynomial is
`∑_{i ≤ d} d^{(i)} · c i · X^i`, where `d^{(i)}` is the descending factorial.  Writing
`c i = γ i / i !` turns this into the classical `∑_i C(d,i) · γ i · X^i`.

The reversed Jensen polynomial `∑_{i ≤ d} d^{(i)} · c i · X^{d-i}` is exactly the constant
coefficient differential operator with symbol `∑ c i X^i` applied to `X^d`, so Hermite–Poulain
makes it real-rooted whenever the symbol is; reflecting the coefficient order transfers this to the
Jensen polynomial itself.
-/

open Polynomial Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The reversed Jensen polynomial of the coefficient sequence `c`. -/
def jensenReverse (c : ℕ → ℝ) (d : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range (d + 1), C (c i * (d.descFactorial i : ℝ)) * X ^ (d - i)

/-- The Jensen polynomial of the coefficient sequence `c`. -/
def jensenPoly (c : ℕ → ℝ) (d : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range (d + 1), C (c i * (d.descFactorial i : ℝ)) * X ^ i

theorem reflect_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) (N : ℕ) :
    Polynomial.reflect N (∑ i ∈ s, f i) = ∑ i ∈ s, Polynomial.reflect N (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [Polynomial.reflect_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Polynomial.reflect_add, ih, Finset.sum_insert ha]

theorem reflect_jensenReverse (c : ℕ → ℝ) (d : ℕ) :
    Polynomial.reflect d (jensenReverse c d) = jensenPoly c d := by
  rw [jensenReverse, jensenPoly, reflect_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Polynomial.reflect_C_mul_X_pow]
  have hle : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [Polynomial.revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hle]

theorem natDegree_jensenReverse_le (c : ℕ → ℝ) (d : ℕ) :
    (jensenReverse c d).natDegree ≤ d := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  simpa using le_trans (Polynomial.natDegree_X_pow_le _) (Nat.sub_le _ _)

theorem diffOpApply_X_pow (P : ℝ[X]) (d : ℕ) :
    diffOpApply P (X ^ d) = jensenReverse (fun i => P.coeff i) d := by
  classical
  set g : ℕ → ℝ[X] := fun i => C (P.coeff i * (d.descFactorial i : ℝ)) * X ^ (d - i) with hg
  have hstep : diffOpApply P (X ^ d) = ∑ i ∈ Finset.range (P.natDegree + 1), g i := by
    rw [diffOpApply, aeval_eq_sum_range]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.pow_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.iterate_derivative_X_pow_eq_C_mul, Polynomial.smul_eq_C_mul, hg]
    rw [← mul_assoc, ← Polynomial.C_mul]
  have hA : ∑ i ∈ Finset.range (P.natDegree + 1), g i
      = ∑ i ∈ Finset.range (max P.natDegree d + 1), g i := by
    refine Finset.sum_subset (Finset.range_subset.2 (by omega)) fun i _ hi => ?_
    have : P.natDegree < i := by
      simpa [Finset.mem_range, Nat.lt_succ_iff] using hi
    rw [hg]
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt this]
  have hB : ∑ i ∈ Finset.range (d + 1), g i
      = ∑ i ∈ Finset.range (max P.natDegree d + 1), g i := by
    refine Finset.sum_subset (Finset.range_subset.2 (by omega)) fun i _ hi => ?_
    have hd : d < i := by
      simpa [Finset.mem_range, Nat.lt_succ_iff] using hi
    have hzero : d.descFactorial i = 0 := Nat.descFactorial_eq_zero_iff_lt.2 hd
    rw [hg]
    simp [hzero]
  rw [hstep, hA, jensenReverse, ← hB]

/-- **The Jensen polynomials of a real-rooted symbol are real-rooted.** -/
theorem splits_jensenPoly_of_splits {P : ℝ[X]} (hP : P.Splits) (d : ℕ) :
    (jensenPoly (fun i => P.coeff i) d).Splits := by
  have h1 : (jensenReverse (fun i => P.coeff i) d).Splits := by
    rw [← diffOpApply_X_pow]
    exact splits_diffOpApply hP (Polynomial.Splits.X.pow d)
  rw [← reflect_jensenReverse]
  exact Splits.reflect h1 (natDegree_jensenReverse_le _ _)

/-- With `c i = γ i / i !` the Jensen polynomial takes its classical binomial form. -/
theorem jensenPoly_div_factorial (γ : ℕ → ℝ) (d : ℕ) :
    jensenPoly (fun i => γ i / (i).factorial) d
      = ∑ i ∈ Finset.range (d + 1), C ((d.choose i : ℝ) * γ i) * X ^ i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  have hfac : ((i.factorial : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero i
  have hdesc : (d.descFactorial i : ℝ) = (i.factorial : ℝ) * (d.choose i : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.descFactorial_eq_factorial_mul_choose d i)
  field_simp [hdesc]
  ring

end

end GaloisForLFunctions.HTGeometry
