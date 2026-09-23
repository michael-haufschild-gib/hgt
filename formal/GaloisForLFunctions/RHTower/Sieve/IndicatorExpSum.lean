import GaloisForLFunctions.RHTower.Sieve.MontgomerySieve

/-!
# The exponential sum of a set of integers

The large sieve of this folder bounds trigonometric polynomials `∑_{n < N} c_n e(nθ)`.  A sieve
applies it at the indicator of a set `A ⊆ [0, N)`, where the polynomial is the exponential sum of
the set and its energy is `|A|`:

`∑_{(a,q) Farey of order Q} |∑_{n ∈ A} e(na/q)|² ≤ (N + Q²(1 + log(Q²/2 + 1))) |A|`.

This is the upper bound that pairs with `MontgomerySieve.lean`'s lower bound: together they bound
`|A|` in terms of the residue classes it omits.
-/

namespace RHTower.Sieve

open Finset

/-- Powers of a circle frequency are the frequencies of the multiples. -/
theorem circleFreq_pow (x : ℝ) (n : ℕ) : (circleFreq x) ^ n = circleFreq ((n : ℝ) * x) := by
  rw [circleFreq, circleFreq, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The indicator of a set of integers, as a coefficient vector. -/
noncomputable def indicatorVec (N : ℕ) (A : Finset ℕ) : Fin N → ℂ :=
  fun n => if (n : ℕ) ∈ A then 1 else 0

/-- The trigonometric polynomial of an indicator is the exponential sum of the set. -/
theorem expSum_indicatorVec {N : ℕ} (A : Finset ℕ) (hA : A ⊆ Finset.range N) (θ : ℝ) :
    expSum N (indicatorVec N A) θ = ∑ n ∈ A, circleFreq ((n : ℝ) * θ) := by
  classical
  have hfilter : (Finset.range N).filter (fun n => n ∈ A) = A := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hA h, h⟩⟩
  have hstep : ∑ n : Fin N, (indicatorVec N A) n * (circleFreq θ) ^ (n : ℕ)
      = ∑ n ∈ Finset.range N, (if n ∈ A then (1 : ℂ) else 0) * (circleFreq θ) ^ n :=
    Fin.sum_univ_eq_sum_range
      (fun n => (if n ∈ A then (1 : ℂ) else 0) * (circleFreq θ) ^ n) N
  have hite : ∀ n : ℕ, (if n ∈ A then (1 : ℂ) else 0) * (circleFreq θ) ^ n
      = if n ∈ A then (circleFreq θ) ^ n else 0 := by
    intro n
    by_cases h : n ∈ A <;> simp [h]
  rw [expSum, hstep, Finset.sum_congr rfl (fun n _ => hite n), ← Finset.sum_filter, hfilter]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [circleFreq_pow]

/-- The energy of an indicator vector is the cardinality. -/
theorem sum_normSq_indicatorVec {N : ℕ} (A : Finset ℕ) (hA : A ⊆ Finset.range N) :
    ∑ n : Fin N, ‖(indicatorVec N A) n‖ ^ (2 : ℕ) = (A.card : ℝ) := by
  classical
  have hfilter : (Finset.range N).filter (fun n => n ∈ A) = A := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hA h, h⟩⟩
  have hstep : ∑ n : Fin N, ‖(indicatorVec N A) n‖ ^ (2 : ℕ)
      = ∑ n ∈ Finset.range N, (if n ∈ A then (1 : ℝ) else 0) := by
    have h1 : ∑ n : Fin N, ‖(indicatorVec N A) n‖ ^ (2 : ℕ)
        = ∑ n ∈ Finset.range N, ‖(if n ∈ A then (1 : ℂ) else 0)‖ ^ (2 : ℕ) :=
      Fin.sum_univ_eq_sum_range (fun n => ‖(if n ∈ A then (1 : ℂ) else 0)‖ ^ (2 : ℕ)) N
    rw [h1]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : n ∈ A <;> simp [h]
  rw [hstep, Finset.sum_boole, hfilter]

/-- **The large sieve for the exponential sum of a set of integers.** -/
theorem largeSieve_set_fareySet (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (A : Finset ℕ)
    (hA : A ⊆ Finset.range N) :
    ∑ p ∈ fareySet Q, ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((p.1 : ℝ) / (p.2 : ℝ)))‖ ^ (2 : ℕ)
      ≤ ((N : ℝ) + (Q : ℝ) ^ (2 : ℕ) * (1 + Real.log ((Q : ℝ) ^ (2 : ℕ) / 2 + 1))) * (A.card : ℝ) := by
  have hbase := largeSieve_expSum_fareySet N hQ (indicatorVec N A)
  rw [sum_normSq_indicatorVec A hA] at hbase
  simp only [expSum_indicatorVec A hA] at hbase
  exact hbase

end RHTower.Sieve
