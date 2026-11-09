import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.TheReturnFormDuality
import GaloisForLFunctions.RHTower.GelfondSchneider

/-!
# The function-field case

Over `𝔽_q[T]` the steps of the prime orbit are `deg(P)·log q`: the system has rank one. Then:

* **Exact returns** (`isDeltaReturn_zero_of_isRankOne`). Every multiple of `2π/log q` is an exact
  return of every set of primes, at every precision: the depth law is degenerate, `R(P, δ) ≤ 2π/log q`.
* **An exact Frobenius** (`frozenJet_add_period`). Every frozen jet `Σ_ν c_ν Λ_ν^j e^{−itΛ_ν}` is
  periodic with period `2π/log q`: the return is the Frobenius `s ↦ s + 2πi/log q`, and every jet of
  every auxiliary is copied exactly. This is what Stepanov's method uses: vanishing at one point is
  vanishing on the whole Frobenius orbit, at every order. Over `𝔽_q` there are no returns to fear
  because every return is exact.
* **Over `ℤ` there is no exact return** (`not_isDeltaReturn_zero_pair`): two distinct primes return
  exactly only at `t = 0`.
* **The rounded system is a function field** (`isRankOne_roundedStep`). The rounded system at `T` has
  rank one with `log q = 2π/T`. So the breadth cap (`exists_matching_system_with_exact_return`)
  says: below `T ≍ 2πK y^K`, every statement about forms of height `≤ K` that holds for the rational
  primes holds for a function field over `𝔽_q`, `q = e^{2π/T}`. Diophantine data of bounded height
  cannot tell `ℤ` from a function field, and so cannot exclude the exact Frobenius that `ℤ` lacks.
-/

open Real Finset

namespace GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit

noncomputable section

open PrimeTorusTheory (dist01)

variable {ι : Type*}

/-- Rank one: every step is an integer multiple of `L` (for `𝔽_q[T]`, `L = log q`, `d = deg`). -/
def IsRankOne (s : Finset ι) (ℓ : ι → ℝ) (L : ℝ) : Prop := ∀ i ∈ s, ∃ d : ℤ, ℓ i = d * L

/-- **Exact returns.** For a rank-one system every multiple of `2π/L` is a `0`-return. -/
theorem isDeltaReturn_zero_of_isRankOne {s : Finset ι} {ℓ : ι → ℝ} {L : ℝ} (h : IsRankOne s ℓ L)
    (hL : L ≠ 0) (k : ℤ) : IsDeltaReturn s ℓ 0 (2 * π * k / L) := fun i hi => by
  obtain ⟨d, hd⟩ := h i hi
  have e : 2 * π * k / L * ℓ i / (2 * π) = ((k * d : ℤ) : ℝ) := by
    rw [hd]; push_cast; field_simp
  rw [e]
  unfold dist01
  rw [round_intCast, sub_self, abs_zero]

/-- A rank-one system has a linear form `Λ_ν = m L` with `m ∈ ℤ`. -/
theorem exists_linForm_eq_intCast_mul {s : Finset ι} {ℓ : ι → ℝ} {L : ℝ} (h : IsRankOne s ℓ L)
    (ν : ι → ℤ) : ∃ m : ℤ, linForm s ℓ ν = m * L := by
  classical
  choose! d hd using h
  refine ⟨∑ i ∈ s, ν i * d i, ?_⟩
  unfold linForm
  push_cast
  rw [sum_mul]
  exact sum_congr rfl fun i hi => by rw [hd i hi]; ring

/-- **The exact Frobenius.** Frozen jets of a rank-one system are periodic with period `2π/L`. -/
theorem frozenJet_add_period {s : Finset ι} {ℓ : ι → ℝ} {L : ℝ} (h : IsRankOne s ℓ L) (hL : L ≠ 0)
    (V : Finset (ι → ℤ)) (c : (ι → ℤ) → ℂ) (j : ℕ) (t : ℝ) :
    ∑ ν ∈ V, c ν * ((linForm s ℓ ν) ^ j : ℝ) *
        Complex.exp (-(((t + 2 * π / L) * linForm s ℓ ν : ℝ) : ℂ) * Complex.I) =
      ∑ ν ∈ V, c ν * ((linForm s ℓ ν) ^ j : ℝ) *
        Complex.exp (-((t * linForm s ℓ ν : ℝ) : ℂ) * Complex.I) := by
  refine sum_congr rfl fun ν _ => ?_
  obtain ⟨m, hm⟩ := exists_linForm_eq_intCast_mul h ν
  congr 1
  have e : -((((t + 2 * π / L) * linForm s ℓ ν : ℝ)) : ℂ) * Complex.I =
      -((t * linForm s ℓ ν : ℝ) : ℂ) * Complex.I + (-m : ℤ) * (2 * π * Complex.I) := by
    have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
    rw [hm]; push_cast; field_simp; ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The rounded system is a function field**: rank one with `L = 2π/T`. -/
theorem isRankOne_roundedStep {T : ℝ} (hT : 0 < T) (s : Finset ι) (ℓ : ι → ℝ) :
    IsRankOne s (roundedStep T ℓ) (2 * π / T) := fun i _ =>
  ⟨round (T * ℓ i / (2 * π)), by unfold roundedStep; field_simp⟩

/-- **No exact return over `ℤ`.** Two distinct primes return exactly only at `t = 0`. -/
theorem not_isDeltaReturn_zero_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {t : ℝ}
    (ht : t ≠ 0) : ¬ IsDeltaReturn {p, q} (fun n : ℕ => Real.log n) 0 t := by
  intro hret
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hint : ∀ r ∈ ({p, q} : Finset ℕ), ∃ m : ℤ, t * Real.log r / (2 * π) = m := fun r hr => by
    have h0 := hret r hr
    have : dist01 (t * Real.log r / (2 * π)) = 0 :=
      le_antisymm h0 (PrimeTorusTheory.dist01_nonneg _)
    refine ⟨round (t * Real.log r / (2 * π)), ?_⟩
    unfold dist01 at this
    linarith [abs_eq_zero.mp this]
  obtain ⟨m, hm⟩ := hint p (mem_insert_self _ _)
  obtain ⟨n, hn⟩ := hint q (mem_insert_of_mem (mem_singleton_self _))
  have hm0 : (m : ℝ) ≠ 0 := by
    rw [← hm]; exact div_ne_zero (mul_ne_zero ht hlp.ne') (by positivity)
  have hratio : Real.log q / Real.log p = ((n / m : ℚ) : ℝ) := by
    push_cast
    rw [← hm, ← hn]
    field_simp
  exact RHTower.log_ratio_transcendental hp hq hpq (hratio ▸ isAlgebraic_algebraMap (n / m : ℚ))

end

end GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit
