import Mathlib
import GaloisForLFunctions.HTGeometry.LinearVersusAlgebraicCollapse

/-!
# The exponential of one is transcendental

Hermite's theorem, from the analytic estimate `LindemannWeierstrass.exp_polynomial_approx`.  A
polynomial relation `∑ₖ aₖ eᵏ = 0` with integer coefficients and `a₀ ≠ 0` is contradicted by feeding
the polynomial `∏_{j=1}^{n} (X − j)` to the estimate: the resulting quantity is an integer congruent
to `−a₀ nₚ` modulo `p`, hence nonzero, hence of absolute value at least one, while the estimate
bounds it by `(∑ₖ |aₖ|) · cᵖ / (p−1)!`, which tends to zero.

This is the analytic skeleton of the Lindemann–Weierstrass argument in the case of integer
exponents, where the auxiliary polynomial's roots are visible without any symmetric-function theory.

* `expWitnessPoly` — the auxiliary polynomial and its two needed properties.
* `transcendental_exp_one` — `Real.exp 1` is transcendental over `ℚ`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Filter Finset Topology Algebra
open scoped Nat

/-- The auxiliary polynomial `∏_{j=1}^{n} (X − j)`, whose complex roots are `1, …, n`. -/
noncomputable def expWitnessPoly (n : ℕ) : ℤ[X] := ∏ j ∈ Finset.Icc 1 n, (X - C (j : ℤ))

theorem expWitnessPoly_monic (n : ℕ) : (expWitnessPoly n).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem expWitnessPoly_ne_zero (n : ℕ) : expWitnessPoly n ≠ 0 :=
  (expWitnessPoly_monic n).ne_zero

theorem eval_zero_expWitnessPoly_ne_zero (n : ℕ) : (expWitnessPoly n).eval 0 ≠ 0 := by
  rw [expWitnessPoly, eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjne : (j : ℤ) ≠ 0 := by
    have hj0 : j ≠ 0 := by omega
    exact_mod_cast hj0
  simp only [eval_sub, eval_X, eval_C, zero_sub, neg_ne_zero]
  exact hjne

theorem mem_aroots_expWitnessPoly {n k : ℕ} (hk : k ∈ Finset.Icc 1 n) :
    ((k : ℂ)) ∈ (expWitnessPoly n).aroots ℂ := by
  rw [Polynomial.mem_aroots]
  refine ⟨expWitnessPoly_ne_zero n, ?_⟩
  rw [expWitnessPoly, map_prod]
  refine Finset.prod_eq_zero hk ?_
  simp

/-- **Transcendence of `e` over the integers.** -/
theorem transcendental_exp_one_int : Transcendental ℤ (Real.exp 1) := by
  intro halg
  have hE0 : (Real.exp 1) ≠ 0 := Real.exp_ne_zero 1
  have hmem : (Real.exp 1) ∈ nonZeroDivisors ℝ := mem_nonZeroDivisors_of_ne_zero hE0
  obtain ⟨q, hq0, hq⟩ := halg.exists_nonzero_coeff_and_aeval_eq_zero hmem
  set n := q.natDegree with hn
  set a : ℕ → ℤ := fun k => q.coeff k with ha
  set E : ℂ := Complex.exp 1 with hE
  have hrel : ∑ k ∈ Finset.range (n + 1), (a k : ℂ) * E ^ k = 0 := by
    have hR : ∑ k ∈ Finset.range (n + 1), (a k : ℝ) * (Real.exp 1) ^ k = 0 := by
      rw [Polynomial.aeval_eq_sum_range] at hq
      simpa [ha, zsmul_eq_mul] using hq
    have hC := congrArg (fun x : ℝ => (x : ℂ)) hR
    push_cast at hC
    simpa [hE, Complex.ofReal_exp] using hC
  have hsplit : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hzero_not : (0 : ℕ) ∉ Finset.Icc 1 n := by simp
  have hrel' : (a 0 : ℂ) = -∑ k ∈ Finset.Icc 1 n, (a k : ℂ) * E ^ k := by
    rw [hsplit, Finset.sum_insert hzero_not] at hrel
    simp only [pow_zero, mul_one] at hrel
    linear_combination hrel
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx (expWitnessPoly n)
    (eval_zero_expWitnessPoly_ne_zero n)
  set S : ℝ := ∑ k ∈ Finset.Icc 1 n, |(a k : ℝ)| with hS
  have hlim : Tendsto (fun m : ℕ => S * (|c| * (|c| ^ m / m !))) atTop (𝓝 0) := by
    have h := FloorSemiring.tendsto_pow_div_factorial_atTop (|c|)
    have h1 := h.const_mul (|c|)
    have h2 := h1.const_mul S
    simpa using h2
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Filter.Tendsto.eventually_lt_const (show (0 : ℝ) < 1 by norm_num) hlim)
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes
    (max (max (((expWitnessPoly n).eval 0).natAbs + 1) ((a 0).natAbs + 1)) (N + 1))
  have hp1 : ((expWitnessPoly n).eval 0).natAbs < p := by omega
  have hp2 : (a 0).natAbs < p := by omega
  have hp3 : N ≤ p - 1 := by omega
  have hppos : 0 < p := hp.pos
  obtain ⟨np, hnp, gp, -, hgp⟩ := hc p hp1 hp
  obtain ⟨Gz, hGz⟩ : ∃ z : ℤ, z = ∑ k ∈ Finset.Icc 1 n, a k * gp.eval (k : ℤ) := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ z : ℤ, z = -(a 0) * np - p * Gz := ⟨_, rfl⟩
  have hval : ∀ k ∈ Finset.Icc 1 n,
      (Polynomial.aeval ((k : ℕ) : ℂ) gp) = ((gp.eval (k : ℤ) : ℤ) : ℂ) := by
    intro k _
    have hcast : ((k : ℕ) : ℂ) = algebraMap ℤ ℂ (k : ℤ) := by simp
    rw [hcast, Polynomial.aeval_algebraMap_apply]
    simp
  have hexp : ∀ k : ℕ, Complex.exp ((k : ℕ) : ℂ) = E ^ k := by
    intro k
    rw [hE, ← Complex.exp_nat_mul]
    norm_num
  have hsum0 : ∑ k ∈ Finset.Icc 1 n, (a k : ℂ) * E ^ k = -(a 0 : ℂ) := by
    linear_combination hrel'
  have hRHS : ∑ k ∈ Finset.Icc 1 n, (a k : ℂ) *
      ((np : ℂ) * Complex.exp ((k : ℕ) : ℂ)
        - (p : ℂ) * (Polynomial.aeval ((k : ℕ) : ℂ) gp))
      = (np : ℂ) * (∑ k ∈ Finset.Icc 1 n, (a k : ℂ) * E ^ k)
        - (p : ℂ) * (∑ k ∈ Finset.Icc 1 n, ((a k * gp.eval (k : ℤ) : ℤ) : ℂ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hexp k, hval k hk]
    push_cast
    ring
  have hsum : ((Z : ℤ) : ℂ)
      = ∑ k ∈ Finset.Icc 1 n, (a k : ℂ) *
          ((np : ℂ) * Complex.exp ((k : ℕ) : ℂ)
            - (p : ℂ) * (Polynomial.aeval ((k : ℕ) : ℂ) gp)) := by
    rw [hRHS, hsum0, hZ, hGz]
    push_cast
    ring

  have hfacpos : (0 : ℝ) < ((p - 1)! : ℝ) := by
    exact_mod_cast Nat.factorial_pos (p - 1)
  have hbound : ‖((Z : ℤ) : ℂ)‖ < 1 := by
    rw [hsum]
    refine lt_of_le_of_lt (norm_sum_le _ _) ?_
    have hterm : ∀ k ∈ Finset.Icc 1 n,
        ‖(a k : ℂ) * ((np : ℂ) * Complex.exp ((k : ℕ) : ℂ)
            - (p : ℂ) * (Polynomial.aeval ((k : ℕ) : ℂ) gp))‖
          ≤ |(a k : ℝ)| * (|c| ^ p / ((p - 1)! : ℝ)) := by
      intro k hk
      rw [norm_mul]
      have hk' := hgp (mem_aroots_expWitnessPoly hk)
      have hnorm : ‖(np : ℂ) * Complex.exp ((k : ℕ) : ℂ)
          - (p : ℂ) * (Polynomial.aeval ((k : ℕ) : ℂ) gp)‖ ≤ c ^ p / ((p - 1)! : ℝ) := by
        simpa [zsmul_eq_mul, nsmul_eq_mul] using hk'
      have hcle : c ^ p / ((p - 1)! : ℝ) ≤ |c| ^ p / ((p - 1)! : ℝ) := by
        rw [div_le_div_iff_of_pos_right hfacpos]
        calc c ^ p ≤ |c ^ p| := le_abs_self _
          _ = |c| ^ p := abs_pow c p
      have hnormcast : ‖(a k : ℂ)‖ = |(a k : ℝ)| := by
        simp
      rw [hnormcast]
      exact mul_le_mul_of_nonneg_left (hnorm.trans hcle) (abs_nonneg _)
    refine lt_of_le_of_lt (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul, ← hS]
    have hp1' : p - 1 + 1 = p := by omega
    have hpow : |c| ^ p = |c| * |c| ^ (p - 1) := by
      rw [← pow_succ', hp1']
    rw [hpow, mul_div_assoc]
    exact hN (p - 1) hp3
  have hZ0 : Z = 0 := by
    have habs : |(Z : ℝ)| < 1 := by
      simpa using hbound
    have hZabs : |Z| < 1 := by exact_mod_cast habs
    exact Int.abs_lt_one_iff.mp hZabs
  have hdvd : (p : ℤ) ∣ (a 0) * np := by
    refine ⟨-Gz, ?_⟩
    have := hZ0
    rw [hZ] at this
    linarith [this]
  rcases (Int.Prime.dvd_mul' hp hdvd) with h | h
  · have hle : (p : ℤ) ≤ |a 0| := Int.le_of_dvd (abs_pos.mpr hq0) ((dvd_abs _ _).mpr h)
    rw [Int.abs_eq_natAbs] at hle
    omega
  · exact hnp h

/-- **Transcendence of `e`.** -/
theorem transcendental_exp_one : Transcendental ℚ (Real.exp 1) :=
  (Algebra.IsAlgebraic.transcendental_iff (R := ℤ) (S := ℚ)).mp transcendental_exp_one_int

end GaloisForLFunctions.HTGeometry
