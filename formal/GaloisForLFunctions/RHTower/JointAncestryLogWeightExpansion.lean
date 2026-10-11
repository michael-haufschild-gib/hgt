import GaloisForLFunctions.RHTower.JointAncestryLogWeightBernoulli
import GaloisForLFunctions.RHTower.JointAncestryLogWeightPrimeSum

/-!
# The log-weight test value as an exponential

With weights `a_p = τ log p / p` on the prime window `(A, B]`, the log-weight Bernoulli value of a
point `s` is

`V(s) = (1/(s(1−s))) ∏_{A<p≤B} (1 + u_p(s))`,
`u_p(s) = τ (log p/p)(e^{iφ} p^{ξ − s} + e^{−iφ} p^{s + ξ̄ − 1})`.

* `Σ_p u_p(s) = τ E(s)` with `E(s) = e^{iφ} S(ξ − s) + e^{−iφ} S(s + ξ̄ − 1)` (`sum_jasLogWeightLocal_sub_one`).
* If every `‖u_p‖ ≤ ½` then `∏(1 + u_p) = exp(Σ u_p + R)` with `‖R‖ ≤ Σ‖u_p‖²`
  (`exists_prod_one_add_eq_exp`).
* The value is real-symmetric under the critical reflection: `V(1 − s̄) = conj V(s)`
  (`jasLogWeightValue_one_sub_conj`), so `Re V` is the same at both copies of an off-line zero.
* For points with `Re(ξ − s), Re(s + ξ̄ − 1) ≤ 1/4` the quadratic remainder is at most
  `16 τ² (log B)²/√A` (`sum_sq_norm_jasLogWeightLocal_sub_one_le`): it vanishes uniformly once
  `τ² ≪ √A/(log B)²`.
-/

open Complex
open scoped ComplexConjugate BigOperators

namespace RHTower

noncomputable section

/-! ## Products of near-one factors -/

/-- `∏ (1 + u_i) = exp(Σ u_i + R)` with `‖R‖ ≤ Σ ‖u_i‖²` when every `‖u_i‖ ≤ 1/2`. -/
theorem exists_prod_one_add_eq_exp {ι : Type*} (s : Finset ι) (u : ι → ℂ)
    (hu : ∀ i ∈ s, ‖u i‖ ≤ 1 / 2) :
    ∃ R : ℂ, ‖R‖ ≤ ∑ i ∈ s, ‖u i‖ ^ 2 ∧ ∏ i ∈ s, (1 + u i) = cexp (∑ i ∈ s, u i + R) := by
  refine ⟨∑ i ∈ s, (Complex.log (1 + u i) - u i), ?_, ?_⟩
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hlt : ‖u i‖ < 1 := by linarith [hu i hi]
    refine (Complex.norm_log_one_add_sub_self_le hlt).trans ?_
    have h1 : 0 < 1 - ‖u i‖ := by linarith
    have h2 : (1 - ‖u i‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ h1 (by norm_num)]; linarith [hu i hi]
    have hsq : 0 ≤ ‖u i‖ ^ 2 := sq_nonneg _
    calc ‖u i‖ ^ 2 * (1 - ‖u i‖)⁻¹ / 2 ≤ ‖u i‖ ^ 2 * 2 / 2 := by gcongr
      _ = ‖u i‖ ^ 2 := by ring
  · rw [← Finset.sum_add_distrib]
    simp only [add_sub_cancel]
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hne : 1 + u i ≠ 0 := by
      intro h
      have : u i = -1 := by linear_combination h
      have := hu i hi
      rw [‹u i = -1›, norm_neg, norm_one] at this
      norm_num at this
    exact (Complex.exp_log hne).symm

/-! ## The value and its exponent -/

/-- The log-weight test value `(∏_{A<p≤B} (1 + u_p(s)))/(s(1−s))`. -/
def jasLogWeightValue (ξ : ℂ) (A B : ℕ) (τ φ : ℝ) (s : ℂ) : ℂ :=
  (∏ p ∈ jasPrimeWindow A B, jasLogWeightLocal ξ s (τ * (Real.log p / p)) φ p) / (s * (1 - s))

/-- The exponent `E(s) = e^{iφ} S(ξ − s) + e^{−iφ} S(s + ξ̄ − 1)`. -/
def jasLogWeightExponent (ξ : ℂ) (A B : ℕ) (φ : ℝ) (s : ℂ) : ℂ :=
  cexp ((φ : ℂ) * I) * jasLogWeightSum A B (ξ - s) +
    cexp (((-φ : ℝ) : ℂ) * I) * jasLogWeightSum A B (s + conj ξ - 1)

theorem jasLogWeightLocal_sub_one (ξ s : ℂ) (a φ : ℝ) (p : Nat.Primes) :
    jasLogWeightLocal ξ s a φ p - 1 =
      (a : ℂ) * (cexp ((φ : ℂ) * I) * cexp ((ξ - s) * (Real.log p : ℂ)) +
        cexp (((-φ : ℝ) : ℂ) * I) * cexp ((s + conj ξ - 1) * (Real.log p : ℂ))) := by
  rw [jasLogWeightLocal]; ring

/-- `Σ_p u_p(s) = τ E(s)`. -/
theorem sum_jasLogWeightLocal_sub_one (ξ : ℂ) (A B : ℕ) (τ φ : ℝ) (s : ℂ) :
    ∑ p ∈ jasPrimeWindow A B, (jasLogWeightLocal ξ s (τ * (Real.log p / p)) φ p - 1) =
      (τ : ℂ) * jasLogWeightExponent ξ A B φ s := by
  simp_rw [jasLogWeightLocal_sub_one]
  rw [jasLogWeightExponent, jasLogWeightSum, jasLogWeightSum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  push_cast
  ring

/-- The local factor is real-symmetric under `s ↦ 1 − s̄`. -/
theorem jasLogWeightLocal_one_sub_conj (ξ s : ℂ) (a φ : ℝ) (p : Nat.Primes) :
    jasLogWeightLocal ξ (1 - conj s) a φ p = conj (jasLogWeightLocal ξ s a φ p) := by
  have c1 : conj (cexp ((φ : ℂ) * I)) = cexp (((-φ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring_nf
  have c2 : conj (cexp (((-φ : ℝ) : ℂ) * I)) = cexp ((φ : ℂ) * I) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring_nf
  have c3 : conj (cexp ((ξ - s) * (Real.log p : ℂ))) =
      cexp ((1 - conj s + conj ξ - 1) * (Real.log p : ℂ)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, map_sub]; ring_nf
  have c4 : conj (cexp ((s + conj ξ - 1) * (Real.log p : ℂ))) =
      cexp ((ξ - (1 - conj s)) * (Real.log p : ℂ)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, map_sub, map_add, map_one,
      Complex.conj_conj]; ring_nf
  rw [jasLogWeightLocal, jasLogWeightLocal, map_add, map_one, map_mul, Complex.conj_ofReal, map_add,
    map_mul, map_mul, c1, c2, c3, c4]
  ring

/-- **Reflection symmetry.**  `V(1 − s̄) = conj V(s)`. -/
theorem jasLogWeightValue_one_sub_conj (ξ : ℂ) (A B : ℕ) (τ φ : ℝ) (s : ℂ) :
    jasLogWeightValue ξ A B τ φ (1 - conj s) = conj (jasLogWeightValue ξ A B τ φ s) := by
  rw [jasLogWeightValue, jasLogWeightValue, map_div₀, map_prod, map_mul, map_sub, map_one]
  congr 1
  · exact Finset.prod_congr rfl fun p _ => jasLogWeightLocal_one_sub_conj ξ s _ φ p
  · ring

theorem re_jasLogWeightValue_one_sub_conj (ξ : ℂ) (A B : ℕ) (τ φ : ℝ) (s : ℂ) :
    (jasLogWeightValue ξ A B τ φ (1 - conj s)).re = (jasLogWeightValue ξ A B τ φ s).re := by
  rw [jasLogWeightValue_one_sub_conj, Complex.conj_re]

/-! ## Size of the local deviations -/

theorem norm_cexp_mul_log (z : ℂ) (p : Nat.Primes) :
    ‖cexp (z * (Real.log p : ℂ))‖ = Real.exp (z.re * Real.log p) := by
  rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- `‖u_p(s)‖ ≤ a (p^{Re(ξ − s)} + p^{Re(s + ξ̄ − 1)})`. -/
theorem norm_jasLogWeightLocal_sub_one_le (ξ s : ℂ) {a : ℝ} (ha : 0 ≤ a) (φ : ℝ)
    (p : Nat.Primes) :
    ‖jasLogWeightLocal ξ s a φ p - 1‖ ≤
      a * (Real.exp ((ξ - s).re * Real.log p) + Real.exp ((s + conj ξ - 1).re * Real.log p)) := by
  rw [jasLogWeightLocal_sub_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) ha
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, one_mul,
    one_mul, norm_cexp_mul_log, norm_cexp_mul_log]

/-- With both shifts at most `ε`, `‖u_p(s)‖ ≤ 2a p^{ε}`. -/
theorem norm_jasLogWeightLocal_sub_one_le_of_re_le (ξ s : ℂ) {a ε : ℝ} (ha : 0 ≤ a) (φ : ℝ)
    (p : Nat.Primes) (h₁ : (ξ - s).re ≤ ε) (h₂ : (s + conj ξ - 1).re ≤ ε) :
    ‖jasLogWeightLocal ξ s a φ p - 1‖ ≤ 2 * a * Real.exp (ε * Real.log p) := by
  refine (norm_jasLogWeightLocal_sub_one_le ξ s ha φ p).trans ?_
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)
  have e₁ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h₁ hlog)
  have e₂ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h₂ hlog)
  nlinarith

/-! ## Telescoping the quadratic remainder -/

/-- `1/(n√n) ≤ 2(1/√(n−1) − 1/√n)` for `n ≥ 2`. -/
theorem inv_mul_sqrt_le_two_mul_sub {n : ℝ} (hn : 2 ≤ n) :
    1 / (n * Real.sqrt n) ≤ 2 * (1 / Real.sqrt (n - 1) - 1 / Real.sqrt n) := by
  have hn1 : 0 < n - 1 := by linarith
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hs1 : 0 < Real.sqrt (n - 1) := Real.sqrt_pos.mpr hn1
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by linarith)
  have hsq1 : Real.sqrt (n - 1) ^ 2 = n - 1 := Real.sq_sqrt hn1.le
  have hle : Real.sqrt (n - 1) ≤ Real.sqrt n := Real.sqrt_le_sqrt (by linarith)
  rw [div_sub_div _ _ hs1.ne' hs.ne', one_mul, mul_one, mul_div_assoc', le_div_iff₀
    (mul_pos hs1 hs), div_mul_eq_mul_div, div_le_iff₀ (mul_pos (by linarith) hs)]
  have key : (Real.sqrt n - Real.sqrt (n - 1)) * (Real.sqrt n + Real.sqrt (n - 1)) = 1 := by
    nlinarith
  have hd : 0 ≤ Real.sqrt n - Real.sqrt (n - 1) := by linarith
  have h1 : (Real.sqrt n - Real.sqrt (n - 1)) * (Real.sqrt n + Real.sqrt (n - 1)) * n ≤
      2 * (Real.sqrt n - Real.sqrt (n - 1)) * (n * Real.sqrt n) := by
    have : 0 ≤ (Real.sqrt n - Real.sqrt (n - 1)) * n * (Real.sqrt n - Real.sqrt (n - 1)) :=
      mul_nonneg (mul_nonneg hd (by linarith)) hd
    nlinarith
  have h2 : Real.sqrt (n - 1) * Real.sqrt n ≤ n := by nlinarith
  rw [key, one_mul] at h1
  linarith

/-- `Σ_{A<n≤B} n^{−3/2} ≤ 2/√A`. -/
theorem sum_Ioc_inv_mul_sqrt_le {A : ℕ} (hA : 1 ≤ A) (B : ℕ) :
    ∑ n ∈ Finset.Ioc A B, 1 / ((n : ℝ) * Real.sqrt n) ≤ 2 / Real.sqrt A := by
  have htel : ∀ k : ℕ, ∑ n ∈ Finset.Ioc A (A + k), 1 / ((n : ℝ) * Real.sqrt n) ≤
      2 * (1 / Real.sqrt A - 1 / Real.sqrt ((A + k : ℕ) : ℝ)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show A + (k + 1) = A + k + 1 by omega, Finset.sum_Ioc_succ_top (by omega)]
      have hstep := inv_mul_sqrt_le_two_mul_sub (n := ((A + k + 1 : ℕ) : ℝ))
        (by push_cast; have : (1 : ℝ) ≤ A := by exact_mod_cast hA
            linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
      rw [show ((A + k + 1 : ℕ) : ℝ) - 1 = ((A + k : ℕ) : ℝ) by push_cast; ring] at hstep
      linarith
  rcases le_or_gt B A with hBA | hAB
  · have : Finset.Ioc A B = ∅ := by ext n; simp; omega
    rw [this, Finset.sum_empty]; positivity
  · obtain ⟨k, rfl⟩ : ∃ k, B = A + k := ⟨B - A, by omega⟩
    refine (htel k).trans ?_
    have : 0 ≤ 1 / Real.sqrt ((A + k : ℕ) : ℝ) := by positivity
    rw [div_eq_mul_one_div 2]
    linarith

/-- **The quadratic remainder.**  If both shifts are at most `1/4`, the squared deviations of the
window sum to at most `16 τ² (log B)²/√A`. -/
theorem sum_sq_norm_jasLogWeightLocal_sub_one_le (ξ s : ℂ) {A B : ℕ} (hA : 1 ≤ A) {τ : ℝ}
    (hτ : 0 ≤ τ) (φ : ℝ) (h₁ : (ξ - s).re ≤ 1 / 4) (h₂ : (s + conj ξ - 1).re ≤ 1 / 4) :
    ∑ p ∈ jasPrimeWindow A B, ‖jasLogWeightLocal ξ s (τ * (Real.log p / p)) φ p - 1‖ ^ 2 ≤
      16 * τ ^ 2 * Real.log B ^ 2 / Real.sqrt A := by
  have hterm : ∀ p ∈ jasPrimeWindow A B,
      ‖jasLogWeightLocal ξ s (τ * (Real.log p / p)) φ p - 1‖ ^ 2 ≤
        4 * τ ^ 2 * Real.log B ^ 2 * (1 / ((p : ℝ) * Real.sqrt p)) := by
    intro p hp
    have hpw := mem_jasPrimeWindow.mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_lt.le
    have hlog0 : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hlogB : Real.log p ≤ Real.log B :=
      Real.log_le_log hp0 (by exact_mod_cast hpw.2)
    have ha : 0 ≤ τ * (Real.log p / p) := mul_nonneg hτ (div_nonneg hlog0 hp0.le)
    have hb := norm_jasLogWeightLocal_sub_one_le_of_re_le ξ s ha φ p h₁ h₂
    have hexp : Real.exp (1 / 4 * Real.log p) = (p : ℝ) ^ (1 / 4 : ℝ) := by
      rw [Real.rpow_def_of_pos hp0, mul_comm]
    rw [hexp] at hb
    have hn0 : 0 ≤ ‖jasLogWeightLocal ξ s (τ * (Real.log p / p)) φ p - 1‖ := norm_nonneg _
    have hsq := pow_le_pow_left₀ hn0 hb 2
    refine hsq.trans ?_
    -- `(2τ (log p/p) p^{1/4})² ≤ 4τ²(log B)²/(p√p)`
    have hq : ((p : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, Real.sqrt_eq_rpow]; norm_num
    have hsqrt : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
    have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
    have e : (2 * (τ * (Real.log p / p)) * (p : ℝ) ^ (1 / 4 : ℝ)) ^ 2 =
        4 * τ ^ 2 * Real.log p ^ 2 * (1 / ((p : ℝ) * Real.sqrt p)) := by
      rw [mul_pow, mul_pow, mul_pow, div_pow, hq]
      generalize Real.log p = L
      generalize hr : Real.sqrt p = r at hsqrt hs0 ⊢
      rw [← hsqrt]
      field_simp
      ring
    rw [e]
    have hlsq : Real.log p ^ 2 ≤ Real.log B ^ 2 := pow_le_pow_left₀ hlog0 hlogB 2
    have hpos : 0 ≤ 1 / ((p : ℝ) * Real.sqrt p) := by positivity
    gcongr
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hsum : ∑ p ∈ jasPrimeWindow A B, 1 / ((p : ℝ) * Real.sqrt p) ≤ 2 / Real.sqrt A := by
    rw [sum_jasPrimeWindow A B (fun n : ℕ => 1 / ((n : ℝ) * Real.sqrt n))]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun n _ _ => by positivity) (sum_Ioc_inv_mul_sqrt_le hA B)
  have hc : 0 ≤ 4 * τ ^ 2 * Real.log B ^ 2 := by positivity
  calc 4 * τ ^ 2 * Real.log B ^ 2 * ∑ p ∈ jasPrimeWindow A B, 1 / ((p : ℝ) * Real.sqrt p)
      ≤ 4 * τ ^ 2 * Real.log B ^ 2 * (2 / Real.sqrt A) := mul_le_mul_of_nonneg_left hsum hc
    _ ≤ 16 * τ ^ 2 * Real.log B ^ 2 / Real.sqrt A := by
      rw [mul_div_assoc']
      have hA0 : 0 < Real.sqrt A := Real.sqrt_pos.mpr (by exact_mod_cast hA)
      rw [div_le_div_iff_of_pos_right hA0]
      nlinarith

/-- **The value as an exponential.**  If every deviation is at most `1/2`, then
`V(s)·s(1−s) = exp(τ E(s) + R)` with `‖R‖` bounded by the sum of squared deviations. -/
theorem exists_jasLogWeightValue_eq_exp (ξ : ℂ) (A B : ℕ) (τ φ : ℝ) (s : ℂ)
    (hu : ∀ p ∈ jasPrimeWindow A B,
      ‖jasLogWeightLocal ξ s (τ * (Real.log p / p)) φ p - 1‖ ≤ 1 / 2) :
    ∃ R : ℂ, ‖R‖ ≤ ∑ p ∈ jasPrimeWindow A B,
        ‖jasLogWeightLocal ξ s (τ * (Real.log p / p)) φ p - 1‖ ^ 2 ∧
      ∏ p ∈ jasPrimeWindow A B, jasLogWeightLocal ξ s (τ * (Real.log p / p)) φ p =
        cexp ((τ : ℂ) * jasLogWeightExponent ξ A B φ s + R) := by
  obtain ⟨R, hR, hprod⟩ := exists_prod_one_add_eq_exp (jasPrimeWindow A B)
    (fun p => jasLogWeightLocal ξ s (τ * (Real.log p / p)) φ p - 1) hu
  refine ⟨R, hR, ?_⟩
  simp only [add_sub_cancel] at hprod
  rw [hprod, sum_jasLogWeightLocal_sub_one]

end

end RHTower
