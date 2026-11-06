import Mathlib

/-!
# The divisor trace of the Eisenstein series on the unitary line

`τ_b(N) = Σ_{nm=N} cos(b log(n/m))` is the Dirichlet convolution of `n^{ib}` and `n^{−ib}`:

* `eisensteinTrace_mul_of_coprime`: it is multiplicative;
* `eisensteinTrace_prime_pow`: `τ_b(p^k) = U_k(cos(b log p))`, the Chebyshev polynomial of the second kind;
* `LSeries_eisensteinTrace`: `Σ τ_b(N) N^{−s} = ζ(s − ib) ζ(s + ib)`;
* `eisensteinTrace_eq_cpow_sum`: `τ_b(N) = N^{ib} Σ_{d∣N} d^{−2ib}`, the arithmetic Fourier coefficient of `E*(z, ½ + ib)`;
* `tsum_trace_second_difference`: the coefficients invert the operator `1 − 2cos(b log p) σ + σ²`;
* `tsum_trace_mul_pow`: at `σ = r < 1` this gives the Euler factor `(1 − 2 cos(b log p) r + r²)⁻¹`.
-/

open Complex Finset
open scoped ArithmeticFunction LSeries.notation

namespace GaloisForLFunctions.CompletedArithmeticForms

noncomputable section

/-- `τ_b(N) = Σ_{nm=N} cos(b log(n/m))`. -/
def eisensteinTrace (b : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ N.divisorsAntidiagonal, Real.cos (b * (Real.log p.1 - Real.log p.2))

/-- `n ↦ n^{ib}` as an arithmetic function. -/
def phaseFunction (b : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else cexp (((b * Real.log n : ℝ) : ℂ) * I), by simp⟩

theorem phaseFunction_apply (b : ℝ) {n : ℕ} (hn : n ≠ 0) :
    phaseFunction b n = cexp (((b * Real.log n : ℝ) : ℂ) * I) :=
  if_neg hn

theorem phaseFunction_isMultiplicative (b : ℝ) : (phaseFunction b).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, ?_⟩
  · simp [phaseFunction_apply]
  · intro m n hm hn _
    rw [phaseFunction_apply b (mul_ne_zero hm hn), phaseFunction_apply b hm, phaseFunction_apply b hn,
      ← Complex.exp_add]
    congr 1
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hn)]
    push_cast
    ring

/-- The sine part of the trace cancels under `d ↦ N/d`. -/
theorem sum_sin_eq_zero (b : ℝ) (N : ℕ) :
    ∑ p ∈ N.divisorsAntidiagonal, Real.sin (b * (Real.log p.1 - Real.log p.2)) = 0 := by
  have hswap := Finset.sum_map N.divisorsAntidiagonal (Equiv.prodComm ℕ ℕ).toEmbedding
    (fun p => Real.sin (b * (Real.log p.1 - Real.log p.2)))
  rw [Nat.map_swap_divisorsAntidiagonal] at hswap
  have hneg : ∑ p ∈ N.divisorsAntidiagonal, Real.sin (b * (Real.log p.2 - Real.log p.1)) =
      -∑ p ∈ N.divisorsAntidiagonal, Real.sin (b * (Real.log p.1 - Real.log p.2)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [show b * (Real.log p.2 - Real.log p.1) = -(b * (Real.log p.1 - Real.log p.2)) by ring,
      Real.sin_neg]
  simp only [Equiv.coe_toEmbedding, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap] at hswap
  linarith only [hswap, hneg]

/-- `τ_b` is the Dirichlet convolution of the two opposite phases. -/
theorem eisensteinTrace_complex (b : ℝ) (N : ℕ) :
    (eisensteinTrace b N : ℂ) = (phaseFunction b * phaseFunction (-b)) N := by
  rw [ArithmeticFunction.mul_apply]
  have hterm : ∀ p ∈ N.divisorsAntidiagonal, phaseFunction b p.1 * phaseFunction (-b) p.2 =
      ((Real.cos (b * (Real.log p.1 - Real.log p.2)) : ℝ) : ℂ) +
        ((Real.sin (b * (Real.log p.1 - Real.log p.2)) : ℝ) : ℂ) * I := by
    intro p hp
    obtain ⟨hmul, hN⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have h1 : p.1 ≠ 0 := fun h => hN (by rw [← hmul, h, zero_mul])
    have h2 : p.2 ≠ 0 := fun h => hN (by rw [← hmul, h, mul_zero])
    rw [phaseFunction_apply _ h1, phaseFunction_apply _ h2, ← Complex.exp_add]
    have he : ((b * Real.log p.1 : ℝ) : ℂ) * I + ((-b * Real.log p.2 : ℝ) : ℂ) * I =
        ((b * (Real.log p.1 - Real.log p.2) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [he, Complex.exp_mul_I]
    push_cast
    rfl
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul]
  have hs : (∑ p ∈ N.divisorsAntidiagonal,
      ((Real.sin (b * (Real.log p.1 - Real.log p.2)) : ℝ) : ℂ)) = 0 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) (sum_sin_eq_zero b N)
    simpa only [Complex.ofReal_sum, Complex.ofReal_zero] using this
  rw [hs, zero_mul, add_zero]
  simp only [eisensteinTrace, Complex.ofReal_sum]

@[simp] theorem eisensteinTrace_zero (b : ℝ) : eisensteinTrace b 0 = 0 := by
  simp [eisensteinTrace]

@[simp] theorem eisensteinTrace_one (b : ℝ) : eisensteinTrace b 1 = 1 := by
  simp [eisensteinTrace]

/-- `τ_b` is multiplicative. -/
theorem eisensteinTrace_mul_of_coprime (b : ℝ) {m n : ℕ} (h : m.Coprime n) :
    eisensteinTrace b (m * n) = eisensteinTrace b m * eisensteinTrace b n := by
  have hm := ((phaseFunction_isMultiplicative b).mul
    (phaseFunction_isMultiplicative (-b))).map_mul_of_coprime h
  rw [← eisensteinTrace_complex, ← eisensteinTrace_complex, ← eisensteinTrace_complex] at hm
  exact_mod_cast hm

/-- The trace is bounded by the divisor count, hence by `N`. -/
theorem abs_eisensteinTrace_le (b : ℝ) (N : ℕ) : |eisensteinTrace b N| ≤ N := by
  unfold eisensteinTrace
  calc
    _ ≤ ∑ p ∈ N.divisorsAntidiagonal, |Real.cos (b * (Real.log p.1 - Real.log p.2))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ N.divisorsAntidiagonal, (1 : ℝ) :=
      Finset.sum_le_sum fun _ _ => Real.abs_cos_le_one _
    _ = ((N.divisorsAntidiagonal).card : ℝ) := by simp
    _ = (N.divisors.card : ℝ) := by
      have h := Nat.sum_divisorsAntidiagonal (n := N) (fun _ _ => (1 : ℕ))
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
      exact_mod_cast h
    _ ≤ N := by exact_mod_cast Nat.card_divisors_le_self N

/-- The cosine sum at a prime power. -/
def cosSum (θ : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ range (k + 1), Real.cos (((2 * j : ℝ) - k) * θ)

/-- The three-term recurrence of the cosine sums. -/
theorem cosSum_add_two (θ : ℝ) (k : ℕ) :
    cosSum θ (k + 2) = 2 * Real.cos θ * cosSum θ (k + 1) - cosSum θ k := by
  have hprod : 2 * Real.cos θ * cosSum θ (k + 1) =
      ∑ j ∈ range (k + 2), (Real.cos (((2 * j : ℝ) - k) * θ) +
        Real.cos (((2 * j : ℝ) - ((k + 2 : ℕ) : ℝ)) * θ)) := by
    unfold cosSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : ((2 * j : ℝ) - k) * θ = ((2 * j : ℝ) - ((k + 1 : ℕ) : ℝ)) * θ + θ := by
      push_cast; ring
    have h2 : ((2 * j : ℝ) - ((k + 2 : ℕ) : ℝ)) * θ =
        ((2 * j : ℝ) - ((k + 1 : ℕ) : ℝ)) * θ - θ := by
      push_cast; ring
    rw [h1, h2, Real.cos_add, Real.cos_sub]
    ring
  have hA : ∑ j ∈ range (k + 2), Real.cos (((2 * j : ℝ) - k) * θ) =
      cosSum θ k + Real.cos (((k : ℝ) + 2) * θ) := by
    rw [Finset.sum_range_succ]
    congr 2
    push_cast
    ring
  have hB : cosSum θ (k + 2) =
      ∑ j ∈ range (k + 2), Real.cos (((2 * j : ℝ) - ((k + 2 : ℕ) : ℝ)) * θ) +
        Real.cos (((k : ℝ) + 2) * θ) := by
    unfold cosSum
    rw [Finset.sum_range_succ]
    congr 2
    push_cast
    ring
  rw [hprod, Finset.sum_add_distrib, hA, hB]
  ring

/-- The cosine sums are the Chebyshev polynomials of the second kind. -/
theorem cosSum_eq_chebyshev (θ : ℝ) (k : ℕ) :
    cosSum θ k = (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos θ) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [cosSum]
  | one =>
      simp only [cosSum, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num [Real.cos_neg]
      ring
  | more k h0 h1 =>
      rw [cosSum_add_two, h0, h1]
      have hU := Polynomial.Chebyshev.U_add_two ℝ (k : ℤ)
      have he : ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 := by push_cast; ring
      have he1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      rw [he, he1, hU]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]

/-- At a prime power the trace is the cosine sum. -/
theorem eisensteinTrace_prime_pow_eq_cosSum (b : ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    eisensteinTrace b (p ^ k) = cosSum (b * Real.log p) k := by
  unfold eisensteinTrace cosSum
  rw [Nat.sum_divisorsAntidiagonal (fun n m => Real.cos (b * (Real.log n - Real.log m))),
    Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Nat.pow_div hj' hp.pos]
  push_cast
  rw [Real.log_pow, Real.log_pow, Nat.cast_sub hj']
  congr 1
  ring

/-- **`τ_b(p^k) = U_k(cos(b log p))`.** -/
theorem eisensteinTrace_prime_pow (b : ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    eisensteinTrace b (p ^ k) =
      (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos (b * Real.log p)) := by
  rw [eisensteinTrace_prime_pow_eq_cosSum b hp, cosSum_eq_chebyshev]

/-- The prime-power trace grows at most linearly in the exponent. -/
theorem abs_eisensteinTrace_prime_pow_le (b : ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    |eisensteinTrace b (p ^ k)| ≤ (k : ℝ) + 1 := by
  rw [eisensteinTrace_prime_pow_eq_cosSum b hp]
  unfold cosSum
  calc
    _ ≤ ∑ j ∈ range (k + 1), |Real.cos (((2 * j : ℝ) - k) * (b * Real.log p))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range (k + 1), (1 : ℝ) := Finset.sum_le_sum fun _ _ => Real.abs_cos_le_one _
    _ = _ := by simp

/-- The recurrence of the prime-power traces. -/
theorem eisensteinTrace_prime_pow_add_two (b : ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    eisensteinTrace b (p ^ (k + 2)) =
      2 * Real.cos (b * Real.log p) * eisensteinTrace b (p ^ (k + 1)) -
        eisensteinTrace b (p ^ k) := by
  simp only [eisensteinTrace_prime_pow_eq_cosSum b hp, cosSum_add_two]

theorem eisensteinTrace_prime (b : ℝ) {p : ℕ} (hp : p.Prime) :
    eisensteinTrace b p = 2 * Real.cos (b * Real.log p) := by
  have h := eisensteinTrace_prime_pow_eq_cosSum b hp 1
  rw [pow_one] at h
  rw [h]
  simp only [cosSum, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Real.cos_neg]
  ring

/-- **The inverse of `1 − 2 cos(b log p) σ + σ²`.** With `g k = f(x + k log p)`, the sum
`Σ τ_b(p^k) g k` is the unique solution of the second-difference equation with source `g 0`. -/
theorem tsum_trace_second_difference (b : ℝ) {p : ℕ} (hp : p.Prime) {g : ℕ → ℝ}
    (h0 : Summable fun k => eisensteinTrace b (p ^ k) * g k)
    (h1 : Summable fun k => eisensteinTrace b (p ^ k) * g (k + 1))
    (h2 : Summable fun k => eisensteinTrace b (p ^ k) * g (k + 2)) :
    (∑' k, eisensteinTrace b (p ^ k) * g k) -
        2 * Real.cos (b * Real.log p) * (∑' k, eisensteinTrace b (p ^ k) * g (k + 1)) +
        (∑' k, eisensteinTrace b (p ^ k) * g (k + 2)) = g 0 := by
  set a : ℕ → ℝ := fun k => eisensteinTrace b (p ^ k) with ha
  set c := Real.cos (b * Real.log p) with hc
  have ha0 : a 0 = 1 := by simp [ha]
  have ha1 : a 1 = 2 * c := by simp only [ha, pow_one]; exact eisensteinTrace_prime b hp
  have hrec (k : ℕ) : a (k + 2) = 2 * c * a (k + 1) - a k :=
    eisensteinTrace_prime_pow_add_two b hp k
  have hs0 : Summable fun k => a (k + 2) * g (k + 2) := (summable_nat_add_iff 2).mpr h0
  have hs1 : Summable fun k => a (k + 1) * g (k + 2) := by
    have := (summable_nat_add_iff 1).mpr h1
    simpa only [add_assoc, one_add_one_eq_two] using this
  have e0 := h0.sum_add_tsum_nat_add 2
  have e1 := h1.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at e0 e1
  have ht : (∑' k, a (k + 2) * g (k + 2)) - 2 * c * (∑' k, a (k + 1) * g (k + 2)) +
      ∑' k, a k * g (k + 2) = 0 := by
    rw [← tsum_mul_left, ← hs0.tsum_sub (hs1.mul_left _), ← (hs0.sub (hs1.mul_left _)).tsum_add h2]
    have : ∀ k, a (k + 2) * g (k + 2) - 2 * c * (a (k + 1) * g (k + 2)) + a k * g (k + 2) = 0 := by
      intro k
      rw [hrec]
      ring
    exact (tsum_congr this).trans tsum_zero
  have e1' : (∑' k, a k * g (k + 1)) = a 0 * g 1 + ∑' k, a (k + 1) * g (k + 2) := by
    simpa only [add_assoc, one_add_one_eq_two, zero_add] using e1.symm
  have e0' : (∑' k, a k * g k) =
      a 0 * g 0 + a 1 * g 1 + ∑' k, a (k + 2) * g (k + 2) := by
    simpa only [zero_add] using e0.symm
  rw [e0', e1', ha0, ha1]
  rw [ha0] at e1'
  linarith only [ht]

/-- The exponential series of the prime-power traces is absolutely convergent. -/
theorem summable_trace_mul_pow (b : ℝ) {p : ℕ} (hp : p.Prime) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun k => eisensteinTrace b (p ^ k) * r ^ k := by
  have hmajor : Summable fun k : ℕ => ((k : ℝ) + 1) * r ^ k := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
      (by rwa [Real.norm_of_nonneg hr0])
    have h2 := summable_geometric_of_lt_one hr0 hr
    simpa only [pow_one, add_mul, one_mul] using h1.add h2
  refine Summable.of_norm_bounded hmajor fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr0 k)]
  exact mul_le_mul_of_nonneg_right (abs_eisensteinTrace_prime_pow_le b hp k) (pow_nonneg hr0 k)

/-- The denominator of the Euler factor is strictly positive. -/
theorem eulerDenominator_pos (θ : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    0 < 1 - 2 * Real.cos θ * r + r ^ 2 := by
  have hc := Real.cos_le_one θ
  nlinarith only [sq_pos_of_pos (sub_pos.mpr hr), mul_nonneg hr0 (sub_nonneg.mpr hc)]

/-- **The Euler factor.** `Σ U_k(cos θ) r^k = (1 − 2 cos θ r + r²)⁻¹`. -/
theorem tsum_trace_mul_pow (b : ℝ) {p : ℕ} (hp : p.Prime) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    (∑' k, eisensteinTrace b (p ^ k) * r ^ k) =
      (1 - 2 * Real.cos (b * Real.log p) * r + r ^ 2)⁻¹ := by
  have hs := summable_trace_mul_pow b hp hr0 hr
  have h := tsum_trace_second_difference b hp (g := fun k => r ^ k) hs
    (by simpa only [pow_succ, mul_assoc] using hs.mul_right r)
    (by simpa only [pow_succ, mul_assoc] using (hs.mul_right r).mul_right r)
  have e1 : (∑' k, eisensteinTrace b (p ^ k) * r ^ (k + 1)) =
      (∑' k, eisensteinTrace b (p ^ k) * r ^ k) * r := by
    rw [← tsum_mul_right]
    exact tsum_congr fun k => by rw [pow_succ]; ring
  have e2 : (∑' k, eisensteinTrace b (p ^ k) * r ^ (k + 2)) =
      (∑' k, eisensteinTrace b (p ^ k) * r ^ k) * r ^ 2 := by
    rw [← tsum_mul_right]
    exact tsum_congr fun k => by rw [pow_add]; ring
  rw [e1, e2, pow_zero] at h
  apply eq_inv_of_mul_eq_one_left
  linear_combination h

/-- The Euler factor is the squared modulus of `1 − r e^{iθ}`, inverted. -/
theorem eulerDenominator_eq_normSq (θ r : ℝ) :
    1 - 2 * Real.cos θ * r + r ^ 2 = ‖1 - (r : ℂ) * cexp ((θ : ℂ) * I)‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.exp_mul_I]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  nlinarith only [Real.sin_sq_add_cos_sq θ]

private theorem term_phaseFunction (b : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (↗(phaseFunction b)) s n = LSeries.term 1 (s - (b : ℂ) * I) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, phaseFunction_apply b hn]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hcpow : (n : ℂ) ^ ((b : ℂ) * I) = cexp (((b * Real.log n : ℝ) : ℂ) * I) := by
      rw [Complex.cpow_def_of_ne_zero hn', ← Complex.natCast_log]
      congr 1
      push_cast
      ring
    rw [Complex.cpow_sub _ _ hn', hcpow]
    simp only [Pi.one_apply]
    field_simp

private theorem summable_phaseFunction (b : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (↗(phaseFunction b)) s := by
  have h : LSeriesSummable 1 (s - (b : ℂ) * I) := by
    rw [LSeriesSummable_one_iff]
    simpa using hs
  unfold LSeriesSummable at h ⊢
  convert h using 1
  funext n
  exact term_phaseFunction b s n

private theorem LSeries_phaseFunction (b : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗(phaseFunction b)) s = riemannZeta (s - (b : ℂ) * I) := by
  rw [← LSeries_one_eq_riemannZeta (by simpa using hs)]
  unfold LSeries
  exact tsum_congr (term_phaseFunction b s)

/-- **The Dirichlet series of the trace.** `Σ τ_b(N) N^{−s} = ζ(s − ib) ζ(s + ib)`, `Re s > 1`. -/
theorem LSeries_eisensteinTrace (b : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun N => (eisensteinTrace b N : ℂ)) s =
      riemannZeta (s - (b : ℂ) * I) * riemannZeta (s + (b : ℂ) * I) := by
  have hfun : (fun N => (eisensteinTrace b N : ℂ)) = ↗(phaseFunction b * phaseFunction (-b)) := by
    funext N
    exact eisensteinTrace_complex b N
  rw [hfun, ArithmeticFunction.LSeries_mul' (summable_phaseFunction b hs)
    (summable_phaseFunction (-b) hs), LSeries_phaseFunction b hs, LSeries_phaseFunction (-b) hs]
  congr 2
  push_cast
  ring

/-- **The arithmetic Fourier coefficient of the Eisenstein series.**
`τ_b(N) = N^{ib} Σ_{d∣N} d^{−2ib}` for `N ≥ 1`. -/
theorem eisensteinTrace_eq_cpow_sum (b : ℝ) {N : ℕ} (hN : N ≠ 0) :
    (eisensteinTrace b N : ℂ) =
      (N : ℂ) ^ ((b : ℂ) * I) * ∑ d ∈ N.divisors, (d : ℂ) ^ (-2 * ((b : ℂ) * I)) := by
  rw [eisensteinTrace_complex, mul_comm (phaseFunction b), ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun n m => phaseFunction (-b) n * phaseFunction b m),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hq : N / d ≠ 0 :=
    (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)).ne'
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  rw [phaseFunction_apply _ hd0, phaseFunction_apply _ hq, ← Complex.exp_add,
    Complex.cpow_def_of_ne_zero hN', Complex.cpow_def_of_ne_zero hd', ← Complex.exp_add,
    ← Complex.natCast_log, ← Complex.natCast_log]
  congr 1
  have hlog : Real.log N = Real.log d + Real.log (N / d : ℕ) := by
    have hmul := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    rw [← Real.log_mul (by exact_mod_cast hd0) (by exact_mod_cast hq)]
    congr 1
    exact_mod_cast hmul.symm
  rw [hlog]
  push_cast
  ring

end

end GaloisForLFunctions.CompletedArithmeticForms

#print axioms GaloisForLFunctions.CompletedArithmeticForms.eisensteinTrace_prime_pow
#print axioms GaloisForLFunctions.CompletedArithmeticForms.LSeries_eisensteinTrace
#print axioms GaloisForLFunctions.CompletedArithmeticForms.tsum_trace_mul_pow
#print axioms GaloisForLFunctions.CompletedArithmeticForms.eisensteinTrace_eq_cpow_sum
