import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanPrimitive
import GaloisForLFunctions.HTGeometry.TrigammaLeadingAsymptotic

/-!
# Gram entries of Ramanujan primitives and their logarithmic growth at primes

For moduli `p, q > 1` the Gram entry `G(p,q) = ∑_N Re C_p(N) Re C_q(N) / (N(N+1))` of the
Ramanujan primitives `C_q(N) = ∑_{n≤N} c_q(n)` converges absolutely because both primitives
are periodic and bounded. For a prime `p`, `C_p(N) = −(N mod p)`, which turns the first `p` terms
of `G(p,q)` into `−∑_{n<p} Re C_q(n)/(n+1)` and bounds the tail by `∑_{n<q} |C_q(n)|`. With the
logarithmic mean `−φ(q)/2` of `C_q`, this gives `G(p,q)/log p → φ(q)/2` as `p → ∞` over primes.

## Main results

- `pmRamanujanPrimitive_prime`: for prime `p`, `C_p(N) = −(N mod p)`.
- `tendsto_pmRamanujanPrimitive_div_nat`: `C_q(N)/N → 0` for `q > 1`.
- `tendsto_pmRamanujanPrimitive_shift_harmonic`: `(1/log N) ∑_{n<N} Re C_q(n)/(n+1) → −φ(q)/2`.
- `summable_pmRamanujanPrimitiveGramTerm`: the Gram series converges for `p, q > 1`.
- `pmRamanujanPrimitiveGram_harmonic_error_le`: for prime `p`, `|G(p,q) + ∑_{n<p} Re C_q(n)/(n+1)| ≤ ∑_{n<q} |C_q(n)|`.
- `tendsto_pmRamanujanPrimitiveGram_prime_div_log`: `G(p,q)/log p → φ(q)/2` as `p → ∞` through the primes.

## Hypotheses

All results are unconditional; they assume `1 < q` (and `p` prime or `1 < p` where stated).
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

/-- For prime `p`, the Ramanujan primitive is `C_p(N) = −(N mod p)`. -/
theorem pmRamanujanPrimitive_prime {p : ℕ} (hp : p.Prime) (N : ℕ) :
    pmRamanujanPrimitive p N = -((N%p : ℕ) : ℂ) := by
  have he : pmRamanujanPrimitive p N = (p : ℂ)*((N/p : ℕ) : ℂ)-(N : ℂ) := by
    rw [pmRamanujanPrimitive_eq_floor,
      Nat.sum_divisorsAntidiagonal (fun a b => (a : ℂ)*(moebius b : ℂ)*((N/a : ℕ) : ℂ)),
      hp.sum_divisors]
    simp [Nat.div_self hp.pos, ArithmeticFunction.moebius_apply_prime hp, sub_eq_add_neg]
  rw [he]
  have hm := congrArg (fun n : ℕ => (n : ℂ)) (Nat.mod_add_div N p)
  push_cast at hm
  linear_combination hm

/-- For prime `p`, `|C_p(N)| ≤ p`. -/
theorem norm_pmRamanujanPrimitive_prime_le {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ‖pmRamanujanPrimitive p N‖ ≤ (p : ℝ) := by
  rw [pmRamanujanPrimitive_prime hp, norm_neg, Complex.norm_natCast]
  exact_mod_cast (Nat.mod_lt N hp.pos).le

/-- For `q > 1`, `C_q(N)/N → 0` (the primitive is bounded). -/
theorem tendsto_pmRamanujanPrimitive_div_nat {q : ℕ} (hq : 1 < q) :
    Tendsto (fun N : ℕ => pmRamanujanPrimitive q N/(N : ℂ)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun N => ?_)
    (show Tendsto (fun N : ℕ => pmRamanujanPrimitiveBound q/(N : ℝ)) atTop (𝓝 0) from
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  simp only [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (norm_pmRamanujanPrimitive_le hq N) (Nat.cast_nonneg N)

theorem pmRamanujanPrimitive_range_sum (q N : ℕ) :
    (∑ n ∈ Finset.range N, pmRamanujanPrimitive q n) =
      (∑ n ∈ Finset.Icc 1 N, pmRamanujanPrimitive q n)-pmRamanujanPrimitive q N := by
  induction N with
  | zero => simp [pmRamanujanPrimitive]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]
    ring

/-- For `q > 1`, the Cesàro mean of the shifted primitive `n ↦ Re C_q(n−1)` tends to `−φ(q)/2`. -/
theorem tendsto_pmRamanujanPrimitive_predecessor_mean {q : ℕ} (hq : 1 < q) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (pmRamanujanPrimitive q (n-1)).re)/(N : ℝ))
      atTop (𝓝 (-(q.totient : ℝ)/2)) := by
  have hz := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_pmRamanujanPrimitive_div_nat hq)
  have hzR : Tendsto (fun N : ℕ => (pmRamanujanPrimitive q N).re/(N : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ← Complex.ofReal_natCast, Complex.div_ofReal_re,
      Complex.zero_re] using hz
  have h := (tendsto_pmRamanujanPrimitive_mean hq).sub hzR
  have he (N : ℕ) :
      (∑ n ∈ Finset.Icc 1 N, (pmRamanujanPrimitive q n).re)/(N : ℝ)-
        (pmRamanujanPrimitive q N).re/(N : ℝ) =
      (∑ n ∈ Finset.Icc 1 N, (pmRamanujanPrimitive q (n-1)).re)/(N : ℝ) := by
    rw [← sub_div, sum_Icc_eq_sum_range_succ (fun n => (pmRamanujanPrimitive q (n-1)).re) N]
    simp only [Nat.add_sub_cancel]
    have hr := congrArg Complex.re (pmRamanujanPrimitive_range_sum q N)
    simpa only [Complex.re_sum, Complex.sub_re] using congrArg (fun r : ℝ => r/(N : ℝ)) hr.symm
  simpa only [sub_zero] using h.congr he

/-- For `q > 1`, `(1/log N) ∑_{n<N} Re C_q(n)/(n+1) → −φ(q)/2`. -/
theorem tendsto_pmRamanujanPrimitive_shift_harmonic {q : ℕ} (hq : 1 < q) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
      (pmRamanujanPrimitive q n).re/((n : ℝ)+1))/Real.log N)
      atTop (𝓝 (-(q.totient : ℝ)/2)) := by
  have h := pm_tendsto_harmonic_average_of_mean
    (tendsto_pmRamanujanPrimitive_predecessor_mean hq)
  simpa only [sum_Icc_eq_sum_range_succ, Nat.add_sub_cancel, Nat.cast_add,
    Nat.cast_one] using h

/-- The Gram term `Re C_p(N) Re C_q(N) / (N(N+1))`. -/
def pmRamanujanPrimitiveGramTerm (p q N : ℕ) : ℝ :=
  (pmRamanujanPrimitive p N).re*(pmRamanujanPrimitive q N).re/
    ((N : ℝ)*((N : ℝ)+1))

/-- The Gram entry `G(p,q) = ∑'_N Re C_p(N) Re C_q(N) / (N(N+1))` of two Ramanujan primitives. -/
def pmRamanujanPrimitiveGram (p q : ℕ) : ℝ :=
  ∑' N : ℕ, pmRamanujanPrimitiveGramTerm p q N

/-- For `p, q > 1`, the Gram series is summable. -/
theorem summable_pmRamanujanPrimitiveGramTerm {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    Summable (pmRamanujanPrimitiveGramTerm p q) := by
  apply (summable_nat_add_iff 1).mp
  have hs := (GaloisForLFunctions.hasSum_one_div_shift_mul_succ (by norm_num : (0 : ℝ)<1)).summable
  apply Summable.of_norm_bounded (hs.mul_left (pmRamanujanPrimitiveBound p*pmRamanujanPrimitiveBound q))
  intro n
  have hpB := (Complex.abs_re_le_norm (pmRamanujanPrimitive p (n+1))).trans
    (norm_pmRamanujanPrimitive_le hp (n+1))
  have hqB := (Complex.abs_re_le_norm (pmRamanujanPrimitive q (n+1))).trans
    (norm_pmRamanujanPrimitive_le hq (n+1))
  simp only [pmRamanujanPrimitiveGramTerm, Real.norm_eq_abs, abs_div,
    Nat.cast_add, Nat.cast_one]
  rw [abs_of_nonneg (by positivity : 0 ≤ ((n : ℝ)+1)*((n : ℝ)+1+1)), abs_mul]
  have hp0 : 0 ≤ pmRamanujanPrimitiveBound p := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hq0 : 0 ≤ pmRamanujanPrimitiveBound q := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc
    _ ≤ (pmRamanujanPrimitiveBound p*pmRamanujanPrimitiveBound q)/
        (((n : ℝ)+1)*((n : ℝ)+1+1)) := by gcongr
    _ = _ := by ring

/-- For prime `p`, the first `p` Gram terms sum to `−∑_{n<p} Re C_q(n)/(n+1)`. -/
theorem pmRamanujanPrimitiveGram_head {p : ℕ} (hp : p.Prime) (q : ℕ) :
    (∑ n ∈ Finset.range p, pmRamanujanPrimitiveGramTerm p q n) =
      -∑ n ∈ Finset.range p, (pmRamanujanPrimitive q n).re/((n : ℝ)+1) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp [pmRamanujanPrimitiveGramTerm, pmRamanujanPrimitive]
  · rw [pmRamanujanPrimitiveGramTerm, pmRamanujanPrimitive_prime hp,
      Nat.mod_eq_of_lt (Finset.mem_range.mp hn)]
    simp only [Complex.neg_re, Complex.natCast_re]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    field_simp

/-- For prime `p` and `q > 1`, the Gram tail from `N = p` is bounded by `∑_{n<q} |C_q(n)|`. -/
theorem pmRamanujanPrimitiveGram_tail_le {p q : ℕ} (hp : p.Prime) (hq : 1 < q) :
    |∑' k : ℕ, pmRamanujanPrimitiveGramTerm p q (p+k)| ≤ pmRamanujanPrimitiveBound q := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have htel := GaloisForLFunctions.hasSum_one_div_shift_mul_succ hpR
  have hmajor := htel.summable.mul_left ((p : ℝ)*pmRamanujanPrimitiveBound q)
  have hs : Summable (fun k : ℕ => pmRamanujanPrimitiveGramTerm p q (p+k)) :=
    (summable_pmRamanujanPrimitiveGramTerm hp.one_lt hq).comp_injective
      (fun a b hab => Nat.add_left_cancel hab)
  have ht (k : ℕ) : ‖pmRamanujanPrimitiveGramTerm p q (p+k)‖ ≤
      ((p : ℝ)*pmRamanujanPrimitiveBound q)*
        (1/(((p : ℝ)+k)*((p : ℝ)+k+1))) := by
    have hpB := (Complex.abs_re_le_norm (pmRamanujanPrimitive p (p+k))).trans
      (norm_pmRamanujanPrimitive_prime_le hp (p+k))
    have hqB := (Complex.abs_re_le_norm (pmRamanujanPrimitive q (p+k))).trans
      (norm_pmRamanujanPrimitive_le hq (p+k))
    simp only [pmRamanujanPrimitiveGramTerm, Real.norm_eq_abs, abs_div, Nat.cast_add]
    rw [abs_of_nonneg (by positivity : 0 ≤ ((p : ℝ)+k)*((p : ℝ)+k+1)), abs_mul]
    calc
      _ ≤ ((p : ℝ)*pmRamanujanPrimitiveBound q)/(((p : ℝ)+k)*((p : ℝ)+k+1)) := by
        gcongr
      _ = _ := by ring
  calc
    _ = ‖∑' k : ℕ, pmRamanujanPrimitiveGramTerm p q (p+k)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' k : ℕ, ‖pmRamanujanPrimitiveGramTerm p q (p+k)‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' k : ℕ, ((p : ℝ)*pmRamanujanPrimitiveBound q)*
        (1/(((p : ℝ)+k)*((p : ℝ)+k+1))) :=
      Summable.tsum_le_tsum ht hs.norm hmajor
    _ = _ := by rw [tsum_mul_left, htel.tsum_eq]; field_simp

/-- For prime `p` and `q > 1`, `|G(p,q) + ∑_{n<p} Re C_q(n)/(n+1)| ≤ ∑_{n<q} |C_q(n)|`. -/
theorem pmRamanujanPrimitiveGram_harmonic_error_le {p q : ℕ} (hp : p.Prime) (hq : 1 < q) :
    |pmRamanujanPrimitiveGram p q +
      ∑ n ∈ Finset.range p, (pmRamanujanPrimitive q n).re/((n : ℝ)+1)| ≤
      pmRamanujanPrimitiveBound q := by
  have hs := summable_pmRamanujanPrimitiveGramTerm hp.one_lt hq
  have hsplit : pmRamanujanPrimitiveGram p q =
      (∑ n ∈ Finset.range p, pmRamanujanPrimitiveGramTerm p q n)+
        ∑' k : ℕ, pmRamanujanPrimitiveGramTerm p q (p+k) := by
    simpa only [pmRamanujanPrimitiveGram, Nat.add_comm] using (hs.sum_add_tsum_nat_add p).symm
  have he : pmRamanujanPrimitiveGram p q +
      (∑ n ∈ Finset.range p, (pmRamanujanPrimitive q n).re/((n : ℝ)+1)) =
        ∑' k : ℕ, pmRamanujanPrimitiveGramTerm p q (p+k) := by
    rw [hsplit, pmRamanujanPrimitiveGram_head hp]
    ring
  rw [he]
  exact pmRamanujanPrimitiveGram_tail_le hp hq

/-- For `q > 1`, `G(p,q)/log p → φ(q)/2` as `p → ∞` through the primes. -/
theorem tendsto_pmRamanujanPrimitiveGram_prime_div_log {q : ℕ} (hq : 1 < q) :
    Tendsto (fun p : {p : ℕ // p.Prime} => pmRamanujanPrimitiveGram p q/Real.log (p : ℕ))
      atTop (𝓝 ((q.totient : ℝ)/2)) := by
  have hcoe : Tendsto (fun p : {p : ℕ // p.Prime} => (p : ℕ)) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes N
    letI : Nonempty {p : ℕ // p.Prime} := ⟨⟨p, hp⟩⟩
    exact eventually_atTop.2 ⟨⟨p, hp⟩, fun r hr => hNp.trans hr⟩
  have hlog : Tendsto (fun p : {p : ℕ // p.Prime} => Real.log (p : ℕ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hcoe)
  let H : ℕ → ℝ := fun p => ∑ n ∈ Finset.range p, (pmRamanujanPrimitive q n).re/((n : ℝ)+1)
  have herror : Tendsto (fun p : {p : ℕ // p.Prime} =>
      (pmRamanujanPrimitiveGram p q+H p)/Real.log (p : ℕ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun p => ?_)
      (show Tendsto (fun p : {p : ℕ // p.Prime} => pmRamanujanPrimitiveBound q/Real.log (p : ℕ))
        atTop (𝓝 0) from tendsto_const_nhds.div_atTop hlog)
    have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.log_pos hp1)]
    exact div_le_div_of_nonneg_right
      (pmRamanujanPrimitiveGram_harmonic_error_le p.property hq) (Real.log_pos hp1).le
  have hmean : Tendsto (fun p : {p : ℕ // p.Prime} => H p/Real.log (p : ℕ))
      atTop (𝓝 (-(q.totient : ℝ)/2)) :=
    (tendsto_pmRamanujanPrimitive_shift_harmonic hq).comp hcoe
  have he (p : {p : ℕ // p.Prime}) :
      (pmRamanujanPrimitiveGram p q+H p)/Real.log (p : ℕ)-H p/Real.log (p : ℕ) =
        pmRamanujanPrimitiveGram p q/Real.log (p : ℕ) := by ring
  simpa only [zero_sub, neg_div, neg_neg] using (herror.sub hmean).congr he

end RHTower
