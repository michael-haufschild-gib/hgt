import GaloisForLFunctions.RHTower.Sieve.DampedSizeFloor
import GaloisForLFunctions.RHTower.Sieve.PrimeInvLogTail

/-!
# The uniform distance cannot exceed the prime mass

`DampedSizeFloor` bounds the damping by twice the prime mass, using only `1 − Re(f(p)·conj(g(p))) ≤ 2`.
That is attained at a single frequency — for `f(p) = −1` at `t = 0` — but a damped route needs a
distance *uniform* over a whole range of frequencies, and averaging shows the uniform level is at most
the prime mass itself, not twice it.

For each prime the oscillatory average is small: expanding
`Re(f(p)·conj(n^{it}))|_{n=p} = Re(f(p))cos(t log p) + Im(f(p))sin(t log p)` and integrating,

`|∫_0^T Re(f(p)·conj(charFn t p)) dt| ≤ 3/log p`.

Summing against `1/p`, the average of the distance over `[0,T]` is at most
`∑_{p ∈ P}1/p + (3/T)∑_{p ∈ P}1/(p log p)`, so some frequency in the range attains that.  Hence in
`dampedSize`, `e^{−δ²}` can never be smaller than `≍ e^{−∑_p 1/p} ≍ (log z)^{-1}` once `T` is large, and
the first part of the damped size is `≳ (log z/A)e^{2A}(log z)^{-1}`, whose minimum over `A = (σ−1)log z`
is `Θ(1)`.  So even with the truncation tail removed, the damped analytic term is `Θ(x^σ)` — exactly the
trivial size, never below it.  The borderline is a theorem about the distance, not a defect of the Euler
bound.
-/

noncomputable section
namespace RHTower.Sieve
open Finset MeasureTheory

/-- The real part of the paired term, expanded. -/
theorem re_mul_conj_charFn (f : ℕ → ℂ) (t : ℝ) (p : ℕ) :
    (f p * (starRingEnd ℂ) (charFn t p)).re
      = (f p).re * Real.cos (t * Real.log (p : ℝ))
        + (f p).im * Real.sin (t * Real.log (p : ℝ)) := by
  rw [charFn, ← Complex.exp_conj, Complex.mul_re]
  have hconj : (starRingEnd ℂ) (((t * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I)
      = -(((t * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hneg : -(((t * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I)
      = (((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hconj, hneg, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg,
    Real.sin_neg]
  ring

/-- **The oscillatory average at one prime.**  Both `∫_0^T cos(ta)dt` and `∫_0^T sin(ta)dt` are
`O(1/|a|)`, so the paired real part averages to `O(1/log p)`. -/
theorem abs_integral_re_mul_conj_charFn_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} (hp : 2 ≤ p)
    (T : ℝ) :
    |∫ t in (0 : ℝ)..T, (f p * (starRingEnd ℂ) (charFn t p)).re| ≤ 3 / Real.log (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hlog : (0 : ℝ) < Real.log (p : ℝ) := Real.log_pos (by linarith)
  set a : ℝ := Real.log (p : ℝ) with ha
  have hane : a ≠ 0 := hlog.ne'
  have hcos : (∫ t in (0 : ℝ)..T, Real.cos (t * a)) = Real.sin (T * a) / a := by
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
        HasDerivAt (fun s : ℝ => Real.sin (s * a) / a) (Real.cos (t * a)) t := by
      intro t _
      have h1 : HasDerivAt (fun s : ℝ => s * a) a t := by
        simpa using (hasDerivAt_id t).mul_const a
      have h2 : HasDerivAt (fun s : ℝ => Real.sin (s * a)) (Real.cos (t * a) * a) t := h1.sin
      have h3 := h2.div_const a
      have hval : Real.cos (t * a) * a / a = Real.cos (t * a) := by field_simp
      rwa [hval] at h3
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((Real.continuous_cos.comp (continuous_id.mul continuous_const)).intervalIntegrable
        (μ := volume) _ _)]
    simp
  have hsin : (∫ t in (0 : ℝ)..T, Real.sin (t * a)) = (1 - Real.cos (T * a)) / a := by
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
        HasDerivAt (fun s : ℝ => -(Real.cos (s * a)) / a) (Real.sin (t * a)) t := by
      intro t _
      have h1 : HasDerivAt (fun s : ℝ => s * a) a t := by
        simpa using (hasDerivAt_id t).mul_const a
      have h2 : HasDerivAt (fun s : ℝ => Real.cos (s * a)) (-Real.sin (t * a) * a) t := h1.cos
      have h3 := (h2.neg).div_const a
      have hval : -(-Real.sin (t * a) * a) / a = Real.sin (t * a) := by field_simp
      rwa [hval] at h3
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((Real.continuous_sin.comp (continuous_id.mul continuous_const)).intervalIntegrable
        (μ := volume) _ _)]
    simp
    ring
  have hsplit : (∫ t in (0 : ℝ)..T,
        ((f p).re * Real.cos (t * a) + (f p).im * Real.sin (t * a)))
      = (f p).re * (∫ t in (0 : ℝ)..T, Real.cos (t * a))
        + (f p).im * (∫ t in (0 : ℝ)..T, Real.sin (t * a)) := by
    have hc1 : IntervalIntegrable (fun t : ℝ => (f p).re * Real.cos (t * a)) volume 0 T := by
      refine Continuous.intervalIntegrable ?_ _ _
      fun_prop
    have hc2 : IntervalIntegrable (fun t : ℝ => (f p).im * Real.sin (t * a)) volume 0 T := by
      refine Continuous.intervalIntegrable ?_ _ _
      fun_prop
    rw [intervalIntegral.integral_add hc1 hc2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hcongr : (∫ t in (0 : ℝ)..T, (f p * (starRingEnd ℂ) (charFn t p)).re)
      = (f p).re * (Real.sin (T * a) / a) + (f p).im * ((1 - Real.cos (T * a)) / a) := by
    rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      (f p).re * Real.cos (t * a) + (f p).im * Real.sin (t * a))
      (fun t _ => by rw [re_mul_conj_charFn]), hsplit, hcos, hsin]
  rw [hcongr]
  have hre : |(f p).re| ≤ 1 := le_trans (Complex.abs_re_le_norm (f p)) (hf p)
  have him : |(f p).im| ≤ 1 := le_trans (Complex.abs_im_le_norm (f p)) (hf p)
  have hs : |Real.sin (T * a)| ≤ 1 := Real.abs_sin_le_one _
  have hc : |1 - Real.cos (T * a)| ≤ 2 := by
    have h1 := Real.neg_one_le_cos (T * a)
    have h2 := Real.cos_le_one (T * a)
    rw [abs_le]
    constructor <;> linarith
  have h1 : |(f p).re * (Real.sin (T * a) / a)| ≤ 1 / a := by
    rw [abs_mul, abs_div, abs_of_pos hlog]
    calc |(f p).re| * (|Real.sin (T * a)| / a) ≤ 1 * (1 / a) := by
          refine mul_le_mul hre (div_le_div_of_nonneg_right hs hlog.le) (by positivity) zero_le_one
      _ = 1 / a := one_mul _
  have h2 : |(f p).im * ((1 - Real.cos (T * a)) / a)| ≤ 2 / a := by
    rw [abs_mul, abs_div, abs_of_pos hlog]
    calc |(f p).im| * (|1 - Real.cos (T * a)| / a) ≤ 1 * (2 / a) := by
          refine mul_le_mul him (div_le_div_of_nonneg_right hc hlog.le) (by positivity) zero_le_one
      _ = 2 / a := one_mul _
  calc |(f p).re * (Real.sin (T * a) / a) + (f p).im * ((1 - Real.cos (T * a)) / a)|
      ≤ |(f p).re * (Real.sin (T * a) / a)| + |(f p).im * ((1 - Real.cos (T * a)) / a)| :=
        abs_add_le _ _
    _ ≤ 1 / a + 2 / a := by linarith [h1, h2]
    _ = 3 / a := by ring

/-- **The average of the distance over a frequency range.**  The oscillatory terms contribute
`O(1/T)` in total, so the mean of `𝔻²` over `[0,T]` is the prime mass up to that. -/
theorem integral_mulDistSqPair_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {x : ℕ} {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, mulDistSqPair f (charFn t) (Nat.primesLE x))
      ≤ T * (∑ p ∈ Nat.primesLE x, 1 / (p : ℝ)) + 3 * primeInvLogConst := by
  classical
  set P : Finset ℕ := Nat.primesLE x with hP
  have hcont : ∀ p ∈ P, Continuous
      (fun t : ℝ => (1 - (f p * (starRingEnd ℂ) (charFn t p)).re) / (p : ℝ)) := by
    intro p _
    have hexp : (fun t : ℝ => (1 - (f p * (starRingEnd ℂ) (charFn t p)).re) / (p : ℝ))
        = fun t : ℝ => (1 - ((f p).re * Real.cos (t * Real.log (p : ℝ))
            + (f p).im * Real.sin (t * Real.log (p : ℝ)))) / (p : ℝ) := by
      funext t
      rw [re_mul_conj_charFn]
    rw [hexp]
    fun_prop
  have hsplit : (∫ t in (0 : ℝ)..T, mulDistSqPair f (charFn t) P)
      = ∑ p ∈ P, ∫ t in (0 : ℝ)..T, (1 - (f p * (starRingEnd ℂ) (charFn t p)).re) / (p : ℝ) := by
    rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      ∑ p ∈ P, (1 - (f p * (starRingEnd ℂ) (charFn t p)).re) / (p : ℝ))
      (fun t _ => by rw [mulDistSqPair])]
    exact intervalIntegral.integral_finsetSum
      (fun p hp => (hcont p hp).intervalIntegrable (μ := volume) _ _)
  have hterm : ∀ p ∈ P,
      (∫ t in (0 : ℝ)..T, (1 - (f p * (starRingEnd ℂ) (charFn t p)).re) / (p : ℝ))
        ≤ T * (1 / (p : ℝ)) + 3 * (1 / ((p : ℝ) * Real.log (p : ℝ))) := by
    intro p hp
    rw [hP, Nat.mem_primesLE] at hp
    have hp2 : 2 ≤ p := hp.2.two_le
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hlogp : (0 : ℝ) < Real.log (p : ℝ) := Real.log_pos (by linarith)
    have hcp : Continuous (fun t : ℝ => (f p * (starRingEnd ℂ) (charFn t p)).re) := by
      have hexp : (fun t : ℝ => (f p * (starRingEnd ℂ) (charFn t p)).re)
          = fun t : ℝ => (f p).re * Real.cos (t * Real.log (p : ℝ))
              + (f p).im * Real.sin (t * Real.log (p : ℝ)) := by
        funext t
        rw [re_mul_conj_charFn]
      rw [hexp]
      fun_prop
    have hdiv : (∫ t in (0 : ℝ)..T, (1 - (f p * (starRingEnd ℂ) (charFn t p)).re) / (p : ℝ))
        = (T - ∫ t in (0 : ℝ)..T, (f p * (starRingEnd ℂ) (charFn t p)).re) / (p : ℝ) := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
        (intervalIntegrable_const (μ := volume)) (hcp.intervalIntegrable (μ := volume) _ _),
        intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
    rw [hdiv]
    have hosc := abs_integral_re_mul_conj_charFn_le hf hp2 T
    have hlow : -(3 / Real.log (p : ℝ))
        ≤ ∫ t in (0 : ℝ)..T, (f p * (starRingEnd ℂ) (charFn t p)).re := (abs_le.1 hosc).1
    rw [div_le_iff₀ hp0]
    have hval : (T * (1 / (p : ℝ)) + 3 * (1 / ((p : ℝ) * Real.log (p : ℝ)))) * (p : ℝ)
        = T + 3 / Real.log (p : ℝ) := by
      field_simp
    rw [hval]
    linarith
  rw [hsplit]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have htail := sum_prime_inv_mul_log_le x
  rw [← hP] at htail
  linarith [mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 3)]

/-- `primeInvLogConst` is positive. -/
theorem primeInvLogConst_pos : 0 < primeInvLogConst := by
  rw [primeInvLogConst]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (1 : ℝ) ≤ mertensBlockConst := by
    rw [mertensBlockConst]
    have h2 : (0 : ℝ) ≤ Real.log 2 := hlog2.le
    have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hL := logSqTailConst_nonneg
    linarith
  have hmax : (1 : ℝ) ≤ max mertensBlockConst (2 * Real.log 4) :=
    le_trans h1 (le_max_left _ _)
  have hnum : (0 : ℝ) < 2 * max mertensBlockConst (2 * Real.log 4) := by linarith
  positivity

/-- **Some frequency in the range is at distance at most the prime mass.**  The uniform distance level a
damped route can use is therefore `∑_{p ≤ x}1/p + O(1/T)`, never more. -/
theorem exists_mulDistSqPair_le_prime_mass {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (x : ℕ) {T : ℝ}
    (hT : 0 < T) :
    ∃ t ∈ Set.Icc (0 : ℝ) T,
      mulDistSqPair f (charFn t) (Nat.primesLE x)
        ≤ (∑ p ∈ Nat.primesLE x, 1 / (p : ℝ)) + 4 * primeInvLogConst / T := by
  classical
  by_contra hcon
  push Not at hcon
  set P : Finset ℕ := Nat.primesLE x with hP
  set A : ℝ := ∑ p ∈ P, 1 / (p : ℝ) with hA
  have hcont : Continuous (fun t : ℝ => mulDistSqPair f (charFn t) P) := by
    have hfun : (fun t : ℝ => mulDistSqPair f (charFn t) P)
        = fun t : ℝ => ∑ p ∈ P, (1 - (f p * (starRingEnd ℂ) (charFn t p)).re) / (p : ℝ) := by
      funext t
      rw [mulDistSqPair]
    rw [hfun]
    refine continuous_finsetSum _ fun p _ => ?_
    have hexp : (fun t : ℝ => (1 - (f p * (starRingEnd ℂ) (charFn t p)).re) / (p : ℝ))
        = fun t : ℝ => (1 - ((f p).re * Real.cos (t * Real.log (p : ℝ))
            + (f p).im * Real.sin (t * Real.log (p : ℝ)))) / (p : ℝ) := by
      funext t
      rw [re_mul_conj_charFn]
    rw [hexp]
    fun_prop
  have hlow : ∀ t ∈ Set.Icc (0 : ℝ) T, A + 4 * primeInvLogConst / T
      ≤ mulDistSqPair f (charFn t) P := fun t ht => le_of_lt (hcon t ht)
  have hmono := intervalIntegral.integral_mono_on hT.le
    (intervalIntegrable_const (μ := volume)) (hcont.intervalIntegrable (μ := volume) _ _) hlow
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
  have hup := integral_mulDistSqPair_le hf (x := x) hT.le
  rw [← hP, ← hA] at hup
  have hval : T * (A + 4 * primeInvLogConst / T) = T * A + 4 * primeInvLogConst := by
    field_simp
  rw [hval] at hmono
  have hC := primeInvLogConst_pos
  linarith [hmono, hup]

/-- **A uniform distance hypothesis is bounded by the prime mass.**  Whatever supplies the level `δ` —
zero-free region, sieve, anything — if it holds uniformly on `|t| ≤ T` then `δ² ≤ ∑_{p ≤ z}1/p + O(1/T)`. -/
theorem sq_le_prime_mass_of_uniform {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {z : ℕ} {δ T : ℝ}
    (hδ : 0 ≤ δ) (hT : 0 < T)
    (hunif : ∀ t : ℝ, |t| ≤ T → δ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z))) :
    δ ^ (2 : ℕ) ≤ (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ)) + 4 * primeInvLogConst / T := by
  obtain ⟨t, ht, hle⟩ := exists_mulDistSqPair_le_prime_mass hf z hT
  rw [Set.mem_Icc] at ht
  have habs : |t| ≤ T := by
    rw [abs_of_nonneg ht.1]
    exact ht.2
  have hnn : 0 ≤ mulDistSqPair f (charFn t) (Nat.primesLE z) :=
    mulDistSqPair_nonneg_disc (fun p _ => hf p) (fun p _ => (norm_charFn t p).le)
      (fun p hp => (Nat.prime_of_mem_primesLE hp).pos)
  have hsq : δ ^ (2 : ℕ) ≤ mulDistSqPair f (charFn t) (Nat.primesLE z) := by
    have h := pow_le_pow_left₀ hδ (hunif t habs) 2
    rwa [Real.sq_sqrt hnn] at h
  exact le_trans hsq hle

/-- **The damped size, floored by the prime mass.**  The fully assembled unconditional obstruction: no
uniform distance level can push `dampedSize` below this, whatever arithmetic input supplies it. -/
theorem dampedSize_ge_of_uniform {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {z : ℕ} {σ δ T : ℝ}
    (hσ : 1 < σ) (hδ : 0 ≤ δ) (hT : 0 < T) (L : ℕ)
    (hunif : ∀ t : ℝ, |t| ≤ T → δ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z))) :
    (1 + 1 / (σ - 1))
        * Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4)
            - ((∑ p ∈ Nat.primesLE z, 1 / (p : ℝ)) + 4 * primeInvLogConst / T))
      ≤ dampedSize σ δ z L :=
  dampedSize_ge_of_sq_le hσ z L (sq_le_prime_mass_of_uniform hf hδ hT hunif)

/-- **The average from below.**  The same oscillatory estimate, with the other sign. -/
theorem le_integral_mulDistSqPair {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {x : ℕ} (T : ℝ) :
    T * (∑ p ∈ Nat.primesLE x, 1 / (p : ℝ)) - 3 * primeInvLogConst
      ≤ ∫ t in (0 : ℝ)..T, mulDistSqPair f (charFn t) (Nat.primesLE x) := by
  classical
  set P : Finset ℕ := Nat.primesLE x with hP
  have hcont : ∀ p ∈ P, Continuous
      (fun t : ℝ => (1 - (f p * (starRingEnd ℂ) (charFn t p)).re) / (p : ℝ)) := by
    intro p _
    have hexp : (fun t : ℝ => (1 - (f p * (starRingEnd ℂ) (charFn t p)).re) / (p : ℝ))
        = fun t : ℝ => (1 - ((f p).re * Real.cos (t * Real.log (p : ℝ))
            + (f p).im * Real.sin (t * Real.log (p : ℝ)))) / (p : ℝ) := by
      funext t
      rw [re_mul_conj_charFn]
    rw [hexp]
    fun_prop
  have hsplit : (∫ t in (0 : ℝ)..T, mulDistSqPair f (charFn t) P)
      = ∑ p ∈ P, ∫ t in (0 : ℝ)..T, (1 - (f p * (starRingEnd ℂ) (charFn t p)).re) / (p : ℝ) := by
    rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      ∑ p ∈ P, (1 - (f p * (starRingEnd ℂ) (charFn t p)).re) / (p : ℝ))
      (fun t _ => by rw [mulDistSqPair])]
    exact intervalIntegral.integral_finsetSum
      (fun p hp => (hcont p hp).intervalIntegrable (μ := volume) _ _)
  have hterm : ∀ p ∈ P,
      T * (1 / (p : ℝ)) - 3 * (1 / ((p : ℝ) * Real.log (p : ℝ)))
        ≤ ∫ t in (0 : ℝ)..T, (1 - (f p * (starRingEnd ℂ) (charFn t p)).re) / (p : ℝ) := by
    intro p hp
    rw [hP, Nat.mem_primesLE] at hp
    have hp2 : 2 ≤ p := hp.2.two_le
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hlogp : (0 : ℝ) < Real.log (p : ℝ) := Real.log_pos (by linarith)
    have hcp : Continuous (fun t : ℝ => (f p * (starRingEnd ℂ) (charFn t p)).re) := by
      have hexp : (fun t : ℝ => (f p * (starRingEnd ℂ) (charFn t p)).re)
          = fun t : ℝ => (f p).re * Real.cos (t * Real.log (p : ℝ))
              + (f p).im * Real.sin (t * Real.log (p : ℝ)) := by
        funext t
        rw [re_mul_conj_charFn]
      rw [hexp]
      fun_prop
    have hdiv : (∫ t in (0 : ℝ)..T, (1 - (f p * (starRingEnd ℂ) (charFn t p)).re) / (p : ℝ))
        = (T - ∫ t in (0 : ℝ)..T, (f p * (starRingEnd ℂ) (charFn t p)).re) / (p : ℝ) := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
        (intervalIntegrable_const (μ := volume)) (hcp.intervalIntegrable (μ := volume) _ _),
        intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
    rw [hdiv]
    have hosc := abs_integral_re_mul_conj_charFn_le hf hp2 T
    have hup : (∫ t in (0 : ℝ)..T, (f p * (starRingEnd ℂ) (charFn t p)).re)
        ≤ 3 / Real.log (p : ℝ) := (abs_le.1 hosc).2
    rw [le_div_iff₀ hp0]
    have hval : (T * (1 / (p : ℝ)) - 3 * (1 / ((p : ℝ) * Real.log (p : ℝ)))) * (p : ℝ)
        = T - 3 / Real.log (p : ℝ) := by
      field_simp
    rw [hval]
    linarith
  rw [hsplit]
  refine le_trans ?_ (Finset.sum_le_sum hterm)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have htail := sum_prime_inv_mul_log_le x
  rw [← hP] at htail
  linarith [mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 3)]

/-- **Some frequency in the range is at distance at least the prime mass.**  The companion of
`exists_mulDistSqPair_le_prime_mass`: the maximum over the range is also the prime mass up to `O(1/T)`,
so the achievable damping is exactly `e^{−∑_p 1/p}` in both directions. -/
theorem exists_prime_mass_le_mulDistSqPair {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (x : ℕ) {T : ℝ}
    (hT : 0 < T) :
    ∃ t ∈ Set.Icc (0 : ℝ) T,
      (∑ p ∈ Nat.primesLE x, 1 / (p : ℝ)) - 4 * primeInvLogConst / T
        ≤ mulDistSqPair f (charFn t) (Nat.primesLE x) := by
  classical
  by_contra hcon
  push Not at hcon
  set P : Finset ℕ := Nat.primesLE x with hP
  set A : ℝ := ∑ p ∈ P, 1 / (p : ℝ) with hA
  have hcont : Continuous (fun t : ℝ => mulDistSqPair f (charFn t) P) := by
    have hfun : (fun t : ℝ => mulDistSqPair f (charFn t) P)
        = fun t : ℝ => ∑ p ∈ P, (1 - (f p * (starRingEnd ℂ) (charFn t p)).re) / (p : ℝ) := by
      funext t
      rw [mulDistSqPair]
    rw [hfun]
    refine continuous_finsetSum _ fun p _ => ?_
    have hexp : (fun t : ℝ => (1 - (f p * (starRingEnd ℂ) (charFn t p)).re) / (p : ℝ))
        = fun t : ℝ => (1 - ((f p).re * Real.cos (t * Real.log (p : ℝ))
            + (f p).im * Real.sin (t * Real.log (p : ℝ)))) / (p : ℝ) := by
      funext t
      rw [re_mul_conj_charFn]
    rw [hexp]
    fun_prop
  have hupper : ∀ t ∈ Set.Icc (0 : ℝ) T,
      mulDistSqPair f (charFn t) P ≤ A - 4 * primeInvLogConst / T := fun t ht =>
    le_of_lt (hcon t ht)
  have hmono := intervalIntegral.integral_mono_on hT.le
    (hcont.intervalIntegrable (μ := volume) _ _) (intervalIntegrable_const (μ := volume)) hupper
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
  have hlow := le_integral_mulDistSqPair hf (x := x) T
  rw [← hP, ← hA] at hlow
  have hval : T * (A - 4 * primeInvLogConst / T) = T * A - 4 * primeInvLogConst := by
    field_simp
  rw [hval] at hmono
  have hC := primeInvLogConst_pos
  linarith [hmono, hlow]

end RHTower.Sieve
end
