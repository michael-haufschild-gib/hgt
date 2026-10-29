import GaloisForLFunctions.HTGeometry.IndependentCoordSeriesConvergence
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Analysis.PSeries

/-!
# Independent centered signs with logarithmic coefficients

For arbitrary Bernoulli biases and coefficients bounded by `log n`, centered partial sums
are almost surely `O(√x log²x)`. Kolmogorov's maximal inequality on dyadic horizons gives
summable exceptional probabilities. The bound includes deterministic biases.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.HTGeometry.LogarithmicSigns

/-- A sign is positive with probability `p`. -/
def bitLaw (p : unitInterval) : Measure Bool := bernoulliMeasure true false p
instance (p : unitInterval) : IsProbabilityMeasure (bitLaw p) := by
  unfold bitLaw
  infer_instance

/-- Independent signs with coordinate-dependent probabilities. -/
def signLaw (q : ℕ → unitInterval) : Measure (ℕ → Bool) :=
  Measure.infinitePi fun n => bitLaw (q n)
instance (q : ℕ → unitInterval) : IsProbabilityMeasure (signLaw q) := by
  unfold signLaw
  infer_instance

/-- The coefficient at `n + 1`, signed by coordinate `n` and centered at its mean. -/
def term (q : ℕ → unitInterval) (a : ℕ → ℝ) (n : ℕ) (b : Bool) : ℂ :=
  (if b then (a (n + 1) : ℂ) else -(a (n + 1) : ℂ)) -
    (((2 * (q n : ℝ) - 1) * a (n + 1) : ℝ) : ℂ)

private theorem measurable_term (q : ℕ → unitInterval) (a : ℕ → ℝ) (n : ℕ) :
    Measurable (term q a n) := measurable_of_countable _

private theorem norm_term_le (q : ℕ → unitInterval) (a : ℕ → ℝ) (n : ℕ) (b : Bool) :
    ‖term q a n b‖ ≤ 2 * |a (n + 1)| := by
  have hq : |2 * (q n : ℝ) - 1| ≤ 1 := abs_le.mpr
    ⟨by linarith only [(q n).2.1], by linarith only [(q n).2.2]⟩
  have hm : |(2 * (q n : ℝ) - 1) * a (n + 1)| ≤ |a (n + 1)| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hq
  have hs : ‖(if b then (a (n + 1) : ℂ) else -(a (n + 1) : ℂ))‖ =
      |a (n + 1)| := by cases b <;> simp
  have h := norm_sub_le
    (if b then (a (n + 1) : ℂ) else -(a (n + 1) : ℂ))
    (((2 * (q n : ℝ) - 1) * a (n + 1) : ℝ) : ℂ)
  rw [hs, Complex.norm_real, Real.norm_eq_abs] at h
  exact h.trans (by linarith only [hm])

private theorem mean_term (q : ℕ → unitInterval) (a : ℕ → ℝ) (n : ℕ) :
    ∫ b, term q a n b ∂bitLaw (q n) = 0 := by
  rw [bitLaw, integral_bernoulliMeasure]
  norm_num [term, Algebra.smul_def]
  ring

/-- Centering a Bernoulli sign leaves variance `4p(1-p)a²`. -/
private theorem second_moment_term (q : ℕ → unitInterval) (a : ℕ → ℝ) (n : ℕ) :
    ∫ b, ‖term q a n b‖ ^ 2 ∂bitLaw (q n) =
      4 * (q n : ℝ) * (1 - (q n : ℝ)) * a (n + 1) ^ 2 := by
  have ht : ‖term q a n true‖ ^ 2 =
      (a (n + 1) - (2 * (q n : ℝ) - 1) * a (n + 1)) ^ 2 := by
    change ‖(a (n + 1) : ℂ) -
      (((2 * (q n : ℝ) - 1) * a (n + 1) : ℝ) : ℂ)‖ ^ 2 = _
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hf : ‖term q a n false‖ ^ 2 =
      (-a (n + 1) - (2 * (q n : ℝ) - 1) * a (n + 1)) ^ 2 := by
    change ‖-(a (n + 1) : ℂ) -
      (((2 * (q n : ℝ) - 1) * a (n + 1) : ℝ) : ℂ)‖ ^ 2 = _
    rw [← Complex.ofReal_neg, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  rw [bitLaw, integral_bernoulliMeasure, ht, hf]
  simp only [smul_eq_mul]
  ring

private theorem second_moment_term_le (q : ℕ → unitInterval) (a : ℕ → ℝ) (n : ℕ) :
    ∫ b, ‖term q a n b‖ ^ 2 ∂bitLaw (q n) ≤ a (n + 1) ^ 2 := by
  rw [second_moment_term]
  have hq : 4 * (q n : ℝ) * (1 - (q n : ℝ)) ≤ 1 := by
    nlinarith only [sq_nonneg (2 * (q n : ℝ) - 1)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hq (sq_nonneg (a (n + 1)))

private theorem second_moment_sum_le (q : ℕ → unitInterval) (a : ℕ → ℝ) (N : ℕ) :
    ∫ ω, ‖coordPartialSum (term q a) N ω‖ ^ 2 ∂(signLaw q) ≤
      ∑ n ∈ range N, a (n + 1) ^ 2 := by
  unfold signLaw
  rw [integral_normSq_coordPartialSum (term q a) (fun n => bitLaw (q n))
    (measurable_term q a) (norm_term_le q a) (mean_term q a)]
  exact sum_le_sum fun n _ => second_moment_term_le q a n

private theorem dyadic_energy_bound (a : ℕ → ℝ)
    (ha : ∀ n, 1 ≤ n → |a n| ≤ Real.log n) (K : ℕ) :
    (∑ n ∈ range (2 ^ (K + 1)), a (n + 1) ^ 2) ≤
      (2 : ℝ) ^ (K + 1) * ((K : ℝ) + 1) ^ 2 := by
  have hl2 : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  calc
    _ ≤ ∑ _n ∈ range (2 ^ (K + 1)), ((K : ℝ) + 1) ^ 2 := by
      refine sum_le_sum fun n hn => ?_
      have hnle : n + 1 ≤ 2 ^ (K + 1) := mem_range.mp hn
      have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (n + 1 : ℕ))
        (show ((n + 1 : ℕ) : ℝ) ≤ (2 ^ (K + 1) : ℕ) by exact_mod_cast hnle)
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hlog
      have hab : |a (n + 1)| ≤ (K : ℝ) + 1 := by
        have hab' := ha (n + 1) (by omega)
        have hK : (0 : ℝ) ≤ (K : ℝ) + 1 := by positivity
        have hmul := mul_le_mul_of_nonneg_left hl2 hK
        push_cast at hlog hab'
        linarith only [hab', hlog, hmul]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (a (n + 1))) hab 2
    _ = _ := by simp

private def exceptional (q : ℕ → unitInterval) (a : ℕ → ℝ) (K : ℕ) : Set (ℕ → Bool) :=
  {ω | ∃ n ≤ 2 ^ (K + 1),
    Real.sqrt ((2 : ℝ) ^ (K + 1)) * ((K : ℝ) + 1) ^ 2 ≤
      ‖coordPartialSum (term q a) n ω‖}

/-- A dyadic maximal fluctuation has probability at most the reciprocal square of its index. -/
private theorem measure_exceptional_le (q : ℕ → unitInterval) (a : ℕ → ℝ)
    (ha : ∀ n, 1 ≤ n → |a n| ≤ Real.log n) (K : ℕ) :
    (signLaw q).real (exceptional q a K) ≤ 1 / ((K : ℝ) + 1) ^ 2 := by
  have hmax := kolmogorov_maximal_inequality (term q a) (fun n => bitLaw (q n)) (fun _ => false)
    (measurable_term q a) (norm_term_le q a) (mean_term q a)
    (2 ^ (K + 1))
    (lam := Real.sqrt ((2 : ℝ) ^ (K + 1)) * ((K : ℝ) + 1) ^ 2) (by positivity)
  change _ * (signLaw q).real (exceptional q a K) ≤
    ∫ ω, ‖coordPartialSum (term q a) (2 ^ (K + 1)) ω‖ ^ 2 ∂(signLaw q) at hmax
  have hvar := (hmax.trans (second_moment_sum_le q a _)).trans (dyadic_energy_bound a ha K)
  rw [mul_pow, Real.sq_sqrt (by positivity)] at hvar
  rw [le_div_iff₀ (by positivity)]
  have hcancel : ((signLaw q).real (exceptional q a K) * ((K : ℝ) + 1) ^ 2) *
      ((2 : ℝ) ^ (K + 1) * ((K : ℝ) + 1) ^ 2) ≤
        1 * ((2 : ℝ) ^ (K + 1) * ((K : ℝ) + 1) ^ 2) := by
    calc
      _ = ((2 : ℝ) ^ (K + 1) * (((K : ℝ) + 1) ^ 2) ^ 2) *
          (signLaw q).real (exceptional q a K) := by ring
      _ ≤ (2 : ℝ) ^ (K + 1) * ((K : ℝ) + 1) ^ 2 := hvar
      _ = _ := by rw [one_mul]
  exact le_of_mul_le_mul_right hcancel (by positivity)

/-- Borel–Cantelli controls every partial sum below each sufficiently large dyadic horizon. -/
private theorem ae_dyadic_bound (q : ℕ → unitInterval) (a : ℕ → ℝ)
    (ha : ∀ n, 1 ≤ n → |a n| ≤ Real.log n) :
    ∀ᵐ ω ∂(signLaw q), ∀ᶠ K : ℕ in atTop, ∀ n ≤ 2 ^ (K + 1),
      ‖coordPartialSum (term q a) n ω‖ ^ 2 ≤
        (2 : ℝ) ^ (K + 1) * ((K : ℝ) + 1) ^ 4 := by
  have hsum : Summable fun K : ℕ => 1 / ((K : ℝ) + 1) ^ 2 := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using h
  have hfinite : ∑' K, signLaw q (exceptional q a K) ≠ ⊤ := by
    refine ne_top_of_le_ne_top
      (ENNReal.ofReal_ne_top (r := ∑' K : ℕ, 1 / ((K : ℝ) + 1) ^ 2)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hsum]
    refine ENNReal.tsum_le_tsum fun K => ?_
    rw [← ENNReal.ofReal_toReal (measure_ne_top (signLaw q) (exceptional q a K)),
      ← measureReal_def]
    exact ENNReal.ofReal_le_ofReal (measure_exceptional_le q a ha K)
  filter_upwards [ae_eventually_notMem hfinite] with ω hω
  filter_upwards [hω] with K hK n hn
  have hnorm : ‖coordPartialSum (term q a) n ω‖ <
      Real.sqrt ((2 : ℝ) ^ (K + 1)) * ((K : ℝ) + 1) ^ 2 :=
    not_le.mp fun h => hK ⟨n, hn, h⟩
  calc
    _ ≤ (Real.sqrt ((2 : ℝ) ^ (K + 1)) * ((K : ℝ) + 1) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm.le 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt (by positivity)]; ring

/-- The adjacent dyadic horizon converts the maximal estimate to a real-horizon bound. -/
private theorem dyadic_bound_real (q : ℕ → unitInterval) (a : ℕ → ℝ) (ω : ℕ → Bool)
    (h : ∀ᶠ K : ℕ in atTop, ∀ n ≤ 2 ^ (K + 1),
      ‖coordPartialSum (term q a) n ω‖ ^ 2 ≤
        (2 : ℝ) ^ (K + 1) * ((K : ℝ) + 1) ^ 4) :
    ∀ᶠ x : ℝ in atTop, ‖coordPartialSum (term q a) ⌊x⌋₊ ω‖ ≤
      32 * Real.sqrt x * Real.log x ^ 2 := by
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp h
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    eventually_ge_atTop ((2 ^ (K₀ + 1) : ℕ) : ℝ)] with x hx hxK
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hl : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hx
  let N := ⌊x⌋₊
  let K := Nat.log 2 N
  have hNbig : 2 ^ (K₀ + 1) ≤ N := Nat.le_floor hxK
  have hN0 : N ≠ 0 := by
    have hpowpos : 0 < 2 ^ (K₀ + 1) := by positivity
    omega
  have hKK₀ : K₀ ≤ K := by
    have hle := Nat.le_log_of_pow_le one_lt_two hNbig
    omega
  have hNpow : N ≤ 2 ^ (K + 1) := (Nat.lt_pow_succ_log_self one_lt_two N).le
  have hbound := hK₀ K hKK₀ N hNpow
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hxpos.le
  have hpow : (2 : ℝ) ^ K ≤ (N : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hN0
  have h2K : (2 : ℝ) ^ (K + 1) ≤ 2 * x := by
    rw [pow_succ]
    nlinarith only [hpow, hNx]
  have hlog : (K : ℝ) * Real.log 2 ≤ Real.log x := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (hpow.trans hNx)
  have hKlog : (K : ℝ) + 1 ≤ 4 * Real.log x := by
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      simpa only [show (1 : ℝ) - (2 : ℝ)⁻¹ = 1 / 2 by norm_num] using
        Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have hKn := Nat.cast_nonneg (α := ℝ) K
    have hmul := mul_le_mul_of_nonneg_left hl2 hKn
    linarith only [hlog, hmul, hl]
  have hsqrt : Real.sqrt x ^ 2 = x := Real.sq_sqrt hxpos.le
  have hsq : ‖coordPartialSum (term q a) N ω‖ ^ 2 ≤
      (32 * Real.sqrt x * Real.log x ^ 2) ^ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (K + 1) * ((K : ℝ) + 1) ^ 4 := hbound
      _ ≤ (2 * x) * (4 * Real.log x) ^ 4 :=
        mul_le_mul h2K (pow_le_pow_left₀ (by positivity) hKlog 4)
          (by positivity) (by positivity)
      _ ≤ 1024 * x * Real.log x ^ 4 := by
        have hp : 0 ≤ x * Real.log x ^ 4 := by positivity
        nlinarith only [hp]
      _ = _ := by rw [mul_pow, mul_pow, hsqrt]; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- Independent signed logarithmic coefficients differ from their mean by square-root
precision almost surely, uniformly over all choices of coordinate biases. -/
theorem ae_eventually_norm_partialSum_floor_le (q : ℕ → unitInterval) (a : ℕ → ℝ)
    (ha : ∀ n, 1 ≤ n → |a n| ≤ Real.log n) :
    ∀ᵐ ω ∂(signLaw q), ∀ᶠ x : ℝ in atTop, ‖coordPartialSum (term q a) ⌊x⌋₊ ω‖ ≤
      32 * Real.sqrt x * Real.log x ^ 2 :=
  (ae_dyadic_bound q a ha).mono fun ω hω => dyadic_bound_real q a ω hω

end GaloisForLFunctions.HTGeometry.LogarithmicSigns
