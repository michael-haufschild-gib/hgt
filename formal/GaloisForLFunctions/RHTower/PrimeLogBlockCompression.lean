import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv


/-!
# Complete Euler quotients after quartic prime-block compression

Group the literal ordinary primes in `[k^4,(k+1)^4)`, `k >= 2`, and replace each
nonempty block by repeated copies of its geometric mean. The zeroth and first
logarithmic moments are retained. Centering removes the linear Taylor term.

The full Euler-log discrepancy, including every prime power, obeys
`norm D_k(s) <= (240 * norm s ^ 2 * exp (2 * norm s) + 30) * k^(1 - 4 * re s)`.
Its sum is holomorphic on `re s > 1/2`. The actual finite Euler quotients converge
to its negative exponential, which is holomorphic and nowhere zero there.
No prime-counting asymptotic, zero-location assumption, or numerical evidence is
used. Primes below 16 are unchanged, so they cancel from the quotient.

This is a source-comparison estimate, not a zero-free theorem for either source.
The comparison supports the paper zero-preservation argument but does not prove RH.
-/

open scoped BigOperators
open Finset Complex

namespace RHTower
noncomputable section

def quarticPrimeBlock (k : ℕ) : Finset ℕ :=
  (Ico (k ^ 4) ((k + 1) ^ 4)).filter Nat.Prime

def quarticPrimeLogCenter (k : ℕ) : ℝ :=
  (∑ p ∈ quarticPrimeBlock k, Real.log p) / (quarticPrimeBlock k).card

def quarticPrimeFirstDiscrepancy (k : ℕ) (s : ℂ) : ℂ :=
  (∑ p ∈ quarticPrimeBlock k, Complex.exp (-s * (Real.log p : ℂ))) -
    (quarticPrimeBlock k).card * Complex.exp (-s * (quarticPrimeLogCenter k : ℂ))

theorem sum_prime_log_centered (k : ℕ) :
    ∑ p ∈ quarticPrimeBlock k, (Real.log p - quarticPrimeLogCenter k) = 0 := by
  classical
  by_cases h : (quarticPrimeBlock k).card = 0
  · simp [Finset.card_eq_zero.mp h]
  · simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, quarticPrimeLogCenter]
    have hc : ((quarticPrimeBlock k).card : ℝ) ≠ 0 := by exact_mod_cast h
    field_simp
    ring

theorem norm_centered_exp_sum_le {ι : Type*} (P : Finset ι) (x : ι → ℝ)
    (c d : ℝ) (s : ℂ) (_hd : 0 ≤ d)
    (hmean : ∑ i ∈ P, (x i - c) = 0) (hdiam : ∀ i ∈ P, |x i - c| ≤ d) :
    ‖(∑ i ∈ P, Complex.exp (-s * (x i : ℂ))) -
      P.card * Complex.exp (-s * (c : ℂ))‖ ≤
      Real.exp (-s.re * c) * P.card * ‖s‖ ^ 2 * d ^ 2 * Real.exp (‖s‖ * d) := by
  classical
  let z : ι → ℂ := fun i => -s * ((x i - c : ℝ) : ℂ)
  have hzsum : ∑ i ∈ P, z i = 0 := by
    simp only [z, ← Finset.mul_sum, ← Complex.ofReal_sum, hmean, ofReal_zero, mul_zero]
  have heq : (∑ i ∈ P, Complex.exp (-s * (x i : ℂ))) -
      P.card * Complex.exp (-s * (c : ℂ)) =
      Complex.exp (-s * (c : ℂ)) * ∑ i ∈ P, (Complex.exp (z i) - 1 - z i) := by
    rw [sum_sub_distrib, sum_sub_distrib, hzsum, sub_zero]
    simp only [sum_const, nsmul_eq_mul, mul_one, mul_sub, Finset.mul_sum]
    have hf : ∀ i, Complex.exp (-s * (c : ℂ)) * Complex.exp (z i) =
        Complex.exp (-s * (x i : ℂ)) := by
      intro i
      rw [← Complex.exp_add]
      congr 1
      dsimp [z]
      push_cast
      ring
    simp_rw [hf]
    ring
  rw [heq, norm_mul, Complex.norm_exp]
  have hreal : (-s * (c : ℂ)).re = -s.re * c := by simp
  rw [hreal]
  have hb : ∀ i ∈ P, ‖Complex.exp (z i) - 1 - z i‖ ≤
      ‖s‖ ^ 2 * d ^ 2 * Real.exp (‖s‖ * d) := by
    intro i hi
    have hz : ‖z i‖ ≤ ‖s‖ * d := by
      simp only [z, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hdiam i hi) (norm_nonneg s)
    have ht := Complex.norm_exp_sub_sum_le_norm_mul_exp (z i) 2
    simp [Finset.sum_range_succ] at ht
    have hr : Complex.exp (z i) - (1 + z i) = Complex.exp (z i) - 1 - z i := by ring
    rw [hr] at ht
    calc
      ‖Complex.exp (z i) - 1 - z i‖ ≤ ‖z i‖ ^ 2 * Real.exp ‖z i‖ := ht
      _ ≤ (‖s‖ * d) ^ 2 * Real.exp (‖s‖ * d) := by gcongr
      _ = ‖s‖ ^ 2 * d ^ 2 * Real.exp (‖s‖ * d) := by ring
  calc
    Real.exp (-s.re * c) * ‖∑ i ∈ P, (Complex.exp (z i) - 1 - z i)‖
      ≤ Real.exp (-s.re * c) * ∑ i ∈ P, ‖Complex.exp (z i) - 1 - z i‖ := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ Real.exp (-s.re * c) * ∑ _i ∈ P,
        (‖s‖ ^ 2 * d ^ 2 * Real.exp (‖s‖ * d)) := by gcongr with i hi; exact hb i hi
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring


theorem quarticPrimeBlock_card_le {k : ℕ} (hk : 1 ≤ k) :
    ((quarticPrimeBlock k).card : ℝ) ≤ 15 * (k : ℝ)^3 := by
  have hnat : (quarticPrimeBlock k).card ≤ (k + 1)^4 - k^4 := by
    exact (Finset.card_filter_le _ _).trans_eq (Nat.card_Ico _ _)
  have hpow : k^4 ≤ (k+1)^4 := Nat.pow_le_pow_left (by omega) 4
  have hr : ((quarticPrimeBlock k).card : ℝ) ≤ ((k : ℝ)+1)^4 - (k : ℝ)^4 := by
    exact_mod_cast hnat
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : (k : ℝ)^2 ≤ (k : ℝ)^3 := by nlinarith [sq_nonneg ((k : ℝ)-1)]
  have h1 : (k : ℝ) ≤ (k : ℝ)^3 := by nlinarith [sq_nonneg ((k : ℝ)-1)]
  have h0 : (1 : ℝ) ≤ (k : ℝ)^3 := h1.trans' hkR
  nlinarith

private theorem quarticPrime_log_bounds {k p : ℕ} (hk : 1 ≤ k)
    (hp : p ∈ quarticPrimeBlock k) :
    4 * Real.log k ≤ Real.log p ∧ Real.log p ≤ 4 * Real.log (k+1) := by
  have hm := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast (Finset.mem_filter.mp hp).2.pos
  constructor
  · have h := Real.log_le_log (pow_pos hk0 4) (show (k : ℝ)^4 ≤ p by exact_mod_cast hm.1)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  · have h := Real.log_le_log hp0 (show (p : ℝ) ≤ ((k : ℝ)+1)^4 by exact_mod_cast hm.2.le)
    simpa only [Real.log_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using h

private theorem quarticPrime_center_bounds {k : ℕ} (hk : 1 ≤ k)
    (hne : (quarticPrimeBlock k).Nonempty) :
    4 * Real.log k ≤ quarticPrimeLogCenter k ∧
    quarticPrimeLogCenter k ≤ 4 * Real.log (k+1) := by
  have hc : (0 : ℝ) < (quarticPrimeBlock k).card := by
    exact_mod_cast Finset.card_pos.mpr hne
  constructor
  · rw [quarticPrimeLogCenter, le_div_iff₀ hc]
    calc
      4 * Real.log k * (quarticPrimeBlock k).card =
        ∑ _p ∈ quarticPrimeBlock k, 4 * Real.log k := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun p hp => (quarticPrime_log_bounds hk hp).1
  · rw [quarticPrimeLogCenter, div_le_iff₀ hc]
    calc
      (∑ p ∈ quarticPrimeBlock k, Real.log p) ≤
        ∑ _p ∈ quarticPrimeBlock k, 4 * Real.log (k+1) :=
          Finset.sum_le_sum fun p hp => (quarticPrime_log_bounds hk hp).2
      _ = _ := by simp [mul_comm]

private theorem quarticPrime_log_width {k : ℕ} (hk : 1 ≤ k) :
    4 * Real.log (k+1) - 4 * Real.log k ≤ 4 / (k : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have h := Real.log_le_sub_one_of_pos (div_pos (show 0 < (k : ℝ)+1 by positivity) hk0)
  rw [Real.log_div (by positivity) hk0.ne'] at h
  have he : ((k : ℝ)+1) / k - 1 = 1 / (k : ℝ) := by field_simp; ring
  rw [he] at h
  calc
    _ = 4 * (Real.log ((k : ℝ)+1) - Real.log k) := by ring
    _ ≤ 4 * (1 / (k : ℝ)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

private theorem quarticPrime_log_diameter {k p : ℕ} (hk : 1 ≤ k)
    (hp : p ∈ quarticPrimeBlock k) :
    |Real.log p - quarticPrimeLogCenter k| ≤ 4 / (k : ℝ) := by
  have h1 := quarticPrime_log_bounds hk hp
  have h2 := quarticPrime_center_bounds hk ⟨p, hp⟩
  have h3 := quarticPrime_log_width hk
  rw [abs_le]
  constructor <;> linarith

/-- Literal all-scale source estimate. No prime-counting asymptotic enters it. -/
theorem quarticPrimeFirstDiscrepancy_bound {k : ℕ} (hk : 2 ≤ k)
    (s : ℂ) (hs : 0 ≤ s.re) :
    ‖quarticPrimeFirstDiscrepancy k s‖ ≤
      240 * ‖s‖^2 * Real.exp (2*‖s‖) * (k : ℝ)^(1-4*s.re) := by
  classical
  by_cases hne : (quarticPrimeBlock k).Nonempty
  swap
  · have hem : quarticPrimeBlock k = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [quarticPrimeFirstDiscrepancy, hem, sum_empty, card_empty, Nat.cast_zero,
      zero_mul, sub_self, norm_zero]
    positivity
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hb := norm_centered_exp_sum_le (quarticPrimeBlock k) (fun p => Real.log p)
    (quarticPrimeLogCenter k) (4 / (k : ℝ)) s (by positivity)
    (sum_prime_log_centered k) (fun p hp => quarticPrime_log_diameter (by omega) hp)
  have hcenter := (quarticPrime_center_bounds (by omega) hne).1
  have hexp : Real.exp (-s.re * quarticPrimeLogCenter k) ≤ (k : ℝ)^(-4*s.re) := by
    rw [Real.rpow_def_of_pos hk0]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hdiam : 4 / (k : ℝ) ≤ 2 := (div_le_iff₀ hk0).mpr (by linarith)
  have hcard := quarticPrimeBlock_card_le (k:=k) (by omega)
  have hpows : (k : ℝ)^(-4*s.re) * (15*(k : ℝ)^3) * ‖s‖^2 * (4/(k : ℝ))^2 *
      Real.exp (2*‖s‖) = 240 * ‖s‖^2 * Real.exp (2*‖s‖) * (k : ℝ)^(1-4*s.re) := by
    rw [show (1 : ℝ)-4*s.re = (-4*s.re)+1 by ring, Real.rpow_add hk0, Real.rpow_one]
    field_simp
    ring
  calc
    ‖quarticPrimeFirstDiscrepancy k s‖ ≤
      Real.exp (-s.re * quarticPrimeLogCenter k) * (quarticPrimeBlock k).card * ‖s‖^2 *
        (4/(k : ℝ))^2 * Real.exp (‖s‖*(4/(k : ℝ))) := hb
    _ ≤ (k : ℝ)^(-4*s.re) * (15*(k : ℝ)^3) * ‖s‖^2 * (4/(k : ℝ))^2 *
        Real.exp (2*‖s‖) := by
          rw [mul_comm 2 ‖s‖]
          gcongr
    _ = _ := hpows


/-- The complete centered first-prime source is absolutely summable throughout the strict
right half-strip, without a prime-distribution premise. -/
theorem summable_quarticPrimeFirstDiscrepancy (s : ℂ) (hs : 1/2 < s.re) :
    Summable fun k : ℕ => quarticPrimeFirstDiscrepancy (k+2) s := by
  have hpow : Summable fun k : ℕ => ((k+2 : ℕ) : ℝ)^(1-4*s.re) :=
    (summable_nat_add_iff 2).mpr (Real.summable_nat_rpow.mpr (by linarith))
  apply Summable.of_norm_bounded (hpow.mul_left (240*‖s‖^2*Real.exp (2*‖s‖)))
  intro k
  exact quarticPrimeFirstDiscrepancy_bound (by omega) s (by linarith)

/-- The holomorphic discrepancy is an actual sum of the literal centered prime blocks. -/
def quarticPrimeFirstDiscrepancySum (s : ℂ) : ℂ :=
  ∑' k : ℕ, quarticPrimeFirstDiscrepancy (k+2) s

theorem differentiable_quarticPrimeFirstDiscrepancy (k : ℕ) :
    Differentiable ℂ (quarticPrimeFirstDiscrepancy k) := by
  unfold quarticPrimeFirstDiscrepancy
  fun_prop

/-- On every bounded part of every strict right half-plane, one explicit summable majorant
works for all blocks and all parameters simultaneously. -/
theorem quarticPrimeFirstDiscrepancy_uniform_bound (σ T : ℝ)
    (hσ : 0 ≤ σ) (_hT : 0 ≤ T) (k : ℕ) (s : ℂ)
    (hs : σ ≤ s.re) (hnorm : ‖s‖ ≤ T) :
    ‖quarticPrimeFirstDiscrepancy (k+2) s‖ ≤
      240*T^2*Real.exp (2*T)*((k+2 : ℕ) : ℝ)^(1-4*σ) := by
  have h := quarticPrimeFirstDiscrepancy_bound (k:=k+2) (by omega) s (hσ.trans hs)
  refine h.trans ?_
  have hbase : (1 : ℝ) ≤ (k+2 : ℕ) := by exact_mod_cast (by omega : 1 ≤ k+2)
  gcongr

/-- Holomorphic continuation of the grouped discrepancy, with its local boundedness proved
from the literal source estimate. -/
theorem differentiableOn_quarticPrimeFirstDiscrepancySum :
    DifferentiableOn ℂ quarticPrimeFirstDiscrepancySum {s : ℂ | 1/2 < s.re} := by
  intro s hs
  change 1/2 < s.re at hs
  let σ : ℝ := (s.re + 1/2)/2
  let r : ℝ := (s.re - 1/2)/2
  let T : ℝ := ‖s‖ + r
  have hr : 0 < r := by dsimp [r]; linarith
  have hσ : 1/2 < σ := by dsimp [σ]; linarith
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hball : ∀ w ∈ Metric.ball s r, σ ≤ w.re ∧ ‖w‖ ≤ T := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hre := Complex.abs_re_le_norm (w-s)
    have hl := (abs_le.mp hre).1
    have hnorm := norm_add_le (w-s) s
    simp only [Complex.sub_re] at hl
    rw [sub_add_cancel] at hnorm
    constructor
    · dsimp [σ, r] at *
      linarith
    · dsimp [T]
      linarith
  have hpow : Summable fun k : ℕ => ((k+2 : ℕ) : ℝ)^(1-4*σ) :=
    (summable_nat_add_iff 2).mpr (Real.summable_nat_rpow.mpr (by linarith))
  have hdiff := differentiableOn_tsum_of_summable_norm
    (hpow.mul_left (240*T^2*Real.exp (2*T)))
    (fun k => (differentiable_quarticPrimeFirstDiscrepancy (k+2)).differentiableOn)
    Metric.isOpen_ball
    (fun k w hw => quarticPrimeFirstDiscrepancy_uniform_bound σ T
      (by linarith) hT k w (hball w hw).1 (hball w hw).2)
  exact (hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self hr))).differentiableWithinAt


/-- One complete prime-power Euler logarithm. -/
def primeScaleEulerLog (x : ℝ) (s : ℂ) : ℂ :=
  -Complex.log (1 - Complex.exp (-s * (x : ℂ)))

/-- The full, grouped Euler-log discrepancy, retaining every prime power. -/
def quarticPrimeEulerDiscrepancy (k : ℕ) (s : ℂ) : ℂ :=
  (∑ p ∈ quarticPrimeBlock k, primeScaleEulerLog (Real.log p) s) -
    (quarticPrimeBlock k).card * primeScaleEulerLog (quarticPrimeLogCenter k) s

private theorem norm_eulerLog_sub_exp {x : ℝ} {s : ℂ}
    (h : ‖Complex.exp (-s * (x : ℂ))‖ ≤ 1/2) :
    ‖primeScaleEulerLog x s - Complex.exp (-s * (x : ℂ))‖ ≤
      Real.exp (-2*s.re*x) := by
  let z := Complex.exp (-s * (x : ℂ))
  have hz : ‖-z‖ < 1 := by dsimp [z]; rw [norm_neg]; linarith
  have ht := Complex.norm_log_one_add_sub_self_le hz
  have hi : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by dsimp [z]; linarith)]
    dsimp [z]
    linarith
  have heq : primeScaleEulerLog x s - z = -(Complex.log (1 + -z) - -z) := by
    dsimp [primeScaleEulerLog, z]
    ring_nf
  rw [heq, norm_neg]
  simp only [norm_neg] at ht
  have hn : ‖z‖^2 = Real.exp (-2*s.re*x) := by
    dsimp [z]
    rw [Complex.norm_exp, ← Real.exp_nat_mul]
    congr 1
    simp
    ring
  calc
    ‖Complex.log (1 + -z) - -z‖ ≤ ‖z‖^2 * (1-‖z‖)⁻¹ / 2 := ht
    _ ≤ ‖z‖^2 := by nlinarith [sq_nonneg ‖z‖]
    _ = _ := hn

private theorem primeScale_exp_bound {k : ℕ} (hk : 2 ≤ k) (s : ℂ)
    (hs : 0 ≤ s.re) {x : ℝ} (hx : 4*Real.log k ≤ x) :
    ‖Complex.exp (-s * (x : ℂ))‖ ≤ (k : ℝ)^(-4*s.re) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  rw [Complex.norm_exp, Real.rpow_def_of_pos hk0]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  nlinarith

private theorem quartic_half_bound {k : ℕ} (hk : 2 ≤ k) {σ : ℝ} (hs : 1/2 ≤ σ) :
    (k : ℝ)^(-4*σ) ≤ 1/2 := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  calc
    (k : ℝ)^(-4*σ) ≤ (k : ℝ)^(-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = 1 / (k : ℝ) := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1/2 := (div_le_iff₀ (by linarith)).mpr (by linarith)

private theorem primeScale_remainder_bound {k : ℕ} (hk : 2 ≤ k) (s : ℂ)
    (hs : 1/2 ≤ s.re) {x : ℝ} (hx : 4*Real.log k ≤ x) :
    ‖primeScaleEulerLog x s - Complex.exp (-s * (x : ℂ))‖ ≤ (k : ℝ)^(-8*s.re) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  refine (norm_eulerLog_sub_exp ((primeScale_exp_bound hk s (by linarith) hx).trans
    (quartic_half_bound hk hs))).trans ?_
  rw [Real.rpow_def_of_pos hk0]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Complete arithmetic tail bound, including all higher prime powers. -/
theorem quarticPrimeEulerDiscrepancy_bound {k : ℕ} (hk : 2 ≤ k)
    (s : ℂ) (hs : 1/2 ≤ s.re) :
    ‖quarticPrimeEulerDiscrepancy k s‖ ≤
      (240*‖s‖^2*Real.exp (2*‖s‖)+30) * (k : ℝ)^(1-4*s.re) := by
  classical
  by_cases hne : (quarticPrimeBlock k).Nonempty
  swap
  · have hem := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [quarticPrimeEulerDiscrepancy, hem, sum_empty, card_empty, Nat.cast_zero,
      zero_mul, sub_self, norm_zero]
    positivity
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hrem : ‖quarticPrimeEulerDiscrepancy k s - quarticPrimeFirstDiscrepancy k s‖ ≤
      2*(quarticPrimeBlock k).card*(k : ℝ)^(-8*s.re) := by
    have he : quarticPrimeEulerDiscrepancy k s - quarticPrimeFirstDiscrepancy k s =
        (∑ p ∈ quarticPrimeBlock k, (primeScaleEulerLog (Real.log p) s -
          Complex.exp (-s * (Real.log p : ℂ)))) -
        (quarticPrimeBlock k).card * (primeScaleEulerLog (quarticPrimeLogCenter k) s -
          Complex.exp (-s * (quarticPrimeLogCenter k : ℂ))) := by
      simp only [quarticPrimeEulerDiscrepancy, quarticPrimeFirstDiscrepancy, sum_sub_distrib]
      ring
    rw [he]
    calc
      _ ≤ (∑ p ∈ quarticPrimeBlock k,
          ‖primeScaleEulerLog (Real.log p) s - Complex.exp (-s * (Real.log p : ℂ))‖) +
          (quarticPrimeBlock k).card * ‖primeScaleEulerLog (quarticPrimeLogCenter k) s -
            Complex.exp (-s * (quarticPrimeLogCenter k : ℂ))‖ := by
        exact (norm_sub_le _ _).trans (add_le_add (norm_sum_le _ _)
          (by rw [norm_mul, Complex.norm_natCast]))
      _ ≤ (∑ _p ∈ quarticPrimeBlock k, (k : ℝ)^(-8*s.re)) +
          (quarticPrimeBlock k).card*(k : ℝ)^(-8*s.re) := by
        gcongr with p hp
        · exact primeScale_remainder_bound hk s hs (quarticPrime_log_bounds (by omega) hp).1
        · exact primeScale_remainder_bound hk s hs (quarticPrime_center_bounds (by omega) hne).1
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring
  have hrem' : ‖quarticPrimeEulerDiscrepancy k s - quarticPrimeFirstDiscrepancy k s‖ ≤
      30 * (k : ℝ)^(1-4*s.re) := by
    refine hrem.trans ?_
    calc
      _ ≤ 2*(15*(k : ℝ)^3)*(k : ℝ)^(-8*s.re) := by
        gcongr
        exact quarticPrimeBlock_card_le (by omega)
      _ = 30*(k : ℝ)^(3-8*s.re) := by
        rw [show (3 : ℝ)-8*s.re = 3+(-8*s.re) by ring, Real.rpow_add hk0, Real.rpow_ofNat]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)) (by norm_num)
  have hfirst := quarticPrimeFirstDiscrepancy_bound hk s (by linarith)
  calc
    _ ≤ ‖quarticPrimeEulerDiscrepancy k s - quarticPrimeFirstDiscrepancy k s‖ +
        ‖quarticPrimeFirstDiscrepancy k s‖ := by simpa only [add_comm] using norm_le_insert' (quarticPrimeEulerDiscrepancy k s) (quarticPrimeFirstDiscrepancy k s)
    _ ≤ 30*(k : ℝ)^(1-4*s.re) +
        240*‖s‖^2*Real.exp (2*‖s‖)*(k : ℝ)^(1-4*s.re) := add_le_add hrem' hfirst
    _ = _ := by ring


private theorem primeScale_factor_mem_slitPlane {x : ℝ} (hx : 0 < x)
    {s : ℂ} (hs : 0 < s.re) :
    1 - Complex.exp (-s * (x : ℂ)) ∈ Complex.slitPlane := by
  have he : ‖Complex.exp (-s * (x : ℂ))‖ < 1 := by
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    nlinarith
  apply Complex.mem_slitPlane_iff.mpr
  left
  have hr := (Complex.re_le_norm (Complex.exp (-s * (x : ℂ)))).trans_lt he
  simp only [Complex.sub_re, Complex.one_re]
  linarith

private theorem differentiableAt_primeScaleEulerLog {x : ℝ} (hx : 0 < x)
    {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (primeScaleEulerLog x) s := by
  have hf : DifferentiableAt ℂ (fun w : ℂ => 1 - Complex.exp (-w * (x : ℂ))) s := by
    fun_prop
  exact (hf.clog (primeScale_factor_mem_slitPlane hx hs)).neg

private theorem differentiableOn_quarticPrimeEulerDiscrepancy {k : ℕ} (hk : 2 ≤ k) :
    DifferentiableOn ℂ (quarticPrimeEulerDiscrepancy k) {s : ℂ | 0 < s.re} := by
  classical
  intro s hs
  change 0 < s.re at hs
  by_cases hne : (quarticPrimeBlock k).Nonempty
  swap
  · have hem := Finset.not_nonempty_iff_eq_empty.mp hne
    have hf : quarticPrimeEulerDiscrepancy k = fun _ => 0 := by
      funext w
      simp [quarticPrimeEulerDiscrepancy, hem]
    rw [hf]
    fun_prop
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hc : 0 < quarticPrimeLogCenter k :=
    lt_of_lt_of_le (by positivity) (quarticPrime_center_bounds (by omega) hne).1
  have hf : DifferentiableAt ℂ (fun w =>
      ∑ p ∈ quarticPrimeBlock k, primeScaleEulerLog (Real.log p) w) s := by
    apply DifferentiableAt.fun_sum
    intro p hp
    apply differentiableAt_primeScaleEulerLog _ hs
    exact lt_of_lt_of_le (by positivity) (quarticPrime_log_bounds (by omega) hp).1
  exact (hf.sub ((differentiableAt_primeScaleEulerLog hc hs).const_mul _)).differentiableWithinAt

/-- Normal convergence includes the complete prime-power arithmetic tail. -/
theorem summable_quarticPrimeEulerDiscrepancy (s : ℂ) (hs : 1/2 < s.re) :
    Summable fun k : ℕ => quarticPrimeEulerDiscrepancy (k+2) s := by
  have hpow : Summable fun k : ℕ => ((k+2 : ℕ) : ℝ)^(1-4*s.re) :=
    (summable_nat_add_iff 2).mpr (Real.summable_nat_rpow.mpr (by linarith))
  apply Summable.of_norm_bounded (hpow.mul_left (240*‖s‖^2*Real.exp (2*‖s‖)+30))
  intro k
  exact quarticPrimeEulerDiscrepancy_bound (by omega) s hs.le

/-- The complete arithmetic logarithm of the Euler comparison. -/
def quarticPrimeEulerDiscrepancySum (s : ℂ) : ℂ :=
  ∑' k : ℕ, quarticPrimeEulerDiscrepancy (k+2) s

private theorem quarticPrimeEulerDiscrepancy_uniform_bound (σ T : ℝ)
    (hσ : 1/2 ≤ σ) (_hT : 0 ≤ T) (k : ℕ) (s : ℂ)
    (hs : σ ≤ s.re) (hnorm : ‖s‖ ≤ T) :
    ‖quarticPrimeEulerDiscrepancy (k+2) s‖ ≤
      (240*T^2*Real.exp (2*T)+30)*((k+2 : ℕ) : ℝ)^(1-4*σ) := by
  have h := quarticPrimeEulerDiscrepancy_bound (k:=k+2) (by omega) s (hσ.trans hs)
  refine h.trans ?_
  have hbase : (1 : ℝ) ≤ (k+2 : ℕ) := by exact_mod_cast (by omega : 1 ≤ k+2)
  gcongr

/-- The full Euler quotient logarithm is holomorphic on the strict right half-plane. -/
theorem differentiableOn_quarticPrimeEulerDiscrepancySum :
    DifferentiableOn ℂ quarticPrimeEulerDiscrepancySum {s : ℂ | 1/2 < s.re} := by
  intro s hs
  change 1/2 < s.re at hs
  let σ : ℝ := (s.re + 1/2)/2
  let r : ℝ := (s.re - 1/2)/2
  let T : ℝ := ‖s‖ + r
  have hr : 0 < r := by dsimp [r]; linarith
  have hσ : 1/2 < σ := by dsimp [σ]; linarith
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hball : ∀ w ∈ Metric.ball s r, σ ≤ w.re ∧ ‖w‖ ≤ T := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hre := Complex.abs_re_le_norm (w-s)
    have hl := (abs_le.mp hre).1
    have hnorm := norm_add_le (w-s) s
    simp only [Complex.sub_re] at hl
    rw [sub_add_cancel] at hnorm
    constructor
    · dsimp [σ, r] at *
      linarith
    · dsimp [T]
      linarith
  have hpow : Summable fun k : ℕ => ((k+2 : ℕ) : ℝ)^(1-4*σ) :=
    (summable_nat_add_iff 2).mpr (Real.summable_nat_rpow.mpr (by linarith))
  have hf : ∀ k : ℕ, DifferentiableOn ℂ (quarticPrimeEulerDiscrepancy (k+2))
      (Metric.ball s r) := by
    intro k
    apply (differentiableOn_quarticPrimeEulerDiscrepancy (by omega)).mono
    intro w hw
    have := (hball w hw).1
    change 0 < w.re
    linarith
  have hdiff := differentiableOn_tsum_of_summable_norm
    (hpow.mul_left (240*T^2*Real.exp (2*T)+30)) hf Metric.isOpen_ball
    (fun k w hw => quarticPrimeEulerDiscrepancy_uniform_bound σ T
      hσ.le hT k w (hball w hw).1 (hball w hw).2)
  exact (hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self hr))).differentiableWithinAt

/-- The all-scale Euler comparison multiplier. Its reciprocal is holomorphic on the same domain. -/
def quarticPrimeCompressionUnit (s : ℂ) : ℂ :=
  Complex.exp (-quarticPrimeEulerDiscrepancySum s)

theorem quarticPrimeCompressionUnit_ne_zero (s : ℂ) :
    quarticPrimeCompressionUnit s ≠ 0 := Complex.exp_ne_zero _

theorem differentiableOn_quarticPrimeCompressionUnit :
    DifferentiableOn ℂ quarticPrimeCompressionUnit {s : ℂ | 1/2 < s.re} :=
  differentiableOn_quarticPrimeEulerDiscrepancySum.neg.cexp

/-- The quotient formed before taking a limit, entirely from literal prime blocks. -/
def quarticPrimeCompressionFinite (N : ℕ) (s : ℂ) : ℂ :=
  ∏ j ∈ Finset.range N,
    (∏ p ∈ quarticPrimeBlock (j+2), (1-Complex.exp (-s*(Real.log p : ℂ)))) /
      (1-Complex.exp (-s*(quarticPrimeLogCenter (j+2) : ℂ)))^
        (quarticPrimeBlock (j+2)).card

private theorem exp_neg_primeScaleEulerLog {x : ℝ} (hx : 0 < x)
    {s : ℂ} (hs : 0 < s.re) :
    Complex.exp (-primeScaleEulerLog x s) = 1-Complex.exp (-s*(x : ℂ)) := by
  simp only [primeScaleEulerLog, neg_neg]
  exact Complex.exp_log (Complex.slitPlane_ne_zero (primeScale_factor_mem_slitPlane hx hs))

private theorem quarticPrimeCompression_block_exp {k : ℕ} (hk : 2 ≤ k)
    {s : ℂ} (hs : 0 < s.re) :
    (∏ p ∈ quarticPrimeBlock k, (1-Complex.exp (-s*(Real.log p : ℂ)))) /
      (1-Complex.exp (-s*(quarticPrimeLogCenter k : ℂ)))^(quarticPrimeBlock k).card =
        Complex.exp (-quarticPrimeEulerDiscrepancy k s) := by
  classical
  by_cases hne : (quarticPrimeBlock k).Nonempty
  swap
  · have hem := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [quarticPrimeEulerDiscrepancy, hem]
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hc : 0 < quarticPrimeLogCenter k :=
    lt_of_lt_of_le (by positivity) (quarticPrime_center_bounds (by omega) hne).1
  have hp : ∀ p ∈ quarticPrimeBlock k, 0 < Real.log (p : ℝ) := by
    intro p hp
    exact lt_of_lt_of_le (by positivity) (quarticPrime_log_bounds (by omega) hp).1
  have he : -quarticPrimeEulerDiscrepancy k s =
      (∑ p ∈ quarticPrimeBlock k, -primeScaleEulerLog (Real.log p) s) -
      (quarticPrimeBlock k).card * (-primeScaleEulerLog (quarticPrimeLogCenter k) s) := by
    simp only [quarticPrimeEulerDiscrepancy, Finset.sum_neg_distrib]
    ring
  rw [he, Complex.exp_sub, Complex.exp_sum, Complex.exp_nat_mul,
    exp_neg_primeScaleEulerLog hc hs]
  congr 1
  apply Finset.prod_congr rfl
  intro p hmem
  exact (exp_neg_primeScaleEulerLog (hp p hmem) hs).symm

/-- Finite physical source quotients are exactly the exponentials of the complete block
logarithms, not of a first-prime truncation. -/
theorem quarticPrimeCompressionFinite_eq_exp (N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    quarticPrimeCompressionFinite N s =
      Complex.exp (-(∑ j ∈ Finset.range N, quarticPrimeEulerDiscrepancy (j+2) s)) := by
  rw [quarticPrimeCompressionFinite, ← Finset.sum_neg_distrib, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro j _
  exact quarticPrimeCompression_block_exp (by omega) hs

/-- A nonzero limit of the actual finite source quotients on every scale; no premise about
zeta zeros, cancellation, or the size of a prime gap is used. -/
theorem tendsto_quarticPrimeCompressionFinite (s : ℂ) (hs : 1/2 < s.re) :
    Filter.Tendsto (fun N : ℕ => quarticPrimeCompressionFinite N s)
      Filter.atTop (nhds (quarticPrimeCompressionUnit s)) := by
  have h := (summable_quarticPrimeEulerDiscrepancy s hs).hasSum.tendsto_sum_nat
  have he := Complex.continuous_exp.continuousAt.tendsto.comp h.neg
  have hs0 : 0 < s.re := by linarith
  simp only [Function.comp_def] at he
  simp_rw [quarticPrimeCompressionFinite_eq_exp _ hs0]
  exact he

end
end RHTower
