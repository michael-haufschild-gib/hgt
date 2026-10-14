import GaloisForLFunctions.RHTower.JointAncestryConstantVectorEveryScale

/-!
# Exponential zero weights with a uniform angle

For a point `s` of the closed critical strip put `z = s(1−s)` and `w = z^{1/2}` (principal branch).
Then `Re z = ¼ − (Re s − ½)² + (Im s)² ≥ (Im s)²`, and the square root satisfies

`Re w ≥ |Im s|`,   `|Im w| ≤ |Re s − ½|`   (`le_re_sqrt_mul_one_sub`, `abs_im_sqrt_mul_one_sub_le`).

So the **exponential zero weight** `ω_λ(s) = e^{−λ w}`, `0 < λ ≤ π`, decays like
`|ω_λ(s)| ≤ e^{−λ |Im s|}` and keeps a uniform angle:
`Re ω_λ(s) ≥ cos(λ/2) |ω_λ(s)|` (`cos_mul_norm_le_re_expZeroWeight`).  On the critical line it is a
positive real number (`expZeroWeight_eq_ofReal_of_re_eq_half`), and it is summable over the zeros
(`summable_norm_expZeroWeight`).

These are exactly the properties the constant-vector JAS receivers use of the weights
`1/(s(1−s))`: positivity on the line, a uniform angle off it, and summability.  The exponential
decay additionally confines every zero that can compete with a target of big sum `Z` to heights
`≲ Z/λ`, where zero-density estimates apply.
-/

open Complex Filter
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- The principal square root of `s(1−s)`. -/
def sqrtMulOneSub (s : ℂ) : ℂ := (s * (1 - s)) ^ (2⁻¹ : ℂ)

/-- The exponential zero weight `e^{−λ √(s(1−s))}`. -/
def expZeroWeight (lam : ℝ) (s : ℂ) : ℂ := cexp (-(lam : ℂ) * sqrtMulOneSub s)

theorem re_mul_one_sub (s : ℂ) :
    (s * (1 - s)).re = 1 / 4 - (s.re - 1 / 2) ^ 2 + s.im ^ 2 := by simp; ring

theorem im_mul_one_sub (s : ℂ) : (s * (1 - s)).im = -2 * (s.re - 1 / 2) * s.im := by simp; ring

theorem sqrtMulOneSub_sq (s : ℂ) : sqrtMulOneSub s ^ 2 = s * (1 - s) := by
  rw [sqrtMulOneSub]; exact Complex.cpow_ofNat_inv_pow _ 2

theorem re_sqrtMulOneSub (s : ℂ) :
    (sqrtMulOneSub s).re = Real.sqrt ((‖s * (1 - s)‖ + (s * (1 - s)).re) / 2) := by
  rw [sqrtMulOneSub]; exact Complex.cpow_inv_two_re _

/-- `Re √(s(1−s)) ≥ |Im s|` in the closed strip. -/
theorem le_re_sqrt_mul_one_sub {s : ℂ} (hs : |s.re - 1 / 2| ≤ 1 / 2) :
    |s.im| ≤ (sqrtMulOneSub s).re := by
  rw [re_sqrtMulOneSub, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  have hd := abs_le.mp hs
  have hz := re_mul_one_sub s
  have hre : s.im ^ 2 ≤ (s * (1 - s)).re := by rw [hz]; nlinarith
  have hn := Complex.re_le_norm (s * (1 - s))
  linarith

/-- `|Im √(s(1−s))| ≤ |Re s − ½|` in the closed strip. -/
theorem abs_im_sqrt_mul_one_sub_le {s : ℂ} (hs : |s.re - 1 / 2| ≤ 1 / 2) :
    |(sqrtMulOneSub s).im| ≤ |s.re - 1 / 2| := by
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = sqrtMulOneSub s := ⟨_, rfl⟩
  have hsq : w ^ 2 = s * (1 - s) := by rw [hw]; exact sqrtMulOneSub_sq s
  have hre : w.re * w.re - w.im * w.im = (s * (1 - s)).re := by
    rw [← hsq]; simp [sq]
  have him : 2 * (w.re * w.im) = (s * (1 - s)).im := by
    rw [← hsq]; simp [sq]; ring
  have hge : |s.im| ≤ w.re := hw ▸ le_re_sqrt_mul_one_sub hs
  rw [← hw]
  rw [im_mul_one_sub] at him
  rw [re_mul_one_sub] at hre
  have hd := abs_le.mp hs
  rcases eq_or_lt_of_le ((abs_nonneg s.im).trans hge) with h0 | hpos
  · -- `Re w = 0`, so `Im s = 0` and `Re z ≥ 0` forces `Im w = 0`
    have hy : s.im = 0 := abs_eq_zero.mp (le_antisymm (h0 ▸ hge) (abs_nonneg _))
    rw [← h0, hy] at hre
    have : w.im * w.im ≤ 0 := by nlinarith
    have hwi : w.im = 0 := by nlinarith [mul_self_nonneg w.im]
    rw [hwi, abs_zero]; exact abs_nonneg _
  · -- `|Im w| = |d| |Im s| / Re w ≤ |d|`
    have h1 : |w.re * w.im| = |s.re - 1 / 2| * |s.im| := by
      have : w.re * w.im = -((s.re - 1 / 2) * s.im) := by linarith
      rw [this, abs_neg, abs_mul]
    rw [abs_mul, abs_of_pos hpos] at h1
    have h2 : w.re * |w.im| ≤ w.re * |s.re - 1 / 2| := by
      rw [h1]; exact mul_le_mul_of_nonneg_left hge (abs_nonneg _) |>.trans_eq (mul_comm _ _)
    exact le_of_mul_le_mul_left h2 hpos

theorem norm_expZeroWeight (lam : ℝ) (s : ℂ) :
    ‖expZeroWeight lam s‖ = Real.exp (-(lam * (sqrtMulOneSub s).re)) := by
  rw [expZeroWeight, Complex.norm_exp]
  congr 1
  simp

/-- **Decay**: `|ω_λ(s)| ≤ e^{−λ |Im s|}` for `λ ≥ 0`. -/
theorem norm_expZeroWeight_le {lam : ℝ} (hlam : 0 ≤ lam) {s : ℂ} (hs : |s.re - 1 / 2| ≤ 1 / 2) :
    ‖expZeroWeight lam s‖ ≤ Real.exp (-(lam * |s.im|)) := by
  rw [norm_expZeroWeight]
  exact Real.exp_le_exp.mpr (by nlinarith [le_re_sqrt_mul_one_sub hs])

/-- **Uniform angle**: `Re ω_λ(s) ≥ cos(λ/2) |ω_λ(s)|` for `0 ≤ λ ≤ π`. -/
theorem cos_mul_norm_le_re_expZeroWeight {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam ≤ Real.pi)
    {s : ℂ} (hs : |s.re - 1 / 2| ≤ 1 / 2) :
    Real.cos (lam / 2) * ‖expZeroWeight lam s‖ ≤ (expZeroWeight lam s).re := by
  have him := abs_im_sqrt_mul_one_sub_le hs
  rw [norm_expZeroWeight, expZeroWeight, Complex.exp_re]
  have e1 : (-(lam : ℂ) * sqrtMulOneSub s).re = -(lam * (sqrtMulOneSub s).re) := by simp
  have e2 : (-(lam : ℂ) * sqrtMulOneSub s).im = -(lam * (sqrtMulOneSub s).im) := by simp
  rw [e1, e2, Real.cos_neg, mul_comm (Real.cos (lam / 2))]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  -- `|λ Im w| ≤ λ/2 ≤ π/2`
  have hb : |lam * (sqrtMulOneSub s).im| ≤ lam / 2 := by
    rw [abs_mul, abs_of_nonneg hlam0]
    have := mul_le_mul_of_nonneg_left (him.trans hs) hlam0
    linarith
  rw [← Real.cos_abs (lam * (sqrtMulOneSub s).im)]
  refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hb

/-- On the critical line the weight is a positive real number. -/
theorem expZeroWeight_eq_ofReal_of_re_eq_half (lam : ℝ) {s : ℂ} (hs : s.re = 1 / 2) :
    expZeroWeight lam s = ((Real.exp (-(lam * Real.sqrt (1 / 4 + s.im ^ 2))) : ℝ) : ℂ) := by
  have hz : s * (1 - s) = ((1 / 4 + s.im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re, re_mul_one_sub, hs]; ring
    · rw [Complex.ofReal_im, im_mul_one_sub, hs]; ring
  have hw : sqrtMulOneSub s = ((Real.sqrt (1 / 4 + s.im ^ 2) : ℝ) : ℂ) := by
    have h2 : (2⁻¹ : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [sqrtMulOneSub, hz, h2, ← Complex.ofReal_cpow (by positivity), Real.sqrt_eq_rpow]
  rw [expZeroWeight, hw, ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  congr 2
  ring

/-- `|ω_λ(s)| ≤ (8/λ²) |1/(s(1−s))|`: the weights are dominated by the JAS weights. -/
theorem norm_expZeroWeight_le_inv {lam : ℝ} (hlam : 0 < lam) {s : ℂ}
    (hs : |s.re - 1 / 2| < 1 / 2) :
    ‖expZeroWeight lam s‖ ≤ 8 / lam ^ 2 * ‖1 / (s * (1 - s))‖ := by
  have hz0 : 0 < (s * (1 - s)).re := by
    rw [re_mul_one_sub]; have := abs_lt.mp hs; nlinarith [sq_nonneg s.im]
  have hzn : 0 < ‖s * (1 - s)‖ := lt_of_lt_of_le hz0 (Complex.re_le_norm _)
  rw [norm_expZeroWeight, norm_div, norm_one, re_sqrtMulOneSub]
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.sqrt ((‖s * (1 - s)‖ + (s * (1 - s)).re) / 2) := ⟨_, rfl⟩
  rw [← hx]
  have hx2 : ‖s * (1 - s)‖ / 2 ≤ x ^ 2 := by
    rw [hx, Real.sq_sqrt (by positivity)]; linarith
  have hx0 : 0 ≤ x := by rw [hx]; exact Real.sqrt_nonneg _
  -- `e^{−λx} ≤ 2/(λx)² ≤ 4/(λ² ‖z‖)`
  have hexp : Real.exp (-(lam * x)) * (lam * x) ^ 2 ≤ 2 := by
    have h1 : (lam * x) ^ 2 / 2 ≤ Real.exp (lam * x) := by
      have := Real.quadratic_le_exp_of_nonneg (show 0 ≤ lam * x by positivity)
      nlinarith [sq_nonneg (lam * x)]
    have h2 : Real.exp (-(lam * x)) * Real.exp (lam * x) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith [Real.exp_pos (-(lam * x))]
  rw [show 8 / lam ^ 2 * (1 / ‖s * (1 - s)‖) = 8 / (lam ^ 2 * ‖s * (1 - s)‖) by
    field_simp]
  have h3 : lam ^ 2 * (‖s * (1 - s)‖ / 2) ≤ (lam * x) ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left hx2 (sq_nonneg _)
  have h4 : Real.exp (-(lam * x)) * (lam ^ 2 * (‖s * (1 - s)‖ / 2)) ≤ 2 :=
    (mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le).trans hexp
  rw [le_div_iff₀ (by positivity)]
  nlinarith [Real.exp_pos (-(lam * x))]

/-- The exponential weights are summable over the zeros. -/
theorem summable_norm_expZeroWeight {lam : ℝ} (hlam : 0 < lam) :
    Summable fun q : XiZeroCopy => ‖expZeroWeight lam (q.1 : ℂ)‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
    (summable_inv_mul_one_sub.norm.mul_left (8 / lam ^ 2))
  refine norm_expZeroWeight_le_inv hlam ?_
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  rw [abs_lt]; constructor <;> linarith

/-! ## The exponentially weighted constant-vector test -/

/-- **Exponentially weighted constant-vector positivity** on a prime set `P` at level `σ`:
`Re Σ_q ω_λ(q) (K_u(q) + K_ū(q)) ≥ 0` for every amplitude `|u| ≤ ½`. -/
def JasExpConstPositiveOn (lam : ℝ) (P : Finset Nat.Primes) (σ : ℝ) : Prop :=
  ∀ u : ℂ, ‖u‖ ≤ 1 / 2 → 0 ≤ (∑' q : XiZeroCopy, expZeroWeight lam (q.1 : ℂ) *
    (jasConstKernel P σ u (q.1 : ℂ) + jasConstKernel P σ (conj u) (q.1 : ℂ))).re

/-- On the critical line the normalized factor is the real number `1 + 2 Re(u p^{−σ−it})`. -/
theorem jasConstFactor_eq_ofReal_of_re_eq_half (σ : ℝ) (u : ℂ) (p : Nat.Primes) {s : ℂ}
    (hs : s.re = 1 / 2) :
    jasConstFactor σ u p s = ((1 + 2 * (u * cexp (-((σ : ℂ) + (s - 1 / 2)) *
      (Real.log p : ℂ))).re : ℝ) : ℂ) := by
  have hconj : conj (u * cexp (-((σ : ℂ) + (s - 1 / 2)) * (Real.log p : ℂ))) =
      conj u * cexp (-((σ : ℂ) - (s - 1 / 2)) * (Real.log p : ℂ)) := by
    rw [map_mul, ← Complex.exp_conj]
    congr 2
    have hs' : conj (s - 1 / 2) = -(s - 1 / 2) := by
      apply Complex.ext <;> simp [hs]
    simp only [map_mul, map_neg, map_add, Complex.conj_ofReal, hs']
    ring
  rw [jasConstFactor, ← hconj, add_assoc, Complex.add_conj]
  push_cast
  ring

/-- On the line the factor is at least `1 − 2|u| p^{−σ} > 0` for `|u| ≤ ½`, `σ > 0`. -/
theorem jasConstFactor_re_pos_of_re_eq_half {σ : ℝ} (hσ : 0 < σ) {u : ℂ} (hu : ‖u‖ ≤ 1 / 2)
    (p : Nat.Primes) {s : ℂ} (hs : s.re = 1 / 2) :
    0 < 1 + 2 * (u * cexp (-((σ : ℂ) + (s - 1 / 2)) * (Real.log p : ℂ))).re := by
  have hn : ‖u * cexp (-((σ : ℂ) + (s - 1 / 2)) * (Real.log p : ℂ))‖ ≤
      1 / 2 * Real.exp (-σ * Real.log p) := by
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul hu (le_of_eq ?_) (Real.exp_pos _).le (by norm_num)
    congr 1
    rw [Complex.re_mul_ofReal]
    simp [hs]
  have hlt : Real.exp (-σ * Real.log p) < 1 := by
    have := log_prime_pos p
    calc Real.exp (-σ * Real.log p) < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith)
      _ = 1 := Real.exp_zero
  have hre := Complex.abs_re_le_norm (u * cexp (-((σ : ℂ) + (s - 1 / 2)) * (Real.log p : ℂ)))
  have := (abs_le.mp (hre.trans hn)).1
  linarith

/-- On the line the kernel is a positive real number. -/
theorem jasConstKernel_eq_ofReal_pos_of_re_eq_half (P : Finset Nat.Primes) {σ : ℝ} (hσ : 0 < σ)
    {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) {s : ℂ} (hs : s.re = 1 / 2) :
    ∃ r : ℝ, 0 < r ∧ jasConstKernel P σ u s = (r : ℂ) := by
  refine ⟨∏ p ∈ P, (1 + 2 * (u * cexp (-((σ : ℂ) + (s - 1 / 2)) * (Real.log p : ℂ))).re),
    Finset.prod_pos fun p _ => jasConstFactor_re_pos_of_re_eq_half hσ hu p hs, ?_⟩
  rw [jasConstKernel, Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun p _ => jasConstFactor_eq_ofReal_of_re_eq_half σ u p hs

/-- **RH makes every exponentially weighted constant-vector test positive**, on every prime set
and at every level `σ > 0`. -/
theorem jasExpConstPositiveOn_of_riemannHypothesis (hRH : RiemannHypothesis) (lam : ℝ)
    (P : Finset Nat.Primes) {σ : ℝ} (hσ : 0 < σ) : JasExpConstPositiveOn lam P σ := by
  intro u hu
  have hcu : ‖conj u‖ ≤ 1 / 2 := by rw [Complex.norm_conj]; exact hu
  have hterm : ∀ q : XiZeroCopy, ∃ r : ℝ, 0 ≤ r ∧ expZeroWeight lam (q.1 : ℂ) *
      (jasConstKernel P σ u (q.1 : ℂ) + jasConstKernel P σ (conj u) (q.1 : ℂ)) = (r : ℂ) := by
    intro q
    have hq := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
    obtain ⟨r₁, hr₁, h₁⟩ := jasConstKernel_eq_ofReal_pos_of_re_eq_half P hσ hu hq
    obtain ⟨r₂, hr₂, h₂⟩ := jasConstKernel_eq_ofReal_pos_of_re_eq_half P hσ hcu hq
    refine ⟨Real.exp (-(lam * Real.sqrt (1 / 4 + (q.1 : ℂ).im ^ 2))) * (r₁ + r₂),
      mul_nonneg (Real.exp_pos _).le (by linarith), ?_⟩
    rw [expZeroWeight_eq_ofReal_of_re_eq_half lam hq, h₁, h₂]
    push_cast; ring
  choose r hr0 hr using hterm
  have e : (∑' q : XiZeroCopy, expZeroWeight lam (q.1 : ℂ) *
      (jasConstKernel P σ u (q.1 : ℂ) + jasConstKernel P σ (conj u) (q.1 : ℂ))) =
      ((∑' q : XiZeroCopy, r q : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr hr
  rw [e, Complex.ofReal_re]
  exact tsum_nonneg hr0

end

end RHTower
