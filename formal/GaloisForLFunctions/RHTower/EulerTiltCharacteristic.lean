import GaloisForLFunctions.RHTower.PrimeCosineDefect
import GaloisForLFunctions.HTGeometry.ArctanSinTaylor

/-!
# The parity–energy characteristic function of the Euler tilt

For independent Bernoulli occupancies with `P(B_p = 1) ∝ p^{-σ}` the parity–energy characteristic
function factors over the primes:

```text
Φ_Y(t) = E e^{i(πN - tE)} = ∏_{p ≤ Y} (1 - p^{-σ-it}) / (1 + p^{-σ}).
```

Its logarithmic modulus is the Euler sum `-∑_{p ≤ Y} p^{-σ}(1 + cos(t log p))` up to an
absolutely convergent correction.
-/

open Filter Topology Set Complex

namespace RHTower

noncomputable section

/-- The parity–energy characteristic function of the Euler tilt, as the normalized Bernoulli
expectation over occupied prime subsets. -/
def eulerTiltCharacteristic (σ t Y : ℝ) : ℂ :=
  (∑ T ∈ (Nat.primesLE ⌊Y⌋₊).powerset,
      (∏ p ∈ T, (((p : ℝ) ^ (-σ) : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((Real.pi * T.card : ℝ) - t * ∑ p ∈ T, Real.log p)))
    / ∏ p ∈ Nat.primesLE ⌊Y⌋₊, ((1 + (p : ℝ) ^ (-σ) : ℝ) : ℂ)

/-- **The characteristic function is a finite Euler product.** -/
theorem eulerTiltCharacteristic_eq (σ t Y : ℝ) :
    eulerTiltCharacteristic σ t Y
      = (∏ p ∈ Nat.primesLE ⌊Y⌋₊,
          (1 - (((p : ℝ) ^ (-σ) : ℝ) : ℂ)
            * Complex.exp (-(t * Real.log p : ℝ) * Complex.I)))
        / ∏ p ∈ Nat.primesLE ⌊Y⌋₊, ((1 + (p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [eulerTiltCharacteristic]
  congr 1
  have hterm : ∀ T ∈ (Nat.primesLE ⌊Y⌋₊).powerset,
      (∏ p ∈ T, (((p : ℝ) ^ (-σ) : ℝ) : ℂ))
          * Complex.exp (Complex.I * ((Real.pi * T.card : ℝ) - t * ∑ p ∈ T, Real.log p))
        = ∏ p ∈ T, (-((((p : ℝ) ^ (-σ) : ℝ) : ℂ)
            * Complex.exp (-(t * Real.log p : ℝ) * Complex.I))) := by
    intro T _
    have hprod : ∏ p ∈ T, (-((((p : ℝ) ^ (-σ) : ℝ) : ℂ)
          * Complex.exp (-(t * Real.log p : ℝ) * Complex.I)))
        = ((-1 : ℂ) ^ T.card * ∏ p ∈ T, (((p : ℝ) ^ (-σ) : ℝ) : ℂ))
          * ∏ p ∈ T, Complex.exp (-(t * Real.log p : ℝ) * Complex.I) := by
      rw [Finset.prod_neg, Finset.prod_mul_distrib]
      ring
    rw [hprod]
    have hexpprod : (∏ p ∈ T, Complex.exp (-(t * Real.log p : ℝ) * Complex.I))
        = Complex.exp (-(t * ∑ p ∈ T, Real.log p : ℝ) * Complex.I) := by
      rw [← Complex.exp_sum]
      congr 1
      push_cast
      rw [← Finset.sum_mul, Finset.sum_neg_distrib, ← Finset.mul_sum]
    rw [hexpprod]
    have hpar : ((-1 : ℂ)) ^ T.card = Complex.exp (Complex.I * (Real.pi * T.card : ℝ)) := by
      rw [show ((Real.pi * T.card : ℝ) : ℂ) = (T.card : ℂ) * (Real.pi : ℂ) by push_cast; ring,
        ← mul_assoc, mul_comm Complex.I (T.card : ℂ), mul_assoc, Complex.exp_nat_mul]
      rw [show Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I by ring,
        Complex.exp_pi_mul_I]
    rw [hpar]
    have hsplit : Complex.exp (Complex.I * ((Real.pi * T.card : ℝ) - t * ∑ p ∈ T, Real.log p))
        = Complex.exp (Complex.I * (Real.pi * T.card : ℝ))
          * Complex.exp (-(t * ∑ p ∈ T, Real.log p : ℝ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hsplit]
    ring
  rw [Finset.sum_congr rfl hterm]
  have hexpand := Finset.prod_add
    (fun p : ℕ => -((((p : ℝ) ^ (-σ) : ℝ) : ℂ)
      * Complex.exp (-(t * Real.log p : ℝ) * Complex.I)))
    (fun _ : ℕ => (1 : ℂ)) (Nat.primesLE ⌊Y⌋₊)
  have hone : ∀ T : Finset ℕ, (∏ _p ∈ Nat.primesLE ⌊Y⌋₊ \ T, (1 : ℂ)) = 1 :=
    fun T => Finset.prod_const_one
  have hcomm : (∏ p ∈ Nat.primesLE ⌊Y⌋₊,
      (1 - (((p : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (-(t * Real.log p : ℝ) * Complex.I)))
      = ∏ p ∈ Nat.primesLE ⌊Y⌋₊,
        (-((((p : ℝ) ^ (-σ) : ℝ) : ℂ)
          * Complex.exp (-(t * Real.log p : ℝ) * Complex.I)) + 1) :=
    Finset.prod_congr rfl fun p _ => by ring
  rw [hcomm, hexpand]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [hone T, mul_one]

/-! ## The logarithmic modulus -/

/-- The local logarithmic defect of one Euler factor. -/
theorem abs_localLog_add_le {r c : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 2) (hc : |c| ≤ 1) :
    |Real.log (1 - 2 * r * c + r ^ 2) - 2 * Real.log (1 + r) + 2 * r * (1 + c)|
      ≤ 405 * r ^ 2 := by
  have hcb := abs_le.mp hc
  have hpos : (0 : ℝ) < 1 - 2 * r * c + r ^ 2 := by nlinarith [hcb.1, hcb.2, hr0, hr]
  rcases le_or_gt r (1 / 5) with hsmall | hbig
  · -- the quadratic Taylor regime
    set x : ℝ := -(2 * r * c) + r ^ 2 with hx
    have hxabs : |x| ≤ 1 / 2 := by
      rw [hx, abs_le]
      constructor <;> nlinarith [hcb.1, hcb.2, hr0, hsmall]
    have hlogx := HTGeometry.abs_log_one_add_sub_self_le hxabs
    have hrabs : |r| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith
    have hlogr := HTGeometry.abs_log_one_add_sub_self_le hrabs
    have hval : (1 : ℝ) - 2 * r * c + r ^ 2 = 1 + x := by
      rw [hx]
      ring
    rw [hval]
    have hid : Real.log (1 + x) - 2 * Real.log (1 + r) + 2 * r * (1 + c)
        = (Real.log (1 + x) - x) - 2 * (Real.log (1 + r) - r) + r ^ 2 := by
      rw [hx]
      ring
    rw [hid]
    have hb1 := abs_le.mp hlogx
    have hb2 := abs_le.mp hlogr
    have hxle : |x| ≤ 11 / 5 * r := by
      rw [hx, abs_le]
      constructor <;> nlinarith [hcb.1, hcb.2, hr0, hsmall]
    have hxsq : x ^ 2 ≤ 5 * r ^ 2 := by
      have hsq := sq_abs x
      nlinarith [hxle, abs_nonneg x, hsq, hr0]
    rw [abs_le]
    constructor <;> nlinarith [hb1.1, hb1.2, hb2.1, hb2.2, hxsq, hr0]
  · -- the crude regime
    have hr5 : (1 : ℝ) / 5 < r := hbig
    have hlow : (1 - r) ^ 2 ≤ 1 - 2 * r * c + r ^ 2 := by nlinarith [hcb.2, hr0]
    have hup : 1 - 2 * r * c + r ^ 2 ≤ (1 + r) ^ 2 := by nlinarith [hcb.1, hr0]
    have hrle : (1 : ℝ) / 2 ≤ 1 - r + 1 / 2 := by linarith
    have hlow0 : (0 : ℝ) < 1 - r := by linarith
    have hlogup : Real.log (1 - 2 * r * c + r ^ 2) ≤ 2 * Real.log (1 + r) := by
      have h := Real.log_le_log hpos hup
      rw [show ((1 : ℝ) + r) ^ 2 = (1 + r) * (1 + r) by ring,
        Real.log_mul (by linarith) (by linarith)] at h
      linarith
    have hloglow : 2 * Real.log (1 - r) ≤ Real.log (1 - 2 * r * c + r ^ 2) := by
      have h := Real.log_le_log (by positivity) hlow
      rw [show ((1 : ℝ) - r) ^ 2 = (1 - r) * (1 - r) by ring,
        Real.log_mul (by linarith) (by linarith)] at h
      linarith
    have hlogr1 : Real.log (1 + r) ≤ r := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + r by linarith)
      linarith
    have hlogr2 : -(2 * r) ≤ Real.log (1 - r) := by
      have h : Real.log (1 - r) = -Real.log (1 / (1 - r)) := by
        rw [Real.log_div one_ne_zero (by linarith), Real.log_one]
        ring
      have h2 : Real.log (1 / (1 - r)) ≤ 1 / (1 - r) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h3 : 1 / (1 - r) - 1 ≤ 2 * r := by
        rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
        nlinarith [hr, hr0]
      linarith [h, h2, h3]
    have hbig2 : (405 : ℝ) * r ^ 2 ≥ 16 := by nlinarith [hr5, hr0]
    rw [abs_le]
    constructor <;> nlinarith [hlogup, hloglow, hlogr1, hlogr2, hcb.1, hcb.2, hr0, hr, hbig2]

private theorem normSq_one_sub_mul_exp (r θ : ℝ) :
    Complex.normSq (1 - (r : ℂ) * Complex.exp (-(θ : ℝ) * Complex.I))
      = 1 - 2 * r * Real.cos θ + r ^ 2 := by
  have hre : (Complex.exp (-(θ : ℝ) * Complex.I)).re = Real.cos θ := by
    rw [show (-(θ : ℝ) : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have him : (Complex.exp (-(θ : ℝ) * Complex.I)).im = -Real.sin θ := by
    rw [show (-(θ : ℝ) : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  have hsq : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hre, him]
  ring_nf
  nlinarith [hsq]

theorem two_mul_log_norm_eulerTiltCharacteristic {σ t Y : ℝ} (hσ : 1 ≤ σ) :
    2 * Real.log ‖eulerTiltCharacteristic σ t Y‖
      = ∑ p ∈ Nat.primesLE ⌊Y⌋₊,
        (Real.log (1 - 2 * (p : ℝ) ^ (-σ) * Real.cos (t * Real.log p) + ((p : ℝ) ^ (-σ)) ^ 2)
          - 2 * Real.log (1 + (p : ℝ) ^ (-σ))) := by
  have hrange : ∀ p ∈ Nat.primesLE ⌊Y⌋₊,
      (0 : ℝ) < (p : ℝ) ^ (-σ) ∧ (p : ℝ) ^ (-σ) ≤ 1 / 2 := by
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    refine ⟨Real.rpow_pos_of_pos hp0 _, ?_⟩
    have hle : (p : ℝ) ^ (-σ) ≤ ((p : ℝ))⁻¹ := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ (p : ℝ) by linarith)
        (show -σ ≤ -1 by linarith)
      rwa [Real.rpow_neg_one] at h
    have hinv : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ hp0 (by norm_num)]
      linarith
    linarith
  have hnormsq : ∀ p ∈ Nat.primesLE ⌊Y⌋₊,
      Complex.normSq ((1 : ℂ) - (((p : ℝ) ^ (-σ) : ℝ) : ℂ)
          * Complex.exp (-(t * Real.log p : ℝ) * Complex.I))
        = 1 - 2 * (p : ℝ) ^ (-σ) * Real.cos (t * Real.log p) + ((p : ℝ) ^ (-σ)) ^ 2 := by
    intro p _
    exact normSq_one_sub_mul_exp _ _
  have hpos : ∀ p ∈ Nat.primesLE ⌊Y⌋₊,
      (0 : ℝ) < 1 - 2 * (p : ℝ) ^ (-σ) * Real.cos (t * Real.log p) + ((p : ℝ) ^ (-σ)) ^ 2 := by
    intro p hp
    obtain ⟨hr0, hrhalf⟩ := hrange p hp
    have hcos := Real.neg_one_le_cos (t * Real.log p)
    have hcos1 := Real.cos_le_one (t * Real.log p)
    nlinarith [hr0, hrhalf, hcos, hcos1]
  have hnumne : ∀ p ∈ Nat.primesLE ⌊Y⌋₊,
      (1 : ℂ) - (((p : ℝ) ^ (-σ) : ℝ) : ℂ)
        * Complex.exp (-(t * Real.log p : ℝ) * Complex.I) ≠ 0 := by
    intro p hp hzero
    have h := hnormsq p hp
    rw [hzero, Complex.normSq_zero] at h
    exact absurd h.symm (ne_of_gt (hpos p hp))
  have hdenne : ∀ p ∈ Nat.primesLE ⌊Y⌋₊, ((1 + (p : ℝ) ^ (-σ) : ℝ) : ℂ) ≠ 0 := by
    intro p hp
    obtain ⟨hr0, _⟩ := hrange p hp
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  -- the modulus of the finite Euler product
  have hnormval : ‖eulerTiltCharacteristic σ t Y‖
      = (∏ p ∈ Nat.primesLE ⌊Y⌋₊, ‖(1 : ℂ) - (((p : ℝ) ^ (-σ) : ℝ) : ℂ)
            * Complex.exp (-(t * Real.log p : ℝ) * Complex.I)‖)
        / ∏ p ∈ Nat.primesLE ⌊Y⌋₊, (1 + (p : ℝ) ^ (-σ)) := by
    rw [eulerTiltCharacteristic_eq, norm_div, norm_prod, norm_prod]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    obtain ⟨hr0, _⟩ := hrange p hp
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hnumpos : ∀ p ∈ Nat.primesLE ⌊Y⌋₊,
      (0 : ℝ) < ‖(1 : ℂ) - (((p : ℝ) ^ (-σ) : ℝ) : ℂ)
        * Complex.exp (-(t * Real.log p : ℝ) * Complex.I)‖ := by
    intro p hp
    exact norm_pos_iff.mpr (hnumne p hp)
  have hdenpos : ∀ p ∈ Nat.primesLE ⌊Y⌋₊, (0 : ℝ) < 1 + (p : ℝ) ^ (-σ) := by
    intro p hp
    obtain ⟨hr0, _⟩ := hrange p hp
    linarith
  have hprodnum : (0 : ℝ) < ∏ p ∈ Nat.primesLE ⌊Y⌋₊,
      ‖(1 : ℂ) - (((p : ℝ) ^ (-σ) : ℝ) : ℂ)
        * Complex.exp (-(t * Real.log p : ℝ) * Complex.I)‖ :=
    Finset.prod_pos hnumpos
  have hprodden : (0 : ℝ) < ∏ p ∈ Nat.primesLE ⌊Y⌋₊, (1 + (p : ℝ) ^ (-σ)) :=
    Finset.prod_pos hdenpos
  rw [hnormval, Real.log_div (ne_of_gt hprodnum) (ne_of_gt hprodden),
    Real.log_prod (fun p hp => ne_of_gt (hnumpos p hp)),
    Real.log_prod (fun p hp => ne_of_gt (hdenpos p hp)),
    mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hsqnorm : ‖(1 : ℂ) - (((p : ℝ) ^ (-σ) : ℝ) : ℂ)
      * Complex.exp (-(t * Real.log p : ℝ) * Complex.I)‖ ^ 2
      = Complex.normSq ((1 : ℂ) - (((p : ℝ) ^ (-σ) : ℝ) : ℂ)
        * Complex.exp (-(t * Real.log p : ℝ) * Complex.I)) := Complex.sq_norm _
  have h2 : 2 * Real.log ‖(1 : ℂ) - (((p : ℝ) ^ (-σ) : ℝ) : ℂ)
      * Complex.exp (-(t * Real.log p : ℝ) * Complex.I)‖
      = Real.log (1 - 2 * (p : ℝ) ^ (-σ) * Real.cos (t * Real.log p)
        + ((p : ℝ) ^ (-σ)) ^ 2) := by
    rw [← hnormsq p hp, ← hsqnorm, Real.log_pow]
    push_cast
    ring
  rw [h2]

/-- **The logarithmic modulus is the Euler sum up to an absolutely convergent correction.** -/
theorem abs_two_log_norm_add_euler_le {σ t Y : ℝ} (hσ : 1 ≤ σ) :
    |2 * Real.log ‖eulerTiltCharacteristic σ t Y‖
        + 2 * ∑ p ∈ Nat.primesLE ⌊Y⌋₊,
          (p : ℝ) ^ (-σ) * (1 + Real.cos (t * Real.log p))|
      ≤ 405 * invSquareTailConst := by
  rw [two_mul_log_norm_eulerTiltCharacteristic hσ, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ Nat.primesLE ⌊Y⌋₊,
      |(Real.log (1 - 2 * (p : ℝ) ^ (-σ) * Real.cos (t * Real.log p) + ((p : ℝ) ^ (-σ)) ^ 2)
          - 2 * Real.log (1 + (p : ℝ) ^ (-σ)))
        + 2 * ((p : ℝ) ^ (-σ) * (1 + Real.cos (t * Real.log p)))|
        ≤ 405 * (1 / (p : ℝ) ^ (2 : ℝ)) := by
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hr0 : (0 : ℝ) < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hp0 _
    have hrle : (p : ℝ) ^ (-σ) ≤ ((p : ℝ))⁻¹ := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ (p : ℝ) by linarith)
        (show -σ ≤ -1 by linarith)
      rwa [Real.rpow_neg_one] at h
    have hinv : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ hp0 (by norm_num)]
      linarith
    have hrhalf : (p : ℝ) ^ (-σ) ≤ 1 / 2 := by linarith
    have hcos : |Real.cos (t * Real.log p)| ≤ 1 := Real.abs_cos_le_one _
    have hlocal := abs_localLog_add_le hr0 hrhalf hcos
    have hid : (Real.log (1 - 2 * (p : ℝ) ^ (-σ) * Real.cos (t * Real.log p)
          + ((p : ℝ) ^ (-σ)) ^ 2) - 2 * Real.log (1 + (p : ℝ) ^ (-σ)))
        + 2 * ((p : ℝ) ^ (-σ) * (1 + Real.cos (t * Real.log p)))
        = Real.log (1 - 2 * (p : ℝ) ^ (-σ) * Real.cos (t * Real.log p) + ((p : ℝ) ^ (-σ)) ^ 2)
          - 2 * Real.log (1 + (p : ℝ) ^ (-σ))
          + 2 * (p : ℝ) ^ (-σ) * (1 + Real.cos (t * Real.log p)) := by ring
    rw [hid]
    refine le_trans hlocal ?_
    have hsq : ((p : ℝ) ^ (-σ)) ^ 2 ≤ 1 / (p : ℝ) ^ (2 : ℝ) := by
      have hle : ((p : ℝ) ^ (-σ)) ^ 2 ≤ (((p : ℝ))⁻¹) ^ 2 := by
        have h := mul_le_mul hrle hrle hr0.le (by positivity)
        nlinarith [h, hr0]
      have hval : (((p : ℝ))⁻¹) ^ 2 = 1 / (p : ℝ) ^ (2 : ℝ) := by
        rw [one_div, ← Real.rpow_neg hp0.le, ← Real.rpow_neg_one, ← Real.rpow_natCast
          ((p : ℝ) ^ (-(1 : ℝ))) 2, ← Real.rpow_mul hp0.le]
        norm_num
      linarith [hle, hval]
    nlinarith [hsq]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsum := sum_inv_rpow_two_le (Nat.primesLE ⌊Y⌋₊)
  nlinarith [hsum]

/-! ## The Euler-edge amplitude -/

/-- The tilted prime sum `∑_{p ≤ Y} p^{-σ}`. -/
def primeRpowSum (σ Y : ℝ) : ℝ := ∑ p ∈ Nat.primesLE ⌊Y⌋₊, (p : ℝ) ^ (-σ)

theorem abs_primeRpowSum_sub_mertensS_le {δ Y : ℝ} (hδ : 0 ≤ δ) :
    |primeRpowSum (1 + δ) Y - Sieve.mertensS ⌊Y⌋₊| ≤ δ * mertensPrimeWeightSum ⌊Y⌋₊ := by
  have hdiff : primeRpowSum (1 + δ) Y - Sieve.mertensS ⌊Y⌋₊
      = ∑ p ∈ Nat.primesLE ⌊Y⌋₊, ((p : ℝ) ^ (-(1 + δ)) - ((p : ℝ))⁻¹) := by
    rw [primeRpowSum, Sieve.mertensS, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by rw [one_div]
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [← sum_primesLE_log_div_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hprime := Nat.prime_of_mem_primesLE hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hinv : (p : ℝ) ^ (-(1 : ℝ)) = ((p : ℝ))⁻¹ := Real.rpow_neg_one _
  have hfactor : (p : ℝ) ^ (-(1 + δ)) = ((p : ℝ))⁻¹ * (p : ℝ) ^ (-δ) := by
    rw [← hinv, ← Real.rpow_add hp0]
    congr 1
    ring
  have htilt : 1 - (p : ℝ) ^ (-δ) ≤ δ * Real.log p := by
    have hexp : (p : ℝ) ^ (-δ) = Real.exp (-(δ * Real.log p)) := by
      rw [Real.rpow_def_of_pos hp0]
      congr 1
      ring
    have h := Real.add_one_le_exp (-(δ * Real.log p))
    rw [hexp]
    linarith
  have htiltle : (p : ℝ) ^ (-δ) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ (p : ℝ) by linarith)
      (show -δ ≤ 0 by linarith)
    rwa [Real.rpow_zero] at h
  rw [hfactor]
  have hval : ((p : ℝ))⁻¹ * (p : ℝ) ^ (-δ) - ((p : ℝ))⁻¹
      = -(((p : ℝ))⁻¹ * (1 - (p : ℝ) ^ (-δ))) := by ring
  rw [hval, abs_neg, abs_of_nonneg (by positivity)]
  have hstep : ((p : ℝ))⁻¹ * (1 - (p : ℝ) ^ (-δ)) ≤ ((p : ℝ))⁻¹ * (δ * Real.log p) :=
    mul_le_mul_of_nonneg_left htilt (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  field_simp

theorem abs_primeRpowSum_sub_logLog_le {δ Y : ℝ} (hδ : 0 ≤ δ) (hY : Real.exp 2 ≤ Y) :
    |primeRpowSum (1 + δ) Y - Real.log (Real.log Y)|
      ≤ eulerTiltMassConst + δ * (Real.log Y + (mertensPrimeWindowBound + 1)) := by
  have hexp2 : (7 : ℝ) < Real.exp 2 := by
    have h := Real.exp_one_gt_d9
    have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [h, Real.exp_pos 1, hsq]
  have hY7 : (7 : ℝ) < Y := lt_of_lt_of_le hexp2 hY
  have hY2 : (2 : ℝ) ≤ Y := by linarith
  have hfloor2 : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (2 : ℝ) ≤ Y))
  have hfloor6 : (6 : ℝ) ≤ ((⌊Y⌋₊ : ℕ) : ℝ) := by
    have h : (6 : ℕ) ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (6 : ℝ) ≤ Y))
    exact_mod_cast h
  have hflog : (0 : ℝ) < Real.log ((⌊Y⌋₊ : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hlogone : (1 : ℝ) ≤ Real.log ((⌊Y⌋₊ : ℕ) : ℝ) := by
    have hexp1 : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ ((⌊Y⌋₊ : ℕ) : ℝ) by linarith)
    rwa [Real.log_exp] at h
  have hsum := abs_primeRpowSum_sub_mertensS_le (δ := δ) (Y := Y) hδ
  have hmertens := Sieve.abs_mertensS_sub_logLog_sub_const_le hfloor2
  have hfloorlog := abs_logLog_floor_sub_le hY
  have hweight := abs_mertensPrimeWeightSum_floor_sub_log_le hY2
  have hdiv : (2 * Sieve.mertensFirstConst + 1 / 2) / Real.log ((⌊Y⌋₊ : ℕ) : ℝ)
      ≤ 2 * Sieve.mertensFirstConst + 1 / 2 := by
    have hnum : 0 ≤ 2 * Sieve.mertensFirstConst + 1 / 2 := by
      have := Sieve.mertensFirstConst_nonneg
      linarith
    rw [div_le_iff₀ hflog]
    nlinarith [hnum, hlogone]
  have hb1 := abs_le.mp hsum
  have hb2 := abs_le.mp hmertens
  have hb3 := abs_le.mp hfloorlog
  have hb4 := abs_le.mp hweight
  have hmabs : Sieve.meisselMertensConst ≤ |Sieve.meisselMertensConst| := le_abs_self _
  have hmabs' : -|Sieve.meisselMertensConst| ≤ Sieve.meisselMertensConst := neg_abs_le _
  have hinvc : 0 ≤ invSquareTailConst := by
    rw [invSquareTailConst]
    exact tsum_nonneg invSquareTail_nonneg
  rw [eulerTiltMassConst, abs_le]
  constructor
  · nlinarith [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2, hb4.1, hb4.2, hdiv, hmabs, hmabs',
      hδ, hinvc]
  · nlinarith [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2, hb4.1, hb4.2, hdiv, hmabs, hmabs',
      hδ, hinvc]

/-- **(14) The Euler-edge amplitude.**  The logarithmic modulus of the characteristic function is
`-2 log log Y` up to the oscillatory defect and absolutely convergent corrections. -/
theorem abs_log_norm_add_two_logLog_le {δ t Y : ℝ} (hδ : 0 ≤ δ) (hY : Real.exp 2 ≤ Y) :
    |Real.log ‖eulerTiltCharacteristic (1 + δ) t Y‖ + 2 * Real.log (Real.log Y)|
      ≤ 405 / 2 * invSquareTailConst + |primeCosineDefect (1 + δ) t Y|
        + 2 * (eulerTiltMassConst + δ * (Real.log Y + (mertensPrimeWindowBound + 1))) := by
  have hσ : (1 : ℝ) ≤ 1 + δ := by linarith
  have hmain := abs_two_log_norm_add_euler_le (σ := 1 + δ) (t := t) (Y := Y) hσ
  have hsplit : ∑ p ∈ Nat.primesLE ⌊Y⌋₊,
      (p : ℝ) ^ (-(1 + δ)) * (1 + Real.cos (t * Real.log p))
      = 2 * primeRpowSum (1 + δ) Y + primeCosineDefect (1 + δ) t Y := by
    rw [primeRpowSum, primeCosineDefect, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => by ring
  rw [hsplit] at hmain
  have hlog := abs_primeRpowSum_sub_logLog_le (δ := δ) (Y := Y) hδ hY
  have hb1 := abs_le.mp hmain
  have hb2 := abs_le.mp hlog
  have hdefect : |primeCosineDefect (1 + δ) t Y| = |primeCosineDefect (1 + δ) t Y| := rfl
  have hb3 := abs_le.mp (le_refl |primeCosineDefect (1 + δ) t Y|)
  have habs1 : primeCosineDefect (1 + δ) t Y ≤ |primeCosineDefect (1 + δ) t Y| := le_abs_self _
  have habs2 : -|primeCosineDefect (1 + δ) t Y| ≤ primeCosineDefect (1 + δ) t Y := neg_abs_le _
  rw [abs_le]
  constructor
  · linarith [hb1.1, hb1.2, hb2.1, hb2.2, habs1, habs2]
  · linarith [hb1.1, hb1.2, hb2.1, hb2.2, habs1, habs2]

end

end RHTower
