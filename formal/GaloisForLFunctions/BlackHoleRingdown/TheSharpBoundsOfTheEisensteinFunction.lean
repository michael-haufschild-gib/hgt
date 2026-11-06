import GaloisForLFunctions.BlackHoleRingdown.TheSharpDecayOfTheBesselKernel
import GaloisForLFunctions.BlackHoleRingdown.TheRingdownExpansion
import GaloisForLFunctions.RHTower.XiSliceCircleDecay

/-!
# Sharp bounds for the Eisenstein function

The sharp decay of the Bessel kernel makes the Whittaker tail and its jets `O((1+|Im u|)^M e^{-π|Im u|/2})`
on vertical strips: summing the Fourier modes costs only a power of `1+|Im u|`. On the other side,
`ξ(s) = O((1+|Im s|)^N e^{-π|Im s|/4})` on vertical strips. Against these, the only remaining exponential
in `E(u; x, Y)` is `e^{-π|Im u|/2} ‖1/ξ(1+2u)‖`, and on `Re u = 0` this is polynomially bounded.

So `E(iξ; x, Y)` and all its jets grow at most polynomially in `ξ`. This is what lets a wave packet have any
rapidly decreasing amplitude, in place of a Gaussian.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

/-! ### Summing the Fourier modes -/

theorem summable_inv_sq_succ : Summable fun N : ℕ => 1 / ((N : ℝ) + 1) ^ 2 := by
  have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have h' := (summable_nat_add_iff 1).mpr h
  refine h'.congr fun N => ?_
  push_cast
  rfl

/-- The constant `∑ 1/(N+1)²`. -/
def inverseSquareSum : ℝ := ∑' N : ℕ, 1 / ((N : ℝ) + 1) ^ 2

theorem inverseSquareSum_nonneg : 0 ≤ inverseSquareSum :=
  tsum_nonneg fun _ => by positivity

theorem pow_mul_exp_neg_le (d : ℕ) {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ((N : ℝ) + 1) ^ d * Real.exp (-(((N : ℝ) + 1) * a)) ≤
      ((d + 2).factorial : ℝ) * (1 / a) ^ (d + 2) * (1 / ((N : ℝ) + 1) ^ 2) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set z := ((N : ℝ) + 1) * a with hz
  have hz0 : 0 < z := by positivity
  have h := Real.pow_div_factorial_le_exp z hz0.le (d + 2)
  have hF : (0 : ℝ) < ((d + 2).factorial : ℝ) := by exact_mod_cast (d + 2).factorial_pos
  rw [div_le_iff₀ hF] at h
  have hE : Real.exp (-z) * z ^ (d + 2) ≤ ((d + 2).factorial : ℝ) := by
    calc Real.exp (-z) * z ^ (d + 2) ≤ Real.exp (-z) * (Real.exp z * ((d + 2).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = ((d + 2).factorial : ℝ) := by
          rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have hid : ((N : ℝ) + 1) ^ d * Real.exp (-z) =
      (Real.exp (-z) * z ^ (d + 2)) * ((1 / a) ^ (d + 2) * (1 / ((N : ℝ) + 1) ^ 2)) := by
    rw [hz, mul_pow, one_div, inv_pow]
    field_simp
    ring
  rw [hid, mul_assoc ((d + 2).factorial : ℝ)]
  exact mul_le_mul_of_nonneg_right hE (by positivity)

theorem summable_pow_mul_exp_neg (d : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable fun N : ℕ => ((N : ℝ) + 1) ^ d * Real.exp (-(((N : ℝ) + 1) * a)) :=
  Summable.of_nonneg_of_le (fun _ => by positivity) (pow_mul_exp_neg_le d ha)
    (summable_inv_sq_succ.mul_left _)

/-- Summing `(N+1)^d e^{-(N+1)a}` costs `a^{-(d+2)}`. -/
theorem tsum_pow_mul_exp_neg_le (d : ℕ) {a : ℝ} (ha : 0 < a) :
    ∑' N : ℕ, ((N : ℝ) + 1) ^ d * Real.exp (-(((N : ℝ) + 1) * a)) ≤
      ((d + 2).factorial : ℝ) * (1 / a) ^ (d + 2) * inverseSquareSum := by
  have hs := summable_inv_sq_succ.mul_left (((d + 2).factorial : ℝ) * (1 / a) ^ (d + 2))
  refine (Summable.tsum_le_tsum (pow_mul_exp_neg_le d ha) (summable_pow_mul_exp_neg d ha) hs).trans
    (le_of_eq ?_)
  rw [tsum_mul_left, inverseSquareSum]

/-! ### The Bessel kernel on a window -/

/-- **The sharp bound on a height window.** -/
theorem exists_norm_bessel_window_sharp {Y₀ : ℝ} (hY₀ : 0 < Y₀) (R : ℝ) :
    ∃ (C : ℝ) (B : ℕ), 0 ≤ C ∧ ∀ (Y : ℝ) (ν : ℂ) (N : ℕ), Y ∈ Icc (Y₀ / 2) (2 * Y₀) → |ν.re| ≤ R →
      ‖modifiedBesselKOrder ((d4BMPositiveFourierScale N : ℝ) * Y) ν‖ ≤
        C * (1 + |ν.im|) ^ B * Real.exp (-(((N : ℝ) + 1) * (Y₀ / (1 + |ν.im|)))) *
          Real.exp (-(Real.pi * |ν.im| / 2)) := by
  obtain ⟨C₀, B, hC₀, h⟩ := exists_norm_modifiedBesselKOrder_sharp R
  have hpi := Real.pi_pos
  refine ⟨C₀ * (1 / (Real.pi * Y₀)) ^ B, B, by positivity, fun Y ν N hY hν => ?_⟩
  have hc : (d4BMPositiveFourierScale N : ℝ) = 2 * Real.pi * ((N : ℝ) + 1) := rfl
  set T := |ν.im| with hT
  have hT0 : 0 ≤ T := abs_nonneg _
  have hT1 : 0 < 1 + T := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  set x := (d4BMPositiveFourierScale N : ℝ) * Y with hx
  have hxl : Real.pi * ((N : ℝ) + 1) * Y₀ ≤ x := by
    rw [hx, hc]
    calc Real.pi * ((N : ℝ) + 1) * Y₀ = 2 * Real.pi * ((N : ℝ) + 1) * (Y₀ / 2) := by ring
      _ ≤ 2 * Real.pi * ((N : ℝ) + 1) * Y := mul_le_mul_of_nonneg_left hY.1 (by positivity)
  have hbase : Real.pi * Y₀ ≤ x := by
    refine le_trans ?_ hxl
    have : 0 ≤ Real.pi * Y₀ := by positivity
    nlinarith
  have hbase0 : 0 < Real.pi * Y₀ := by positivity
  have hx0 : 0 < x := lt_of_lt_of_le hbase0 hbase
  have hratio : (1 + T) / x ≤ (1 + T) * (1 / (Real.pi * Y₀)) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hbase0 hbase) hT1.le
  have hpow : ((1 + T) / x) ^ B ≤ (1 + T) ^ B * (1 / (Real.pi * Y₀)) ^ B := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hratio B
  have hexp : Real.exp (-(x / (Real.pi * (1 + T)))) ≤
      Real.exp (-(((N : ℝ) + 1) * (Y₀ / (1 + T)))) := by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    have hd : 0 < Real.pi * (1 + T) := by positivity
    rw [le_div_iff₀ hd]
    calc ((N : ℝ) + 1) * (Y₀ / (1 + T)) * (Real.pi * (1 + T)) = Real.pi * ((N : ℝ) + 1) * Y₀ := by
          field_simp
      _ ≤ x := hxl
  have hmain := h x ν hx0 hν
  refine hmain.trans ?_
  have hE1 := Real.exp_pos (-(x / (Real.pi * (1 + T))))
  have hE2 := Real.exp_pos (-(Real.pi * T / 2))
  calc C₀ * ((1 + T) / x) ^ B * Real.exp (-(x / (Real.pi * (1 + T)))) * Real.exp (-(Real.pi * T / 2))
      ≤ C₀ * ((1 + T) ^ B * (1 / (Real.pi * Y₀)) ^ B) *
          Real.exp (-(((N : ℝ) + 1) * (Y₀ / (1 + T)))) * Real.exp (-(Real.pi * T / 2)) := by
        gcongr
    _ = _ := by ring

/-! ### The Whittaker functions at the sharp scale -/

theorem norm_firstJet_le_of_bessel {Y₀ Y : ℝ} (hY₀ : 0 < Y₀) (hY : Y ∈ Icc (Y₀ / 2) (2 * Y₀))
    {ν : ℂ} {b : ℝ} (N : ℕ)
    (h0 : ‖modifiedBesselKOrder ((d4BMPositiveFourierScale N : ℝ) * Y) ν‖ ≤ b)
    (h1 : ‖modifiedBesselKOrder ((d4BMPositiveFourierScale N : ℝ) * Y) (ν + 1)‖ ≤ b)
    (h2 : ‖modifiedBesselKOrder ((d4BMPositiveFourierScale N : ℝ) * Y) (ν - 1)‖ ≤ b) :
    ‖d4BMWhittakerP0FirstJet (d4BMPositiveFourierScale N) ν Y‖ ≤
      (1 / (2 * Real.sqrt (Y₀ / 2)) + Real.sqrt (2 * Y₀) * (2 * Real.pi)) * (((N : ℝ) + 1) * b) := by
  have hb : 0 ≤ b := (norm_nonneg _).trans h0
  have hc : ‖((d4BMPositiveFourierScale N : ℝ) : ℂ)‖ = 2 * Real.pi * ((N : ℝ) + 1) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (d4BMPositiveFourierScale N).2.le]
    rfl
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hinv : ‖((1 / (2 * Real.sqrt Y) : ℝ) : ℂ)‖ ≤ 1 / (2 * Real.sqrt (Y₀ / 2)) := by
    have hYpos := window_pos hY₀ hY
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact window_inv_sqrt_le hY₀ hY
  have hsq : ‖(Real.sqrt Y : ℂ)‖ ≤ Real.sqrt (2 * Y₀) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact window_sqrt_le hY
  rw [d4BMWhittakerP0FirstJet]
  refine (norm_add_le _ _).trans ?_
  have hA : ‖((1 / (2 * Real.sqrt Y) : ℝ) : ℂ) *
        modifiedBesselKOrder ((d4BMPositiveFourierScale N : ℝ) * Y) ν‖ ≤
      1 / (2 * Real.sqrt (Y₀ / 2)) * (((N : ℝ) + 1) * b) := by
    rw [norm_mul]
    refine mul_le_mul hinv ?_ (norm_nonneg _) (by positivity)
    exact h0.trans (by nlinarith)
  have hB : ‖(Real.sqrt Y : ℂ) * ((d4BMPositiveFourierScale N : ℝ) : ℂ) * (-(1 / 2 : ℂ)) *
        (modifiedBesselKOrder ((d4BMPositiveFourierScale N : ℝ) * Y) (ν + 1) +
          modifiedBesselKOrder ((d4BMPositiveFourierScale N : ℝ) * Y) (ν - 1))‖ ≤
      Real.sqrt (2 * Y₀) * (2 * Real.pi) * (((N : ℝ) + 1) * b) := by
    rw [norm_mul, norm_mul, norm_mul, hc, norm_neg]
    have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [hhalf]
    have hsum : ‖modifiedBesselKOrder ((d4BMPositiveFourierScale N : ℝ) * Y) (ν + 1) +
        modifiedBesselKOrder ((d4BMPositiveFourierScale N : ℝ) * Y) (ν - 1)‖ ≤ 2 * b :=
      (norm_add_le _ _).trans (by linarith)
    have hpre : ‖(Real.sqrt Y : ℂ)‖ * (2 * Real.pi * ((N : ℝ) + 1)) * (1 / 2) ≤
        Real.sqrt (2 * Y₀) * (2 * Real.pi * ((N : ℝ) + 1)) * (1 / 2) := by
      gcongr
    calc _ ≤ Real.sqrt (2 * Y₀) * (2 * Real.pi * ((N : ℝ) + 1)) * (1 / 2) * (2 * b) :=
          mul_le_mul hpre hsum (norm_nonneg _) (by positivity)
      _ = _ := by ring
  refine (add_le_add hA hB).trans (le_of_eq ?_)
  ring

/-- A family of modes at the sharp scale sums to a tail at the sharp scale. -/
theorem norm_tsum_modeCoefficient_le_sharp {Y₀ R : ℝ} (hY₀ : 0 < Y₀) {K C₁ : ℝ} {B₁ : ℕ} (hK : 0 ≤ K)
    (hC₁ : 0 ≤ C₁) {f : ℕ → ℂ} {u : ℂ} (hu : |u.re| ≤ R)
    (hf : ∀ N : ℕ, ‖f N‖ ≤ K * ((N : ℝ) + 1) ^ 2 * (C₁ * (1 + |u.im|) ^ B₁ *
      Real.exp (-(((N : ℝ) + 1) * (Y₀ / (1 + |u.im|)))) * Real.exp (-(Real.pi * |u.im| / 2)))) :
    ‖∑' N : ℕ, modeCoefficient u N * f N‖ ≤
      K * C₁ * (((⌈3 * R + 1⌉₊ + 2 + 2).factorial : ℝ) * (1 / Y₀) ^ (⌈3 * R + 1⌉₊ + 2 + 2) *
        inverseSquareSum) * (1 + |u.im|) ^ (B₁ + (⌈3 * R + 1⌉₊ + 2 + 2)) *
          Real.exp (-(Real.pi * |u.im| / 2)) := by
  set T := |u.im| with hT
  have hT0 : 0 ≤ T := abs_nonneg _
  have hT1 : 0 < 1 + T := by linarith
  set e := ⌈3 * R + 1⌉₊ with he
  set a := Y₀ / (1 + T) with ha
  have ha0 : 0 < a := by positivity
  set P := K * C₁ * (1 + T) ^ B₁ * Real.exp (-(Real.pi * T / 2)) with hP
  have hP0 : 0 ≤ P := by positivity
  have hsum := (summable_pow_mul_exp_neg (e + 2) ha0).mul_left P
  have hbound : ∀ N : ℕ, ‖modeCoefficient u N * f N‖ ≤
      P * (((N : ℝ) + 1) ^ (e + 2) * Real.exp (-(((N : ℝ) + 1) * a))) := by
    intro N
    rw [norm_mul]
    have h1 := norm_modeCoefficient_le hu N
    calc ‖modeCoefficient u N‖ * ‖f N‖
        ≤ ((N : ℝ) + 1) ^ e * (K * ((N : ℝ) + 1) ^ 2 * (C₁ * (1 + T) ^ B₁ *
            Real.exp (-(((N : ℝ) + 1) * a)) * Real.exp (-(Real.pi * T / 2)))) :=
          mul_le_mul h1 (hf N) (norm_nonneg _) (by positivity)
      _ = _ := by
          rw [hP, pow_add]
          ring
  refine (tsum_of_norm_bounded hsum.hasSum hbound).trans ?_
  have htsum := tsum_pow_mul_exp_neg_le (e + 2) ha0
  have hinva : 1 / a = (1 + T) * (1 / Y₀) := by
    rw [ha]
    field_simp
  have hS := inverseSquareSum_nonneg
  rw [hinva, mul_pow] at htsum
  rw [tsum_mul_left]
  calc P * ∑' N : ℕ, ((N : ℝ) + 1) ^ (e + 2) * Real.exp (-(((N : ℝ) + 1) * a))
      ≤ P * (((e + 2 + 2).factorial : ℝ) * ((1 + T) ^ (e + 2 + 2) * (1 / Y₀) ^ (e + 2 + 2)) *
          inverseSquareSum) := mul_le_mul_of_nonneg_left htsum hP0
    _ = _ := by
        rw [hP, pow_add (1 + T) B₁]
        ring

/-- The sharp scale of the `N`-th mode. -/
def sharpScale (C₁ : ℝ) (B₁ : ℕ) (Y₀ T : ℝ) (N : ℕ) : ℝ :=
  C₁ * (1 + T) ^ B₁ * Real.exp (-(((N : ℝ) + 1) * (Y₀ / (1 + T)))) * Real.exp (-(Real.pi * T / 2))

theorem sharpScale_nonneg {C₁ : ℝ} (hC₁ : 0 ≤ C₁) (B₁ : ℕ) (Y₀ : ℝ) {T : ℝ} (hT : 0 ≤ T) (N : ℕ) :
    0 ≤ sharpScale C₁ B₁ Y₀ T N := by
  unfold sharpScale
  positivity

/-- Lower powers of `N+1` are absorbed by the square. -/
theorem mul_le_mul_sq_succ {c b : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b) (N : ℕ) {k : ℕ} (hk : k ≤ 2) :
    c * (((N : ℝ) + 1) ^ k * b) ≤ c * ((N : ℝ) + 1) ^ 2 * b := by
  have h1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have h2 : ((N : ℝ) + 1) ^ k ≤ ((N : ℝ) + 1) ^ 2 := pow_le_pow_right₀ h1 hk
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hb) hc

section TailFamily

variable {Y₀ R C₁ : ℝ} {B₁ : ℕ} (hY₀ : 0 < Y₀) (hC₁ : 0 ≤ C₁)
  (hB : ∀ (Y : ℝ) (ν : ℂ) (N : ℕ), Y ∈ Icc (Y₀ / 2) (2 * Y₀) → |ν.re| ≤ R + 1 →
    ‖modifiedBesselKOrder ((d4BMPositiveFourierScale N : ℝ) * Y) ν‖ ≤
      sharpScale C₁ B₁ Y₀ |ν.im| N)
  {u : ℂ} (negative : Bool) (x : ℝ) {Y : ℝ} (hu : |u.re| ≤ R) (hY : Y ∈ Icc (Y₀ / 2) (2 * Y₀))

/-- The constant of the sum over modes. -/
def tailSum (Y₀ R : ℝ) : ℝ :=
  ((⌈3 * R + 1⌉₊ + 2 + 2).factorial : ℝ) * (1 / Y₀) ^ (⌈3 * R + 1⌉₊ + 2 + 2) * inverseSquareSum

/-- The exponent of the sum over modes. -/
def tailPower (R : ℝ) (B₁ : ℕ) : ℕ := B₁ + (⌈3 * R + 1⌉₊ + 2 + 2)

include hY₀ hC₁ hB hu hY

theorem norm_mode_sharp (N : ℕ) :
    ‖d4BMSignedWhittakerMode negative N u x Y‖ ≤
      Real.sqrt (2 * Y₀) * sharpScale C₁ B₁ Y₀ |u.im| N := by
  have hsqrt : ‖((Real.sqrt Y : ℝ) : ℂ)‖ ≤ Real.sqrt (2 * Y₀) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact window_sqrt_le hY
  rw [d4BMSignedWhittakerMode, norm_mul, norm_fourierPhase, one_mul, d4BMWhittakerP0, norm_mul]
  exact mul_le_mul hsqrt (hB Y u N hY (by linarith)) (norm_nonneg _) (Real.sqrt_nonneg _)

theorem norm_tail_sharp :
    ‖weightedTail u negative x Y‖ ≤ Real.sqrt (2 * Y₀) * C₁ * tailSum Y₀ R * (1 + |u.im|) ^ tailPower R B₁ *
      Real.exp (-(Real.pi * |u.im| / 2)) :=
  norm_tsum_modeCoefficient_le_sharp hY₀ (Real.sqrt_nonneg _) hC₁ hu fun N => by
    have hb := sharpScale_nonneg hC₁ B₁ Y₀ (abs_nonneg u.im) N
    have h := norm_mode_sharp hY₀ hC₁ hB negative x hu hY N
    have hw := mul_le_mul_sq_succ (Real.sqrt_nonneg (2 * Y₀)) hb N (k := 0) (by norm_num)
    rw [pow_zero, one_mul] at hw
    exact h.trans hw

theorem norm_tailX_sharp :
    ‖weightedTailX u negative x Y‖ ≤ (2 * Real.pi * Real.sqrt (2 * Y₀)) * C₁ * tailSum Y₀ R *
      (1 + |u.im|) ^ tailPower R B₁ * Real.exp (-(Real.pi * |u.im| / 2)) :=
  norm_tsum_modeCoefficient_le_sharp hY₀ (by positivity) hC₁ hu fun N => by
    have hb := sharpScale_nonneg hC₁ B₁ Y₀ (abs_nonneg u.im) N
    rw [d4BMSignedWhittakerModeHorizontalFirstJet, norm_mul, norm_signedFourierRate]
    have h := mul_le_mul_of_nonneg_left (norm_mode_sharp hY₀ hC₁ hB negative x hu hY N)
      (by positivity : 0 ≤ 2 * Real.pi * ((N : ℝ) + 1))
    refine h.trans ?_
    have hw := mul_le_mul_sq_succ (by positivity : 0 ≤ 2 * Real.pi * Real.sqrt (2 * Y₀)) hb N
      (k := 1) (by norm_num)
    rw [pow_one] at hw
    refine le_trans (le_of_eq ?_) hw
    ring

theorem norm_tailXX_sharp :
    ‖weightedTailXX u negative x Y‖ ≤ ((2 * Real.pi) ^ 2 * Real.sqrt (2 * Y₀)) * C₁ * tailSum Y₀ R *
      (1 + |u.im|) ^ tailPower R B₁ * Real.exp (-(Real.pi * |u.im| / 2)) :=
  norm_tsum_modeCoefficient_le_sharp hY₀ (by positivity) hC₁ hu fun N => by
    have hb := sharpScale_nonneg hC₁ B₁ Y₀ (abs_nonneg u.im) N
    rw [d4BMSignedWhittakerModeHorizontalSecondJet, norm_mul, norm_pow, norm_signedFourierRate]
    have h := mul_le_mul_of_nonneg_left (norm_mode_sharp hY₀ hC₁ hB negative x hu hY N)
      (by positivity : 0 ≤ (2 * Real.pi * ((N : ℝ) + 1)) ^ 2)
    refine h.trans (le_of_eq ?_)
    ring

theorem norm_tailY_sharp :
    ‖weightedTailY u negative x Y‖ ≤
      (1 / (2 * Real.sqrt (Y₀ / 2)) + Real.sqrt (2 * Y₀) * (2 * Real.pi)) * C₁ * tailSum Y₀ R *
        (1 + |u.im|) ^ tailPower R B₁ * Real.exp (-(Real.pi * |u.im| / 2)) :=
  norm_tsum_modeCoefficient_le_sharp hY₀ (by positivity) hC₁ hu fun N => by
    have hb := sharpScale_nonneg hC₁ B₁ Y₀ (abs_nonneg u.im) N
    rw [d4BMSignedWhittakerModeVerticalFirstJet, norm_mul, norm_fourierPhase, one_mul]
    have hre0 : |u.re| ≤ R + 1 := by linarith
    have hre1 : |(u + 1).re| ≤ R + 1 := by
      have h1 : (u + 1).re = u.re + 1 := by simp
      rw [h1]
      have := abs_add_le u.re 1
      rw [abs_one] at this
      linarith
    have hre2 : |(u - 1).re| ≤ R + 1 := by
      have h1 : (u - 1).re = u.re - 1 := by simp
      rw [h1]
      have := abs_sub u.re 1
      rw [abs_one] at this
      linarith
    have him1 : (u + 1).im = u.im := by simp
    have him2 : (u - 1).im = u.im := by simp
    have h0 := hB Y u N hY hre0
    have h1 := hB Y (u + 1) N hY hre1
    have h2 := hB Y (u - 1) N hY hre2
    rw [him1] at h1
    rw [him2] at h2
    have hJ := norm_firstJet_le_of_bessel hY₀ hY N h0 h1 h2
    refine hJ.trans ?_
    have hw := mul_le_mul_sq_succ
      (by positivity : 0 ≤ 1 / (2 * Real.sqrt (Y₀ / 2)) + Real.sqrt (2 * Y₀) * (2 * Real.pi)) hb N
      (k := 1) (by norm_num)
    rwa [pow_one] at hw

end TailFamily

/-- `∂_Y²` of a tail from the eigen-equation, at any scale. -/
theorem norm_weightedTailYY_le_of {Y₀ Y R b : ℝ} (hY₀ : 0 < Y₀) (hY : Y ∈ Icc (Y₀ / 2) (2 * Y₀))
    {u : ℂ} (hu : |u.re| ≤ R) (negative : Bool) (x : ℝ) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hT : ‖weightedTail u negative x Y‖ ≤ b) (hXX : ‖weightedTailXX u negative x Y‖ ≤ b) :
    ‖weightedTailYY u negative x Y‖ ≤
      (((R + 1) ^ 2 + 1 / 4) * (4 / Y₀ ^ 2) + 1) * (1 + |u.im|) ^ 2 * b := by
  have hYpos := window_pos hY₀ hY
  set T := |u.im| with hTdef
  have hT0 : 0 ≤ T := abs_nonneg _
  have hp1 : 1 ≤ 1 + T := by linarith
  have hsq1 : (1 : ℝ) ≤ (1 + T) ^ 2 := one_le_pow₀ hp1
  rw [weightedTailYY_eq u negative x hYpos]
  refine (norm_sub_le _ _).trans ?_
  have hYsq : 1 / Y ^ 2 ≤ 4 / Y₀ ^ 2 := window_inv_sq_le hY₀ hY
  have hn : ‖u‖ ≤ (R + 1) * (1 + T) := by
    refine (Complex.norm_le_abs_re_add_abs_im u).trans ?_
    nlinarith
  have hunorm : ‖u ^ 2 - 1 / 4‖ ≤ ((R + 1) ^ 2 + 1 / 4) * (1 + T) ^ 2 := by
    refine (norm_sub_le _ _).trans ?_
    have hq : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
    have hsq : ‖u‖ ^ 2 ≤ ((R + 1) * (1 + T)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    rw [norm_pow, hq]
    rw [mul_pow] at hsq
    nlinarith
  have hq : ‖(u ^ 2 - 1 / 4) * weightedTail u negative x Y / (Y : ℂ) ^ 2‖ ≤
      ((R + 1) ^ 2 + 1 / 4) * (1 + T) ^ 2 * b * (4 / Y₀ ^ 2) := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hYpos,
      div_eq_mul_one_div]
    exact mul_le_mul (mul_le_mul hunorm hT (norm_nonneg _) (by positivity)) hYsq (by positivity)
      (by positivity)
  have hX2 : ‖weightedTailXX u negative x Y‖ ≤ (1 + T) ^ 2 * b :=
    hXX.trans (le_mul_of_one_le_left hb hsq1)
  refine (add_le_add hq hX2).trans (le_of_eq ?_)
  ring

/-- **Sharp bounds for the tail and its jets** on vertical strips. -/
theorem exists_weightedTail_jets_le_sharp {Y₀ R : ℝ} (hY₀ : 0 < Y₀) (hR : 0 ≤ R) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ (u : ℂ) (negative : Bool) (x Y : ℝ), |u.re| ≤ R →
      Y ∈ Icc (Y₀ / 2) (2 * Y₀) →
      ‖weightedTail u negative x Y‖ ≤
          C * (1 + |u.im|) ^ M * Real.exp (-(Real.pi * |u.im| / 2)) ∧
        ‖weightedTailX u negative x Y‖ ≤
          C * (1 + |u.im|) ^ M * Real.exp (-(Real.pi * |u.im| / 2)) ∧
        ‖weightedTailXX u negative x Y‖ ≤
          C * (1 + |u.im|) ^ M * Real.exp (-(Real.pi * |u.im| / 2)) ∧
        ‖weightedTailY u negative x Y‖ ≤
          C * (1 + |u.im|) ^ M * Real.exp (-(Real.pi * |u.im| / 2)) ∧
        ‖weightedTailYY u negative x Y‖ ≤
          C * (1 + |u.im|) ^ M * Real.exp (-(Real.pi * |u.im| / 2)) := by
  obtain ⟨C₁, B₁, hC₁, hB⟩ := exists_norm_bessel_window_sharp hY₀ (R + 1)
  have hB' : ∀ (Y : ℝ) (ν : ℂ) (N : ℕ), Y ∈ Icc (Y₀ / 2) (2 * Y₀) → |ν.re| ≤ R + 1 →
      ‖modifiedBesselKOrder ((d4BMPositiveFourierScale N : ℝ) * Y) ν‖ ≤
        sharpScale C₁ B₁ Y₀ |ν.im| N := hB
  have hS : 0 ≤ tailSum Y₀ R := by
    unfold tailSum
    exact mul_nonneg (by positivity) inverseSquareSum_nonneg
  set K₀ := Real.sqrt (2 * Y₀) with hK₀
  set J := 1 / (2 * Real.sqrt (Y₀ / 2)) + K₀ * (2 * Real.pi) with hJ
  have hK₀0 : 0 ≤ K₀ := Real.sqrt_nonneg _
  have hpi := Real.pi_pos
  have hJ0 : 0 ≤ J := by positivity
  set K := K₀ + 2 * Real.pi * K₀ + (2 * Real.pi) ^ 2 * K₀ + J with hK
  have hX1 : 0 ≤ 2 * Real.pi * K₀ := by positivity
  have hX2 : 0 ≤ (2 * Real.pi) ^ 2 * K₀ := by positivity
  have hK0 : 0 ≤ K := by positivity
  set E := ((R + 1) ^ 2 + 1 / 4) * (4 / Y₀ ^ 2) + 1 with hE
  have hE0 : 0 ≤ E := by positivity
  set W := K * C₁ * tailSum Y₀ R with hW
  have hW0 : 0 ≤ W := by positivity
  refine ⟨(1 + E) * W, tailPower R B₁ + 2, by positivity, fun u negative x Y hu hY => ?_⟩
  set T := |u.im| with hT
  have hT0 : 0 ≤ T := abs_nonneg _
  have hp1 : 1 ≤ 1 + T := by linarith
  set G := Real.exp (-(Real.pi * T / 2)) with hG
  have hG0 : 0 < G := Real.exp_pos _
  set p := (1 + T) ^ tailPower R B₁ with hp
  have hp0 : 0 ≤ p := by positivity
  have hb : ∀ K' : ℝ, 0 ≤ K' → K' ≤ K → K' * C₁ * tailSum Y₀ R * p * G ≤ W * p * G := by
    intro K' _ hK'
    rw [hW]
    gcongr
  have hstep : W * p * G ≤ (1 + E) * W * (1 + T) ^ (tailPower R B₁ + 2) * G := by
    have h1 : p ≤ (1 + T) ^ (tailPower R B₁ + 2) := pow_le_pow_right₀ hp1 (by omega)
    have h2 : W ≤ (1 + E) * W := le_mul_of_one_le_left hW0 (by linarith)
    gcongr
  have ht0 := (norm_tail_sharp hY₀ hC₁ hB' negative x hu hY).trans (hb K₀ hK₀0 (by
    rw [hK]; linarith))
  have ht1 := (norm_tailX_sharp hY₀ hC₁ hB' negative x hu hY).trans (hb _ hX1 (by
    rw [hK]; linarith))
  have ht2 := (norm_tailXX_sharp hY₀ hC₁ hB' negative x hu hY).trans (hb _ hX2 (by
    rw [hK]; linarith))
  have ht3 := (norm_tailY_sharp hY₀ hC₁ hB' negative x hu hY).trans (hb J hJ0 (by
    rw [hK]; linarith))
  refine ⟨ht0.trans hstep, ht1.trans hstep, ht2.trans hstep, ht3.trans hstep, ?_⟩
  have hWG : 0 ≤ W * p * G := by positivity
  have hYY := norm_weightedTailYY_le_of hY₀ hY hu negative x hWG hR ht0 ht2
  refine hYY.trans ?_
  rw [← hE, ← hT]
  have hpw : (1 + T) ^ (tailPower R B₁ + 2) = p * (1 + T) ^ 2 := pow_add _ _ _
  rw [hpw]
  have hsq : 0 ≤ (1 + T) ^ 2 * (W * p * G) := by positivity
  calc E * (1 + T) ^ 2 * (W * p * G) ≤ (1 + E) * ((1 + T) ^ 2 * (W * p * G)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (by linarith) hsq
    _ = _ := by ring

end GaloisForLFunctions.BlackHoleRingdown

end
