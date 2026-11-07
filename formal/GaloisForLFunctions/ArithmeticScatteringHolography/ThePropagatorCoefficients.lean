import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# The coefficients of the wave propagator

The wave propagator `P_d(A)` of a black hole with odd groups `G`, `G'` has its entries at the core given by one power
series,

  `R(z) = 1 / ((1 - q² z)(1 - t z + q z²))`,

and by the series obtained from `R` by the factors `(1 ∓ q z)`. The pole at `z = q⁻²` is the constant function, and it
dominates: the coefficients grow like `q^{2n}`, while those of `1/(1 - t z + q z²)` grow at most like `(q+1)^n`. This holds for
every `|t| ≤ q`, whether the roots of the denominator are on the circle or not. So all these coefficients are nonnegative,
in the order `σ ≥ η ≥ γ ≥ γ'`, and the terms `(-q)^n` coming from the dead ends are smaller than them.

Here `propR n` is the coefficient of `z^{n-2}`, so that `propR 0 = propR 1 = 0`. This module is algebra on these
sequences; the graph appears in `TheWavePropagatorIsPositive`.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography

/-- The coefficients of `1/(1 - t z + q z²)`. -/
def denomSeq (q t : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => t
  | n + 2 => t * denomSeq q t (n + 1) - q * denomSeq q t n

/-- The coefficients of `z²/((1 - q² z)(1 - t z + q z²))`. -/
def propR (q t : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | n + 2 => q ^ 2 * propR q t (n + 1) + denomSeq q t n

variable (q t : ℝ)

@[simp] theorem propR_zero : propR q t 0 = 0 := rfl
@[simp] theorem propR_one : propR q t 1 = 0 := rfl
@[simp] theorem propR_two : propR q t 2 = 1 := by simp [propR, denomSeq]
@[simp] theorem propR_three : propR q t 3 = q ^ 2 + t := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, propR, propR_two]
  simp [denomSeq]

theorem propR_add_two (n : ℕ) : propR q t (n + 2) = q ^ 2 * propR q t (n + 1) + denomSeq q t n := rfl

/-- The recurrence of the denominator `(1 - q² z)(1 - t z + q z²)`. -/
theorem propR_rec (n : ℕ) :
    propR q t (n + 3) =
      (q ^ 2 + t) * propR q t (n + 2) - (q ^ 2 * t + q) * propR q t (n + 1) + q ^ 3 * propR q t n := by
  cases n with
  | zero => simp
  | succ m =>
    have h1 := propR_add_two q t (m + 2)
    have h2 := propR_add_two q t (m + 1)
    have h3 := propR_add_two q t m
    have h4 : denomSeq q t (m + 2) = t * denomSeq q t (m + 1) - q * denomSeq q t m := rfl
    rw [show m + 1 + 3 = m + 2 + 2 by ring, show m + 1 + 2 = m + 1 + 2 from rfl]
    rw [show m + 2 + 1 = m + 3 by ring] at h1
    rw [show m + 1 + 1 = m + 2 by ring] at h2
    linear_combination h1 + h4 - t * h2 + q * h3

/-- `(1 + q z) R`. -/
def sigmaS (n : ℕ) : ℝ := propR q t (n + 2) + q * propR q t (n + 1)
/-- `(1 - q z) R`. -/
def etaS (n : ℕ) : ℝ := propR q t (n + 2) - q * propR q t (n + 1)
/-- `(1 - q² z²) R`. -/
def rhoS (n : ℕ) : ℝ := propR q t (n + 2) - q ^ 2 * propR q t n
/-- `(1 - q z)² R`. -/
def gammaS (n : ℕ) : ℝ := propR q t (n + 2) - 2 * q * propR q t (n + 1) + q ^ 2 * propR q t n
/-- `(1 - q z)²(1 + q z) R`. -/
def phiS : ℕ → ℝ
  | 0 => 1
  | n + 1 => gammaS q t (n + 1) + q * gammaS q t n
/-- `(1 - q z)² R / (1 + q z)`. -/
def gpS : ℕ → ℝ
  | 0 => 1
  | n + 1 => gammaS q t (n + 1) - q * gpS n

/-- The weight of the dead ends in the core equation: `#G' (q + 1) / 2`, with `#G' = q + 1 + t`. -/
def kappaOne : ℝ := (q + 1 + t) * (q + 1) / 2
/-- The weight of the necks in the core equation: `#G (q - 1) / 2`, with `#G = q + 1 - t`. -/
def kappaTwo : ℝ := (q + 1 - t) * (q - 1) / 2

@[simp] theorem sigmaS_zero : sigmaS q t 0 = 1 := by simp [sigmaS]
@[simp] theorem etaS_zero : etaS q t 0 = 1 := by simp [etaS]
@[simp] theorem rhoS_zero : rhoS q t 0 = 1 := by simp [rhoS]
@[simp] theorem gammaS_zero : gammaS q t 0 = 1 := by simp [gammaS]
@[simp] theorem phiS_zero : phiS q t 0 = 1 := rfl
@[simp] theorem gpS_zero : gpS q t 0 = 1 := rfl

theorem phiS_succ (n : ℕ) : phiS q t (n + 1) = gammaS q t (n + 1) + q * gammaS q t n := rfl
theorem gpS_succ (n : ℕ) : gpS q t (n + 1) = gammaS q t (n + 1) - q * gpS q t n := rfl

/-! ### Identities among the series -/

theorem rhoS_succ (n : ℕ) : rhoS q t (n + 1) = phiS q t (n + 1) + q * rhoS q t n := by
  simp only [rhoS, phiS_succ, gammaS]
  ring

theorem sigmaS_succ (n : ℕ) : sigmaS q t (n + 1) = rhoS q t (n + 1) + q * sigmaS q t n := by
  simp only [sigmaS, rhoS]
  ring

theorem etaS_succ (n : ℕ) : etaS q t (n + 1) = rhoS q t (n + 1) - q * etaS q t n := by
  simp only [etaS, rhoS]
  ring

theorem etaS_succ' (n : ℕ) : etaS q t (n + 1) = gammaS q t (n + 1) + q * etaS q t n := by
  simp only [etaS, gammaS]
  ring

theorem gammaS_succ (n : ℕ) : gammaS q t (n + 1) = phiS q t (n + 1) - q * gammaS q t n := by
  rw [phiS_succ]
  ring

theorem phiS_one : phiS q t 1 = kappaOne q t + kappaTwo q t - 2 * q := by
  simp only [phiS_succ, gammaS, kappaOne, kappaTwo]
  simp
  ring

/-- The core equation on the coefficient of the core. -/
theorem phiS_rec (n : ℕ) :
    phiS q t (n + 2) + q * phiS q t (n + 1) =
      kappaOne q t * gammaS q t (n + 1) + kappaTwo q t * rhoS q t (n + 1) := by
  have h1 := propR_rec q t (n + 1)
  have h0 := propR_rec q t n
  simp only [phiS_succ, gammaS, rhoS, kappaOne, kappaTwo]
  rw [show n + 1 + 3 = n + 4 by ring, show n + 1 + 2 = n + 3 by ring, show n + 1 + 1 = n + 2 by ring]
    at h1 ⊢
  linear_combination h1 - q * h0

/-- The core equation on the coefficient of the necks. -/
theorem rhoS_rec (n : ℕ) :
    rhoS q t (n + 1) + q * rhoS q t n =
      kappaOne q t * etaS q t n + kappaTwo q t * sigmaS q t n := by
  have h0 := propR_rec q t n
  simp only [etaS, sigmaS, rhoS, kappaOne, kappaTwo]
  rw [show n + 1 + 2 = n + 3 by ring]
  linear_combination h0

/-- The core equation on the coefficient of the dead ends: the term `(-q)^n` is the sector of the cusp forms. -/
theorem gammaS_rec (n : ℕ) :
    gammaS q t (n + 1) + q * gammaS q t n =
      kappaOne q t * gpS q t n + kappaTwo q t * etaS q t n + 2 * (-q) ^ (n + 1) := by
  induction n with
  | zero =>
    simp only [gammaS, zero_add, gpS_zero, etaS_zero, kappaOne, kappaTwo]
    simp
    ring
  | succ n ih =>
    have hphi := phiS_rec q t n
    simp only [phiS_succ] at hphi
    rw [gpS_succ, etaS_succ, pow_succ (-q) (n + 1)]
    rw [show n + 1 + 1 = n + 2 by ring] at hphi ⊢
    linear_combination hphi + q * (-1 : ℝ) * ih

/-! ### Growth -/

section Bounds

variable {q t}

/-- The denominator grows at most like `q + 1`. -/
theorem abs_denomSeq_le (hq : 1 ≤ q) (ht : |t| ≤ q) (n : ℕ) :
    |denomSeq q t (n + 1)| ≤ q * (q + 1) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [denomSeq] using ht
  | one =>
    have h0 : denomSeq q t 2 = t * t - q := by simp [denomSeq]
    rw [show 1 + 1 = 2 from rfl, h0, abs_le]
    have h1 := abs_le.mp ht
    constructor <;> nlinarith [h1.1, h1.2, sq_nonneg t]
  | more n h0 h1 =>
    have e : denomSeq q t (n + 2 + 1) = t * denomSeq q t (n + 1 + 1) - q * denomSeq q t (n + 1) := rfl
    have hp : (0 : ℝ) ≤ (q + 1) ^ n := by positivity
    have hq0 : 0 ≤ q := by linarith
    calc |denomSeq q t (n + 2 + 1)| ≤ |t * denomSeq q t (n + 1 + 1)| + |q * denomSeq q t (n + 1)| := by
          rw [e]
          exact abs_sub _ _
      _ = |t| * |denomSeq q t (n + 1 + 1)| + q * |denomSeq q t (n + 1)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hq0]
      _ ≤ q * (q * (q + 1) ^ (n + 1)) + q * (q * (q + 1) ^ n) := by
          gcongr
      _ ≤ q * (q + 1) ^ (n + 2) := by
          have : q * (q * (q + 1) ^ (n + 1)) + q * (q * (q + 1) ^ n) =
              q * (q + 1) ^ n * (q * (q + 2)) := by ring
          rw [this, show q * (q + 1) ^ (n + 2) = q * (q + 1) ^ n * (q + 1) ^ 2 by ring]
          have : 0 ≤ q * (q + 1) ^ n := by positivity
          exact mul_le_mul_of_nonneg_left (by nlinarith) this

/-- **The pole at the constant function dominates.** -/
theorem propR_growth (hq : 3 ≤ q) (ht : |t| ≤ q) (n : ℕ) :
    (q ^ 2 - q) * propR q t (n + 2) ≤ propR q t (n + 3) ∧ (q ^ 2 - q) ^ n ≤ propR q t (n + 2) := by
  have hq2 : q + 1 ≤ q ^ 2 - q := by nlinarith
  have hq0 : 0 ≤ q ^ 2 - q := by nlinarith
  induction n with
  | zero =>
    have h1 := (abs_le.mp ht).1
    simp only [zero_add, propR_two, pow_zero, le_refl, and_true, propR_three]
    nlinarith
  | succ n ih =>
    have hn : (q ^ 2 - q) ^ (n + 1) ≤ propR q t (n + 3) := by
      rw [pow_succ']
      exact (mul_le_mul_of_nonneg_left ih.2 hq0).trans ih.1
    refine ⟨?_, by simpa [show n + 1 + 2 = n + 3 by ring] using hn⟩
    have hrec : propR q t (n + 1 + 3) = q ^ 2 * propR q t (n + 3) + denomSeq q t (n + 2) := by
      rw [show n + 1 + 3 = (n + 2) + 2 by ring, propR_add_two]
    have hbound := (abs_le.mp (abs_denomSeq_le (by linarith : 1 ≤ q) ht (n + 1))).1
    have hpow : (q + 1) ^ (n + 1) ≤ propR q t (n + 3) :=
      (pow_le_pow_left₀ (by linarith) hq2 (n + 1)).trans hn
    rw [show n + 1 + 2 = n + 3 by ring, hrec]
    have hq' : 0 ≤ q := by linarith
    have : q * (q + 1) ^ (n + 1) ≤ q * propR q t (n + 3) := mul_le_mul_of_nonneg_left hpow hq'
    rw [show n + 2 = n + 1 + 1 by ring] at *
    nlinarith

variable (hq : 7 ≤ q) (ht : |t| ≤ q)

include hq ht

theorem propR_nonneg (n : ℕ) : 0 ≤ propR q t n := by
  have hq0 : 0 ≤ q ^ 2 - q := by nlinarith
  rcases n with _ | _ | n
  · simp
  · simp
  · exact (pow_nonneg hq0 n).trans (propR_growth (by linarith) ht n).2

/-- The ratio of two consecutive coefficients is at least `q² - q`. -/
theorem propR_ratio (n : ℕ) : (q ^ 2 - q) * propR q t n ≤ propR q t (n + 1) := by
  rcases n with _ | _ | n
  · simp
  · simp
  · exact (propR_growth (by linarith) ht n).1

theorem propR_ge_pow (n : ℕ) : q ^ n ≤ propR q t (n + 2) := by
  have hq1 : q ≤ q ^ 2 - q := by nlinarith
  exact (pow_le_pow_left₀ (by linarith) hq1 n).trans (propR_growth (by linarith) ht n).2

theorem propR_ge_two_pow (n : ℕ) : 2 * q ^ (n + 1) ≤ propR q t (n + 3) := by
  have hq1 : q ≤ q ^ 2 - q := by nlinarith
  have hq0 : 0 ≤ q := by linarith
  induction n with
  | zero =>
    have := (abs_le.mp ht).1
    simp only [zero_add, pow_one, propR_three]
    nlinarith
  | succ n ih =>
    have h := propR_ratio hq ht (n + 3)
    have hp : 0 ≤ q ^ (n + 1) := by positivity
    rw [show n + 1 + 3 = n + 3 + 1 by ring, pow_succ]
    have h2 : q * propR q t (n + 3) ≤ (q ^ 2 - q) * propR q t (n + 3) :=
      mul_le_mul_of_nonneg_right hq1 (propR_nonneg hq ht _)
    nlinarith

theorem etaS_nonneg (n : ℕ) : 0 ≤ etaS q t n := by
  have h := propR_ratio hq ht (n + 1)
  have h1 := propR_nonneg hq ht (n + 1)
  have : q * propR q t (n + 1) ≤ (q ^ 2 - q) * propR q t (n + 1) :=
    mul_le_mul_of_nonneg_right (by nlinarith) h1
  unfold etaS
  linarith

theorem gammaS_nonneg (n : ℕ) : 0 ≤ gammaS q t n := by
  have h := propR_ratio hq ht (n + 1)
  have h1 := propR_nonneg hq ht (n + 1)
  have h0 := propR_nonneg hq ht n
  have : 2 * q * propR q t (n + 1) ≤ (q ^ 2 - q) * propR q t (n + 1) :=
    mul_le_mul_of_nonneg_right (by nlinarith) h1
  have hq2 : 0 ≤ q ^ 2 * propR q t n := by positivity
  unfold gammaS
  linarith

theorem phiS_nonneg (n : ℕ) : 0 ≤ phiS q t n := by
  have hq0 : 0 ≤ q := by linarith
  cases n with
  | zero => simp
  | succ n =>
    rw [phiS_succ]
    exact add_nonneg (gammaS_nonneg hq ht _) (mul_nonneg hq0 (gammaS_nonneg hq ht _))

theorem gammaS_le_etaS (n : ℕ) : gammaS q t n ≤ etaS q t n := by
  have hq0 : 0 ≤ q := by linarith
  cases n with
  | zero => simp
  | succ n =>
    rw [etaS_succ']
    linarith [mul_nonneg hq0 (etaS_nonneg hq ht n)]

theorem etaS_le_sigmaS (n : ℕ) : etaS q t n ≤ sigmaS q t n := by
  have hq0 : 0 ≤ q := by linarith
  simp only [etaS, sigmaS]
  linarith [mul_nonneg hq0 (propR_nonneg hq ht (n + 1))]

theorem gammaS_le_rhoS (n : ℕ) : gammaS q t n ≤ rhoS q t n := by
  have hq0 : 0 ≤ q := by linarith
  cases n with
  | zero => simp
  | succ n =>
    have h : rhoS q t (n + 1) - gammaS q t (n + 1) = 2 * q * etaS q t n := by
      simp only [rhoS, gammaS, etaS]
      ring
    have := mul_nonneg (by linarith : 0 ≤ 2 * q) (etaS_nonneg hq ht n)
    linarith

theorem rhoS_nonneg (n : ℕ) : 0 ≤ rhoS q t n :=
  (gammaS_nonneg hq ht n).trans (gammaS_le_rhoS hq ht n)

theorem sigmaS_nonneg (n : ℕ) : 0 ≤ sigmaS q t n :=
  (etaS_nonneg hq ht n).trans (etaS_le_sigmaS hq ht n)

/-- The third difference is positive: `(1 - q z)³ R`. -/
theorem gammaS_step (n : ℕ) :
    (q ^ 2 - 4 * q - 1) * propR q t (n + 2) ≤ gammaS q t (n + 1) - q * gammaS q t n := by
  have h2 := propR_ratio hq ht (n + 2)
  have h1 := propR_ratio hq ht (n + 1)
  have h0 := propR_ratio hq ht n
  have hn0 := propR_nonneg hq ht n
  have hn1 := propR_nonneg hq ht (n + 1)
  have hn2 := propR_nonneg hq ht (n + 2)
  have hq1 : q ^ 2 - q ≥ 0 := by nlinarith
  -- `q³ r_n ≤ r_{n+2}`
  have hthree : q ^ 3 * propR q t n ≤ propR q t (n + 2) := by
    have h3 : (q ^ 2 - q) * ((q ^ 2 - q) * propR q t n) ≤ (q ^ 2 - q) * propR q t (n + 1) :=
      mul_le_mul_of_nonneg_left h0 hq1
    have h4 : q ^ 3 * propR q t n ≤ (q ^ 2 - q) * ((q ^ 2 - q) * propR q t n) := by
      have h5 : q ^ 3 ≤ (q ^ 2 - q) * (q ^ 2 - q) := by
        have : (q ^ 2 - q) * (q ^ 2 - q) - q ^ 3 = q ^ 2 * ((q - 1) ^ 2 - q) := by ring
        have h6 : 0 ≤ q ^ 2 * ((q - 1) ^ 2 - q) := by
          have : 0 ≤ (q - 1) ^ 2 - q := by nlinarith
          positivity
        linarith
      calc q ^ 3 * propR q t n ≤ (q ^ 2 - q) * (q ^ 2 - q) * propR q t n :=
            mul_le_mul_of_nonneg_right h5 hn0
        _ = _ := by ring
    linarith
  simp only [gammaS]
  rw [show n + 1 + 2 = n + 3 by ring, show n + 1 + 1 = n + 2 by ring]
  rw [show n + 2 + 1 = n + 3 by ring] at h2
  have hq2 : 0 ≤ q ^ 2 * propR q t (n + 1) := by positivity
  nlinarith

theorem gpS_bounds (n : ℕ) : 0 ≤ gpS q t n ∧ gpS q t n ≤ gammaS q t n := by
  have hq0 : 0 ≤ q := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    rw [gpS_succ]
    have h := gammaS_step hq ht n
    have hr := propR_nonneg hq ht (n + 2)
    have hc : 0 ≤ q ^ 2 - 4 * q - 1 := by nlinarith
    have h1 : q * gpS q t n ≤ q * gammaS q t n := mul_le_mul_of_nonneg_left ih.2 hq0
    have h2 := mul_nonneg hc hr
    have h3 := mul_nonneg hq0 ih.1
    constructor <;> linarith

theorem gpS_nonneg (n : ℕ) : 0 ≤ gpS q t n := (gpS_bounds hq ht n).1

theorem gpS_le_etaS (n : ℕ) : gpS q t n ≤ etaS q t n :=
  (gpS_bounds hq ht n).2.trans (gammaS_le_etaS hq ht n)

/-- The dead coefficient beats the term of the cusp forms by a factor `2`. -/
theorem two_pow_le_gpS (n : ℕ) : 2 * q ^ (n + 1) ≤ gpS q t (n + 1) := by
  have hq0 : 0 ≤ q := by linarith
  rw [gpS_succ]
  have h := gammaS_step hq ht n
  have h1 : q * gpS q t n ≤ q * gammaS q t n := mul_le_mul_of_nonneg_left (gpS_bounds hq ht n).2 hq0
  have h2 := propR_ge_pow hq ht n
  have hc : 2 * q ≤ q ^ 2 - 4 * q - 1 := by nlinarith
  have hp : 0 ≤ q ^ n := by positivity
  have h3 : 2 * q * q ^ n ≤ (q ^ 2 - 4 * q - 1) * propR q t (n + 2) :=
    mul_le_mul hc h2 hp (by nlinarith)
  rw [pow_succ']
  linarith

theorem pow_le_gpS (n : ℕ) : q ^ n ≤ gpS q t n := by
  cases n with
  | zero => simp
  | succ n =>
    have := two_pow_le_gpS hq ht n
    have hp : 0 ≤ q ^ (n + 1) := by positivity
    linarith

omit ht in
theorem neg_pow_le (m : ℕ) : (-q) ^ m ≤ q ^ m := by
  have hp : 0 ≤ q ^ m := by positivity
  rcases neg_one_pow_eq_or ℝ m with h | h <;> rw [neg_pow, h] <;> linarith

omit ht in
theorem neg_pow_ge (m : ℕ) : -q ^ m ≤ (-q) ^ m := by
  have hp : 0 ≤ q ^ m := by positivity
  rcases neg_one_pow_eq_or ℝ m with h | h <;> rw [neg_pow, h] <;> linarith

/-! ### The inequalities at the pin and at the cap -/

/-- The inequality shared by the pin and the cap. -/
theorem pin_B (n : ℕ) :
    (-q) ^ (n + 1) ≤
      (q - 1) * (sigmaS q t n - etaS q t n) / 4 + (q + 1) * (etaS q t n - gpS q t n) / 4 := by
  have hq0 : 0 ≤ q := by linarith
  cases n with
  | zero =>
    have h1 : sigmaS q t 0 - etaS q t 0 = 0 := by simp
    have h2 : etaS q t 0 - gpS q t 0 = 0 := by simp
    rw [h1, h2]
    simp
    linarith
  | succ n =>
    have hE1 : sigmaS q t (n + 1) - etaS q t (n + 1) = 2 * q * propR q t (n + 2) := by
      simp only [sigmaS, etaS]
      ring
    have hE2 : etaS q t (n + 1) - gpS q t (n + 1) = q * (etaS q t n + gpS q t n) := by
      rw [gpS_succ, etaS_succ']
      ring
    rw [hE1, hE2]
    have h1 := propR_ge_pow hq ht n
    have h2 := pow_le_gpS hq ht n
    have h3 := h2.trans (gpS_le_etaS hq ht n)
    have hp := neg_pow_le hq (n + 1 + 1)
    have hqp : 0 ≤ q ^ n := by positivity
    have e : q ^ (n + 1 + 1) = (q - 1) * (2 * q * q ^ n) / 4 + (q + 1) * (q * (q ^ n + q ^ n)) / 4 := by
      ring
    have hm1 : (q - 1) * (2 * q * q ^ n) / 4 ≤ (q - 1) * (2 * q * propR q t (n + 2)) / 4 := by
      gcongr
      linarith
    have hm2 : (q + 1) * (q * (q ^ n + q ^ n)) / 4 ≤ (q + 1) * (q * (etaS q t n + gpS q t n)) / 4 := by
      gcongr
    linarith

/-- The mass of the pin stays nonnegative. -/
theorem pin_A (n : ℕ) :
    0 ≤ (q - 1) ^ 2 * sigmaS q t (n + 1) / 4 + (q ^ 2 - 1) * etaS q t (n + 1) / 2 +
      (q + 1) ^ 2 * gpS q t (n + 1) / 4 + (q + 1) * (-q) ^ (n + 2) := by
  have h0 := two_pow_le_gpS hq ht n
  have h1 := gpS_le_etaS hq ht (n + 1)
  have h2 := etaS_le_sigmaS hq ht (n + 1)
  have hp := neg_pow_ge hq (n + 2)
  have hqp : 0 ≤ q ^ (n + 1) := by positivity
  have ha : (q - 1) ^ 2 * (2 * q ^ (n + 1)) / 4 ≤ (q - 1) ^ 2 * sigmaS q t (n + 1) / 4 := by
    gcongr
    linarith
  have hb : (q ^ 2 - 1) * (2 * q ^ (n + 1)) / 2 ≤ (q ^ 2 - 1) * etaS q t (n + 1) / 2 := by
    have : 0 ≤ q ^ 2 - 1 := by nlinarith
    gcongr
    linarith
  have hc : (q + 1) ^ 2 * (2 * q ^ (n + 1)) / 4 ≤ (q + 1) ^ 2 * gpS q t (n + 1) / 4 := by
    gcongr
  have hd : -((q + 1) * q ^ (n + 2)) ≤ (q + 1) * (-q) ^ (n + 2) := by
    have : (q + 1) * (-q ^ (n + 2)) ≤ (q + 1) * (-q) ^ (n + 2) :=
      mul_le_mul_of_nonneg_left hp (by linarith)
    linarith
  have he : (q - 1) ^ 2 * (2 * q ^ (n + 1)) / 4 + (q ^ 2 - 1) * (2 * q ^ (n + 1)) / 2 +
      (q + 1) ^ 2 * (2 * q ^ (n + 1)) / 4 - (q + 1) * q ^ (n + 2) = q ^ (n + 1) * (q * (q - 1)) := by
    ring
  have hf : 0 ≤ q ^ (n + 1) * (q * (q - 1)) := by
    have : 0 ≤ q * (q - 1) := by nlinarith
    positivity
  linarith

/-- The cap: its coefficient stays nonnegative after the cusp forms are subtracted. -/
theorem cap_B (n : ℕ) :
    0 ≤ (q ^ 2 - 1) * (sigmaS q t (n + 1) - 2 * etaS q t (n + 1) + gpS q t (n + 1)) / 4 +
      (q - 1) * (-q) ^ (n + 2) := by
  have hq1 : 0 ≤ q - 1 := by linarith
  have hq0 : 0 ≤ q := by linarith
  cases n with
  | zero =>
    have hZ : sigmaS q t 1 - 2 * etaS q t 1 + gpS q t 1 = 0 := by
      have : gpS q t 1 = gammaS q t 1 - q * gpS q t 0 := gpS_succ q t 0
      rw [this]
      simp [sigmaS, etaS, gammaS]
      ring
    rw [show 0 + 1 = 1 from rfl, hZ]
    simp only [mul_zero, zero_div, zero_add]
    positivity
  | succ m =>
    have hZ : sigmaS q t (m + 1 + 1) - 2 * etaS q t (m + 1 + 1) + gpS q t (m + 1 + 1) =
        q ^ 2 * (3 * propR q t (m + 2) - q * propR q t (m + 1) + gpS q t m) := by
      rw [gpS_succ, gpS_succ]
      simp only [sigmaS, etaS, gammaS]
      rw [show m + 1 + 1 + 2 = m + 4 by ring, show m + 1 + 1 + 1 = m + 3 by ring,
        show m + 1 + 2 = m + 3 by ring, show m + 1 + 1 = m + 2 by ring]
      ring
    have hkey : 4 * q ^ m ≤ 3 * propR q t (m + 2) - q * propR q t (m + 1) + gpS q t m := by
      cases m with
      | zero =>
        simp
        norm_num
      | succ k =>
        have h1 := propR_ge_two_pow hq ht k
        have h2 := propR_ratio hq ht (k + 2)
        have h3 := propR_nonneg hq ht (k + 2)
        have h4 : q * propR q t (k + 2) ≤ (q ^ 2 - q) * propR q t (k + 2) :=
          mul_le_mul_of_nonneg_right (by nlinarith) h3
        have h5 := gpS_nonneg hq ht (k + 1)
        rw [show k + 1 + 2 = k + 3 by ring, show k + 1 + 1 = k + 2 by ring]
        rw [show k + 2 + 1 = k + 3 by ring] at h2
        linarith
    rw [hZ]
    have hsq : 0 ≤ q ^ 2 - 1 := by nlinarith
    have hp := neg_pow_ge hq (m + 1 + 2)
    have ha : (q ^ 2 - 1) * (q ^ 2 * (4 * q ^ m)) / 4 ≤
        (q ^ 2 - 1) * (q ^ 2 * (3 * propR q t (m + 2) - q * propR q t (m + 1) + gpS q t m)) / 4 := by
      gcongr
    have hb : (q - 1) * (-q ^ (m + 1 + 2)) ≤ (q - 1) * (-q) ^ (m + 1 + 2) :=
      mul_le_mul_of_nonneg_left hp hq1
    have hc : (q ^ 2 - 1) * (q ^ 2 * (4 * q ^ m)) / 4 + (q - 1) * (-q ^ (m + 1 + 2)) =
        (q - 1) * q ^ (m + 2) := by
      ring
    have hd : 0 ≤ (q - 1) * q ^ (m + 2) := by positivity
    linarith

/-- The dead end: the cusp forms are smaller than the Eisenstein mass. -/
theorem dead_diag (n : ℕ) : 0 ≤ (q + 1) * gpS q t (n + 1) + 2 * (-q) ^ (n + 2) := by
  have h0 := two_pow_le_gpS hq ht n
  have hp := neg_pow_ge hq (n + 2)
  have hq0 : 0 ≤ q := by linarith
  have ha : (q + 1) * (2 * q ^ (n + 1)) ≤ (q + 1) * gpS q t (n + 1) :=
    mul_le_mul_of_nonneg_left h0 (by linarith)
  have hb : (q + 1) * (2 * q ^ (n + 1)) - 2 * q ^ (n + 2) = 2 * q ^ (n + 1) := by ring
  have hc : 0 ≤ q ^ (n + 1) := by positivity
  linarith

/-- The gap between `η` and `γ'` beats the cusp forms. -/
theorem eta_sub_gp_ge (n : ℕ) :
    (-q) ^ (n + 2) ≤ (q + 1) * (etaS q t (n + 1) - gpS q t (n + 1)) / 2 := by
  have hq0 : 0 ≤ q := by linarith
  have hE2 : etaS q t (n + 1) - gpS q t (n + 1) = q * (etaS q t n + gpS q t n) := by
    rw [gpS_succ, etaS_succ']
    ring
  rw [hE2]
  have h2 := pow_le_gpS hq ht n
  have h3 := h2.trans (gpS_le_etaS hq ht n)
  have hp := neg_pow_le hq (n + 2)
  have hm : (q + 1) * (q * (q ^ n + q ^ n)) / 2 ≤ (q + 1) * (q * (etaS q t n + gpS q t n)) / 2 := by
    gcongr
  have hqp : 0 ≤ q ^ (n + 1) := by positivity
  have e : (q + 1) * (q * (q ^ n + q ^ n)) / 2 = q ^ (n + 2) + q ^ (n + 1) := by ring
  linarith

/-- `γ'` beats the cusp forms at the pin. -/
theorem gp_pin (n : ℕ) : 0 ≤ q * gpS q t (n + 1) + (-q) ^ (n + 2) := by
  have hq0 : 0 ≤ q := by linarith
  have h0 := two_pow_le_gpS hq ht n
  have hp := neg_pow_ge hq (n + 2)
  have hm : q * (2 * q ^ (n + 1)) ≤ q * gpS q t (n + 1) := mul_le_mul_of_nonneg_left h0 hq0
  have e : q * (2 * q ^ (n + 1)) = 2 * q ^ (n + 2) := by ring
  have hqp : 0 ≤ q ^ (n + 2) := by positivity
  linarith

/-- The second difference of `σ, η, γ'` is nonnegative. -/
theorem second_diff_nonneg (n : ℕ) :
    0 ≤ sigmaS q t (n + 1) - 2 * etaS q t (n + 1) + gpS q t (n + 1) := by
  have hq0 : 0 ≤ q := by linarith
  cases n with
  | zero =>
    have hZ : sigmaS q t 1 - 2 * etaS q t 1 + gpS q t 1 = 0 := by
      have : gpS q t 1 = gammaS q t 1 - q * gpS q t 0 := gpS_succ q t 0
      rw [this]
      simp [sigmaS, etaS, gammaS]
      ring
    exact hZ.ge
  | succ m =>
    have hZ : sigmaS q t (m + 1 + 1) - 2 * etaS q t (m + 1 + 1) + gpS q t (m + 1 + 1) =
        q ^ 2 * (3 * propR q t (m + 2) - q * propR q t (m + 1) + gpS q t m) := by
      rw [gpS_succ, gpS_succ]
      simp only [sigmaS, etaS, gammaS]
      rw [show m + 1 + 1 + 2 = m + 4 by ring, show m + 1 + 1 + 1 = m + 3 by ring,
        show m + 1 + 2 = m + 3 by ring, show m + 1 + 1 = m + 2 by ring]
      ring
    rw [hZ]
    have h2 := propR_ratio hq ht (m + 1)
    have h3 := propR_nonneg hq ht (m + 1)
    have h4 : q * propR q t (m + 1) ≤ (q ^ 2 - q) * propR q t (m + 1) :=
      mul_le_mul_of_nonneg_right (by nlinarith) h3
    have h5 := gpS_nonneg hq ht m
    have h6 := propR_nonneg hq ht (m + 2)
    rw [show m + 1 + 1 = m + 2 by ring] at h2
    have : 0 ≤ 3 * propR q t (m + 2) - q * propR q t (m + 1) + gpS q t m := by linarith
    positivity

end Bounds

end GaloisForLFunctions.ArithmeticScatteringHolography

end
