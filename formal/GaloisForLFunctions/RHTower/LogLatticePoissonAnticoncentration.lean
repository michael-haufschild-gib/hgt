import Mathlib
import GaloisForLFunctions.RHTower.VanDerCorputLocal
import GaloisForLFunctions.RHTower.PrimeMassLowerBound

/-!
# Anti-concentration for functions vanishing on a logarithmic lattice

Let `h` be continuous, supported in `[-W, W]`, with integrable spectral function `F`
(`h(y) = ∫ F(r) e^{iry} dr`), and suppose `h(log(n/X)) = 0` for every integer `n ≥ 1`.
Transporting `h` to the integer lattice by `x = X e^y` and applying Poisson summation
expresses `X ∫ h` as minus the sum of the nonzero Fourier coefficients of the transported
function.  Each coefficient is an oscillatory integral with phase `r y - 2π j X e^y`.
Two integrations by parts bound the non-stationary coefficients by `O((jX)^{-2})`, and the
second-derivative test bounds the `O(|r|/X)` stationary ones by `O((jX)^{-1/2})`.

The result: `|∫ h|` is at most `X^{-2}` times the total spectral mass plus `X^{-1/2}`
times the spectral mass above height `≍ X`, weighted by `√(|r|/X)`.
-/

open MeasureTheory intervalIntegral Complex Set

noncomputable section

namespace RHTower.LogLatticePoisson

/-- Integration by parts with vanishing boundary values. -/
theorem integral_mul_cexp_eq_neg_of_antideriv {a b : ℝ} {φ ψ : ℝ → ℝ} {A B B' : ℝ → ℂ}
    (hφ : ∀ x ∈ uIcc a b, HasDerivAt φ (ψ x) x)
    (hB : ∀ x ∈ uIcc a b, HasDerivAt B (B' x) x)
    (hB'c : ContinuousOn B' (uIcc a b)) (hAc : ContinuousOn A (uIcc a b))
    (hrel : ∀ x ∈ uIcc a b, B x * (I * (ψ x : ℂ)) = A x)
    (ha : B a = 0) (hb : B b = 0) :
    ∫ t in a..b, A t * Complex.exp (I * φ t) = - ∫ t in a..b, B' t * Complex.exp (I * φ t) := by
  have hφc : ContinuousOn φ (uIcc a b) := fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hVc : ContinuousOn (fun t : ℝ => Complex.exp (I * φ t)) (uIcc a b) :=
    Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφc))
  have hprod : ∀ x ∈ uIcc a b, HasDerivAt (fun t : ℝ => B t * Complex.exp (I * φ t))
      (B' x * Complex.exp (I * φ x) + A x * Complex.exp (I * φ x)) x := by
    intro x hx
    have hV : HasDerivAt (fun t : ℝ => Complex.exp (I * φ t))
        (Complex.exp (I * φ x) * (I * (ψ x : ℂ))) x :=
      (((hφ x hx).ofReal_comp).const_mul I).cexp
    have h := (hB x hx).mul hV
    have hr := hrel x hx
    have hcalc : B' x * Complex.exp (I * φ x) + B x * (Complex.exp (I * φ x) * (I * (ψ x : ℂ)))
        = B' x * Complex.exp (I * φ x) + A x * Complex.exp (I * φ x) := by
      rw [← hr]; ring
    exact hcalc ▸ h
  have hint : IntervalIntegrable
      (fun t => B' t * Complex.exp (I * φ t) + A t * Complex.exp (I * φ t)) volume a b :=
    ((hB'c.mul hVc).add (hAc.mul hVc)).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hprod hint
  rw [ha, hb, zero_mul, zero_mul, sub_zero] at hftc
  have h1 : IntervalIntegrable (fun t => B' t * Complex.exp (I * φ t)) volume a b :=
    (hB'c.mul hVc).intervalIntegrable
  have h2 : IntervalIntegrable (fun t => A t * Complex.exp (I * φ t)) volume a b :=
    (hAc.mul hVc).intervalIntegrable
  rw [intervalIntegral.integral_add h1 h2] at hftc
  linear_combination hftc

/-- **Two integrations by parts.**  For a `C²` amplitude `η` vanishing to first order at both
ends and a phase whose derivative `ψ` never vanishes, the oscillatory integral equals
`-∫ p₁·exp(iφ)` with the explicit real density
`p₁ = η''/ψ² − 3η'ψ'/ψ³ − ηψ''/ψ³ + 3ηψ'²/ψ⁴`. -/
theorem integral_mul_cexp_eq_two_ibp {a b : ℝ} {φ ψ ψ1 ψ2 η η1 η2 : ℝ → ℝ}
    (hφ : ∀ x ∈ uIcc a b, HasDerivAt φ (ψ x) x)
    (hψ : ∀ x ∈ uIcc a b, HasDerivAt ψ (ψ1 x) x)
    (hψ1 : ∀ x ∈ uIcc a b, HasDerivAt ψ1 (ψ2 x) x)
    (hη : ∀ x ∈ uIcc a b, HasDerivAt η (η1 x) x)
    (hη1 : ∀ x ∈ uIcc a b, HasDerivAt η1 (η2 x) x)
    (hψ2c : ContinuousOn ψ2 (uIcc a b)) (hη2c : ContinuousOn η2 (uIcc a b))
    (hψ0 : ∀ x ∈ uIcc a b, ψ x ≠ 0)
    (hηa : η a = 0) (hηb : η b = 0) (hη1a : η1 a = 0) (hη1b : η1 b = 0) :
    ∫ t in a..b, (η t : ℂ) * Complex.exp (I * φ t) =
      - ∫ t in a..b, ((η2 t / ψ t ^ 2 - 3 * η1 t * ψ1 t / ψ t ^ 3 - η t * ψ2 t / ψ t ^ 3
          + 3 * η t * ψ1 t ^ 2 / ψ t ^ 4 : ℝ) : ℂ) * Complex.exp (I * φ t) := by
  set q1 : ℝ → ℝ := fun x => η1 x / ψ x - η x * ψ1 x / ψ x ^ 2 with hq1
  set p1 : ℝ → ℝ := fun x => η2 x / ψ x ^ 2 - 3 * η1 x * ψ1 x / ψ x ^ 3 - η x * ψ2 x / ψ x ^ 3
      + 3 * η x * ψ1 x ^ 2 / ψ x ^ 4 with hp1
  have hψc : ContinuousOn ψ (uIcc a b) := fun x hx => (hψ x hx).continuousAt.continuousWithinAt
  have hψ1c : ContinuousOn ψ1 (uIcc a b) := fun x hx => (hψ1 x hx).continuousAt.continuousWithinAt
  have hηc : ContinuousOn η (uIcc a b) := fun x hx => (hη x hx).continuousAt.continuousWithinAt
  have hη1c : ContinuousOn η1 (uIcc a b) := fun x hx => (hη1 x hx).continuousAt.continuousWithinAt
  -- derivative of q = η/ψ
  have hq : ∀ x ∈ uIcc a b, HasDerivAt (fun t => η t / ψ t) (q1 x) x := by
    intro x hx
    have hx0 := hψ0 x hx
    have h := (hη x hx).div (hψ x hx) hx0
    exact h.congr_deriv (by simp only [hq1]; field_simp)
  -- derivative of p = q1/ψ
  have hp : ∀ x ∈ uIcc a b, HasDerivAt (fun t => q1 t / ψ t) (p1 x) x := by
    intro x hx
    have hx0 := hψ0 x hx
    have h1 := (hη1 x hx).div (hψ x hx) hx0
    have h2 := ((hη x hx).mul (hψ1 x hx)).div ((hψ x hx).pow 2) (pow_ne_zero 2 hx0)
    have h := (h1.sub h2).div (hψ x hx) hx0
    exact h.congr_deriv (by
      simp only [hp1, Pi.pow_apply, Pi.div_apply, Pi.mul_apply, Pi.sub_apply]
      push_cast; field_simp; ring)
  have hq1c : ContinuousOn q1 (uIcc a b) := by
    refine (hη1c.div hψc hψ0).sub ((hηc.mul hψ1c).div (hψc.pow 2) fun x hx => pow_ne_zero 2 (hψ0 x hx))
  have hp1c : ContinuousOn p1 (uIcc a b) := by
    have h2 : ∀ x ∈ uIcc a b, ψ x ^ 2 ≠ 0 := fun x hx => pow_ne_zero 2 (hψ0 x hx)
    have h3 : ∀ x ∈ uIcc a b, ψ x ^ 3 ≠ 0 := fun x hx => pow_ne_zero 3 (hψ0 x hx)
    have h4 : ∀ x ∈ uIcc a b, ψ x ^ 4 ≠ 0 := fun x hx => pow_ne_zero 4 (hψ0 x hx)
    exact (((hη2c.div (hψc.pow 2) h2).sub (((continuousOn_const.mul hη1c).mul hψ1c).div (hψc.pow 3) h3)).sub
      ((hηc.mul hψ2c).div (hψc.pow 3) h3)).add
      (((continuousOn_const.mul hηc).mul (hψ1c.pow 2)).div (hψc.pow 4) h4)
  -- first integration by parts
  have step1 : ∫ t in a..b, (η t : ℂ) * Complex.exp (I * φ t) =
      - ∫ t in a..b, (-I * (q1 t : ℂ)) * Complex.exp (I * φ t) := by
    refine integral_mul_cexp_eq_neg_of_antideriv (B := fun t => -I * ((η t / ψ t : ℝ) : ℂ)) hφ ?_ ?_ ?_ ?_ ?_ ?_
    · intro x hx
      exact ((hq x hx).ofReal_comp).const_mul (-I)
    · exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hq1c)
    · exact Complex.continuous_ofReal.comp_continuousOn hηc
    · intro x hx
      have hx0c : ((ψ x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hψ0 x hx)
      push_cast
      rw [show (-I * ((η x : ℂ) / (ψ x : ℂ))) * (I * (ψ x : ℂ))
          = (-(I * I)) * (η x : ℂ) * ((ψ x : ℂ) / (ψ x : ℂ)) by ring, div_self hx0c, Complex.I_mul_I]
      ring
    · simp [hηa]
    · simp [hηb]
  have step2 : ∫ t in a..b, (q1 t : ℂ) * Complex.exp (I * φ t) =
      - ∫ t in a..b, (-I * (p1 t : ℂ)) * Complex.exp (I * φ t) := by
    refine integral_mul_cexp_eq_neg_of_antideriv (B := fun t => -I * ((q1 t / ψ t : ℝ) : ℂ)) hφ ?_ ?_ ?_ ?_ ?_ ?_
    · intro x hx
      exact ((hp x hx).ofReal_comp).const_mul (-I)
    · exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hp1c)
    · exact Complex.continuous_ofReal.comp_continuousOn hq1c
    · intro x hx
      have hx0c : ((ψ x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hψ0 x hx)
      rw [show ((q1 x / ψ x : ℝ) : ℂ) = (q1 x : ℂ) / (ψ x : ℂ) by push_cast; ring]
      rw [show (-I * ((q1 x : ℂ) / (ψ x : ℂ))) * (I * (ψ x : ℂ))
          = (-(I * I)) * (q1 x : ℂ) * ((ψ x : ℂ) / (ψ x : ℂ)) by ring, div_self hx0c, Complex.I_mul_I]
      ring
    · simp [hq1, hηa, hη1a]
    · simp [hq1, hηb, hη1b]
  rw [step1]
  have e1 : (∫ t in a..b, (-I * (q1 t : ℂ)) * Complex.exp (I * φ t)) =
      -I * ∫ t in a..b, (q1 t : ℂ) * Complex.exp (I * φ t) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; ext t; ring
  have e2 : (∫ t in a..b, (-I * (p1 t : ℂ)) * Complex.exp (I * φ t)) =
      -I * ∫ t in a..b, (p1 t : ℂ) * Complex.exp (I * φ t) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; ext t; ring
  rw [e1, step2, e2]
  have : (-(-I * -(-I * ∫ t in a..b, (p1 t : ℂ) * Complex.exp (I * φ t)))) =
      -∫ t in a..b, (p1 t : ℂ) * Complex.exp (I * φ t) := by
    ring_nf; simp [Complex.I_sq]
  rw [this]

theorem abs_div_pow_le {N ψ K μ : ℝ} (k : ℕ) (hμ : 0 < μ) (hψ : μ ≤ |ψ|) (hN : |N| ≤ K) :
    |N / ψ ^ k| ≤ K / μ ^ k := by
  have hK : 0 ≤ K := (abs_nonneg _).trans hN
  have hμk : 0 < μ ^ k := pow_pos hμ k
  have hψk : μ ^ k ≤ |ψ| ^ k := pow_le_pow_left₀ hμ.le hψ k
  rw [abs_div, abs_pow]
  calc |N| / |ψ| ^ k ≤ K / |ψ| ^ k := div_le_div_of_nonneg_right hN (hμk.le.trans hψk)
    _ ≤ K / μ ^ k := div_le_div_of_nonneg_left hK hμk hψk

/-- **Second-order oscillatory bound.**  Under the hypotheses of
`integral_mul_cexp_eq_two_ibp`, with `|ψ| ≥ μ > 0`, `|ψ'|, |ψ''| ≤ ν` and
`|η| ≤ M₀`, `|η'| ≤ M₁`, `|η''| ≤ M₂` on the interval, the oscillatory integral is
`O(1/μ²)` uniformly in the size of the phase. -/
theorem norm_integral_mul_cexp_le_two_ibp {a b μ ν M0 M1 M2 : ℝ} (hab : a ≤ b) (hμ : 0 < μ)
    {φ ψ ψ1 ψ2 η η1 η2 : ℝ → ℝ}
    (hφ : ∀ x ∈ uIcc a b, HasDerivAt φ (ψ x) x)
    (hψ : ∀ x ∈ uIcc a b, HasDerivAt ψ (ψ1 x) x)
    (hψ1 : ∀ x ∈ uIcc a b, HasDerivAt ψ1 (ψ2 x) x)
    (hη : ∀ x ∈ uIcc a b, HasDerivAt η (η1 x) x)
    (hη1 : ∀ x ∈ uIcc a b, HasDerivAt η1 (η2 x) x)
    (hψ2c : ContinuousOn ψ2 (uIcc a b)) (hη2c : ContinuousOn η2 (uIcc a b))
    (hψμ : ∀ x ∈ uIcc a b, μ ≤ |ψ x|)
    (hψ1ν : ∀ x ∈ uIcc a b, |ψ1 x| ≤ ν) (hψ2ν : ∀ x ∈ uIcc a b, |ψ2 x| ≤ ν)
    (hM0 : ∀ x ∈ uIcc a b, |η x| ≤ M0) (hM1 : ∀ x ∈ uIcc a b, |η1 x| ≤ M1)
    (hM2 : ∀ x ∈ uIcc a b, |η2 x| ≤ M2)
    (hηa : η a = 0) (hηb : η b = 0) (hη1a : η1 a = 0) (hη1b : η1 b = 0) :
    ‖∫ t in a..b, (η t : ℂ) * Complex.exp (I * φ t)‖ ≤
      (b - a) * (M2 / μ ^ 2 + (3 * M1 + M0) * ν / μ ^ 3 + 3 * M0 * ν ^ 2 / μ ^ 4) := by
  have hψ0 : ∀ x ∈ uIcc a b, ψ x ≠ 0 := fun x hx h0 => by
    have := hψμ x hx; rw [h0, abs_zero] at this; linarith
  rw [integral_mul_cexp_eq_two_ibp hφ hψ hψ1 hη hη1 hψ2c hη2c hψ0 hηa hηb hη1a hη1b, norm_neg]
  have hbd : ∀ x ∈ Set.uIoc a b, ‖((η2 x / ψ x ^ 2 - 3 * η1 x * ψ1 x / ψ x ^ 3 - η x * ψ2 x / ψ x ^ 3
        + 3 * η x * ψ1 x ^ 2 / ψ x ^ 4 : ℝ) : ℂ) * Complex.exp (I * φ x)‖ ≤
      M2 / μ ^ 2 + (3 * M1 + M0) * ν / μ ^ 3 + 3 * M0 * ν ^ 2 / μ ^ 4 := by
    intro x hx
    have hxI : x ∈ uIcc a b := Set.uIoc_subset_uIcc hx
    have hexp : ‖Complex.exp (I * (φ x : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [norm_mul, hexp, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hν : 0 ≤ ν := (abs_nonneg _).trans (hψ1ν x hxI)
    have hM0' : 0 ≤ M0 := (abs_nonneg _).trans (hM0 x hxI)
    have hM1' : 0 ≤ M1 := (abs_nonneg _).trans (hM1 x hxI)
    have t1 := abs_div_pow_le 2 hμ (hψμ x hxI) (hM2 x hxI)
    have t2 := abs_div_pow_le (N := 3 * η1 x * ψ1 x) (K := 3 * M1 * ν) 3 hμ (hψμ x hxI) (by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hM1 x hxI) (by norm_num)) (hψ1ν x hxI)
        (abs_nonneg _) (by positivity))
    have t3 := abs_div_pow_le (N := η x * ψ2 x) (K := M0 * ν) 3 hμ (hψμ x hxI) (by
      rw [abs_mul]; exact mul_le_mul (hM0 x hxI) (hψ2ν x hxI) (abs_nonneg _) hM0')
    have t4 := abs_div_pow_le (N := 3 * η x * ψ1 x ^ 2) (K := 3 * M0 * ν ^ 2) 4 hμ (hψμ x hxI) (by
      rw [abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 3)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hM0 x hxI) (by norm_num))
        (pow_le_pow_left₀ (abs_nonneg _) (hψ1ν x hxI) 2) (by positivity) (by positivity))
    calc |η2 x / ψ x ^ 2 - 3 * η1 x * ψ1 x / ψ x ^ 3 - η x * ψ2 x / ψ x ^ 3
          + 3 * η x * ψ1 x ^ 2 / ψ x ^ 4|
        ≤ |η2 x / ψ x ^ 2| + |3 * η1 x * ψ1 x / ψ x ^ 3| + |η x * ψ2 x / ψ x ^ 3|
          + |3 * η x * ψ1 x ^ 2 / ψ x ^ 4| := by
          have := abs_add_le (η2 x / ψ x ^ 2 - 3 * η1 x * ψ1 x / ψ x ^ 3 - η x * ψ2 x / ψ x ^ 3)
            (3 * η x * ψ1 x ^ 2 / ψ x ^ 4)
          have h2 := abs_sub (η2 x / ψ x ^ 2 - 3 * η1 x * ψ1 x / ψ x ^ 3) (η x * ψ2 x / ψ x ^ 3)
          have h3 := abs_sub (η2 x / ψ x ^ 2) (3 * η1 x * ψ1 x / ψ x ^ 3)
          linarith
      _ ≤ M2 / μ ^ 2 + 3 * M1 * ν / μ ^ 3 + M0 * ν / μ ^ 3 + 3 * M0 * ν ^ 2 / μ ^ 4 := by
          linarith
      _ = M2 / μ ^ 2 + (3 * M1 + M0) * ν / μ ^ 3 + 3 * M0 * ν ^ 2 / μ ^ 4 := by ring
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h
  linarith

/-- Data of a `C²` cutoff on `[-a, a]` vanishing to first order at both ends. -/
structure Cutoff (a : ℝ) where
  η : ℝ → ℝ
  η1 : ℝ → ℝ
  η2 : ℝ → ℝ
  M0 : ℝ
  M1 : ℝ
  M2 : ℝ
  L1 : ℝ
  hη : ∀ x ∈ uIcc (-a) a, HasDerivAt η (η1 x) x
  hη1 : ∀ x ∈ uIcc (-a) a, HasDerivAt η1 (η2 x) x
  hη2c : ContinuousOn η2 (uIcc (-a) a)
  hM0 : ∀ x ∈ uIcc (-a) a, |η x| ≤ M0
  hM1 : ∀ x ∈ uIcc (-a) a, |η1 x| ≤ M1
  hM2 : ∀ x ∈ uIcc (-a) a, |η2 x| ≤ M2
  hL1 : ∫ t in (-a)..a, ‖(η1 t : ℂ)‖ ≤ L1
  ha0 : η (-a) = 0
  hb0 : η a = 0
  ha1 : η1 (-a) = 0
  hb1 : η1 a = 0

/-- The oscillatory integral `∫_{-a}^{a} η(y) e^{i(ry - κ e^y)} dy`. -/
def osc {a : ℝ} (c : Cutoff a) (r κ : ℝ) : ℂ :=
  ∫ y in (-a)..a, (c.η y : ℂ) * Complex.exp (I * ((r * y - κ * Real.exp y : ℝ) : ℂ))

theorem phase_hasDerivAt (r κ y : ℝ) :
    HasDerivAt (fun y => r * y - κ * Real.exp y) (r - κ * Real.exp y) y := by
  have h := ((hasDerivAt_id y).const_mul r).fun_sub ((Real.hasDerivAt_exp y).const_mul κ)
  simpa using h

theorem phase'_hasDerivAt (r κ y : ℝ) :
    HasDerivAt (fun y => r - κ * Real.exp y) (-(κ * Real.exp y)) y := by
  have h := (hasDerivAt_const y r).fun_sub ((Real.hasDerivAt_exp y).const_mul κ)
  simpa using h

theorem phase''_hasDerivAt (κ y : ℝ) :
    HasDerivAt (fun y => -(κ * Real.exp y)) (-(κ * Real.exp y)) y := by
  have h := ((Real.hasDerivAt_exp y).const_mul κ).fun_neg
  simpa using h

/-- **Non-stationary coefficients.**  If `|r - κ e^y| ≥ μ > 0` on `[-a, a]`, the oscillatory
integral is `O(1/μ²)`, with `ν = |κ| e^a`. -/
theorem norm_osc_le_far {a r κ μ : ℝ} (ha : 0 < a) (c : Cutoff a) (hμ : 0 < μ)
    (hfar : ∀ y ∈ uIcc (-a) a, μ ≤ |r - κ * Real.exp y|) :
    ‖osc c r κ‖ ≤ (2 * a) * (c.M2 / μ ^ 2 + (3 * c.M1 + c.M0) * (|κ| * Real.exp a) / μ ^ 3
      + 3 * c.M0 * (|κ| * Real.exp a) ^ 2 / μ ^ 4) := by
  have hle : -a ≤ a := by linarith
  have hν : ∀ y ∈ uIcc (-a) a, |-(κ * Real.exp y)| ≤ |κ| * Real.exp a := by
    intro y hy
    rw [Set.uIcc_of_le hle] at hy
    rw [abs_neg, abs_mul, abs_of_pos (Real.exp_pos y)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hy.2) (abs_nonneg _)
  have h := norm_integral_mul_cexp_le_two_ibp (φ := fun y => r * y - κ * Real.exp y)
    (ψ := fun y => r - κ * Real.exp y) (ψ1 := fun y => -(κ * Real.exp y))
    (ψ2 := fun y => -(κ * Real.exp y)) hle hμ
    (fun y _ => phase_hasDerivAt r κ y) (fun y _ => phase'_hasDerivAt r κ y)
    (fun y _ => phase''_hasDerivAt κ y) c.hη c.hη1
    ((continuous_const.mul Real.continuous_exp).neg.continuousOn) c.hη2c hfar hν hν
    c.hM0 c.hM1 c.hM2 c.ha0 c.hb0 c.ha1 c.hb1
  have e : a - -a = 2 * a := by ring
  rw [e] at h
  exact h

theorem osc_neg {a : ℝ} (ha : 0 < a) (c : Cutoff a) (r κ : ℝ) :
    osc c (-r) (-κ) = (starRingEnd ℂ) (osc c r κ) := by
  have hle : -a ≤ a := by linarith
  unfold osc
  rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle, ← integral_conj]
  congr 1
  ext y
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 2
  push_cast
  ring

theorem norm_osc_neg {a : ℝ} (ha : 0 < a) (c : Cutoff a) (r κ : ℝ) :
    ‖osc c (-r) (-κ)‖ = ‖osc c r κ‖ := by
  rw [osc_neg ha c, Complex.norm_conj]

/-- **Stationary coefficients (second-derivative test).**  For `κ ≠ 0` the oscillatory integral is
at most `32 L₁ / √(|κ| e^{-a})`, uniformly in `r`. -/
theorem norm_osc_le_vdC {a r κ : ℝ} (ha : 0 < a) (c : Cutoff a) (hκ : κ ≠ 0) :
    ‖osc c r κ‖ ≤ 32 * c.L1 / Real.sqrt (|κ| * Real.exp (-a)) := by
  have hle : -a ≤ a := by linarith
  -- reduce to κ < 0
  suffices key : ∀ r κ : ℝ, κ < 0 → ‖osc c r κ‖ ≤ 32 * c.L1 / Real.sqrt (|κ| * Real.exp (-a)) by
    rcases lt_or_gt_of_ne hκ with hneg | hpos
    · exact key r κ hneg
    · have := key (-r) (-κ) (by linarith)
      rwa [norm_osc_neg ha c, abs_neg] at this
  intro r κ hκneg
  have hmu : 0 < |κ| * Real.exp (-a) := mul_pos (abs_pos.mpr hκneg.ne) (Real.exp_pos _)
  have hI : uIcc (-a) a = Icc (-a) a := Set.uIcc_of_le hle
  have h := RHTower.secondDerivTestOn (a := -a) (b := a) (mu := |κ| * Real.exp (-a)) hle hmu
    (φ := fun y => r * y - κ * Real.exp y) (φ' := fun y => r - κ * Real.exp y)
    (φ'' := fun y => -(κ * Real.exp y)) (A := fun y => (c.η y : ℂ)) (A' := fun y => (c.η1 y : ℂ))
    (fun y _ => phase_hasDerivAt r κ y) (fun y _ => phase'_hasDerivAt r κ y)
    ((continuous_const.mul Real.continuous_exp).neg.continuousOn)
    (fun y hy => (c.hη y (hI ▸ hy)).ofReal_comp)
    (Complex.continuous_ofReal.comp_continuousOn (hI ▸ (fun x hx => (c.hη1 x hx).continuousAt.continuousWithinAt)))
    (fun y hy => by
      have : Real.exp (-a) ≤ Real.exp y := Real.exp_le_exp.mpr hy.1
      rw [abs_of_neg hκneg]
      nlinarith [Real.exp_pos (-a)])
  have hA : ‖(c.η a : ℂ)‖ = 0 := by rw [c.hb0]; simp
  have hA' : ‖(c.η (-a) : ℂ)‖ = 0 := by rw [c.ha0]; simp
  rw [hA, hA', zero_add, zero_add] at h
  unfold osc
  refine h.trans ?_
  have hsq : 0 < Real.sqrt (|κ| * Real.exp (-a)) := Real.sqrt_pos.mpr hmu
  exact div_le_div_of_nonneg_right (by linarith [c.hL1]) hsq.le

/-- The far-field constant: `2a e^{2a} (M₂ + 2e^{2a}(3M₁ + M₀) + 12 e^{4a} M₀)/π²`. -/
def Kfar {a : ℝ} (c : Cutoff a) : ℝ :=
  2 * a * Real.exp (2 * a) *
    (c.M2 + 2 * Real.exp (2 * a) * (3 * c.M1 + c.M0) + 12 * Real.exp (4 * a) * c.M0) / Real.pi ^ 2

/-- **Coefficient bound.**  For `j ≠ 0` and `κ = 2πjX`:
`‖osc‖ ≤ K_far/(j²X²)`, plus `32 L₁/√(2π|j|X e^{-a})` when `|j| < |r| e^a/(πX)`. -/
theorem norm_osc_le_coeff {a X r : ℝ} (ha : 0 < a) (c : Cutoff a) (hX : 0 < X) {j : ℤ}
    (hj : j ≠ 0) :
    ‖osc c r (2 * Real.pi * j * X)‖ ≤ Kfar c / ((j : ℝ) ^ 2 * X ^ 2)
      + (if |(j : ℝ)| < |r| * Real.exp a / (Real.pi * X) then
          32 * c.L1 / Real.sqrt (2 * Real.pi * |(j : ℝ)| * X * Real.exp (-a)) else 0) := by
  have hle : -a ≤ a := by linarith
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  have hjpos : 0 < |(j : ℝ)| := abs_pos.mpr hjR
  have hπ := Real.pi_pos
  have hM0 : 0 ≤ c.M0 := (abs_nonneg _).trans (c.hM0 a Set.right_mem_uIcc)
  have hM1 : 0 ≤ c.M1 := (abs_nonneg _).trans (c.hM1 a Set.right_mem_uIcc)
  have hM2 : 0 ≤ c.M2 := (abs_nonneg _).trans (c.hM2 a Set.right_mem_uIcc)
  have hKfar : 0 ≤ Kfar c := by unfold Kfar; positivity
  have hfar0 : 0 ≤ Kfar c / ((j : ℝ) ^ 2 * X ^ 2) := by positivity
  have hκabs : |2 * Real.pi * (j : ℝ) * X| = 2 * Real.pi * |(j : ℝ)| * X := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hπ, abs_of_pos hX, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  split_ifs with hnear
  · -- stationary range: second-derivative test
    have hκ : 2 * Real.pi * (j : ℝ) * X ≠ 0 := by positivity
    have h := norm_osc_le_vdC (r := r) ha c hκ
    rw [hκabs] at h
    linarith
  · -- far range
    push Not at hnear
    set μ := Real.pi * |(j : ℝ)| * X * Real.exp (-a) with hμdef
    have hμ : 0 < μ := by positivity
    have hr : |r| ≤ μ := by
      have h1 : |r| * Real.exp a ≤ |(j : ℝ)| * (Real.pi * X) := by
        have := (div_le_iff₀ (by positivity : (0:ℝ) < Real.pi * X)).mp hnear
        linarith
      have he : Real.exp a * Real.exp (-a) = 1 := by rw [← Real.exp_add]; simp
      calc |r| = |r| * Real.exp a * Real.exp (-a) := by rw [mul_assoc, he, mul_one]
        _ ≤ |(j : ℝ)| * (Real.pi * X) * Real.exp (-a) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = μ := by rw [hμdef]; ring
    have hfar : ∀ y ∈ uIcc (-a) a, μ ≤ |r - 2 * Real.pi * (j : ℝ) * X * Real.exp y| := by
      intro y hy
      rw [Set.uIcc_of_le hle] at hy
      have hey : Real.exp (-a) ≤ Real.exp y := Real.exp_le_exp.mpr hy.1
      have hbig : 2 * μ ≤ |2 * Real.pi * (j : ℝ) * X * Real.exp y| := by
        rw [abs_mul, hκabs, abs_of_pos (Real.exp_pos y), hμdef]
        have : 0 ≤ 2 * Real.pi * |(j : ℝ)| * X := by positivity
        nlinarith
      have := abs_sub_abs_le_abs_sub (2 * Real.pi * (j : ℝ) * X * Real.exp y) r
      rw [abs_sub_comm] at this
      linarith
    have h := norm_osc_le_far ha c hμ hfar
    rw [hκabs] at h
    have hν : 2 * Real.pi * |(j : ℝ)| * X * Real.exp a = 2 * Real.exp (2 * a) * μ := by
      rw [hμdef]
      have : Real.exp (2 * a) * Real.exp (-a) = Real.exp a := by rw [← Real.exp_add]; ring_nf
      linear_combination (-(2 * Real.pi * |(j : ℝ)| * X)) * this
    rw [hν] at h
    have hval : (2 * a) * (c.M2 / μ ^ 2 + (3 * c.M1 + c.M0) * (2 * Real.exp (2 * a) * μ) / μ ^ 3
        + 3 * c.M0 * (2 * Real.exp (2 * a) * μ) ^ 2 / μ ^ 4) = Kfar c / ((j : ℝ) ^ 2 * X ^ 2) := by
      have he4 : Real.exp (4 * a) = Real.exp (2 * a) ^ 2 := by
        rw [← Real.exp_nat_mul]; ring_nf
      have hμ2 : μ ^ 2 = Real.pi ^ 2 * (j : ℝ) ^ 2 * X ^ 2 / Real.exp (2 * a) := by
        rw [hμdef]
        have hea : Real.exp (-a) ^ 2 = 1 / Real.exp (2 * a) := by
          rw [← Real.exp_nat_mul, one_div, ← Real.exp_neg]; ring_nf
        rw [mul_pow, mul_pow, mul_pow, sq_abs, hea]; ring
      have step1 : (2 * a) * (c.M2 / μ ^ 2 + (3 * c.M1 + c.M0) * (2 * Real.exp (2 * a) * μ) / μ ^ 3
          + 3 * c.M0 * (2 * Real.exp (2 * a) * μ) ^ 2 / μ ^ 4)
          = 2 * a * (c.M2 + 2 * Real.exp (2 * a) * (3 * c.M1 + c.M0)
              + 12 * Real.exp (2 * a) ^ 2 * c.M0) / μ ^ 2 := by
        field_simp; ring
      rw [step1, hμ2]
      unfold Kfar
      rw [he4]
      have hE : 0 < Real.exp (2 * a) := Real.exp_pos _
      field_simp
    rw [hval] at h
    linarith

/-- Height threshold `T = |r| e^a/(πX)` of the stationary range. -/
def thr (a X r : ℝ) : ℝ := |r| * Real.exp a / (Real.pi * X)

/-- The stationary-range coefficient bound, indexed by `n = |j|`. -/
def nearB {a : ℝ} (c : Cutoff a) (X r : ℝ) (n : ℕ) : ℝ :=
  if (n : ℝ) < thr a X r then 32 * c.L1 / Real.sqrt (2 * Real.pi * n * X * Real.exp (-a)) else 0

/-- The total bound for the coefficient sum. -/
def Bnd {a : ℝ} (c : Cutoff a) (X r : ℝ) : ℝ :=
  4 * Kfar c / X ^ 2 + (if 1 < thr a X r then
    4 * (32 * c.L1 / Real.sqrt (2 * Real.pi * X * Real.exp (-a))) * Real.sqrt (thr a X r) else 0)

theorem Cutoff.L1_nonneg {a : ℝ} (ha : 0 < a) (c : Cutoff a) : 0 ≤ c.L1 :=
  le_trans (intervalIntegral.integral_nonneg (by linarith) (fun _ _ => norm_nonneg _)) c.hL1

theorem Cutoff.M_nonneg {a : ℝ} (c : Cutoff a) : 0 ≤ c.M0 ∧ 0 ≤ c.M1 ∧ 0 ≤ c.M2 :=
  ⟨(abs_nonneg _).trans (c.hM0 a Set.right_mem_uIcc), (abs_nonneg _).trans (c.hM1 a Set.right_mem_uIcc),
    (abs_nonneg _).trans (c.hM2 a Set.right_mem_uIcc)⟩

theorem Kfar_nonneg {a : ℝ} (ha : 0 < a) (c : Cutoff a) : 0 ≤ Kfar c := by
  obtain ⟨h0, h1, h2⟩ := c.M_nonneg
  unfold Kfar; positivity

theorem nearB_nonneg {a : ℝ} (ha : 0 < a) (c : Cutoff a) (X r : ℝ) (n : ℕ) : 0 ≤ nearB c X r n := by
  unfold nearB
  split_ifs
  · have := c.L1_nonneg ha; positivity
  · exact le_rfl

/-- `Σ_{0<n<M} nearB(n) ≤ 2C√T` when `T > 1`, and `0` otherwise. -/
theorem sum_nearB_le {a X r : ℝ} (ha : 0 < a) (c : Cutoff a) (hX : 0 < X) (M : ℕ) :
    ∑ n ∈ Finset.Ioo 0 M, nearB c X r n ≤
      (if 1 < thr a X r then
        2 * (32 * c.L1 / Real.sqrt (2 * Real.pi * X * Real.exp (-a))) * Real.sqrt (thr a X r) else 0) := by
  have hL1 := c.L1_nonneg ha
  set C := 32 * c.L1 / Real.sqrt (2 * Real.pi * X * Real.exp (-a)) with hC
  have hC0 : 0 ≤ C := by positivity
  have hterm : ∀ n ∈ Finset.Ioo 0 M, nearB c X r n ≤
      (if (n : ℝ) < thr a X r then C * (1 / Real.sqrt n) else 0) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioo.mp hn).1
    unfold nearB
    split_ifs with h1
    · rw [hC]
      have hsplit : Real.sqrt (2 * Real.pi * n * X * Real.exp (-a))
          = Real.sqrt n * Real.sqrt (2 * Real.pi * X * Real.exp (-a)) := by
        rw [← Real.sqrt_mul (by positivity)]; ring_nf
      rw [hsplit]
      have hs1 : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
      have hs2 : 0 < Real.sqrt (2 * Real.pi * X * Real.exp (-a)) := Real.sqrt_pos.mpr (by positivity)
      rw [div_mul_div_comm, mul_one, mul_comm (Real.sqrt n)]
    · exact le_rfl
  refine (Finset.sum_le_sum hterm).trans ?_
  split_ifs with hT
  · -- the indicator sum is a sum over `1 ≤ n ≤ ⌊T⌋`
    have hsub : ∑ n ∈ Finset.Ioo 0 M, (if (n : ℝ) < thr a X r then C * (1 / Real.sqrt n) else 0)
        ≤ ∑ n ∈ Finset.Icc 1 ⌊thr a X r⌋₊, C * (1 / Real.sqrt n) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        simp only [Finset.mem_filter, Finset.mem_Ioo] at hn
        simp only [Finset.mem_Icc]
        exact ⟨hn.1.1, Nat.le_floor hn.2.le⟩
      · intro n _ _; positivity
    refine hsub.trans ?_
    rw [← Finset.mul_sum]
    have h1 := RHTower.sum_one_div_sqrt_le ⌊thr a X r⌋₊
    have h2 : Real.sqrt (⌊thr a X r⌋₊ : ℝ) ≤ Real.sqrt (thr a X r) :=
      Real.sqrt_le_sqrt (Nat.floor_le (by linarith))
    calc C * ∑ n ∈ Finset.Icc 1 ⌊thr a X r⌋₊, 1 / Real.sqrt n
        ≤ C * (2 * Real.sqrt (thr a X r)) :=
          mul_le_mul_of_nonneg_left (h1.trans (by linarith)) hC0
      _ = 2 * C * Real.sqrt (thr a X r) := by ring
  · -- no `n ≥ 1` lies strictly below a threshold `≤ 1`
    refine (Finset.sum_le_sum (g := fun _ => (0:ℝ)) ?_).trans (by simp)
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioo.mp hn).1
    rw [if_neg (by push Not at hT; linarith)]

/-- A sum over nonzero integers of a function of `|j|` is at most twice any uniform bound on its
partial sums over `0 < n < M`. -/
theorem sum_int_natAbs_le {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) {B : ℝ}
    (hB : ∀ M : ℕ, ∑ n ∈ Finset.Ioo 0 M, g n ≤ B) (s : Finset ℤ) :
    ∑ j ∈ s with j ≠ 0, g j.natAbs ≤ 2 * B := by
  classical
  set M := s.sup Int.natAbs + 1 with hM
  have hbound : ∀ t : Finset ℤ, t ⊆ s → (∀ j ∈ t, j ≠ 0) → Set.InjOn Int.natAbs (t : Set ℤ) →
      ∑ j ∈ t, g j.natAbs ≤ B := by
    intro t hts hne hinj
    rw [← Finset.sum_image hinj]
    refine le_trans ?_ (hB M)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
      simp only [Finset.mem_Ioo]
      refine ⟨Int.natAbs_pos.mpr (hne j hj), ?_⟩
      have := Finset.le_sup (f := Int.natAbs) (hts hj)
      omega
    · intro n _ _; exact hg n
  rw [← Finset.sum_filter_add_sum_filter_not (s.filter (· ≠ 0)) (fun j => 0 < j)]
  have h1 := hbound ((s.filter (· ≠ 0)).filter (fun j => 0 < j))
    (fun j hj => (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1)
    (fun j hj => (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2)
    (by
      intro i hi j hj hij
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      omega)
  have h2 := hbound ((s.filter (· ≠ 0)).filter (fun j => ¬ 0 < j))
    (fun j hj => (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1)
    (fun j hj => (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2)
    (by
      intro i hi j hj hij
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      have hi0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
      have hj0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
      simp only [Finset.mem_coe] at *
      omega)
  linarith

/-- **Coefficient sum bound.**  Every finite partial sum of `‖osc c r (2πjX)‖` over nonzero `j`
is at most `Bnd c X r = 4K_far/X² + [T > 1]·4C√T`. -/
theorem sum_norm_osc_le {a X r : ℝ} (ha : 0 < a) (c : Cutoff a) (hX : 0 < X) (s : Finset ℤ) :
    ∑ j ∈ s with j ≠ 0, ‖osc c r (2 * Real.pi * j * X)‖ ≤ Bnd c X r := by
  set g : ℕ → ℝ := fun n => Kfar c / ((n : ℝ) ^ 2 * X ^ 2) + nearB c X r n with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => add_nonneg (by have := Kfar_nonneg ha c; positivity)
    (nearB_nonneg ha c X r n)
  have hterm : ∀ j ∈ s.filter (· ≠ 0), ‖osc c r (2 * Real.pi * j * X)‖ ≤ g j.natAbs := by
    intro j hj
    have hj0 := (Finset.mem_filter.mp hj).2
    have hcast : ((j.natAbs : ℕ) : ℝ) = |(j : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    have h := norm_osc_le_coeff (r := r) ha c hX hj0
    simp only [hg, nearB, thr, hcast]
    have hsq : ((j : ℝ)) ^ 2 = |(j : ℝ)| ^ 2 := (sq_abs _).symm
    rw [← hsq]
    exact h
  refine (Finset.sum_le_sum hterm).trans ?_
  have hB : ∀ M : ℕ, ∑ n ∈ Finset.Ioo 0 M, g n ≤
      2 * Kfar c / X ^ 2 + (if 1 < thr a X r then
        2 * (32 * c.L1 / Real.sqrt (2 * Real.pi * X * Real.exp (-a))) * Real.sqrt (thr a X r) else 0) := by
    intro M
    rw [Finset.sum_add_distrib]
    have hfar : ∑ n ∈ Finset.Ioo 0 M, Kfar c / ((n : ℝ) ^ 2 * X ^ 2) ≤ 2 * Kfar c / X ^ 2 := by
      have hK := Kfar_nonneg ha c
      have hs := sum_Ioo_inv_sq_le (α := ℝ) 0 M
      simp only [Nat.cast_zero, zero_add, div_one] at hs
      calc ∑ n ∈ Finset.Ioo 0 M, Kfar c / ((n : ℝ) ^ 2 * X ^ 2)
          = (Kfar c / X ^ 2) * ∑ n ∈ Finset.Ioo 0 M, ((n : ℝ) ^ 2)⁻¹ := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => ?_; field_simp
        _ ≤ (Kfar c / X ^ 2) * 2 := mul_le_mul_of_nonneg_left hs (by positivity)
        _ = 2 * Kfar c / X ^ 2 := by ring
    linarith [sum_nearB_le (r := r) ha c hX M]
  have := sum_int_natAbs_le hg0 hB s
  unfold Bnd
  split_ifs at this ⊢ <;> exact this.trans (le_of_eq (by ring))

/-- The function with spectral density `F`: `h(y) = ∫ F(r) e^{iry} dr`. -/
def specFn (F : ℝ → ℂ) (y : ℝ) : ℂ := ∫ r, F r * Complex.exp (I * ((r * y : ℝ) : ℂ))

theorem continuous_specFn {F : ℝ → ℂ} (hF : Integrable F) : Continuous (specFn F) := by
  unfold specFn
  refine continuous_of_dominated (bound := fun r => ‖F r‖) ?_ ?_ hF.norm ?_
  · intro y
    refine hF.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)
    exact Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)))
  · intro y
    refine Filter.Eventually.of_forall fun r => ?_
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  · refine Filter.Eventually.of_forall fun r => ?_
    exact continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id))))

/-- Transport to the integer lattice: `H(x) = h(log(x/X))·X/x` for `x > 0`, and `0` otherwise. -/
def transported (h : ℝ → ℂ) (X x : ℝ) : ℂ :=
  if 0 < x then h (Real.log (x / X)) * ((X / x : ℝ) : ℂ) else 0

section Transport

variable {h : ℝ → ℂ} {X W : ℝ}

theorem transported_eq_zero_of_lt (hX : 0 < X) (hW0 : 0 ≤ W) (hsupp : ∀ y, W < |y| → h y = 0)
    {x : ℝ} (hx : x < X * Real.exp (-W)) : transported h X x = 0 := by
  unfold transported
  split_ifs with hpos
  · have hlog : Real.log (x / X) < -W := by
      rw [Real.log_lt_iff_lt_exp (div_pos hpos hX), div_lt_iff₀ hX]; linarith
    have hW : W < |Real.log (x / X)| := by
      rw [abs_of_neg (by linarith)]; linarith
    rw [hsupp _ hW, zero_mul]
  · rfl

theorem transported_eq_zero_of_gt (hX : 0 < X) (hW0 : 0 ≤ W) (hsupp : ∀ y, W < |y| → h y = 0)
    {x : ℝ} (hx : X * Real.exp W < x) : transported h X x = 0 := by
  have hpos : 0 < x := lt_trans (by positivity) hx
  unfold transported
  rw [if_pos hpos]
  have hlog : W < Real.log (x / X) := by
    rw [Real.lt_log_iff_exp_lt (div_pos hpos hX), lt_div_iff₀ hX]; linarith
  have hW : W < |Real.log (x / X)| := by
    rw [abs_of_pos (by linarith)]; exact hlog
  rw [hsupp _ hW, zero_mul]

theorem continuous_transported (hX : 0 < X) (hW0 : 0 ≤ W) (hsupp : ∀ y, W < |y| → h y = 0)
    (hc : Continuous h) : Continuous (transported h X) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_or_ge x (X * Real.exp (-W)) with hlt | hge
  · -- zero on a neighbourhood
    have hev : transported h X =ᶠ[nhds x] fun _ => 0 :=
      Filter.eventually_of_mem (Iio_mem_nhds hlt) fun y hy =>
        transported_eq_zero_of_lt hX hW0 hsupp hy
    exact (continuousAt_const).congr hev.symm
  · have hpos : 0 < x := lt_of_lt_of_le (by positivity) hge
    have hev : transported h X =ᶠ[nhds x]
        fun y => h (Real.log (y / X)) * ((X / y : ℝ) : ℂ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hpos) fun y hy => by
        unfold transported; rw [if_pos (show (0:ℝ) < y from hy)]
    refine ContinuousAt.congr ?_ hev.symm
    have hlogc : ContinuousAt (fun y => Real.log (y / X)) x :=
      ContinuousAt.comp (f := fun y : ℝ => y / X) (g := Real.log)
        (Real.continuousAt_log (div_pos hpos hX).ne') (continuousAt_id.div_const X)
    exact (hc.continuousAt.comp hlogc).mul
      (Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.div continuousAt_id hpos.ne'))

theorem transported_int_eq_zero
    (hvan : ∀ n : ℕ, 1 ≤ n → h (Real.log (n / X)) = 0) (n : ℤ) :
    transported h X n = 0 := by
  unfold transported
  split_ifs with hpos
  · have hn : (1 : ℤ) ≤ n := by exact_mod_cast hpos
    have hnat : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (by omega)
    have := hvan n.toNat (by omega)
    rw [hnat] at this
    rw [this, zero_mul]
  · rfl

theorem exp_mul_transported (hX : 0 < X) (y : ℝ) :
    ((X * Real.exp y : ℝ) : ℂ) * transported h X (X * Real.exp y) = (X : ℂ) * h y := by
  have hpos : 0 < X * Real.exp y := by positivity
  unfold transported
  rw [if_pos hpos]
  have hlog : Real.log (X * Real.exp y / X) = y := by
    rw [show X * Real.exp y / X = Real.exp y by field_simp, Real.log_exp]
  rw [hlog]
  have hne : (X * Real.exp y : ℝ) ≠ 0 := hpos.ne'
  push_cast
  field_simp

end Transport

/-- **Fourier coefficients after transport.**  With `0 ≤ W < a`,
`𝓕H(w) = ∫_{-a}^{a} X h(y) e^{-2πi X e^y w} dy`. -/
theorem fourier_transported_eq {a : ℝ} (hX : 0 < X) (hW0 : 0 ≤ W) (hWa : W < a)
    (hsupp : ∀ y, W < |y| → h y = 0) (hc : Continuous h) (w : ℝ) :
    FourierTransform.fourier (transported h X) w =
      ∫ y in (-a)..a, Complex.exp (((-2 * Real.pi * (X * Real.exp y) * w : ℝ) : ℂ) * I)
        * ((X : ℂ) * h y) := by
  have hle : -a ≤ a := by linarith
  set G : ℝ → ℂ := fun v => Complex.exp (((-2 * Real.pi * v * w : ℝ) : ℂ) * I) * transported h X v
    with hG
  have hGc : Continuous G := by
    refine Continuous.mul ?_ (continuous_transported hX hW0 hsupp hc)
    exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      ((continuous_const.mul continuous_id).mul continuous_const)).mul continuous_const)
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hlo : X * Real.exp (-a) ≤ X * Real.exp a :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) hX.le
  have hzero : ∀ v ∉ Set.Ioc (X * Real.exp (-a)) (X * Real.exp a), G v = 0 := by
    intro v hv
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hv
    simp only [hG]
    rcases hv with h1 | h1
    · rw [transported_eq_zero_of_lt hX hW0 hsupp (lt_of_le_of_lt h1
        (mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by linarith)) hX)), mul_zero]
    · rw [transported_eq_zero_of_gt hX hW0 hsupp (lt_trans
        (mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hWa) hX) h1), mul_zero]
  have hfull : (∫ v, G v) = ∫ v in (X * Real.exp (-a))..(X * Real.exp a), G v := by
    rw [intervalIntegral.integral_of_le hlo, setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  simp only [smul_eq_mul]
  change (∫ v, G v) = _
  rw [hfull]
  have hsub := intervalIntegral.integral_deriv_smul_comp (a := -a) (b := a)
    (f := fun y => X * Real.exp y) (f' := fun y => X * Real.exp y) (g := G)
    (fun y _ => by simpa using (Real.hasDerivAt_exp y).const_mul X)
    ((continuous_const.mul Real.continuous_exp).continuousOn) hGc
  rw [← hsub]
  refine intervalIntegral.integral_congr fun y _ => ?_
  simp only [hG, Function.comp]
  rw [Complex.real_smul]
  have e := exp_mul_transported (h := h) hX y
  calc ((X * Real.exp y : ℝ) : ℂ) * (Complex.exp (((-2 * Real.pi * (X * Real.exp y) * w : ℝ) : ℂ) * I)
        * transported h X (X * Real.exp y))
      = Complex.exp (((-2 * Real.pi * (X * Real.exp y) * w : ℝ) : ℂ) * I)
        * (((X * Real.exp y : ℝ) : ℂ) * transported h X (X * Real.exp y)) := by ring
    _ = _ := by rw [e]

/-- **Spectral form of the transported coefficients (Fubini).** -/
theorem fourier_transported_specFn {a : ℝ} (c : Cutoff a) {F : ℝ → ℂ} (hF : Integrable F)
    (hX : 0 < X) (hW0 : 0 ≤ W) (hWa : W < a) (hη1 : ∀ y, |y| ≤ W → c.η y = 1)
    (hsupp : ∀ y, W < |y| → specFn F y = 0) (w : ℝ) :
    FourierTransform.fourier (transported (specFn F) X) w =
      (X : ℂ) * ∫ r, F r * osc c r (2 * Real.pi * w * X) := by
  have hle : -a ≤ a := by linarith
  rw [fourier_transported_eq hX hW0 hWa hsupp (continuous_specFn hF) w]
  -- insert the cutoff
  have hcut : ∀ y, (c.η y : ℂ) * specFn F y = specFn F y := by
    intro y
    by_cases hy : |y| ≤ W
    · rw [hη1 y hy]; simp
    · push Not at hy; rw [hsupp y hy, mul_zero]
  set P : ℝ → ℂ := fun y => Complex.exp (((-2 * Real.pi * (X * Real.exp y) * w : ℝ) : ℂ) * I)
    with hP
  have step1 : (∫ y in (-a)..a, P y * ((X : ℂ) * specFn F y))
      = (X : ℂ) * ∫ y in Set.Ioc (-a) a, ∫ r, (c.η y : ℂ) * F r *
          Complex.exp (I * ((r * y : ℝ) : ℂ)) * P y := by
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
    rw [← hcut y]
    simp only [specFn]
    rw [← MeasureTheory.integral_const_mul]
    have e : (∫ r, (c.η y : ℂ) * F r * Complex.exp (I * ((r * y : ℝ) : ℂ)) * P y)
        = (∫ r, (c.η y : ℂ) * (F r * Complex.exp (I * ((r * y : ℝ) : ℂ)))) * P y := by
      rw [← MeasureTheory.integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
      ring
    rw [e]
    ring
  rw [step1]
  congr 1
  -- Fubini
  have hηmeas : AEStronglyMeasurable (fun y => (c.η y : ℂ)) (volume.restrict (Set.Ioc (-a) a)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    intro y hy
    have hy' : y ∈ uIcc (-a) a := by rw [Set.uIcc_of_le hle]; exact Set.Ioc_subset_Icc_self hy
    exact (c.hη y hy').continuousAt.continuousWithinAt
  have hint : Integrable (Function.uncurry fun y r => (c.η y : ℂ) * F r *
      Complex.exp (I * ((r * y : ℝ) : ℂ)) * P y) ((volume.restrict (Set.Ioc (-a) a)).prod volume) := by
    have hηint : Integrable (fun y => ‖(c.η y : ℂ)‖) (volume.restrict (Set.Ioc (-a) a)) := by
      have hcont : ContinuousOn (fun y => ‖(c.η y : ℂ)‖) (Set.Icc (-a) a) := by
        refine continuous_norm.comp_continuousOn (Complex.continuous_ofReal.comp_continuousOn ?_)
        intro y hy
        have hy' : y ∈ uIcc (-a) a := by rw [Set.uIcc_of_le hle]; exact hy
        exact (c.hη y hy').continuousAt.continuousWithinAt
      exact (hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    have hdom : Integrable (fun z : ℝ × ℝ => ‖(c.η z.1 : ℂ)‖ * ‖F z.2‖)
        ((volume.restrict (Set.Ioc (-a) a)).prod volume) :=
      hηint.mul_prod hF.norm
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine ((hηmeas.comp_fst.mul hF.aestronglyMeasurable.comp_snd).mul ?_).mul ?_
      · exact (Continuous.aestronglyMeasurable (Complex.continuous_exp.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_snd.mul continuous_fst)))))
      · exact (Continuous.aestronglyMeasurable (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp (((continuous_const.mul (continuous_const.mul
            (Real.continuous_exp.comp continuous_fst)))).mul continuous_const)).mul continuous_const)))
    · rcases z with ⟨y, r⟩
      simp only [Function.uncurry_apply_pair, hP]
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, Complex.norm_exp_ofReal_mul_I]
      simp
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only [osc]
  rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hP]
  have : Complex.exp (I * ((r * y : ℝ) : ℂ)) *
      Complex.exp (((-2 * Real.pi * (X * Real.exp y) * w : ℝ) : ℂ) * I)
      = Complex.exp (I * ((r * y - 2 * Real.pi * w * X * Real.exp y : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  calc (c.η y : ℂ) * F r * Complex.exp (I * ((r * y : ℝ) : ℂ)) *
        Complex.exp (((-2 * Real.pi * (X * Real.exp y) * w : ℝ) : ℂ) * I)
      = F r * ((c.η y : ℂ) * (Complex.exp (I * ((r * y : ℝ) : ℂ)) *
        Complex.exp (((-2 * Real.pi * (X * Real.exp y) * w : ℝ) : ℂ) * I))) := by ring
    _ = _ := by rw [this]

theorem continuous_osc {a : ℝ} (ha : 0 < a) (c : Cutoff a) (κ : ℝ) :
    Continuous fun r => osc c r κ := by
  have hle : -a ≤ a := by linarith
  have hcont : ContinuousOn (fun y => (c.η y : ℂ)) (Set.Icc (-a) a) := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    intro y hy
    have hy' : y ∈ uIcc (-a) a := by rw [Set.uIcc_of_le hle]; exact hy
    exact (c.hη y hy').continuousAt.continuousWithinAt
  have hηint : Integrable (fun y => ‖(c.η y : ℂ)‖) (volume.restrict (Set.Ioc (-a) a)) :=
    ((continuous_norm.comp_continuousOn hcont).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  unfold osc
  simp only [intervalIntegral.integral_of_le hle]
  refine continuous_of_dominated (bound := fun y => ‖(c.η y : ℂ)‖) ?_ ?_ hηint ?_
  · intro r
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine (hcont.mono Set.Ioc_subset_Icc_self).mul ?_
    exact (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_const.mul continuous_id).sub (continuous_const.mul Real.continuous_exp))))).continuousOn
  · intro r
    refine Filter.Eventually.of_forall fun y => ?_
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  · refine Filter.Eventually.of_forall fun y => ?_
    exact continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp ((continuous_id.mul continuous_const).sub continuous_const))))

theorem norm_osc_le_const {a : ℝ} (ha : 0 < a) (c : Cutoff a) (r κ : ℝ) :
    ‖osc c r κ‖ ≤ c.M0 * (2 * a) := by
  have hle : -a ≤ a := by linarith
  unfold osc
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -a) (b := a) (C := c.M0)
    (f := fun y => (c.η y : ℂ) * Complex.exp (I * ((r * y - κ * Real.exp y : ℝ) : ℂ))) (by
      intro y hy
      rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact c.hM0 y (Set.uIoc_subset_uIcc hy))
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ a - -a)] at h
  linarith

/-- **Log-lattice Poisson anti-concentration.**  Let `h = specFn F` be supported in `[-W, W]`, with
`F` integrable, and suppose `h(log(n/X)) = 0` for every integer `n ≥ 1`.  For any `C²` cutoff `η` on
`[-a, a]` (`W < a`) equal to `1` on `[-W, W]`:
`‖∫ h‖ ≤ ∫ ‖F(r)‖·(4K_far/X² + [|r| e^a/(πX) > 1]·4C√(|r| e^a/(πX))) dr`,
where `C = 32 L₁/√(2πX e^{-a})`. -/
theorem norm_integral_le_of_vanish_logLattice {a W X : ℝ} (ha : 0 < a) (c : Cutoff a)
    {F : ℝ → ℂ} (hF : Integrable F) (hFB : Integrable (fun r => ‖F r‖ * Bnd c X r))
    (hX : 0 < X) (hW0 : 0 ≤ W) (hWa : W < a) (hη1 : ∀ y, |y| ≤ W → c.η y = 1)
    (hsupp : ∀ y, W < |y| → specFn F y = 0)
    (hvan : ∀ n : ℕ, 1 ≤ n → specFn F (Real.log (n / X)) = 0) :
    ‖∫ y, specFn F y‖ ≤ ∫ r, ‖F r‖ * Bnd c X r := by
  classical
  have hle : -a ≤ a := by linarith
  set H := transported (specFn F) X with hH
  have hHc : Continuous H := continuous_transported hX hW0 hsupp (continuous_specFn hF)
  -- coefficients in spectral form
  have hcoef : ∀ j : ℤ, FourierTransform.fourier H j =
      (X : ℂ) * ∫ r, F r * osc c r (2 * Real.pi * j * X) := fun j =>
    fourier_transported_specFn c hF hX hW0 hWa hη1 hsupp (j : ℝ)
  have hint_j : ∀ κ : ℝ, Integrable (fun r => ‖osc c r κ‖ * ‖F r‖) := by
    intro κ
    refine hF.norm.bdd_mul (c := c.M0 * (2 * a)) ((continuous_osc ha c κ).norm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun r => ?_)
    simp only [norm_norm]; exact norm_osc_le_const ha c r κ
  have hnorm_j : ∀ j : ℤ, ‖FourierTransform.fourier H j‖ ≤
      X * ∫ r, ‖osc c r (2 * Real.pi * j * X)‖ * ‖F r‖ := by
    intro j
    rw [hcoef j, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX]
    refine mul_le_mul_of_nonneg_left ?_ hX.le
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [norm_mul]; ring
  -- partial sums over nonzero frequencies
  have hpartial : ∀ u : Finset ℤ, ∑ j ∈ u with j ≠ 0, ‖FourierTransform.fourier H j‖ ≤
      X * ∫ r, ‖F r‖ * Bnd c X r := by
    intro u
    refine (Finset.sum_le_sum fun j _ => hnorm_j j).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hX.le
    rw [← integral_finsetSum _ (fun j _ => hint_j _)]
    refine integral_mono (integrable_finsetSum _ (fun j _ => hint_j _)) hFB
      (fun r => ?_)
    simp only
    rw [← Finset.sum_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (sum_norm_osc_le (r := r) ha c hX u) (norm_nonneg _)
  set B := X * ∫ r, ‖F r‖ * Bnd c X r with hBdef
  set f : ℤ → ℂ := fun j => FourierTransform.fourier H j with hf
  -- summability of the coefficients
  have hsumnorm : Summable fun j => ‖f j‖ := by
    refine summable_of_sum_le (c := ‖f 0‖ + B) (fun j => norm_nonneg _) (fun u => ?_)
    rw [← Finset.sum_filter_add_sum_filter_not u (fun j => j ≠ 0)]
    have h0 : ∑ j ∈ u with ¬ j ≠ 0, ‖f j‖ ≤ ‖f 0‖ := by
      have hsub : u.filter (fun j => ¬ j ≠ 0) ⊆ {0} := by
        intro j hj; simp only [Finset.mem_filter, not_not] at hj; simp [hj.2]
      calc ∑ j ∈ u with ¬ j ≠ 0, ‖f j‖ ≤ ∑ j ∈ ({0} : Finset ℤ), ‖f j‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
        _ = ‖f 0‖ := by simp
    have h1 := hpartial u
    linarith
  have hsum : Summable f := hsumnorm.of_norm
  -- decay of the transported function (compact support)
  have hBigO : H =O[Filter.cocompact ℝ] fun x => |x| ^ (-(2 : ℝ)) := by
    have hev : H =ᶠ[Filter.cocompact ℝ] fun _ => 0 := by
      refine Filter.eventually_of_mem
        (isCompact_Icc (a := X * Real.exp (-W)) (b := X * Real.exp W)).compl_mem_cocompact ?_
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with h1 | h1
      · exact transported_eq_zero_of_lt hX hW0 hsupp h1
      · exact transported_eq_zero_of_gt hX hW0 hsupp h1
    exact (Asymptotics.isBigO_zero _ _).congr' hev.symm (Filter.EventuallyEq.refl _ _)
  -- Poisson summation at 0
  have hpois := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hHc (by norm_num : (1:ℝ) < 2)
    hBigO hsum 0
  have hlhs : ∑' n : ℤ, H (0 + n) = 0 := by
    have : ∀ n : ℤ, H (0 + n) = 0 := fun n => by
      rw [zero_add]; exact transported_int_eq_zero hvan n
    calc ∑' n : ℤ, H (0 + n) = ∑' _ : ℤ, (0 : ℂ) := tsum_congr this
      _ = 0 := tsum_zero
  have hrhs : ∑' n : ℤ, FourierTransform.fourier H n * (fourier n) ((0 : ℝ) : UnitAddCircle)
      = ∑' n : ℤ, f n := by
    refine tsum_congr fun n => ?_
    rw [fourier_coe_apply]; simp [hf]
  rw [hlhs, hrhs] at hpois
  -- isolate the zeroth coefficient
  have hsplit := hsum.tsum_eq_add_tsum_ite 0
  rw [← hpois] at hsplit
  have hf0 : f 0 = -∑' n : ℤ, (if n = 0 then 0 else f n) := by
    linear_combination -hsplit
  have hitesum : Summable fun n : ℤ => ‖(if n = 0 then 0 else f n)‖ :=
    hsumnorm.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by split_ifs <;> simp)
  have hbound0 : ‖f 0‖ ≤ B := by
    rw [hf0, norm_neg]
    refine (norm_tsum_le_tsum_norm hitesum).trans ?_
    refine hitesum.tsum_le_of_sum_le fun u => ?_
    calc ∑ n ∈ u, ‖(if n = 0 then 0 else f n)‖ = ∑ n ∈ u with n ≠ 0, ‖f n‖ := by
          rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun n _ => ?_
          by_cases hn : n = 0 <;> simp [hn]
      _ ≤ B := hpartial u
  -- the zeroth coefficient is `X ∫ h`
  have hzero : f 0 = (X : ℂ) * ∫ y, specFn F y := by
    simp only [hf, Int.cast_zero]
    rw [fourier_transported_eq hX hW0 hWa hsupp (continuous_specFn hF) 0]
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hle]
    congr 1
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => hsupp y ?_
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hy
    rcases hy with h1 | h1
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [hzero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX] at hbound0
  rw [hBdef] at hbound0
  exact le_of_mul_le_mul_left hbound0 hX

end RHTower.LogLatticePoisson