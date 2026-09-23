import GaloisForLFunctions.RHTower.ThetaCuspReflection
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# The theta-cusp source is a Schwartz function

The positive logarithmic tail is a polynomial-Gaussian series.  Splitting each Gaussian into two
half-Gaussians gives a summable discrete majorant and an `exp(-x)` bound for every derivative on
the positive half-line.  Reflection supplies the negative half-line.
-/

open Filter Topology Set Polynomial MeasureTheory
open scoped ContDiff SchwartzMap

noncomputable section

namespace RHTower

/-- Sum of the absolute coefficients of a real polynomial. -/
def thetaCuspCoeffMass (P : ℝ[X]) : ℝ :=
  ∑ k ∈ P.support, |P.coeff k|

theorem thetaCuspCoeffMass_nonneg (P : ℝ[X]) : 0 ≤ thetaCuspCoeffMass P := by
  unfold thetaCuspCoeffMass
  positivity

/-- A polynomial times a half-Gaussian has a uniform elementary bound. -/
theorem pow_mul_exp_neg_half_pi_sq_le (p : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    y ^ p * Real.exp (-(Real.pi / 2) * y ^ (2 : ℕ)) ≤
      Real.exp ((p : ℝ) ^ (2 : ℕ) / (2 * Real.pi)) := by
  have hyle : y ≤ Real.exp y := by
    calc
      y ≤ y + 1 := by linarith
      _ ≤ Real.exp y := Real.add_one_le_exp y
  have hpow : y ^ p ≤ Real.exp ((p : ℝ) * y) := by
    calc
      y ^ p ≤ Real.exp y ^ p := pow_le_pow_left₀ hy hyle p
      _ = Real.exp ((p : ℝ) * y) := by
        rw [← Real.exp_nat_mul]
  have hquad : (p : ℝ) * y - (Real.pi / 2) * y ^ (2 : ℕ) ≤
      (p : ℝ) ^ (2 : ℕ) / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity : 0 < 2 * Real.pi)]
    nlinarith [sq_nonneg (Real.pi * y - p), Real.pi_pos]
  calc
    y ^ p * Real.exp (-(Real.pi / 2) * y ^ (2 : ℕ)) ≤
        Real.exp ((p : ℝ) * y) * Real.exp (-(Real.pi / 2) * y ^ (2 : ℕ)) := by
      gcongr
    _ = Real.exp ((p : ℝ) * y - (Real.pi / 2) * y ^ (2 : ℕ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((p : ℝ) ^ (2 : ℕ) / (2 * Real.pi)) := Real.exp_le_exp.mpr hquad

/-- On `y ≥ 1`, evaluation is bounded by coefficient mass times the top-degree monomial. -/
theorem abs_eval_le_coeffMass_mul_pow (P : ℝ[X]) {y : ℝ} (hy : 1 ≤ y) :
    |eval y P| ≤ thetaCuspCoeffMass P * y ^ P.natDegree := by
  have hy0 : 0 ≤ y := zero_le_one.trans hy
  calc
    |eval y P| ≤ ∑ k ∈ P.support, |P.coeff k| * y ^ k :=
      abs_eval_le_coefficient_sum P hy0
    _ ≤ ∑ k ∈ P.support, |P.coeff k| * y ^ P.natDegree := by
      apply Finset.sum_le_sum
      intro k hk
      have hkdeg : k ≤ P.natDegree :=
        le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)
      gcongr
    _ = thetaCuspCoeffMass P * y ^ P.natDegree := by
      rw [thetaCuspCoeffMass, Finset.sum_mul]

/-- The derivative polynomial has no constant term, so the zero-index atom vanishes. -/
theorem thetaCuspPolynomialAtom_derivative_zero (m : ℕ) (x : ℝ) :
    thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial m) 0 x = 0 := by
  have heval : eval 0 (thetaCuspLogDerivativePolynomial m) = 0 := by
    rw [← coeff_zero_eq_eval_zero, thetaCuspLogDerivativePolynomial_coeff_zero]
  simp [thetaCuspPolynomialAtom, heval]

/-- Constant in the positive-half Gaussian bound for a polynomial atom. -/
def thetaCuspGaussianConstant (P : ℝ[X]) : ℝ :=
  thetaCuspCoeffMass P *
    Real.exp (((P.natDegree + 2 : ℕ) : ℝ) ^ (2 : ℕ) / (2 * Real.pi))

theorem thetaCuspGaussianConstant_nonneg (P : ℝ[X]) :
    0 ≤ thetaCuspGaussianConstant P := by
  unfold thetaCuspGaussianConstant
  exact mul_nonneg (thetaCuspCoeffMass_nonneg P) (Real.exp_pos _).le

/-- Every positive-index polynomial atom has a summable half-Gaussian bound after multiplication
by `exp x` on the positive logarithmic half-line. -/
theorem exp_mul_abs_thetaCuspPolynomialAtom_le_of_pos
    (P : ℝ[X]) {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : 0 < n) :
    Real.exp x * |thetaCuspPolynomialAtom P n x| ≤
      thetaCuspGaussianConstant P *
        Real.exp (-(Real.pi / 2) * (n : ℝ) ^ (2 : ℕ)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  focus
      let q : ℕ := n + 1
      let y : ℝ := (q : ℝ) * Real.exp x
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hexp1 : 1 ≤ Real.exp x := by simpa using Real.exp_le_exp.mpr hx
      have hy1 : 1 ≤ y := by
        dsimp [y]
        nlinarith [Real.exp_pos x]
      have hy0 : 0 ≤ y := zero_le_one.trans hy1
      have hqy : (q : ℝ) ≤ y := by
        dsimp [y]
        nlinarith
      have hexy : Real.exp x ≤ y := by
        dsimp [y]
        nlinarith [Real.exp_pos x]
      have hhalf : Real.exp (x / 2) ≤ y := by
        exact (Real.exp_le_exp.mpr (by linarith)).trans hexy
      have hfront : Real.exp x * Real.exp (x / 2) ≤ y ^ (2 : ℕ) := by
        rw [pow_two]
        exact mul_le_mul hexy hhalf (Real.exp_pos _).le hy0
      have heval := abs_eval_le_coeffMass_mul_pow P hy1
      let d : ℕ := P.natDegree
      let B : ℝ := Real.exp (((d + 2 : ℕ) : ℝ) ^ (2 : ℕ) / (2 * Real.pi))
      have hgauss : y ^ (d + 2) * Real.exp (-(Real.pi / 2) * y ^ (2 : ℕ)) ≤ B := by
        simpa [B] using pow_mul_exp_neg_half_pi_sq_le (d + 2) hy0
      have hmass : 0 ≤ thetaCuspCoeffMass P := thetaCuspCoeffMass_nonneg P
      have hB : 0 ≤ B := (Real.exp_pos _).le
      have htail : Real.exp (-(Real.pi / 2) * y ^ (2 : ℕ)) ≤
          Real.exp (-(Real.pi / 2) * (q : ℝ) ^ (2 : ℕ)) := by
        apply Real.exp_le_exp.mpr
        have hsq : (q : ℝ) ^ (2 : ℕ) ≤ y ^ (2 : ℕ) := by nlinarith
        nlinarith [Real.pi_pos]
      have hsplit : Real.exp (-Real.pi * y ^ (2 : ℕ)) =
          Real.exp (-(Real.pi / 2) * y ^ (2 : ℕ)) *
            Real.exp (-(Real.pi / 2) * y ^ (2 : ℕ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [thetaCuspPolynomialAtom, abs_mul, abs_mul,
        abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      change Real.exp x *
          (Real.exp (x / 2) * |eval y P| * Real.exp (-Real.pi * y ^ (2 : ℕ))) ≤ _
      calc
        Real.exp x *
            (Real.exp (x / 2) * |eval y P| * Real.exp (-Real.pi * y ^ (2 : ℕ))) =
            (Real.exp x * Real.exp (x / 2)) * |eval y P| *
              Real.exp (-Real.pi * y ^ (2 : ℕ)) := by ring
        _ ≤
            y ^ (2 : ℕ) * (thetaCuspCoeffMass P * y ^ d) *
              Real.exp (-Real.pi * y ^ (2 : ℕ)) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul hfront heval (abs_nonneg _) (sq_nonneg y)
          · positivity
        _ = thetaCuspCoeffMass P *
            (y ^ (d + 2) * Real.exp (-(Real.pi / 2) * y ^ (2 : ℕ))) *
              Real.exp (-(Real.pi / 2) * y ^ (2 : ℕ)) := by
          rw [hsplit, pow_add]
          ring
        _ ≤ thetaCuspCoeffMass P * B *
            Real.exp (-(Real.pi / 2) * (q : ℝ) ^ (2 : ℕ)) := by
          calc
            thetaCuspCoeffMass P *
                (y ^ (d + 2) * Real.exp (-(Real.pi / 2) * y ^ (2 : ℕ))) *
                  Real.exp (-(Real.pi / 2) * y ^ (2 : ℕ)) ≤
                thetaCuspCoeffMass P * B *
                  Real.exp (-(Real.pi / 2) * y ^ (2 : ℕ)) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hgauss hmass) (Real.exp_pos _).le
            _ ≤ thetaCuspCoeffMass P * B *
                Real.exp (-(Real.pi / 2) * (q : ℝ) ^ (2 : ℕ)) := by
              exact mul_le_mul_of_nonneg_left htail (mul_nonneg hmass hB)
        _ = thetaCuspGaussianConstant P *
            Real.exp (-(Real.pi / 2) * (q : ℝ) ^ (2 : ℕ)) := by
          rfl

/-- Zero constant term extends the positive-index bound across the zero atom. -/
theorem exp_mul_abs_thetaCuspPolynomialAtom_le
    (P : ℝ[X]) (hP0 : P.coeff 0 = 0) {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    Real.exp x * |thetaCuspPolynomialAtom P n x| ≤
      thetaCuspGaussianConstant P *
        Real.exp (-(Real.pi / 2) * (n : ℝ) ^ (2 : ℕ)) := by
  rcases n with _ | n
  · have heval : eval 0 P = 0 := by rw [← coeff_zero_eq_eval_zero, hP0]
    simpa [thetaCuspPolynomialAtom, heval] using thetaCuspGaussianConstant_nonneg P
  · exact exp_mul_abs_thetaCuspPolynomialAtom_le_of_pos P hx (Nat.succ_pos n)

theorem summable_thetaCuspHalfGaussian :
    Summable (fun n : ℕ => Real.exp (-(Real.pi / 2) * (n : ℝ) ^ (2 : ℕ))) := by
  simpa using summable_pow_mul_exp_neg_nat_sq 0 (by positivity : 0 < Real.pi / 2)

/-- Constant in the `exp(-x)` bound for the `m`-th derivative. -/
def thetaCuspDerivativeExpConstant (m : ℕ) : ℝ :=
  thetaCuspGaussianConstant (thetaCuspLogDerivativePolynomial m) *
    ∑' n : ℕ, Real.exp (-(Real.pi / 2) * (n : ℝ) ^ (2 : ℕ))

theorem thetaCuspDerivativeExpConstant_nonneg (m : ℕ) :
    0 ≤ thetaCuspDerivativeExpConstant m := by
  unfold thetaCuspDerivativeExpConstant
  exact mul_nonneg (thetaCuspGaussianConstant_nonneg _)
    (tsum_nonneg fun _ => (Real.exp_pos _).le)

/-- Constant in the positive-half `exp(-x)` bound for a derivative of the raw theta tail. -/
def thetaCuspTailDerivativeExpConstant (m : ℕ) : ℝ :=
  thetaCuspGaussianConstant (thetaCuspTailDerivativePolynomial m) *
    ∑' n : ℕ, Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ))

theorem thetaCuspTailDerivativeExpConstant_nonneg (m : ℕ) :
    0 ≤ thetaCuspTailDerivativeExpConstant m := by
  unfold thetaCuspTailDerivativeExpConstant
  exact mul_nonneg (thetaCuspGaussianConstant_nonneg _)
    (tsum_nonneg fun _ => (Real.exp_pos _).le)

/-- Every derivative of the raw positive theta tail decays exponentially at `+∞`. -/
theorem abs_thetaCuspTailDerivative_le_exp_neg
    (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |thetaCuspTailDerivative m x| ≤
      thetaCuspTailDerivativeExpConstant m * Real.exp (-x) := by
  let P : ℝ[X] := thetaCuspTailDerivativePolynomial m
  let a : ℕ → ℝ := fun n => thetaCuspPolynomialAtom P (n + 1) x
  let g : ℕ → ℝ := fun n => Real.exp (-(Real.pi / 2) * ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ))
  have ha : Summable a := by
    simpa [a, P, thetaCuspTailDerivative] using summable_thetaCuspTailDerivative m x
  have hg0 : Summable g := by
    exact (summable_nat_add_iff 1).mpr summable_thetaCuspHalfGaussian
  have hag : Summable (fun n => Real.exp x * |a n|) :=
    ha.norm.mul_left (Real.exp x)
  have hg : Summable (fun n => thetaCuspGaussianConstant P * g n) := hg0.mul_left _
  have hterm (n : ℕ) : Real.exp x * |a n| ≤ thetaCuspGaussianConstant P * g n := by
    dsimp [a, g, P]
    exact exp_mul_abs_thetaCuspPolynomialAtom_le_of_pos _ hx (Nat.succ_pos n)
  have hsum : Real.exp x * |∑' n, a n| ≤
      thetaCuspGaussianConstant P * ∑' n, g n := by
    calc
      Real.exp x * |∑' n, a n| ≤ Real.exp x * ∑' n, |a n| := by
        gcongr
        exact norm_tsum_le_tsum_norm ha.norm
      _ = ∑' n, Real.exp x * |a n| := by rw [tsum_mul_left]
      _ ≤ ∑' n, thetaCuspGaussianConstant P * g n :=
        hag.tsum_le_tsum hterm hg
      _ = thetaCuspGaussianConstant P * ∑' n, g n := by rw [tsum_mul_left]
  rw [thetaCuspTailDerivative]
  change |∑' n, a n| ≤ _
  calc
    |∑' n, a n| = Real.exp (-x) * (Real.exp x * |∑' n, a n|) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (-x) * (thetaCuspGaussianConstant P * ∑' n, g n) := by
      gcongr
    _ = thetaCuspTailDerivativeExpConstant m * Real.exp (-x) := by
      simp [thetaCuspTailDerivativeExpConstant, P, g]
      ring

theorem integrableOn_thetaCuspTailDerivative_Ioi (m : ℕ) :
    IntegrableOn (thetaCuspTailDerivative m) (Ioi 0) := by
  let C := thetaCuspTailDerivativeExpConstant m
  have hdom : IntegrableOn (fun x : ℝ => C * Real.exp (-x)) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).const_mul C
  have hC : 0 ≤ C := thetaCuspTailDerivativeExpConstant_nonneg m
  apply Integrable.mono hdom
  · exact (differentiable_thetaCuspTailDerivative m).continuous.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hC (Real.exp_pos _).le)]
    exact abs_thetaCuspTailDerivative_le_exp_neg m hx.le

theorem thetaCuspTailDerivative_tendsto_atTop_zero (m : ℕ) :
    Tendsto (thetaCuspTailDerivative m) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hle : ∀ᶠ x : ℝ in atTop,
      ‖thetaCuspTailDerivative m x‖ ≤
        thetaCuspTailDerivativeExpConstant m * Real.exp (-x) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Real.norm_eq_abs]
    exact abs_thetaCuspTailDerivative_le_exp_neg m hx
  have hmajor : Tendsto
      (fun x : ℝ => thetaCuspTailDerivativeExpConstant m * Real.exp (-x))
      atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul
      (thetaCuspTailDerivativeExpConstant m)
  exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hle hmajor

/-- Every derivative of the full theta-cusp source has a uniform exponential bound on the
positive logarithmic half-line. -/
theorem abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg
    (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |iteratedDeriv m thetaCuspFullSource x| ≤
      thetaCuspDerivativeExpConstant m * Real.exp (-x) := by
  let P : ℝ[X] := thetaCuspLogDerivativePolynomial m
  let a : ℕ → ℝ := fun n => thetaCuspPolynomialAtom P n x
  let g : ℕ → ℝ := fun n => Real.exp (-(Real.pi / 2) * (n : ℝ) ^ (2 : ℕ))
  have hatom :
      (fun n : ℕ => iteratedDeriv m (fun y => thetaCuspSourceTerm y n) x) = a := by
    funext n
    dsimp [a, P]
    exact congrFun (iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom m n) x
  have ha : Summable a := by
    rw [← hatom]
    exact summable_iteratedDeriv_thetaCuspSourceTerm m x
  have hag : Summable (fun n => Real.exp x * |a n|) :=
    ha.norm.mul_left (Real.exp x)
  have hg : Summable (fun n => thetaCuspGaussianConstant P * g n) :=
    summable_thetaCuspHalfGaussian.mul_left _
  have hterm (n : ℕ) : Real.exp x * |a n| ≤ thetaCuspGaussianConstant P * g n := by
    dsimp [a, g, P]
    exact exp_mul_abs_thetaCuspPolynomialAtom_le _
      (thetaCuspLogDerivativePolynomial_coeff_zero m) hx n
  have hsum : Real.exp x * |∑' n, a n| ≤
      thetaCuspGaussianConstant P * ∑' n, g n := by
    calc
      Real.exp x * |∑' n, a n| ≤ Real.exp x * ∑' n, |a n| := by
        gcongr
        exact norm_tsum_le_tsum_norm ha.norm
      _ = ∑' n, Real.exp x * |a n| := by rw [tsum_mul_left]
      _ ≤ ∑' n, thetaCuspGaussianConstant P * g n :=
        hag.tsum_le_tsum hterm hg
      _ = thetaCuspGaussianConstant P * ∑' n, g n := by rw [tsum_mul_left]
  rw [iteratedDeriv_thetaCuspFullSource, thetaCuspFullDerivative, hatom]
  calc
    |∑' n, a n| = Real.exp (-x) * (Real.exp x * |∑' n, a n|) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (-x) *
        (thetaCuspGaussianConstant P * ∑' n, g n) := by
      gcongr
    _ = thetaCuspDerivativeExpConstant m * Real.exp (-x) := by
      simp [thetaCuspDerivativeExpConstant, P, g]
      ring

theorem pow_mul_exp_neg_le_factorial (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k * Real.exp (-x) ≤ (Nat.factorial k : ℝ) := by
  have h := Real.pow_div_factorial_le_exp x hx k
  have hfac : (0 : ℝ) < Nat.factorial k := by positivity
  rw [div_le_iff₀ hfac] at h
  calc
    x ^ k * Real.exp (-x) ≤
        ((Nat.factorial k : ℝ) * Real.exp x) * Real.exp (-x) := by
      exact mul_le_mul_of_nonneg_right (by simpa [mul_comm] using h) (Real.exp_pos _).le
    _ = (Nat.factorial k : ℝ) := by
      rw [mul_assoc, ← Real.exp_add]
      simp

/-- Global Schwartz-seminorm bound, using reflection to transfer the positive-half estimate. -/
theorem weighted_iteratedDeriv_thetaCuspFullSource_le (k m : ℕ) (x : ℝ) :
    ‖x‖ ^ k * ‖iteratedDeriv m thetaCuspFullSource x‖ ≤
      thetaCuspDerivativeExpConstant m * (Nat.factorial k : ℝ) := by
  let y : ℝ := |x|
  have hy : 0 ≤ y := abs_nonneg x
  have hder : |iteratedDeriv m thetaCuspFullSource x| =
      |iteratedDeriv m thetaCuspFullSource y| := by
    rcases le_or_gt 0 x with hx | hx
    · simp [y, abs_of_nonneg hx]
    · have href := abs_iteratedDeriv_thetaCuspFullSource_neg m (-x)
      simpa [y, abs_of_neg hx] using href
  have hsource := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg m hy
  have hpow := pow_mul_exp_neg_le_factorial k hy
  have hC := thetaCuspDerivativeExpConstant_nonneg m
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hder]
  change y ^ k * |iteratedDeriv m thetaCuspFullSource y| ≤ _
  calc
    y ^ k * |iteratedDeriv m thetaCuspFullSource y| ≤
        y ^ k * (thetaCuspDerivativeExpConstant m * Real.exp (-y)) := by
      gcongr
    _ = thetaCuspDerivativeExpConstant m * (y ^ k * Real.exp (-y)) := by ring
    _ ≤ thetaCuspDerivativeExpConstant m * (Nat.factorial k : ℝ) :=
      mul_le_mul_of_nonneg_left hpow hC

/-- The actual all-integer theta-cusp source as a real Schwartz function. -/
def thetaCuspSchwartzReal : 𝓢(ℝ, ℝ) where
  toFun := thetaCuspFullSource
  smooth' := contDiff_thetaCuspFullSource
  decay' k m := by
    refine ⟨thetaCuspDerivativeExpConstant m * (Nat.factorial k : ℝ), ?_⟩
    intro x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact weighted_iteratedDeriv_thetaCuspFullSource_le k m x

@[simp] theorem thetaCuspSchwartzReal_apply (x : ℝ) :
    thetaCuspSchwartzReal x = thetaCuspFullSource x := rfl

/-- The actual theta-cusp source in complex Schwartz space. -/
def thetaCuspSchwartz : 𝓢(ℝ, ℂ) :=
  thetaCuspSchwartzReal.postcompCLM Complex.ofRealCLM

@[simp] theorem thetaCuspSchwartz_apply (x : ℝ) :
    thetaCuspSchwartz x = (thetaCuspFullSource x : ℂ) := rfl

end RHTower
