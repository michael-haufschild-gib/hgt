import GaloisForLFunctions.RHTower.ThetaCuspFinitePrimeWeightedTail
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceUnconditional
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments

/-!
# Arbitrary exponential moments of every completed theta-source derivative

Polynomial--Gaussian atom estimate used for finite-prime sources also controls the full
all-integer derivative series. Reflection upgrades the positive-ray estimate to arbitrary
two-sided exponential moments for every actual derivative.
-/

open Filter Topology Set Polynomial MeasureTheory

noncomputable section

namespace RHTower

theorem exp_natSucc_mul_abs_thetaCuspFullDerivative_le
    (m q : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (((q + 1 : ℕ) : ℝ) * x) *
        |thetaCuspFullDerivative m x| ≤
      finitePrimeThetaCuspWeightedDerivativeConstant m q := by
  let a : ℕ → ℝ := fun n ↦
    thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial m) n x
  let g : ℕ → ℝ := fun n ↦
    Real.exp (-(Real.pi / 2) * (n : ℝ) ^ (2 : ℕ))
  let C : ℝ := thetaCuspGaussianConstant
    (thetaCuspWeightedPolynomial (thetaCuspLogDerivativePolynomial m) q)
  have ha : Summable a := by
    exact (summable_iteratedDeriv_thetaCuspSourceTerm m x).congr
      (fun n ↦ by
        dsimp [a]
        rw [iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom])
  have hgauss : Summable g := by
    simpa [g] using summable_thetaCuspHalfGaussian
  have hweighted : Summable (fun n : ℕ ↦
      Real.exp (((q + 1 : ℕ) : ℝ) * x) * |a n|) :=
    ha.norm.mul_left _
  have hmajor : Summable (fun n : ℕ ↦ C * g n) := hgauss.mul_left C
  have hterm (n : ℕ) :
      Real.exp (((q + 1 : ℕ) : ℝ) * x) * |a n| ≤ C * g n := by
    rcases n with _ | n
    · dsimp [a, C, g]
      rw [thetaCuspPolynomialAtom_derivative_zero, abs_zero, mul_zero]
      exact mul_nonneg (thetaCuspGaussianConstant_nonneg _) (Real.exp_pos _).le
    · dsimp [a, C, g]
      exact exp_natSucc_mul_abs_thetaCuspPolynomialAtom_le _ q hx (Nat.succ_pos n)
  have hsource : thetaCuspFullDerivative m x = ∑' n : ℕ, a n := by
    unfold thetaCuspFullDerivative
    apply tsum_congr
    intro n
    dsimp [a]
    rw [iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom]
  rw [hsource]
  calc
    Real.exp (((q + 1 : ℕ) : ℝ) * x) * |∑' n : ℕ, a n| ≤
        Real.exp (((q + 1 : ℕ) : ℝ) * x) * ∑' n : ℕ, |a n| := by
      gcongr
      exact norm_tsum_le_tsum_norm ha.norm
    _ = ∑' n : ℕ,
        Real.exp (((q + 1 : ℕ) : ℝ) * x) * |a n| := by
      rw [tsum_mul_left]
    _ ≤ ∑' n : ℕ, C * g n := hweighted.tsum_le_tsum hterm hmajor
    _ = C * ∑' n : ℕ, g n := by rw [tsum_mul_left]
    _ = finitePrimeThetaCuspWeightedDerivativeConstant m q := by rfl

theorem exp_mul_abs_thetaCuspFullDerivative_le
    (m q : ℕ) (A : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (A * x) * |thetaCuspFullDerivative m x| ≤
      finitePrimeThetaCuspWeightedDerivativeConstant m q *
        Real.exp (-(((q + 1 : ℕ) : ℝ) - A) * x) := by
  have hbase := exp_natSucc_mul_abs_thetaCuspFullDerivative_le m q hx
  have hre : A * x = -(((q + 1 : ℕ) : ℝ) - A) * x +
      ((q + 1 : ℕ) : ℝ) * x := by ring
  rw [hre, Real.exp_add]
  calc
    Real.exp (-(((q + 1 : ℕ) : ℝ) - A) * x) *
        Real.exp (((q + 1 : ℕ) : ℝ) * x) * |thetaCuspFullDerivative m x| =
      Real.exp (-(((q + 1 : ℕ) : ℝ) - A) * x) *
        (Real.exp (((q + 1 : ℕ) : ℝ) * x) * |thetaCuspFullDerivative m x|) := by
      ring
    _ ≤ Real.exp (-(((q + 1 : ℕ) : ℝ) - A) * x) *
        finitePrimeThetaCuspWeightedDerivativeConstant m q := by gcongr
    _ = finitePrimeThetaCuspWeightedDerivativeConstant m q *
        Real.exp (-(((q + 1 : ℕ) : ℝ) - A) * x) := by ring

theorem exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource_le
    (m q : ℕ) (A : ℝ) (x : ℝ) :
    Real.exp (A * |x|) * |iteratedDeriv m thetaCuspFullSource x| ≤
      finitePrimeThetaCuspWeightedDerivativeConstant m q *
        Real.exp (-(((q + 1 : ℕ) : ℝ) - A) * |x|) := by
  let y : ℝ := |x|
  have hy : 0 ≤ y := abs_nonneg x
  have hder : |iteratedDeriv m thetaCuspFullSource x| =
      |thetaCuspFullDerivative m y| := by
    rw [← congrFun (iteratedDeriv_thetaCuspFullSource m) y]
    rcases le_total 0 x with hx | hx
    · simp only [y, abs_of_nonneg hx]
    · have hp := abs_iteratedDeriv_thetaCuspFullSource_neg m (-x)
      simpa [y, abs_of_nonpos hx] using hp
  rw [hder]
  exact exp_mul_abs_thetaCuspFullDerivative_le m q A hy

/-- Every actual derivative of the completed theta source has every two-sided exponential
moment. -/
theorem integrable_exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource
    (m : ℕ) (A : ℝ) :
    Integrable (fun x : ℝ ↦
      Real.exp (A * |x|) * |iteratedDeriv m thetaCuspFullSource x|) := by
  obtain ⟨q : ℕ, hq⟩ := exists_nat_gt A
  have hA : A < (q + 1 : ℕ) :=
    lt_trans hq (by exact_mod_cast Nat.lt_succ_self q)
  let c : ℝ := ((q + 1 : ℕ) : ℝ) - A
  let C : ℝ := finitePrimeThetaCuspWeightedDerivativeConstant m q
  have hc : 0 < c := sub_pos.mpr hA
  have hmajor : Integrable (fun x : ℝ ↦ C * Real.exp (-c * |x|)) := by
    have h := (HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hc).const_mul C
    simpa only [pow_zero, one_mul] using h
  apply Integrable.mono hmajor
  · exact (((Real.continuous_exp.comp
      (continuous_const.mul continuous_abs))).mul
        (contDiff_thetaCuspFullSource.continuous_iteratedDeriv m
          (by exact_mod_cast (ENat.coe_lt_top m).le)).abs).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ Real.exp (A * |x|) * |iteratedDeriv m thetaCuspFullSource x|),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (finitePrimeThetaCuspWeightedDerivativeConstant_nonneg m q)
        (Real.exp_pos _).le)]
    dsimp only [C, c]
    simpa only [neg_mul] using
      exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource_le m q A x

end RHTower
