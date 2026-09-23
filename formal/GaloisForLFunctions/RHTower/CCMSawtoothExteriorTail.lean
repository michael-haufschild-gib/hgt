import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Normed.Group.Tannery
import GaloisForLFunctions.RHTower.CCMSawtoothDilationMean
import GaloisForLFunctions.RHTower.CCMSawtoothDilationIncidence

/-!
# The exterior tail of the dilated sawtooth is uniformly `O(1/n)`

The exterior weight `L x^{-2}` is the multiplicative image of the exponential density `e^{-s}`.  Two
independent estimates for the exterior response are proved here.

* `invSqWeight`, `integral_invSqWeight`, `integral_abs_invSqWeightDeriv`,
  `abs_integral_invSqWeight_mul_sawDilate_sub_mean_le`,
  `abs_integral_expWeight_sawDilate_sub_mean_le` — the response equals the exact mean `1/(12 n)` up to
  `4/(3L)`, uniformly in the dilation and in the outer endpoint.
* `exteriorPiece`, `abs_integral_exteriorPiece_mul_le`, `abs_integral_exteriorPiece_period_le`,
  `abs_integral_invSqWeight_mul_sawDilate_int_window_le`,
  `abs_integral_invSqWeight_mul_sawDilate_window_le` — the response is `O(1/n)` with the absolute
  constant `13/8`, uniformly in `L ≥ 1` and in the outer endpoint.  On each period the slow factor
  `L x^{-2}(k + 1/2 - x)` is smooth, so no bounded-variation theory is needed: the same distributional
  integration by parts applies, paired against the dilated sawtooth primitive.
* `integrableOn_invSqWeight_mul_sawDilate`, `abs_integral_Ioi_invSqWeight_mul_sawDilate_le`,
  `abs_integral_Ioi_invSqWeight_mul_sawDilate_sub_mean_le` — both estimates on the half-line.
* `summable_fullPrimeResponse`, `tendsto_fullPrimeResponse` — the full von Mangoldt series converges
  absolutely, uniformly in `L ≥ 1`, and converges to `(1/12) ∑ Λ(n) n^{-2}` as the aperture grows.
* `integral_comp_exp_scale_Ioi`, `integral_expWeight_Ioi_eq_invSqWeight` — the additive and
  multiplicative readings of the full exterior integral agree.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory intervalIntegral Set ArithmeticFunction Filter Topology

/-! ## The exterior inverse-square weight -/

/-- The exterior weight `L/x²`, which is the image of the density `e^{-s}` under `x = L e^s`. -/
def invSqWeight (L : ℝ) : ℝ → ℝ := fun x => L / x ^ (2 : ℕ)

def invSqWeightDeriv (L : ℝ) : ℝ → ℝ := fun x => -(2 * L) / x ^ (3 : ℕ)

theorem measurable_invSqWeightDeriv (L : ℝ) : Measurable (invSqWeightDeriv L) := by
  unfold invSqWeightDeriv
  fun_prop

theorem hasDerivAt_invSqWeight {L x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (invSqWeight L) (invSqWeightDeriv L x) x := by
  have hc : HasDerivAt (fun _ : ℝ => L) 0 x := hasDerivAt_const x L
  have hd : HasDerivAt (fun y : ℝ => y ^ (2 : ℕ)) (2 * x ^ (1 : ℕ)) x := by
    simpa using hasDerivAt_pow 2 x
  have h := hc.div hd (pow_ne_zero 2 hx)
  have hval : (0 * x ^ (2 : ℕ) - L * (2 * x ^ (1 : ℕ))) / (x ^ (2 : ℕ)) ^ (2 : ℕ) = invSqWeightDeriv L x := by
    rw [invSqWeightDeriv]
    field_simp
    ring
  show HasDerivAt (fun y : ℝ => L / y ^ (2 : ℕ)) (invSqWeightDeriv L x) x
  rw [← hval]
  exact h

theorem abs_invSqWeightDeriv_le {L T x : ℝ} (hL : 0 < L) (hx : x ∈ Icc L T) :
    |invSqWeightDeriv L x| ≤ 2 / L ^ (2 : ℕ) := by
  have hxpos : 0 < x := lt_of_lt_of_le hL hx.1
  have hcube : L ^ (3 : ℕ) ≤ x ^ (3 : ℕ) := by gcongr; exact hx.1
  rw [invSqWeightDeriv, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * L),
    abs_of_pos (by positivity : (0 : ℝ) < x ^ (3 : ℕ))]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hcube, hL.le]

/-- The total variation of the exterior weight on a window. -/
theorem integral_abs_invSqWeightDeriv {L T : ℝ} (hL : 0 < L) (hLT : L ≤ T) :
    (∫ x in L..T, |invSqWeightDeriv L x|) = 1 / L - L / T ^ (2 : ℕ) := by
  have hTpos : 0 < T := lt_of_lt_of_le hL hLT
  have hcongr : (∫ x in L..T, |invSqWeightDeriv L x|) = ∫ x in L..T, (2 * L) / x ^ (3 : ℕ) := by
    refine integral_congr_of_Ioo hLT fun x hx => ?_
    have hxpos : 0 < x := lt_trans hL hx.1
    rw [invSqWeightDeriv, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * L),
      abs_of_pos (by positivity : (0 : ℝ) < x ^ (3 : ℕ))]
  rw [hcongr]
  have hd : ∀ x ∈ uIcc L T, HasDerivAt (fun y : ℝ => -(L / y ^ (2 : ℕ))) ((2 * L) / x ^ (3 : ℕ)) x := by
    intro x hx
    rw [uIcc_of_le hLT] at hx
    have hxpos : 0 < x := lt_of_lt_of_le hL hx.1
    have h := (hasDerivAt_invSqWeight (L := L) (ne_of_gt hxpos)).neg
    have hval : -invSqWeightDeriv L x = (2 * L) / x ^ (3 : ℕ) := by
      rw [invSqWeightDeriv]
      field_simp
    rw [← hval]
    exact h
  have hint : IntervalIntegrable (fun x : ℝ => (2 * L) / x ^ (3 : ℕ)) volume L T := by
    refine intervalIntegrable_of_bound_on (by fun_prop) (C := 2 * L / L ^ (3 : ℕ)) hLT ?_
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hL hx.1
    have hcube : L ^ (3 : ℕ) ≤ x ^ (3 : ℕ) := by gcongr; exact hx.1
    rw [abs_of_pos (by positivity)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hcube, hL.le]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  field_simp
  ring

/-- The exterior weight integrates to `1 - L/T`. -/
theorem integral_invSqWeight {L T : ℝ} (hL : 0 < L) (hLT : L ≤ T) :
    (∫ x in L..T, invSqWeight L x) = 1 - L / T := by
  have hTpos : 0 < T := lt_of_lt_of_le hL hLT
  have hd : ∀ x ∈ uIcc L T, HasDerivAt (fun y : ℝ => -(L / y)) (invSqWeight L x) x := by
    intro x hx
    rw [uIcc_of_le hLT] at hx
    have hxpos : 0 < x := lt_of_lt_of_le hL hx.1
    have hc : HasDerivAt (fun _ : ℝ => L) 0 x := hasDerivAt_const x L
    have h := (hc.div (hasDerivAt_id x) (ne_of_gt hxpos)).neg
    have hval : -((0 * x - L * 1) / x ^ (2 : ℕ)) = invSqWeight L x := by
      rw [invSqWeight]
      field_simp
      ring
    rw [← hval]
    exact h
  have hint : IntervalIntegrable (invSqWeight L) volume L T := by
    refine intervalIntegrable_of_bound_on (by unfold invSqWeight; fun_prop)
      (C := L / L ^ (2 : ℕ)) hLT ?_
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hL hx.1
    have hsq : L ^ (2 : ℕ) ≤ x ^ (2 : ℕ) := by gcongr; exact hx.1
    rw [invSqWeight, abs_of_pos (by positivity)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsq, hL.le]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  field_simp
  ring

/-- **Equation (18), on a finite window.**  The exponentially weighted dilated sawtooth product has
the exact mean `1/(12 n)` up to `4/(3L)`, uniformly in the dilation and in the outer endpoint.  The
integration by parts is the distributional one, so the discontinuity of the sawtooth costs nothing. -/
theorem abs_integral_invSqWeight_mul_sawDilate_sub_mean_le {n : ℕ} (hn : 0 < n) {L T : ℝ}
    (hL : 0 < L) (hLT : L ≤ T) :
    |(∫ x in L..T, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))
      - (1 / (12 * (n : ℝ))) * (1 - L / T)| ≤ 4 / (3 * L) := by
  have hTpos : 0 < T := lt_of_lt_of_le hL hLT
  have hgm := measurable_sawDilateCentered n
  have hgb := abs_sawDilateCentered_le hn
  have hwint : IntervalIntegrable (invSqWeight L) volume L T := by
    refine intervalIntegrable_of_bound_on (by unfold invSqWeight; fun_prop)
      (C := L / L ^ (2 : ℕ)) hLT ?_
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hL hx.1
    have hsq : L ^ (2 : ℕ) ≤ x ^ (2 : ℕ) := by gcongr; exact hx.1
    rw [invSqWeight, abs_of_pos (by positivity)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsq, hL.le]
  have hcent : IntervalIntegrable
      (fun x => invSqWeight L x *
        (sawUnit x * sawUnit ((n : ℝ) * x) - 1 / (12 * (n : ℝ)))) volume L T := by
    refine (intervalIntegrable_sawDilateCentered n L T).continuousOn_mul ?_
    refine ContinuousOn.mono (s := {x : ℝ | x ≠ 0}) ?_ ?_
    · unfold invSqWeight
      exact ContinuousOn.div continuousOn_const (continuousOn_pow 2)
        fun x hx => pow_ne_zero 2 hx
    · intro x hx
      rw [uIcc_of_le hLT] at hx
      exact ne_of_gt (lt_of_lt_of_le hL hx.1)
  -- split off the mean
  have hsplit : (∫ x in L..T, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))
      = (∫ x in L..T, invSqWeight L x *
          (sawUnit x * sawUnit ((n : ℝ) * x) - 1 / (12 * (n : ℝ))))
        + (1 / (12 * (n : ℝ))) * (1 - L / T) := by
    have hpt : ∀ x : ℝ, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))
        = invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x) - 1 / (12 * (n : ℝ)))
          + (1 / (12 * (n : ℝ))) * invSqWeight L x := fun x => by ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_add hcent (hwint.const_mul _),
      intervalIntegral.integral_const_mul, integral_invSqWeight hL hLT]
  rw [hsplit, add_sub_cancel_right]
  -- integration by parts
  have hibp := integral_deriv_mul_primitive hLT hgm hgb (measurable_invSqWeightDeriv L)
    (fun x hx => hasDerivAt_invSqWeight (ne_of_gt (lt_of_lt_of_le hL hx.1)))
    (fun x hx => abs_invSqWeightDeriv_le hL hx)
  simp only [integral_sawDilateCentered_eq n L] at hibp
  have hPbound : ∀ x : ℝ, |sawDilatePrimitive n x - sawDilatePrimitive n L| ≤ 2 / 3 := by
    intro x
    calc |sawDilatePrimitive n x - sawDilatePrimitive n L|
        ≤ |sawDilatePrimitive n x| + |sawDilatePrimitive n L| := abs_sub _ _
      _ ≤ 1 / 3 + 1 / 3 := add_le_add (abs_sawDilatePrimitive_le hn x)
          (abs_sawDilatePrimitive_le hn L)
      _ = 2 / 3 := by norm_num
  have hd'int : IntervalIntegrable (invSqWeightDeriv L) volume L T :=
    intervalIntegrable_of_bound_on (measurable_invSqWeightDeriv L) hLT
      (fun x hx => abs_invSqWeightDeriv_le hL hx)
  have hprod : IntervalIntegrable (fun x => invSqWeightDeriv L x *
      (sawDilatePrimitive n x - sawDilatePrimitive n L)) volume L T :=
    hd'int.mul_continuousOn
      (((continuous_sawDilatePrimitive n).sub continuous_const).continuousOn)
  have habs1 : |∫ x in L..T, invSqWeightDeriv L x *
      (sawDilatePrimitive n x - sawDilatePrimitive n L)| ≤ (2 / 3) * (1 / L - L / T ^ (2 : ℕ)) := by
    calc |∫ x in L..T, invSqWeightDeriv L x *
          (sawDilatePrimitive n x - sawDilatePrimitive n L)|
        ≤ ∫ x in L..T, |invSqWeightDeriv L x *
            (sawDilatePrimitive n x - sawDilatePrimitive n L)| :=
          intervalIntegral.abs_integral_le_integral_abs hLT
      _ ≤ ∫ x in L..T, (2 / 3) * |invSqWeightDeriv L x| := by
          refine intervalIntegral.integral_mono_on hLT hprod.abs (hd'int.abs.const_mul _) ?_
          intro x _
          rw [abs_mul]
          nlinarith [abs_nonneg (invSqWeightDeriv L x), hPbound x,
            abs_nonneg (sawDilatePrimitive n x - sawDilatePrimitive n L)]
      _ = (2 / 3) * (1 / L - L / T ^ (2 : ℕ)) := by
          rw [intervalIntegral.integral_const_mul, integral_abs_invSqWeightDeriv hL hLT]
  have hwT : invSqWeight L T ≤ 1 / L := by
    rw [invSqWeight]
    have hsq : L ^ (2 : ℕ) ≤ T ^ (2 : ℕ) := by nlinarith
    rw [div_le_div_iff₀ (by positivity) hL]
    nlinarith [hsq, hL.le]
  have hwTnn : 0 ≤ invSqWeight L T := by
    rw [invSqWeight]; positivity
  have hkey : (∫ x in L..T, invSqWeight L x *
      (sawUnit x * sawUnit ((n : ℝ) * x) - 1 / (12 * (n : ℝ))))
      = invSqWeight L T * (sawDilatePrimitive n T - sawDilatePrimitive n L)
        - ∫ x in L..T, invSqWeightDeriv L x *
            (sawDilatePrimitive n x - sawDilatePrimitive n L) := by
    linarith [hibp]
  rw [hkey]
  have hvar : (0 : ℝ) ≤ 1 / L - L / T ^ (2 : ℕ) := by
    rw [← integral_abs_invSqWeightDeriv hL hLT]
    exact intervalIntegral.integral_nonneg hLT fun x _ => abs_nonneg _
  have hvarle : 1 / L - L / T ^ (2 : ℕ) ≤ 1 / L := by
    have hnn : (0 : ℝ) ≤ L / T ^ (2 : ℕ) := by positivity
    linarith
  calc |invSqWeight L T * (sawDilatePrimitive n T - sawDilatePrimitive n L)
        - ∫ x in L..T, invSqWeightDeriv L x *
            (sawDilatePrimitive n x - sawDilatePrimitive n L)|
      ≤ |invSqWeight L T * (sawDilatePrimitive n T - sawDilatePrimitive n L)|
        + |∫ x in L..T, invSqWeightDeriv L x *
            (sawDilatePrimitive n x - sawDilatePrimitive n L)| := abs_sub _ _
    _ ≤ (1 / L) * (2 / 3) + (2 / 3) * (1 / L) := by
        refine add_le_add ?_ (habs1.trans (by linarith [hvarle]))
        rw [abs_mul, abs_of_nonneg hwTnn]
        have hLpos : (0 : ℝ) < 1 / L := by positivity
        nlinarith [hPbound T, abs_nonneg (sawDilatePrimitive n T - sawDilatePrimitive n L),
          hwTnn, hwT]
    _ = 4 / (3 * L) := by
        field_simp
        ring

/-- The exterior weight is the multiplicative image of the exponential density. -/
theorem additiveWeight_invSqWeight {L : ℝ} (hL : 0 < L) :
    additiveWeight L (invSqWeight L) = fun s => Real.exp (-s) := by
  funext s
  have hpos : (0 : ℝ) < L * Real.exp s := by positivity
  have hne : Real.exp s ≠ 0 := Real.exp_ne_zero s
  rw [additiveWeight, invSqWeight, Real.exp_neg]
  field_simp

theorem integral_expWeight_eq_invSqWeight {L : ℝ} (hL : 0 < L) {S : ℝ} (hS : 0 ≤ S) (h : ℝ → ℝ) :
    (∫ s in (0 : ℝ)..S, Real.exp (-s) * h (L * Real.exp s))
      = ∫ x in L..(L * Real.exp S), invSqWeight L x * h x := by
  have hbase := integral_additiveWeight_mul_comp hL hS (invSqWeight L) h
  rw [additiveWeight_invSqWeight hL] at hbase
  rw [Real.exp_zero, mul_one] at hbase
  exact hbase

/-- **Equation (18), in the card's additive variable, on a finite window.**  The card's `O(1/L)` is
made explicit: the constant is `4/3`, uniformly in the dilation and in the outer endpoint. -/
theorem abs_integral_expWeight_sawDilate_sub_mean_le {n : ℕ} (hn : 0 < n) {L S : ℝ} (hL : 0 < L)
    (hS : 0 ≤ S) :
    |(∫ s in (0 : ℝ)..S,
        Real.exp (-s) * (sawUnit (L * Real.exp s) * sawUnit ((n : ℝ) * (L * Real.exp s))))
      - (1 / (12 * (n : ℝ))) * (1 - Real.exp (-S))| ≤ 4 / (3 * L) := by
  have hLS : L ≤ L * Real.exp S := by
    have h1 : (1 : ℝ) ≤ Real.exp S := Real.one_le_exp hS
    nlinarith
  have hratio : L / (L * Real.exp S) = Real.exp (-S) := by
    have hne : Real.exp S ≠ 0 := Real.exp_ne_zero S
    rw [Real.exp_neg]
    field_simp
  rw [integral_expWeight_eq_invSqWeight hL hS
    (fun x => sawUnit x * sawUnit ((n : ℝ) * x)), ← hratio]
  exact abs_integral_invSqWeight_mul_sawDilate_sub_mean_le hn hL hLS

/-! ## The exterior integrand on one period -/

/-- On the period `[k, k+1]` the slow factor `L x^{-2} S(x)` of the exterior integrand is smooth: the
sawtooth is affine there.  This is the piece on which the `O(1/n)` estimate is proved. -/
def exteriorPiece (L : ℝ) (k : ℤ) : ℝ → ℝ := fun x => (L / x ^ (2 : ℕ)) * ((k : ℝ) + 1 / 2 - x)

def exteriorPieceDeriv (L : ℝ) (k : ℤ) : ℝ → ℝ :=
  fun x => (-(2 * L) / x ^ (3 : ℕ)) * ((k : ℝ) + 1 / 2 - x) + (L / x ^ (2 : ℕ)) * (-1)

theorem measurable_exteriorPieceDeriv (L : ℝ) (k : ℤ) : Measurable (exteriorPieceDeriv L k) := by
  unfold exteriorPieceDeriv
  fun_prop

theorem hasDerivAt_exteriorPiece {L : ℝ} (k : ℤ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (exteriorPiece L k) (exteriorPieceDeriv L k x) x := by
  have h1 : HasDerivAt (fun y : ℝ => L / y ^ (2 : ℕ)) (-(2 * L) / x ^ (3 : ℕ)) x :=
    hasDerivAt_invSqWeight hx
  have h2 : HasDerivAt (fun y : ℝ => (k : ℝ) + 1 / 2 - y) (-1) x := by
    have h := (hasDerivAt_const x ((k : ℝ) + 1 / 2)).fun_sub (hasDerivAt_id x)
    simpa using h
  exact h1.mul h2

theorem abs_exteriorPiece_le {L : ℝ} (hL : 0 < L) (k : ℤ) {x : ℝ}
    (hk : (k : ℝ) ≤ x) (hk1 : x ≤ (k : ℝ) + 1) (hx : 0 < x) :
    |exteriorPiece L k x| ≤ L / (2 * x ^ (2 : ℕ)) := by
  have hb : |(k : ℝ) + 1 / 2 - x| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  rw [exteriorPiece, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < L / x ^ (2 : ℕ))]
  calc L / x ^ (2 : ℕ) * |(k : ℝ) + 1 / 2 - x| ≤ L / x ^ (2 : ℕ) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = L / (2 * x ^ (2 : ℕ)) := by ring

theorem abs_exteriorPieceDeriv_le {L : ℝ} (hL : 0 < L) (k : ℤ) {x : ℝ}
    (hk : (k : ℝ) ≤ x) (hk1 : x ≤ (k : ℝ) + 1) (hx : 0 < x) :
    |exteriorPieceDeriv L k x| ≤ L / x ^ (3 : ℕ) + L / x ^ (2 : ℕ) := by
  have hb : |(k : ℝ) + 1 / 2 - x| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have h1 : |(-(2 * L) / x ^ (3 : ℕ)) * ((k : ℝ) + 1 / 2 - x)| ≤ L / x ^ (3 : ℕ) := by
    rw [abs_mul, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * L),
      abs_of_pos (by positivity : (0 : ℝ) < x ^ (3 : ℕ))]
    calc 2 * L / x ^ (3 : ℕ) * |(k : ℝ) + 1 / 2 - x| ≤ 2 * L / x ^ (3 : ℕ) * (1 / 2) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = L / x ^ (3 : ℕ) := by ring
  have h2 : |(L / x ^ (2 : ℕ)) * (-1)| = L / x ^ (2 : ℕ) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < L / x ^ (2 : ℕ))]
    simp
  rw [exteriorPieceDeriv]
  calc |(-(2 * L) / x ^ (3 : ℕ)) * ((k : ℝ) + 1 / 2 - x) + (L / x ^ (2 : ℕ)) * (-1)|
      ≤ |(-(2 * L) / x ^ (3 : ℕ)) * ((k : ℝ) + 1 / 2 - x)| + |(L / x ^ (2 : ℕ)) * (-1)| :=
          abs_add_le _ _
    _ ≤ L / x ^ (3 : ℕ) + L / x ^ (2 : ℕ) := by rw [h2] at *; linarith

/-- **The per-period `O(1/n)` estimate.**  On a sub-interval of one period, the exterior integrand
pairs the smooth slow factor against the dilated sawtooth, whose primitive is `O(1/n)`; the
distributional integration by parts turns this into a bound with the slow factor's boundary value and
total variation. -/
theorem abs_integral_exteriorPiece_mul_le {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L) (k : ℤ)
    {c d : ℝ} (hcd : c ≤ d) (hc : 0 < c) (hkc : (k : ℝ) ≤ c) (hdk : d ≤ (k : ℝ) + 1) :
    |∫ x in c..d, exteriorPiece L k x * sawUnit ((n : ℝ) * x)|
      ≤ (1 / (4 * (n : ℝ))) * (L / (2 * d ^ (2 : ℕ)) + ∫ x in c..d, (L / x ^ (3 : ℕ) + L / x ^ (2 : ℕ))) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdpos : 0 < d := lt_of_lt_of_le hc hcd
  have hxpos : ∀ x ∈ Icc c d, 0 < x := fun x hx => lt_of_lt_of_le hc hx.1
  have hgm : Measurable fun x : ℝ => sawUnit ((n : ℝ) * x) :=
    measurable_sawUnit.comp (measurable_const_mul _)
  have hgb : ∀ x : ℝ, |sawUnit ((n : ℝ) * x)| ≤ 1 / 2 := fun x => abs_sawUnit_le _
  have hd'b : ∀ x ∈ Icc c d, |exteriorPieceDeriv L k x| ≤ L / c ^ (3 : ℕ) + L / c ^ (2 : ℕ) := by
    intro x hx
    have hxp := hxpos x hx
    refine (abs_exteriorPieceDeriv_le hL k (le_trans hkc hx.1) (le_trans hx.2 hdk) hxp).trans ?_
    have h3 : c ^ (3 : ℕ) ≤ x ^ (3 : ℕ) := by gcongr; exact hx.1
    have h2 : c ^ (2 : ℕ) ≤ x ^ (2 : ℕ) := by gcongr; exact hx.1
    have hb3 : L / x ^ (3 : ℕ) ≤ L / c ^ (3 : ℕ) := by
      apply div_le_div_of_nonneg_left hL.le (by positivity) h3
    have hb2 : L / x ^ (2 : ℕ) ≤ L / c ^ (2 : ℕ) := by
      apply div_le_div_of_nonneg_left hL.le (by positivity) h2
    linarith
  have hibp := integral_deriv_mul_primitive hcd hgm hgb (measurable_exteriorPieceDeriv L k)
    (fun x hx => hasDerivAt_exteriorPiece k (ne_of_gt (hxpos x hx))) hd'b
  have hd'int : IntervalIntegrable (exteriorPieceDeriv L k) volume c d :=
    intervalIntegrable_of_bound_on (measurable_exteriorPieceDeriv L k) hcd hd'b
  have hPb : ∀ x : ℝ, |∫ t in c..x, sawUnit ((n : ℝ) * t)| ≤ 1 / (4 * (n : ℝ)) :=
    fun x => abs_integral_sawUnit_comp_mul_le hn c x
  have hPcont : Continuous fun x : ℝ => ∫ t in c..x, sawUnit ((n : ℝ) * t) :=
    intervalIntegral.continuous_primitive
      (fun a b => intervalIntegrable_sawUnit_comp_mul n a b) c
  have hprod : IntervalIntegrable
      (fun x => exteriorPieceDeriv L k x * (∫ t in c..x, sawUnit ((n : ℝ) * t))) volume c d :=
    hd'int.mul_continuousOn hPcont.continuousOn
  have hboundfn : IntervalIntegrable (fun x : ℝ => L / x ^ (3 : ℕ) + L / x ^ (2 : ℕ)) volume c d := by
    refine intervalIntegrable_of_bound_on (by fun_prop) (C := L / c ^ (3 : ℕ) + L / c ^ (2 : ℕ)) hcd ?_
    intro x hx
    have hxp := hxpos x hx
    have h3 : c ^ (3 : ℕ) ≤ x ^ (3 : ℕ) := by gcongr; exact hx.1
    have h2 : c ^ (2 : ℕ) ≤ x ^ (2 : ℕ) := by gcongr; exact hx.1
    rw [abs_of_pos (by positivity)]
    have hb3 : L / x ^ (3 : ℕ) ≤ L / c ^ (3 : ℕ) := div_le_div_of_nonneg_left hL.le (by positivity) h3
    have hb2 : L / x ^ (2 : ℕ) ≤ L / c ^ (2 : ℕ) := div_le_div_of_nonneg_left hL.le (by positivity) h2
    linarith
  have hvar : (∫ x in c..d, |exteriorPieceDeriv L k x|)
      ≤ ∫ x in c..d, (L / x ^ (3 : ℕ) + L / x ^ (2 : ℕ)) := by
    refine intervalIntegral.integral_mono_on hcd hd'int.abs hboundfn ?_
    intro x hx
    exact abs_exteriorPieceDeriv_le hL k (le_trans hkc hx.1) (le_trans hx.2 hdk) (hxpos x hx)
  have hterm2 : |∫ x in c..d, exteriorPieceDeriv L k x *
      (∫ t in c..x, sawUnit ((n : ℝ) * t))|
      ≤ (1 / (4 * (n : ℝ))) * ∫ x in c..d, (L / x ^ (3 : ℕ) + L / x ^ (2 : ℕ)) := by
    calc |∫ x in c..d, exteriorPieceDeriv L k x * (∫ t in c..x, sawUnit ((n : ℝ) * t))|
        ≤ ∫ x in c..d, |exteriorPieceDeriv L k x * (∫ t in c..x, sawUnit ((n : ℝ) * t))| :=
          intervalIntegral.abs_integral_le_integral_abs hcd
      _ ≤ ∫ x in c..d, (1 / (4 * (n : ℝ))) * |exteriorPieceDeriv L k x| := by
          refine intervalIntegral.integral_mono_on hcd hprod.abs (hd'int.abs.const_mul _) ?_
          intro x _
          rw [abs_mul]
          nlinarith [abs_nonneg (exteriorPieceDeriv L k x), hPb x,
            abs_nonneg (∫ t in c..x, sawUnit ((n : ℝ) * t))]
      _ = (1 / (4 * (n : ℝ))) * ∫ x in c..d, |exteriorPieceDeriv L k x| :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ (1 / (4 * (n : ℝ))) * ∫ x in c..d, (L / x ^ (3 : ℕ) + L / x ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hvar (by positivity)
  have hterm1 : |exteriorPiece L k d * (∫ t in c..d, sawUnit ((n : ℝ) * t))|
      ≤ (1 / (4 * (n : ℝ))) * (L / (2 * d ^ (2 : ℕ))) := by
    rw [abs_mul]
    have hb1 := abs_exteriorPiece_le hL k (le_trans hkc hcd) hdk hdpos
    have hb2 := hPb d
    nlinarith [abs_nonneg (exteriorPiece L k d),
      abs_nonneg (∫ t in c..d, sawUnit ((n : ℝ) * t))]
  have hkey : (∫ x in c..d, exteriorPiece L k x * sawUnit ((n : ℝ) * x))
      = exteriorPiece L k d * (∫ t in c..d, sawUnit ((n : ℝ) * t))
        - ∫ x in c..d, exteriorPieceDeriv L k x * (∫ t in c..x, sawUnit ((n : ℝ) * t)) := by
    linarith [hibp]
  rw [hkey]
  calc |exteriorPiece L k d * (∫ t in c..d, sawUnit ((n : ℝ) * t))
        - ∫ x in c..d, exteriorPieceDeriv L k x * (∫ t in c..x, sawUnit ((n : ℝ) * t))|
      ≤ |exteriorPiece L k d * (∫ t in c..d, sawUnit ((n : ℝ) * t))|
        + |∫ x in c..d, exteriorPieceDeriv L k x *
            (∫ t in c..x, sawUnit ((n : ℝ) * t))| := abs_sub _ _
    _ ≤ (1 / (4 * (n : ℝ))) * (L / (2 * d ^ (2 : ℕ)))
        + (1 / (4 * (n : ℝ))) * ∫ x in c..d, (L / x ^ (3 : ℕ) + L / x ^ (2 : ℕ)) :=
        add_le_add hterm1 hterm2
    _ = (1 / (4 * (n : ℝ))) * (L / (2 * d ^ (2 : ℕ)) + ∫ x in c..d, (L / x ^ (3 : ℕ) + L / x ^ (2 : ℕ))) := by
        ring

/-- On one period the exterior integrand is the piece integrand. -/
theorem invSqWeight_mul_sawDilate_eq_exteriorPiece {L : ℝ} (k : ℤ) {x : ℝ}
    (hx : x ∈ Ico ((k : ℝ)) ((k : ℝ) + 1)) (n : ℕ) :
    invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))
      = exteriorPiece L k x * sawUnit ((n : ℝ) * x) := by
  rw [invSqWeight, exteriorPiece, sawUnit_eq_of_mem_Ico_int k hx]
  ring

/-! ## The exterior tail bound over whole periods -/

theorem hasDerivAt_invPowPrimitive {L : ℝ} (α : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => -(1 / 2) * (L / y ^ (2 : ℕ)) + (-α) * (L / y))
      (L / x ^ (3 : ℕ) + α * (L / x ^ (2 : ℕ))) x := by
  have h1 : HasDerivAt (fun y : ℝ => L / y ^ (2 : ℕ)) (-(2 * L) / x ^ (3 : ℕ)) x :=
    hasDerivAt_invSqWeight hx
  have h2 : HasDerivAt (fun y : ℝ => L / y) ((0 * x - L * 1) / x ^ (2 : ℕ)) x :=
    (hasDerivAt_const x L).div (hasDerivAt_id x) hx
  have h := (h1.const_mul (-(1 / 2) : ℝ)).add (h2.const_mul (-α))
  have hval : (-(1 / 2) : ℝ) * (-(2 * L) / x ^ (3 : ℕ)) + (-α) * ((0 * x - L * 1) / x ^ (2 : ℕ))
      = L / x ^ (3 : ℕ) + α * (L / x ^ (2 : ℕ)) := by
    field_simp
    ring
  rw [← hval]
  exact h

theorem integral_invPow {L c d α : ℝ} (hL : 0 < L) (hα : 0 ≤ α) (hc : 0 < c) (hcd : c ≤ d) :
    (∫ x in c..d, (L / x ^ (3 : ℕ) + α * (L / x ^ (2 : ℕ))))
      = (-(1 / 2) * (L / d ^ (2 : ℕ)) + (-α) * (L / d))
        - (-(1 / 2) * (L / c ^ (2 : ℕ)) + (-α) * (L / c)) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y : ℝ => -(1 / 2) * (L / y ^ (2 : ℕ)) + (-α) * (L / y)) (fun x hx => ?_) ?_
  · rw [uIcc_of_le hcd] at hx
    exact hasDerivAt_invPowPrimitive α (ne_of_gt (lt_of_lt_of_le hc hx.1))
  · refine intervalIntegrable_of_bound_on (by fun_prop)
      (C := L / c ^ (3 : ℕ) + α * (L / c ^ (2 : ℕ))) hcd ?_
    intro x hx
    have hxp : 0 < x := lt_of_lt_of_le hc hx.1
    have h3 : c ^ (3 : ℕ) ≤ x ^ (3 : ℕ) := by gcongr; exact hx.1
    have h2 : c ^ (2 : ℕ) ≤ x ^ (2 : ℕ) := by gcongr; exact hx.1
    have hb3 : L / x ^ (3 : ℕ) ≤ L / c ^ (3 : ℕ) := div_le_div_of_nonneg_left hL.le (by positivity) h3
    have hb2 : L / x ^ (2 : ℕ) ≤ L / c ^ (2 : ℕ) := div_le_div_of_nonneg_left hL.le (by positivity) h2
    rw [abs_of_pos (by positivity)]
    nlinarith [hb3, hb2, hα]

/-- **Equation (21), over one whole period.**  The boundary term of the per-period estimate is absorbed
by widening the weight `L x^{-3} + L x^{-2}` to `L x^{-3} + 2 L x^{-2}`, because over a full period
`∫ L x^{-2} = L/(k(k+1))` already dominates `L/(2(k+1)²)`. -/
theorem abs_integral_exteriorPiece_period_le {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L) {k : ℤ}
    (hk : (0 : ℝ) < (k : ℝ)) :
    |∫ x in (k : ℝ)..((k : ℝ) + 1), exteriorPiece L k x * sawUnit ((n : ℝ) * x)|
      ≤ (1 / (4 * (n : ℝ))) * ∫ x in (k : ℝ)..((k : ℝ) + 1), (L / x ^ (3 : ℕ) + 2 * (L / x ^ (2 : ℕ))) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcd : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have h := abs_integral_exteriorPiece_mul_le hn hL k hcd hk le_rfl le_rfl
  refine h.trans ?_
  have hone : (∫ x in (k : ℝ)..((k : ℝ) + 1), (L / x ^ (3 : ℕ) + L / x ^ (2 : ℕ)))
      = ∫ x in (k : ℝ)..((k : ℝ) + 1), (L / x ^ (3 : ℕ) + 1 * (L / x ^ (2 : ℕ))) :=
    intervalIntegral.integral_congr fun x _ => by ring
  rw [hone, integral_invPow hL zero_le_one hk hcd,
    integral_invPow hL (by norm_num : (0 : ℝ) ≤ 2) hk hcd]
  have hgap : L / (2 * ((k : ℝ) + 1) ^ (2 : ℕ)) ≤ L / (k : ℝ) - L / ((k : ℝ) + 1) := by
    rw [div_sub_div _ _ (ne_of_gt hk) (ne_of_gt hk1), div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith [hL.le, hk.le, sq_nonneg ((k : ℝ) - 1)]
  have hcoef : (0 : ℝ) < 1 / (4 * (n : ℝ)) := by positivity
  have hstep : L / (2 * ((k : ℝ) + 1) ^ (2 : ℕ))
      + ((-(1 / 2) * (L / ((k : ℝ) + 1) ^ (2 : ℕ)) + (-1 : ℝ) * (L / ((k : ℝ) + 1)))
        - (-(1 / 2) * (L / (k : ℝ) ^ (2 : ℕ)) + (-1 : ℝ) * (L / (k : ℝ))))
      ≤ (-(1 / 2) * (L / ((k : ℝ) + 1) ^ (2 : ℕ)) + (-2 : ℝ) * (L / ((k : ℝ) + 1)))
        - (-(1 / 2) * (L / (k : ℝ) ^ (2 : ℕ)) + (-2 : ℝ) * (L / (k : ℝ))) := by
    nlinarith [hgap]
  exact mul_le_mul_of_nonneg_left hstep hcoef.le

theorem intervalIntegrable_invSqWeight_mul_sawDilate (L : ℝ) (n : ℕ) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) : IntervalIntegrable
      (fun x => invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))) volume a b := by
  refine intervalIntegrable_of_bound_on (C := |L| / a ^ (2 : ℕ) * (1 / 4)) ?_ hab ?_
  · unfold invSqWeight
    exact (by fun_prop : Measurable fun x : ℝ => L / x ^ (2 : ℕ)).mul
      (measurable_sawUnit.mul (measurable_sawUnit.comp (measurable_const_mul _)))
  · intro x hx
    have hxp : 0 < x := lt_of_lt_of_le ha hx.1
    have h2 : a ^ (2 : ℕ) ≤ x ^ (2 : ℕ) := by gcongr; exact hx.1
    have hw : |invSqWeight L x| ≤ |L| / a ^ (2 : ℕ) := by
      rw [invSqWeight, abs_div, abs_of_pos (by positivity : (0 : ℝ) < x ^ (2 : ℕ))]
      exact div_le_div_of_nonneg_left (abs_nonneg L) (by positivity) h2
    have hs : |sawUnit x * sawUnit ((n : ℝ) * x)| ≤ 1 / 4 := by
      rw [abs_mul]
      calc |sawUnit x| * |sawUnit ((n : ℝ) * x)| ≤ (1 / 2) * (1 / 2) :=
            mul_le_mul (abs_sawUnit_le x) (abs_sawUnit_le _) (abs_nonneg _) (by norm_num)
        _ = 1 / 4 := by norm_num
    rw [abs_mul]
    exact mul_le_mul hw hs (abs_nonneg _) (by positivity)

/-- **Equation (21), over a whole number of periods.**  The exterior response over an integer window
beyond `L` is `O(1/n)` with the absolute constant `5/8`, uniformly in the window and in `L`.  This is
the estimate the card obtains by Stieltjes integration by parts; here every period is handled by the
distributional integration by parts against the dilated primitive, whose sup norm is `O(1/n)`. -/
theorem abs_integral_invSqWeight_mul_sawDilate_int_window_le {n : ℕ} (hn : 0 < n) {L : ℝ}
    (hL : 0 < L) {m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) (hLm : L ≤ (m : ℝ)) :
    |∫ x in (m : ℝ)..(M : ℝ), invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))|
      ≤ 5 / (8 * (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmMr : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
  have hcast : ∀ j : ℕ, ((m + (j + 1) : ℕ) : ℝ) = ((m + j : ℕ) : ℝ) + 1 := by
    intro j; push_cast; ring
  have hpos : ∀ j : ℕ, (0 : ℝ) < ((m + j : ℕ) : ℝ) := by
    intro j
    have : (0 : ℕ) < m + j := by omega
    exact_mod_cast this
  -- partition the window into periods
  have hpart := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => ((m + j : ℕ) : ℝ))
    (f := fun x => invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))
    (n := M - m)
    (fun j _ => by
      rw [hcast j]
      exact intervalIntegrable_invSqWeight_mul_sawDilate L n (hpos j) (by linarith))
  have hpartB := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => ((m + j : ℕ) : ℝ))
    (f := fun x : ℝ => L / x ^ (3 : ℕ) + 2 * (L / x ^ (2 : ℕ)))
    (n := M - m)
    (fun j _ => by
      rw [hcast j]
      refine intervalIntegrable_of_bound_on (by fun_prop)
        (C := L / ((m + j : ℕ) : ℝ) ^ (3 : ℕ) + 2 * (L / ((m + j : ℕ) : ℝ) ^ (2 : ℕ))) (by linarith) ?_
      intro x hx
      have hxp : 0 < x := lt_of_lt_of_le (hpos j) hx.1
      have h3 : ((m + j : ℕ) : ℝ) ^ (3 : ℕ) ≤ x ^ (3 : ℕ) := by gcongr; exact hx.1
      have h2 : ((m + j : ℕ) : ℝ) ^ (2 : ℕ) ≤ x ^ (2 : ℕ) := by gcongr; exact hx.1
      have hb3 : L / x ^ (3 : ℕ) ≤ L / ((m + j : ℕ) : ℝ) ^ (3 : ℕ) :=
        div_le_div_of_nonneg_left hL.le (by positivity) h3
      have hb2 : L / x ^ (2 : ℕ) ≤ L / ((m + j : ℕ) : ℝ) ^ (2 : ℕ) :=
        div_le_div_of_nonneg_left hL.le (by positivity) h2
      rw [abs_of_pos (by positivity)]
      nlinarith [hb3, hb2])
  have hends : ((m + 0 : ℕ) : ℝ) = (m : ℝ) ∧ ((m + (M - m) : ℕ) : ℝ) = (M : ℝ) := by
    refine ⟨by norm_num, ?_⟩
    congr 1
    omega
  rw [hends.1, hends.2] at hpart hpartB
  -- bound each period
  have hpiece : ∀ j ∈ Finset.range (M - m),
      |∫ x in ((m + j : ℕ) : ℝ)..((m + (j + 1) : ℕ) : ℝ),
          invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))|
        ≤ (1 / (4 * (n : ℝ))) *
          ∫ x in ((m + j : ℕ) : ℝ)..((m + (j + 1) : ℕ) : ℝ), (L / x ^ (3 : ℕ) + 2 * (L / x ^ (2 : ℕ))) := by
    intro j _
    set k : ℤ := ((m + j : ℕ) : ℤ) with hk
    have hkr : ((k : ℤ) : ℝ) = ((m + j : ℕ) : ℝ) := by rw [hk]; push_cast; ring
    rw [hcast j, ← hkr]
    have hcongr : (∫ x in (k : ℝ)..((k : ℝ) + 1),
        invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))
        = ∫ x in (k : ℝ)..((k : ℝ) + 1), exteriorPiece L k x * sawUnit ((n : ℝ) * x) := by
      refine integral_congr_of_Ioo (by linarith) fun x hx => ?_
      exact invSqWeight_mul_sawDilate_eq_exteriorPiece k ⟨hx.1.le, hx.2⟩ n
    rw [hcongr]
    exact abs_integral_exteriorPiece_period_le hn hL (by rw [hkr]; exact hpos j)
  -- assemble
  rw [← hpart]
  calc |∑ j ∈ Finset.range (M - m), ∫ x in ((m + j : ℕ) : ℝ)..((m + (j + 1) : ℕ) : ℝ),
        invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))|
      ≤ ∑ j ∈ Finset.range (M - m), |∫ x in ((m + j : ℕ) : ℝ)..((m + (j + 1) : ℕ) : ℝ),
          invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))| :=
        Finset.abs_sum_le_sum_abs
          (fun j => ∫ x in ((m + j : ℕ) : ℝ)..((m + (j + 1) : ℕ) : ℝ),
            invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))) (Finset.range (M - m))
    _ ≤ ∑ j ∈ Finset.range (M - m), (1 / (4 * (n : ℝ))) *
          ∫ x in ((m + j : ℕ) : ℝ)..((m + (j + 1) : ℕ) : ℝ), (L / x ^ (3 : ℕ) + 2 * (L / x ^ (2 : ℕ))) :=
        Finset.sum_le_sum hpiece
    _ = (1 / (4 * (n : ℝ))) * ∑ j ∈ Finset.range (M - m),
          ∫ x in ((m + j : ℕ) : ℝ)..((m + (j + 1) : ℕ) : ℝ), (L / x ^ (3 : ℕ) + 2 * (L / x ^ (2 : ℕ))) := by
        rw [Finset.mul_sum]
    _ = (1 / (4 * (n : ℝ))) * ∫ x in (m : ℝ)..(M : ℝ), (L / x ^ (3 : ℕ) + 2 * (L / x ^ (2 : ℕ))) := by
        rw [hpartB]
    _ ≤ 5 / (8 * (n : ℝ)) := by
        rw [integral_invPow hL (by norm_num : (0 : ℝ) ≤ 2) hmpos hmMr]
        have hMpos : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le hmpos hmMr
        have hb1 : L / (m : ℝ) ≤ 1 := by
          rw [div_le_one hmpos]; exact hLm
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hb2 : L / (m : ℝ) ^ (2 : ℕ) ≤ 1 := by
          rw [div_le_one (by positivity)]
          nlinarith [hLm, hm1]
        have hnn1 : (0 : ℝ) ≤ L / (M : ℝ) := by positivity
        have hnn2 : (0 : ℝ) ≤ L / (2 * (M : ℝ) ^ (2 : ℕ)) := by positivity
        have hnn3 : (0 : ℝ) ≤ L / (M : ℝ) ^ (2 : ℕ) := by positivity
        have hnn4 : (0 : ℝ) ≤ L / (m : ℝ) ^ (2 : ℕ) := by positivity
        have hkey : (-(1 / 2) * (L / (M : ℝ) ^ (2 : ℕ)) + (-2 : ℝ) * (L / (M : ℝ)))
            - (-(1 / 2) * (L / (m : ℝ) ^ (2 : ℕ)) + (-2 : ℝ) * (L / (m : ℝ))) ≤ 5 / 2 := by
          nlinarith [hb1, hb2, hnn1, hnn3, hnn4]
        have hcoef : (0 : ℝ) < 1 / (4 * (n : ℝ)) := by positivity
        calc (1 / (4 * (n : ℝ))) * ((-(1 / 2) * (L / (M : ℝ) ^ (2 : ℕ)) + (-2 : ℝ) * (L / (M : ℝ)))
              - (-(1 / 2) * (L / (m : ℝ) ^ (2 : ℕ)) + (-2 : ℝ) * (L / (m : ℝ))))
            ≤ (1 / (4 * (n : ℝ))) * (5 / 2) := mul_le_mul_of_nonneg_left hkey hcoef.le
          _ = 5 / (8 * (n : ℝ)) := by ring

/-- The partial-period bound: on a sub-interval of one period lying beyond `max 1 L`, the exterior
response is at most `1/(2n)`. -/
theorem abs_integral_invSqWeight_mul_sawDilate_partial_le {n : ℕ} (hn : 0 < n) {L : ℝ}
    (hL : 0 < L) {k : ℤ} {c d : ℝ} (hc1 : 1 ≤ c) (hLc : L ≤ c) (hcd : c ≤ d)
    (hkc : (k : ℝ) ≤ c) (hdk : d ≤ (k : ℝ) + 1) :
    |∫ x in c..d, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))|
      ≤ 2 / (4 * (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcpos : (0 : ℝ) < c := by linarith
  have hdpos : (0 : ℝ) < d := by linarith
  have hcongr : (∫ x in c..d, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))
      = ∫ x in c..d, exteriorPiece L k x * sawUnit ((n : ℝ) * x) := by
    refine integral_congr_of_Ioo hcd fun x hx => ?_
    exact invSqWeight_mul_sawDilate_eq_exteriorPiece k
      ⟨le_trans hkc hx.1.le, lt_of_lt_of_le hx.2 hdk⟩ n
  rw [hcongr]
  refine (abs_integral_exteriorPiece_mul_le hn hL k hcd hcpos hkc hdk).trans ?_
  have hone : (∫ x in c..d, (L / x ^ (3 : ℕ) + L / x ^ (2 : ℕ)))
      = ∫ x in c..d, (L / x ^ (3 : ℕ) + 1 * (L / x ^ (2 : ℕ))) :=
    intervalIntegral.integral_congr fun x _ => by ring
  rw [hone, integral_invPow hL zero_le_one hcpos hcd]
  have hLc1 : L / c ≤ 1 := by rw [div_le_one hcpos]; exact hLc
  have hLc2 : L / c ^ (2 : ℕ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [hLc, hc1]
  have hLd1 : (0 : ℝ) ≤ L / d := by positivity
  have hLd2 : (0 : ℝ) ≤ L / d ^ (2 : ℕ) := by positivity
  have hbd : L / (2 * d ^ (2 : ℕ)) ≤ 1 / 2 := by
    have hd2 : (1 : ℝ) ≤ d ^ (2 : ℕ) := by nlinarith [hc1, hcd]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hLc, hc1, hcd, hd2]
  have hcoef : (0 : ℝ) < 1 / (4 * (n : ℝ)) := by positivity
  have hstep : L / (2 * d ^ (2 : ℕ)) + ((-(1 / 2) * (L / d ^ (2 : ℕ)) + (-1 : ℝ) * (L / d))
      - (-(1 / 2) * (L / c ^ (2 : ℕ)) + (-1 : ℝ) * (L / c))) ≤ 2 := by
    nlinarith [hbd, hLc1, hLc2, hLd1, hLd2]
  calc (1 / (4 * (n : ℝ))) * (L / (2 * d ^ (2 : ℕ))
        + ((-(1 / 2) * (L / d ^ (2 : ℕ)) + (-1 : ℝ) * (L / d))
          - (-(1 / 2) * (L / c ^ (2 : ℕ)) + (-1 : ℝ) * (L / c))))
      ≤ (1 / (4 * (n : ℝ))) * 2 := mul_le_mul_of_nonneg_left hstep hcoef.le
    _ = 2 / (4 * (n : ℝ)) := by ring

/-- **Equation (21).**  For every `L ≥ 1` and every outer endpoint, the exterior response is `O(1/n)`
with the absolute constant `13/8`, uniformly in `L` and in the endpoint.  The window is cut into the
two partial end periods and a whole number of interior periods. -/
theorem abs_integral_invSqWeight_mul_sawDilate_window_le {n : ℕ} (hn : 0 < n) {L T : ℝ}
    (hL : 1 ≤ L) (hLT : L ≤ T) :
    |∫ x in L..T, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))|
      ≤ 13 / (8 * (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hLpos : (0 : ℝ) < L := by linarith
  have hfl1 : (1 : ℤ) ≤ ⌊L⌋ := by
    rw [Int.le_floor]
    exact_mod_cast hL
  have hflL : ((⌊L⌋ : ℤ) : ℝ) ≤ L := Int.floor_le L
  have hLfl : L < ((⌊L⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one L
  by_cases hcase : T < ((⌊L⌋ : ℤ) : ℝ) + 1
  · have h := abs_integral_invSqWeight_mul_sawDilate_partial_le hn hLpos (k := ⌊L⌋)
      hL le_rfl hLT hflL hcase.le
    refine h.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hn0]
  · -- the window contains at least one whole period
    replace hcase : ((⌊L⌋ : ℤ) : ℝ) + 1 ≤ T := not_lt.mp hcase
    set m : ℕ := ⌊L⌋.toNat + 1 with hm
    set M : ℕ := ⌊T⌋.toNat with hM
    have htn : ((⌊L⌋.toNat : ℕ) : ℝ) = ((⌊L⌋ : ℤ) : ℝ) := by
      have hz : ((⌊L⌋.toNat : ℕ) : ℤ) = ⌊L⌋ := Int.toNat_of_nonneg (by omega)
      exact_mod_cast hz
    have hmr : ((m : ℕ) : ℝ) = ((⌊L⌋ : ℤ) : ℝ) + 1 := by
      rw [hm]
      push_cast
      linarith [htn]
    have hMr : ((M : ℕ) : ℝ) = ((⌊T⌋ : ℤ) : ℝ) := by
      rw [hM]
      have hT0 : (0 : ℤ) ≤ ⌊T⌋ := by
        rw [Int.le_floor]
        push_cast
        linarith
      exact_mod_cast Int.toNat_of_nonneg hT0
    have hLm : L ≤ ((m : ℕ) : ℝ) := by rw [hmr]; linarith
    have hm1 : 1 ≤ m := by omega
    have hflT : (⌊L⌋ + 1 : ℤ) ≤ ⌊T⌋ := by
      rw [Int.le_floor]
      push_cast
      linarith
    have hmM : m ≤ M := by
      rw [hm, hM]
      omega
    have hMT : ((M : ℕ) : ℝ) ≤ T := by rw [hMr]; exact Int.floor_le T
    have hmMr : ((m : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) := by exact_mod_cast hmM
    have hmpos : (0 : ℝ) < ((m : ℕ) : ℝ) := by rw [hmr]; linarith
    -- split
    have hi1 := intervalIntegrable_invSqWeight_mul_sawDilate L n hLpos hLm
    have hi2 := intervalIntegrable_invSqWeight_mul_sawDilate L n hmpos hmMr
    have hi3 := intervalIntegrable_invSqWeight_mul_sawDilate L n
      (lt_of_lt_of_le hmpos hmMr) hMT
    have hadj1 := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hadj2 := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_invSqWeight_mul_sawDilate L n hLpos (le_trans hLm hmMr)) hi3
    have hsplit : (∫ x in L..T, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))
        = (∫ x in L..((m : ℕ) : ℝ), invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))
          + (∫ x in ((m : ℕ) : ℝ)..((M : ℕ) : ℝ),
              invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))
          + ∫ x in ((M : ℕ) : ℝ)..T, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)) := by
      linarith [hadj1, hadj2]
    have hb1 : |∫ x in L..((m : ℕ) : ℝ),
        invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))| ≤ 2 / (4 * (n : ℝ)) := by
      refine abs_integral_invSqWeight_mul_sawDilate_partial_le hn hLpos (k := ⌊L⌋)
        hL le_rfl hLm hflL ?_
      rw [hmr]
    have hb2 := abs_integral_invSqWeight_mul_sawDilate_int_window_le hn hLpos hm1 hmM hLm
    have hb3 : |∫ x in ((M : ℕ) : ℝ)..T,
        invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))| ≤ 2 / (4 * (n : ℝ)) := by
      refine abs_integral_invSqWeight_mul_sawDilate_partial_le hn hLpos (k := ⌊T⌋) ?_ ?_ hMT ?_ ?_
      · rw [hMr]
        exact_mod_cast Int.le_floor.mpr (by push_cast; linarith)
      · exact le_trans hLm hmMr
      · rw [hMr]
      · exact (Int.lt_floor_add_one T).le
    rw [hsplit]
    calc |(∫ x in L..((m : ℕ) : ℝ), invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))
          + (∫ x in ((m : ℕ) : ℝ)..((M : ℕ) : ℝ),
              invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))
          + ∫ x in ((M : ℕ) : ℝ)..T, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))|
        ≤ |∫ x in L..((m : ℕ) : ℝ), invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))|
          + |∫ x in ((m : ℕ) : ℝ)..((M : ℕ) : ℝ),
              invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))|
          + |∫ x in ((M : ℕ) : ℝ)..T,
              invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))| := abs_add_three _ _ _
      _ ≤ 2 / (4 * (n : ℝ)) + 5 / (8 * (n : ℝ)) + 2 / (4 * (n : ℝ)) :=
          add_le_add (add_le_add hb1 hb2) hb3
      _ = 13 / (8 * (n : ℝ)) := by ring

/-! ## The full exterior half-line -/

theorem intervalIntegrable_invSqWeight {L a b : ℝ} (hL : 0 < L) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (invSqWeight L) volume a b := by
  refine intervalIntegrable_of_bound_on (by unfold invSqWeight; fun_prop)
    (C := L / a ^ (2 : ℕ)) hab ?_
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
  have hsq : a ^ (2 : ℕ) ≤ x ^ (2 : ℕ) := by gcongr; exact hx.1
  rw [invSqWeight, abs_of_pos (by positivity)]
  exact div_le_div_of_nonneg_left hL.le (by positivity) hsq

theorem tendsto_shift_natCast_atTop (L : ℝ) :
    Tendsto (fun i : ℕ => L + (i : ℝ)) atTop atTop :=
  Filter.tendsto_atTop_add_const_left atTop L tendsto_natCast_atTop_atTop

theorem integrableOn_invSqWeight_mul_sawDilate {L : ℝ} (hL : 0 < L) (n : ℕ) :
    IntegrableOn (fun x => invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))) (Ioi L) := by
  refine MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded (1 / 4) L
    (b := fun i : ℕ => L + (i : ℝ)) ?_ (tendsto_shift_natCast_atTop L) ?_
  · intro i
    have hle : L ≤ L + (i : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg i)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      (intervalIntegrable_invSqWeight_mul_sawDilate L n hL hle)
  · refine Filter.Eventually.of_forall fun i => ?_
    have hle : L ≤ L + (i : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg i)
    have hwi : IntervalIntegrable (invSqWeight L) volume L (L + (i : ℝ)) :=
      intervalIntegrable_invSqWeight hL hL hle
    have hfi : IntervalIntegrable
        (fun x => invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))) volume L (L + (i : ℝ)) :=
      intervalIntegrable_invSqWeight_mul_sawDilate L n hL hle
    have hptw : ∀ x ∈ Icc L (L + (i : ℝ)),
        ‖invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))‖
          ≤ (1 / 4) * invSqWeight L x := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hL hx.1
      have hwnn : (0 : ℝ) ≤ invSqWeight L x := by rw [invSqWeight]; positivity
      have hs : |sawUnit x * sawUnit ((n : ℝ) * x)| ≤ 1 / 4 := by
        rw [abs_mul]
        calc |sawUnit x| * |sawUnit ((n : ℝ) * x)| ≤ (1 / 2) * (1 / 2) :=
              mul_le_mul (abs_sawUnit_le x) (abs_sawUnit_le _) (abs_nonneg _) (by norm_num)
          _ = 1 / 4 := by norm_num
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hwnn]
      nlinarith [hs, hwnn, abs_nonneg (sawUnit x * sawUnit ((n : ℝ) * x))]
    calc (∫ x in L..(L + (i : ℝ)), ‖invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))‖)
        ≤ ∫ x in L..(L + (i : ℝ)), (1 / 4) * invSqWeight L x :=
          intervalIntegral.integral_mono_on hle hfi.norm (hwi.const_mul _) hptw
      _ = (1 / 4) * ∫ x in L..(L + (i : ℝ)), invSqWeight L x :=
          intervalIntegral.integral_const_mul _ _
      _ = (1 / 4) * (1 - L / (L + (i : ℝ))) := by rw [integral_invSqWeight hL hle]
      _ ≤ 1 / 4 := by
          have hnn : (0 : ℝ) ≤ L / (L + (i : ℝ)) := by positivity
          nlinarith [hnn]

theorem tendsto_integral_invSqWeight_mul_sawDilate {L : ℝ} (hL : 0 < L) (n : ℕ) :
    Tendsto (fun i : ℕ => ∫ x in L..(L + (i : ℝ)),
        invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))
      atTop (nhds (∫ x in Ioi L, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))) :=
  MeasureTheory.intervalIntegral_tendsto_integral_Ioi L
    (integrableOn_invSqWeight_mul_sawDilate hL n) (tendsto_shift_natCast_atTop L)

/-- **Equations (20)--(21).**  The full exterior response `J_n(L)/L` is `O(1/n)`, uniformly in
`L ≥ 1`. -/
theorem abs_integral_Ioi_invSqWeight_mul_sawDilate_le {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 1 ≤ L) :
    |∫ x in Ioi L, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))|
      ≤ 13 / (8 * (n : ℝ)) := by
  have hLpos : (0 : ℝ) < L := by linarith
  have habs := (tendsto_integral_invSqWeight_mul_sawDilate hLpos n).abs
  refine le_of_tendsto habs (Filter.Eventually.of_forall fun i => ?_)
  exact abs_integral_invSqWeight_mul_sawDilate_window_le hn hL
    (le_add_of_nonneg_right (Nat.cast_nonneg i))

/-- **Equation (18).**  The full exterior response equals the exact mean `1/(12 n)` up to `4/(3L)`,
uniformly in the dilation. -/
theorem abs_integral_Ioi_invSqWeight_mul_sawDilate_sub_mean_le {n : ℕ} (hn : 0 < n) {L : ℝ}
    (hL : 0 < L) :
    |(∫ x in Ioi L, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))
      - 1 / (12 * (n : ℝ))| ≤ 4 / (3 * L) := by
  have hzero : Tendsto (fun i : ℕ => L / (L + (i : ℝ))) atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds (tendsto_shift_natCast_atTop L)
  have hmean : Tendsto (fun i : ℕ => (1 / (12 * (n : ℝ))) * (1 - L / (L + (i : ℝ)))) atTop
      (nhds ((1 / (12 * (n : ℝ))) * (1 - 0))) :=
    (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub
      hzero).const_mul _)
  have hdiff := ((tendsto_integral_invSqWeight_mul_sawDilate hL n).sub hmean).abs
  have hlim : (∫ x in Ioi L, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))
      - (1 / (12 * (n : ℝ))) * (1 - 0) = (∫ x in Ioi L,
        invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))) - 1 / (12 * (n : ℝ)) := by
    ring
  rw [← hlim]
  refine le_of_tendsto hdiff (Filter.Eventually.of_forall fun i => ?_)
  exact abs_integral_invSqWeight_mul_sawDilate_sub_mean_le hn hL
    (le_add_of_nonneg_right (Nat.cast_nonneg i))

/-! ## The full prime response -/

theorem summable_fullPrimeResponse {L : ℝ} (hL : 1 ≤ L) :
    Summable (fun n : ℕ => Λ n / (n : ℝ) *
      ∫ x in Ioi L, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => (13 / 8) * (Λ n / (n : ℝ) ^ (2 : ℕ)))
    (summable_vonMangoldt_div_sq.mul_left _) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hLam : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    have hw : (0 : ℝ) ≤ Λ n / (n : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    calc Λ n / (n : ℝ) *
          |∫ x in Ioi L, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))|
        ≤ Λ n / (n : ℝ) * (13 / (8 * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (abs_integral_Ioi_invSqWeight_mul_sawDilate_le hn hL) hw
      _ = (13 / 8) * (Λ n / (n : ℝ) ^ (2 : ℕ)) := by
          field_simp

theorem tendsto_integral_Ioi_invSqWeight_mul_sawDilate {n : ℕ} (hn : 0 < n) :
    Tendsto (fun L : ℝ => ∫ x in Ioi L,
        invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))
      atTop (nhds (1 / (12 * (n : ℝ)))) := by
  have hbound : Tendsto (fun L : ℝ => 4 / (3 * L)) atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 3) tendsto_id)
  have hz : Tendsto (fun L : ℝ => (∫ x in Ioi L,
      invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))) - 1 / (12 * (n : ℝ)))
      atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hLpos
    rw [Real.norm_eq_abs]
    exact abs_integral_Ioi_invSqWeight_mul_sawDilate_sub_mean_le hn hLpos
  have hsum := hz.add (tendsto_const_nhds (α := ℝ) (x := 1 / (12 * (n : ℝ))) (f := atTop))
  simpa using hsum

/-- **Equation (23).**  As the aperture grows, the full prime response converges to the universal Euler
scalar `(1/12) ∑ Λ(n) n^{-2}`, which by `(17)` is `-(1/12) ζ'(2)/ζ(2)`.  The domination is the uniform
`O(1/n)` bound `(21)`; the termwise limit is `(18)`. -/
theorem tendsto_fullPrimeResponse :
    Tendsto (fun L : ℝ => ∑' n : ℕ, Λ n / (n : ℝ) *
        ∫ x in Ioi L, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x)))
      atTop (nhds ((1 / 12) * ∑' n : ℕ, Λ n / (n : ℝ) ^ (2 : ℕ))) := by
  have hlim : ((1 / 12 : ℝ) * ∑' n : ℕ, Λ n / (n : ℝ) ^ (2 : ℕ))
      = ∑' n : ℕ, (1 / 12 : ℝ) * (Λ n / (n : ℝ) ^ (2 : ℕ)) := by
    rw [tsum_mul_left]
  rw [hlim]
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun n : ℕ => (13 / 8) * (Λ n / (n : ℝ) ^ (2 : ℕ)))
    (summable_vonMangoldt_div_sq.mul_left _) (fun n => ?_) ?_
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h := (tendsto_integral_Ioi_invSqWeight_mul_sawDilate hn).const_mul (Λ n / (n : ℝ))
      have hval : Λ n / (n : ℝ) * (1 / (12 * (n : ℝ)))
          = (1 / 12 : ℝ) * (Λ n / (n : ℝ) ^ (2 : ℕ)) := by
        field_simp
      rw [hval] at h
      exact h
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hLam : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
      have hw : (0 : ℝ) ≤ Λ n / (n : ℝ) := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
      calc Λ n / (n : ℝ) *
            |∫ x in Ioi L, invSqWeight L x * (sawUnit x * sawUnit ((n : ℝ) * x))|
          ≤ Λ n / (n : ℝ) * (13 / (8 * (n : ℝ))) :=
            mul_le_mul_of_nonneg_left
              (abs_integral_Ioi_invSqWeight_mul_sawDilate_le hn hL) hw
        _ = (13 / 8) * (Λ n / (n : ℝ) ^ (2 : ℕ)) := by
            field_simp

/-! ## Equation (20): the two readings of the exterior integral -/

theorem image_Ioi_exp_scale {L : ℝ} (hL : 0 < L) :
    (fun s => L * Real.exp s) '' Ioi 0 = Ioi L := by
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    have h1 : (1 : ℝ) < Real.exp s := by
      have := Real.exp_lt_exp.mpr hs
      simpa using this
    have : L * 1 < L * Real.exp s := by nlinarith
    simpa using this
  · intro hy
    have hypos : (0 : ℝ) < y := lt_trans hL hy
    have hdiv : (1 : ℝ) < y / L := by
      rw [lt_div_iff₀ hL, one_mul]
      exact hy
    refine ⟨Real.log (y / L), ?_, ?_⟩
    · exact Real.log_pos hdiv
    · show L * Real.exp (Real.log (y / L)) = y
      rw [Real.exp_log (by positivity)]
      field_simp

/-- The change of variables `x = L e^s` on the half-line. -/
theorem integral_comp_exp_scale_Ioi {L : ℝ} (hL : 0 < L) (F : ℝ → ℝ) :
    (∫ x in Ioi L, F x) = ∫ s in Ioi (0 : ℝ), (L * Real.exp s) * F (L * Real.exp s) := by
  have hderiv : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun s => L * Real.exp s) (L * Real.exp s) (Ioi (0 : ℝ)) s :=
    fun s _ => ((Real.hasDerivAt_exp s).const_mul L).hasDerivWithinAt
  have hinj : InjOn (fun s => L * Real.exp s) (Ioi (0 : ℝ)) := by
    intro u _ v _ huv
    have hmul : L * Real.exp u = L * Real.exp v := huv
    exact Real.exp_eq_exp.mp (mul_left_cancel₀ (ne_of_gt hL) hmul)
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (f := fun s => L * Real.exp s) (f' := fun s => L * Real.exp s) (s := Ioi (0 : ℝ))
    measurableSet_Ioi hderiv hinj F
  rw [image_Ioi_exp_scale hL] at hcov
  rw [hcov]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [smul_eq_mul, abs_of_pos (by positivity)]

/-- **Equation (20).**  The additive and multiplicative readings of the full exterior integral agree:
`∫_0^∞ e^{-s} h(L e^s) ds = L ∫_L^∞ h(x) x^{-2} dx`. -/
theorem integral_expWeight_Ioi_eq_invSqWeight {L : ℝ} (hL : 0 < L) (h : ℝ → ℝ) :
    (∫ s in Ioi (0 : ℝ), Real.exp (-s) * h (L * Real.exp s))
      = ∫ x in Ioi L, invSqWeight L x * h x := by
  rw [integral_comp_exp_scale_Ioi hL (fun x => invSqWeight L x * h x)]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  have hpos : (0 : ℝ) < L * Real.exp s := by positivity
  have hne : Real.exp s ≠ 0 := Real.exp_ne_zero s
  rw [invSqWeight, Real.exp_neg]
  field_simp

end GaloisForLFunctions.RHTower

end
