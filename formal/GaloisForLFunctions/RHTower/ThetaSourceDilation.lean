import GaloisForLFunctions.RHTower.ThetaTiltFluxCarrier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Mass-preserving dilation of theta sources

Normalized source dilation preserves positivity, evenness, rapid decay,
and total mass. Its bilateral transform undergoes reciprocal coordinate
scaling, and its source Bezoutian has an exact positive scaling law.
-/

noncomputable section

open Complex MeasureTheory
open scoped ComplexConjugate

namespace RHTower

/-- The normalized dilation action on positive even rapidly decaying sources. -/
def thetaSourceDilation (S : ThetaSource) (r : ℝ) : ThetaSource where
  k x := Real.exp (-r) * S.k (Real.exp (-r) * x)
  pos x := mul_pos (Real.exp_pos _) (S.pos _)
  even' x := by rw [mul_neg, S.even']
  cont := continuous_const.mul (S.cont.comp (continuous_const.mul continuous_id))
  decay M := by
    obtain ⟨C, hC, hbd⟩ := S.decay (M * Real.exp r)
    refine ⟨Real.exp (-r) * C, mul_pos (Real.exp_pos _) hC, fun x => ?_⟩
    have hc : Real.exp r * Real.exp (-r) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have he : (M * Real.exp r) * |Real.exp (-r) * x| = M * |x| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        _ = M * (Real.exp r * Real.exp (-r)) * |x| := by ring
        _ = _ := by rw [hc, mul_one]
    calc
      _ ≤ Real.exp (-r) * (C * Real.exp (-((M * Real.exp r) * |Real.exp (-r) * x|))) :=
        mul_le_mul_of_nonneg_left (hbd _) (Real.exp_pos _).le
      _ = _ := by rw [he]; ring

theorem thetaSourceDilation_zero (S : ThetaSource) : thetaSourceDilation S 0 = S := by
  cases S
  simp [thetaSourceDilation]

/-- Normalized dilations form a real additive action on the source space. -/
theorem thetaSourceDilation_add (S : ThetaSource) (r s : ℝ) :
    thetaSourceDilation (thetaSourceDilation S r) s = thetaSourceDilation S (r + s) := by
  unfold thetaSourceDilation
  congr 1
  funext x
  simp only [neg_add, Real.exp_add, mul_assoc, mul_left_comm, mul_comm]

theorem bilateralLaplace_thetaSourceDilation (S : ThetaSource) (r : ℝ) (w : ℂ) :
    bilateralLaplace (thetaSourceDilation S r) w =
      bilateralLaplace S ((Real.exp r : ℂ) * w) := by
  have hc : (Real.exp r : ℂ) * (Real.exp (-r) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  have he (x : ℝ) : ((Real.exp r : ℂ) * w) * ((Real.exp (-r) * x : ℝ) : ℂ) = w * x := by
    rw [Complex.ofReal_mul]
    calc
      _ = ((Real.exp r : ℂ) * (Real.exp (-r) : ℂ)) * (w * x) := by ring
      _ = _ := by rw [hc, one_mul]
  have hf : (fun x : ℝ => ((thetaSourceDilation S r).k x : ℂ) * Complex.exp (w * x)) =
      fun x : ℝ => (Real.exp (-r) : ℂ) *
        ((S.k (Real.exp (-r) * x) : ℂ) *
          Complex.exp (((Real.exp r : ℂ) * w) * ((Real.exp (-r) * x : ℝ) : ℂ))) := by
    funext x
    rw [he]
    simp only [thetaSourceDilation, Complex.ofReal_mul, mul_assoc]
  unfold bilateralLaplace
  rw [hf, integral_const_mul]
  rw [Measure.integral_comp_mul_left
    (fun y : ℝ => (S.k y : ℂ) * Complex.exp (((Real.exp r : ℂ) * w) * (y : ℂ)))
      (Real.exp (-r))]
  simp only [Real.exp_neg, inv_inv, abs_of_pos (Real.exp_pos _), Complex.real_smul]
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (Real.exp_ne_zero r),
    Complex.ofReal_one, one_mul]

/-- Dilation is a symmetry of the source's total mass. -/
theorem bilateralLaplace_thetaSourceDilation_zero (S : ThetaSource) (r : ℝ) :
    bilateralLaplace (thetaSourceDilation S r) 0 = bilateralLaplace S 0 := by
  rw [bilateralLaplace_thetaSourceDilation, mul_zero]

theorem bilateralLaplaceDeriv_thetaSourceDilation (S : ThetaSource) (r : ℝ) (w : ℂ) :
    bilateralLaplaceDeriv (thetaSourceDilation S r) w =
      (Real.exp r : ℂ) * bilateralLaplaceDeriv S ((Real.exp r : ℂ) * w) := by
  have hi : HasDerivAt (fun z : ℂ => (Real.exp r : ℂ) * z) (Real.exp r : ℂ) w := by
    simpa using (hasDerivAt_id w).const_mul (Real.exp r : ℂ)
  have h := (hasDerivAt_bilateralLaplace S ((Real.exp r : ℂ) * w)).comp w hi
  have hf : (fun z : ℂ => bilateralLaplace S ((Real.exp r : ℂ) * z)) =
      bilateralLaplace (thetaSourceDilation S r) :=
    (funext (bilateralLaplace_thetaSourceDilation S r)).symm
  change HasDerivAt (fun z : ℂ => bilateralLaplace S ((Real.exp r : ℂ) * z)) _ w at h
  rw [hf] at h
  exact ((hasDerivAt_bilateralLaplace (thetaSourceDilation S r) w).unique h).trans (mul_comm _ _)

/-- A positive scale factor transports every diagonal and cross-node source Bezoutian. -/
theorem sourceBezoutian_thetaSourceDilation (S : ThetaSource) (r : ℝ) (w v : ℂ) :
    sourceBezoutian (thetaSourceDilation S r) w v =
      (Real.exp r : ℂ) ^ 2 * sourceBezoutian S ((Real.exp r : ℂ) * w) ((Real.exp r : ℂ) * v) := by
  simp only [sourceBezoutian, bilateralLaplace_thetaSourceDilation,
    bilateralLaplaceDeriv_thetaSourceDilation, map_mul, Complex.conj_ofReal]
  have hc : (Real.exp r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero r)
  have he : (Real.exp r : ℂ) * w + (Real.exp r : ℂ) * conj v =
      (Real.exp r : ℂ) * (w + conj v) := by ring
  rw [he]
  by_cases hd : w + conj v = 0
  · simp only [hd, mul_zero, div_zero]
  · field_simp

end RHTower
