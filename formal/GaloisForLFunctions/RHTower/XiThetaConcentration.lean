import GaloisForLFunctions.RHTower.XiThetaPolynomialExpectation
import GaloisForLFunctions.RHTower.ThetaJensenCenteredMomentLimit

/-!
# Concentration of the actual Xi moment source

Fixed pointwise comparison with the leading theta channel transfers every
centered-moment limit to the full source defining the Xi Jensen coefficients.
-/

open Real MeasureTheory Set Filter Topology Polynomial

noncomputable section

namespace RHTower

theorem integrableOn_xiTheta_centered (n k : ℕ) (s : ℝ) :
    IntegrableOn (fun x : ℝ => (x ^ 2 - s ^ 2) ^ k * x ^ (2 * n) * thetaCuspFullSource x) (Ioi 0) := by
  apply (integrableOn_xiTheta_polynomial n ((X - C (s ^ 2)) ^ k)).congr
  filter_upwards [] with x
  simp only [eval_pow, eval_sub, eval_X, eval_C]

theorem xiThetaCenteredMoment_mul_le_leading (n p : ℕ) (s : ℝ) :
    xiThetaCenteredMoment n (2 * p) s * thetaJensenCenteredMoment n 0 s ≤
      xiThetaSourceComparisonFactor * thetaJensenCenteredMoment n (2 * p) s := by
  have hI := integral_mono_ae (integrableOn_xiTheta_centered n (2 * p) s)
    ((integrableOn_thetaJensen_centered n (2 * p) s).const_mul
      (2 * Real.pi ^ 2 * xiThetaSourceComparisonFactor)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 ≤ x := hx.le
      have hfactor : 0 ≤ (x ^ 2 - s ^ 2) ^ (2 * p) * x ^ (2 * n) := by
        rw [pow_mul]
        positivity
      have h := mul_le_mul_of_nonneg_left (thetaCuspFullSource_le_jensenWeight hx.le) hfactor
      convert h using 1
      ring)
  rw [integral_const_mul, ← thetaJensenCenteredMoment_eq_integral] at hI
  have hmass := mul_le_mul_of_nonneg_right (thetaCuspRawEvenMoment_ge_jensenWeight n s)
    (xiThetaCenteredMoment_even_nonneg n p s)
  have hm := thetaCuspRawEvenMoment_pos n
  have hnorm : xiThetaCenteredMoment n (2 * p) s * thetaCuspRawEvenMoment n =
      2 * ∫ x : ℝ in Ioi 0, (x ^ 2 - s ^ 2) ^ (2 * p) * x ^ (2 * n) * thetaCuspFullSource x := by
    rw [xiThetaCenteredMoment_eq_integral]
    field_simp
  apply le_of_mul_le_mul_left (a := 4 * Real.pi ^ 2) _ (by positivity)
  nlinarith

def xiThetaNormalizedCenteredMoment (n p : ℕ) : ℝ :=
  ((n : ℝ) + 1 / 2) ^ p * xiThetaCenteredMoment n (2 * p) (thetaJensenSaddle n) /
    thetaJensenSaddle n ^ (4 * p)

theorem xiThetaNormalizedCenteredMoment_nonneg (n p : ℕ) :
    0 ≤ xiThetaNormalizedCenteredMoment n p := by
  have hs := thetaJensenSaddle_pos n
  have hm := xiThetaCenteredMoment_even_nonneg n p (thetaJensenSaddle n)
  unfold xiThetaNormalizedCenteredMoment
  positivity

theorem xiThetaNormalizedCenteredMoment_le (n p : ℕ) :
    xiThetaNormalizedCenteredMoment n p ≤
      xiThetaSourceComparisonFactor * thetaJensenNormalizedCenteredMoment n p := by
  have hs := thetaJensenSaddle_pos n
  have h0 := thetaJensenCenteredMoment_zero_pos n (thetaJensenSaddle n)
  have h := mul_le_mul_of_nonneg_left
    (xiThetaCenteredMoment_mul_le_leading n p (thetaJensenSaddle n))
    (show 0 ≤ ((n : ℝ) + 1 / 2) ^ p by positivity)
  have hd := div_le_div_of_nonneg_right h
    (show 0 ≤ thetaJensenSaddle n ^ (4 * p) * thetaJensenCenteredMoment n 0 (thetaJensenSaddle n)
      by positivity)
  unfold xiThetaNormalizedCenteredMoment thetaJensenNormalizedCenteredMoment
  convert hd using 1 <;> try rfl
  all_goals field_simp

theorem tendsto_xiThetaNormalizedCenteredMoment_succ (p : ℕ) :
    Tendsto (fun n => xiThetaNormalizedCenteredMoment n (p + 1)) atTop (𝓝 0) := by
  have h := (tendsto_thetaJensenNormalizedCenteredMoment_succ p).const_mul xiThetaSourceComparisonFactor
  apply squeeze_zero' (Eventually.of_forall (fun n => xiThetaNormalizedCenteredMoment_nonneg n _))
    (Eventually.of_forall (fun n => xiThetaNormalizedCenteredMoment_le n _))
  simpa using h

/-- Hermite width, in the probabilists' normalization. -/
def xiJensenDelta (n : ℕ) : ℝ := (Real.sqrt ((n : ℝ) + 1 / 2))⁻¹

/-- The affine scale set by the actual theta moment saddle. -/
def xiJensenScale (n : ℕ) : ℝ := thetaJensenSaddle n ^ 2 / (4 * ((n : ℝ) + 1 / 2))

theorem xiJensenDelta_pos (n : ℕ) : 0 < xiJensenDelta n := by
  unfold xiJensenDelta
  positivity

theorem xiJensenScale_pos (n : ℕ) : 0 < xiJensenScale n := by
  have hs := thetaJensenSaddle_pos n
  unfold xiJensenScale
  positivity

theorem xiJensenDelta_sq (n : ℕ) :
    ((n : ℝ) + 1 / 2) * xiJensenDelta n ^ 2 = 1 := by
  rw [xiJensenDelta, inv_pow, Real.sq_sqrt (by positivity)]
  have hr : (n : ℝ) + 1 / 2 ≠ 0 := by positivity
  exact mul_inv_cancel₀ hr

def xiThetaFluctuation (n : ℕ) : ℝ[X] :=
  C (Real.sqrt ((n : ℝ) + 1 / 2) / thetaJensenSaddle n ^ 2) *
    (X - C (thetaJensenSaddle n ^ 2))

theorem xiThetaExpectation_fluctuation_pow (n k : ℕ) :
    xiThetaExpectation n (xiThetaFluctuation n ^ k) =
      (Real.sqrt ((n : ℝ) + 1 / 2) / thetaJensenSaddle n ^ 2) ^ k *
        xiThetaCenteredMoment n k (thetaJensenSaddle n) := by
  rw [xiThetaFluctuation, mul_pow, ← map_pow, xiThetaExpectation_C_mul]
  rfl

theorem xiThetaExpectation_fluctuation_even (n p : ℕ) :
    xiThetaExpectation n (xiThetaFluctuation n ^ (2 * p)) = xiThetaNormalizedCenteredMoment n p := by
  rw [xiThetaExpectation_fluctuation_pow]
  have hpow : (Real.sqrt ((n : ℝ) + 1 / 2) / thetaJensenSaddle n ^ 2) ^ (2 * p) =
      ((n : ℝ) + 1 / 2) ^ p / thetaJensenSaddle n ^ (4 * p) := by
    rw [div_pow, pow_mul, Real.sq_sqrt (by positivity), ← pow_mul,
      show 2 * (2 * p) = 4 * p by omega]
  rw [hpow, xiThetaNormalizedCenteredMoment]
  ring

theorem xiThetaExpectation_fluctuation_sq_le (n k : ℕ) :
    xiThetaExpectation n (xiThetaFluctuation n ^ k) ^ 2 ≤
      xiThetaExpectation n (xiThetaFluctuation n ^ (2 * k)) := by
  rw [xiThetaExpectation_fluctuation_pow, xiThetaExpectation_fluctuation_pow, mul_pow]
  have h := mul_le_mul_of_nonneg_left
    (xiThetaCenteredMoment_sq_le n k (thetaJensenSaddle n))
    (sq_nonneg ((Real.sqrt ((n : ℝ) + 1 / 2) / thetaJensenSaddle n ^ 2) ^ k))
  simpa only [← pow_mul, Nat.mul_comm k 2] using h

/-- All positive fluctuation moments of the actual Xi source vanish. -/
theorem tendsto_xiThetaExpectation_fluctuation_succ (k : ℕ) :
    Tendsto (fun n => xiThetaExpectation n (xiThetaFluctuation n ^ (k + 1))) atTop (𝓝 0) := by
  have heven : Tendsto (fun n => xiThetaExpectation n (xiThetaFluctuation n ^ (2 * (k + 1))))
      atTop (𝓝 0) := by
    simpa only [xiThetaExpectation_fluctuation_even] using tendsto_xiThetaNormalizedCenteredMoment_succ k
  have hsqrt : Tendsto (fun n => Real.sqrt (xiThetaExpectation n (xiThetaFluctuation n ^ (2 * (k + 1)))))
      atTop (𝓝 0) := by
    convert (Real.continuous_sqrt.tendsto 0).comp heven using 1 <;>
      first | rfl | simp only [Real.sqrt_zero]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hsqrt
  apply Eventually.of_forall
  intro n
  have hnonneg : 0 ≤ xiThetaExpectation n (xiThetaFluctuation n ^ (2 * (k + 1))) := by
    rw [xiThetaExpectation_fluctuation_even]
    exact xiThetaNormalizedCenteredMoment_nonneg n _
  rw [Real.norm_eq_abs]
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt hnonneg]
  exact xiThetaExpectation_fluctuation_sq_le n (k + 1)

end RHTower
