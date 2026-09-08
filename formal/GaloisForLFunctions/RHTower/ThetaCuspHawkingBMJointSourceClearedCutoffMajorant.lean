import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceClearedUniformBound
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceContinuedAdmission

/-! A single square-integrable horizon majorant for the actual cleared cutoff family near a QNM. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore D4BMJointWave
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The actual undivided cutoff numerator retains the original horizon factor. -/
def clearedCutoffRadialCoefficient (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (i : Fin 3) (t : ℝ) : ℂ :=
  (horizonCoordinate t:ℂ)*clearedPrincipalDifference q branch w a i t

/-- Equality to the actual cutoff coefficient after clearing the common original denominator. -/
theorem clearedCutoffRadialCoefficient_eq (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (i : Fin 3)
    (hs : w-2*physicalRate q branch ≠ 0) (hc : connection w (principalFrequency q i) ≠ 0) (t : ℝ) :
    clearedCutoffRadialCoefficient q branch w a i t =
      principalClearingFactor q branch w i*continuedCutoffRadialCoefficient q branch w a i t := by
  rw [clearedCutoffRadialCoefficient,clearedPrincipalDifference_eq q branch w a i hs hc t,
    continuedCutoffRadialCoefficient]
  ring

/-- Every positive horizon exponential is square-integrable on the actual negative ray. -/
theorem horizonExponential_memLp (b C : ℝ) (hb : 0 < b) (hC : 0 ≤ C) :
    MemLp (fun t : ℝ => C*Real.exp (b*t)) 2 radialMeasure := by
  have h := (laplaceProfile_memLp (b:ℂ) (by simpa using hb) (fun _ => (C:ℂ)) continuousOn_const).norm
  apply h.ae_eq
  filter_upwards [] with t
  simp only [norm_mul,Complex.norm_exp,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  ring

/-- One positive decay exponent and one constant dominate the full cleared cutoff on a frequency ball,
including its analytic values at connection zeros. -/
theorem clearedCutoffRadialCoefficient_local_bound (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (hwr : |w.re| < 2) (i : Fin 3) :
    ∃ R b C : ℝ, 0 < R ∧ 0 < b ∧ 0 ≤ C ∧
      MemLp (fun t : ℝ => C*Real.exp (b*t)) 2 radialMeasure ∧
      ∀ u ∈ ball w R, ∀ t < 0,
        ‖clearedCutoffRadialCoefficient q branch u a i t‖ ≤ C*Real.exp (b*t) := by
  let b := (2-|w.re|)/2
  have hb : 0 < b := by dsimp [b]; linarith
  have hwb : |w.re| < 2-b := by dsimp [b]; linarith
  have hn : {u : ℂ | u.im ≠ 0 ∧ |u.re| < 2-b ∧ -2 < u.re} ∈ 𝓝 w :=
    (Complex.continuous_im.continuousAt.eventually_ne hw).and
      ((Complex.continuous_re.continuousAt.abs.eventually_lt_const hwb).and
        (Complex.continuous_re.continuousAt.eventually_const_lt hwre))
  obtain ⟨R,hR,hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hn
  have hstrip (u : ℂ) (hu : u ∈ closedBall w R) : u.im ≠ 0 ∧ -2 < u.re := by
    have h := hsub hu
    exact ⟨h.1,h.2.2⟩
  obtain ⟨C,hC,hbound⟩ := clearedPrincipalDifference_compact_bound q branch a i (closedBall w R)
    (isCompact_closedBall w R) hstrip
  refine ⟨R,b,4*C,hR,hb,by positivity,horizonExponential_memLp b (4*C) hb (by positivity),?_⟩
  intro u hu t ht
  have hui : u ∈ interior (closedBall w R) :=
    mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds_of_mem hu)
  have hbu : b ≤ 2-|u.re| := by linarith [(hsub (ball_subset_closedBall hu)).2.1]
  rw [clearedCutoffRadialCoefficient,norm_mul]
  calc
    _ ≤ (4*Real.exp (2*t))*(C*Real.exp (-|u.re| *t)) :=
      mul_le_mul (horizonCoordinate_norm_le_exp t ht) (hbound u hui t ht) (norm_nonneg _) (by positivity)
    _ = (4*C)*(Real.exp (2*t)*Real.exp (-|u.re| *t)) := by ring
    _ = (4*C)*Real.exp ((2-|u.re|)*t) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_right hbu ht.le)) (by positivity)

end
end RHTower.D4BMJointSource
