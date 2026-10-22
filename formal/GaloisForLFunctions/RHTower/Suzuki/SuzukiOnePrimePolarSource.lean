import GaloisForLFunctions.RHTower.RealL2SmoothOnsetTail
import GaloisForLFunctions.RHTower.Suzuki.SuzukiPolarConvolutionRate
import GaloisForLFunctions.HTGeometry.ExponentialDividedDifference

/-!
# Literal one-prime polar source as a whole-line weak-derivative pair

The finite-aperture Suzuki polar convolution is centered at a physical endpoint, pulled back by
the logarithmic boundary chart, clamped to `L ≥ 0`, and smoothly activated.  Its exponential
collar estimate yields a globally Lipschitz `L²` primitive whose classical derivative is in `L²`.
The resulting complex representatives satisfy the exact tempered-distribution derivative identity,
with no abstract source, regularity, or weak-derivative premise.
-/

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ENNReal SchwartzMap LineDeriv

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Endpoint-centered polar trace, clamped to the physical logarithmic half-line. -/
def suzukiClampedCenteredPolarTrace
    (a : ℝ) (u : ℝ → ℝ) (x₀ ε : ℝ) (L : ℝ) : ℝ :=
  suzukiPolarBoundaryTrace a u x₀ ε (max L 0) - suzukiPolarConvolution a u x₀

/-- Literal exponential envelope of the centered polar trace. -/
def suzukiPolarTailConstant (a : ℝ) (u : ℝ → ℝ) : ℝ :=
  suzukiPolarLip a * ∫ y in (-a)..a, |u y|

theorem suzukiPolarTailConstant_nonneg {a : ℝ} (ha : 0 ≤ a) (u : ℝ → ℝ) :
    0 ≤ suzukiPolarTailConstant a u := by
  apply mul_nonneg (suzukiPolarLip_nonneg a)
  apply intervalIntegral.integral_nonneg (by linarith)
  intro y _
  exact abs_nonneg _

theorem abs_suzukiClampedCenteredPolarTrace_le
    {a x₀ ε L : ℝ} (ha : 0 ≤ a) (hx₀ : |x₀| ≤ a) (hε : |ε| ≤ 1)
    {u : ℝ → ℝ} (hu : IntervalIntegrable u volume (-a) a) :
    |suzukiClampedCenteredPolarTrace a u x₀ ε L| ≤
      suzukiPolarTailConstant a u * Real.exp (-(max L 0)) := by
  simpa [suzukiClampedCenteredPolarTrace, suzukiPolarTailConstant] using
    abs_suzukiPolarBoundaryTrace_sub_le ha hx₀ hε (le_max_right L 0) hu

theorem abs_suzukiClampedCenteredPolarTrace_le_exp
    {a x₀ ε L : ℝ} (ha : 0 ≤ a) (hx₀ : |x₀| ≤ a) (hε : |ε| ≤ 1)
    (hL : 0 ≤ L) {u : ℝ → ℝ} (hu : IntervalIntegrable u volume (-a) a) :
    |suzukiClampedCenteredPolarTrace a u x₀ ε L| ≤
      suzukiPolarTailConstant a u * Real.exp (-L) := by
  simpa [max_eq_left hL] using
    abs_suzukiClampedCenteredPolarTrace_le ha hx₀ hε (L := L) hu

theorem lipschitz_suzukiClampedCenteredPolarTrace
    {a x₀ ε : ℝ} (ha : 0 ≤ a) (hx₀ : |x₀| ≤ a) (hε : |ε| ≤ 1)
    {u : ℝ → ℝ} (hu : IntervalIntegrable u volume (-a) a) :
    LipschitzWith (Real.toNNReal (suzukiPolarTailConstant a u))
      (suzukiClampedCenteredPolarTrace a u x₀ ε) := by
  have hC : 0 ≤ suzukiPolarTailConstant a u := suzukiPolarTailConstant_nonneg ha u
  apply LipschitzWith.of_dist_le_mul
  intro L M
  let L' : ℝ := max L 0
  let M' : ℝ := max M 0
  have hL' : 0 ≤ L' := le_max_right L 0
  have hM' : 0 ≤ M' := le_max_right M 0
  have heL : Real.exp (-L') ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hL')
  have heM : Real.exp (-M') ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hM')
  have hxL : |x₀ + ε * Real.exp (-L')| ≤ a + 1 := by
    have hshift : |ε * Real.exp (-L')| ≤ 1 := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      nlinarith [abs_nonneg ε, Real.exp_pos (-L')]
    calc
      |x₀ + ε * Real.exp (-L')| ≤ |x₀| + |ε * Real.exp (-L')| := abs_add_le _ _
      _ ≤ a + 1 := by linarith
  have hxM : |x₀ + ε * Real.exp (-M')| ≤ a + 1 := by
    have hshift : |ε * Real.exp (-M')| ≤ 1 := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      nlinarith [abs_nonneg ε, Real.exp_pos (-M')]
    calc
      |x₀ + ε * Real.exp (-M')| ≤ |x₀| + |ε * Real.exp (-M')| := abs_add_le _ _
      _ ≤ a + 1 := by linarith
  have hbase := abs_suzukiPolarConvolution_sub_le (a := a)
    (x := x₀ + ε * Real.exp (-L')) (x' := x₀ + ε * Real.exp (-M'))
    ha hxL hxM hu
  have hexp : |Real.exp (-L') - Real.exp (-M')| ≤ |L' - M'| := by
    have h := abs_exp_sub_exp_le_of_nonpos (neg_nonpos.mpr hL') (neg_nonpos.mpr hM')
    simpa only [neg_sub_neg, abs_neg, abs_sub_comm] using h
  have hmax := (LipschitzWith.id.max_const (0 : ℝ)).dist_le_mul L M
  have hmax' : |L' - M'| ≤ |L - M| := by
    simpa [L', M', Real.dist_eq] using hmax
  have hpos :
      |(x₀ + ε * Real.exp (-L')) - (x₀ + ε * Real.exp (-M'))| ≤ |L - M| := by
    calc
      |(x₀ + ε * Real.exp (-L')) - (x₀ + ε * Real.exp (-M'))| =
          |ε| * |Real.exp (-L') - Real.exp (-M')| := by
            rw [show (x₀ + ε * Real.exp (-L')) - (x₀ + ε * Real.exp (-M')) =
              ε * (Real.exp (-L') - Real.exp (-M')) by ring, abs_mul]
      _ ≤ 1 * |Real.exp (-L') - Real.exp (-M')| := by
        exact mul_le_mul hε le_rfl (abs_nonneg _) (by norm_num)
      _ ≤ |L' - M'| := by simpa using hexp
      _ ≤ |L - M| := hmax'
  have hInt : 0 ≤ ∫ y in (-a)..a, |u y| := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro y _
    exact abs_nonneg _
  change |suzukiClampedCenteredPolarTrace a u x₀ ε L -
      suzukiClampedCenteredPolarTrace a u x₀ ε M| ≤
    (Real.toNNReal (suzukiPolarTailConstant a u) : ℝ) * |L - M|
  rw [Real.coe_toNNReal _ hC]
  change |(suzukiPolarConvolution a u (x₀ + ε * Real.exp (-L')) -
      suzukiPolarConvolution a u x₀) -
      (suzukiPolarConvolution a u (x₀ + ε * Real.exp (-M')) -
      suzukiPolarConvolution a u x₀)| ≤ _
  rw [show (suzukiPolarConvolution a u (x₀ + ε * Real.exp (-L')) -
      suzukiPolarConvolution a u x₀) -
      (suzukiPolarConvolution a u (x₀ + ε * Real.exp (-M')) -
      suzukiPolarConvolution a u x₀) =
      suzukiPolarConvolution a u (x₀ + ε * Real.exp (-L')) -
      suzukiPolarConvolution a u (x₀ + ε * Real.exp (-M')) by ring]
  refine hbase.trans ?_
  change suzukiPolarLip a *
      |(x₀ + ε * Real.exp (-L')) - (x₀ + ε * Real.exp (-M'))| *
      (∫ y in (-a)..a, |u y|) ≤
    suzukiPolarTailConstant a u * |L - M|
  rw [suzukiPolarTailConstant]
  calc
    suzukiPolarLip a *
        |(x₀ + ε * Real.exp (-L')) - (x₀ + ε * Real.exp (-M'))| *
        (∫ y in (-a)..a, |u y|) ≤
      suzukiPolarLip a * |L - M| * (∫ y in (-a)..a, |u y|) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpos (suzukiPolarLip_nonneg a)) hInt
    _ = (suzukiPolarLip a * ∫ y in (-a)..a, |u y|) * |L - M| := by ring

theorem abs_deriv_suzukiClampedCenteredPolarTrace_le_exp
    {a x₀ ε L : ℝ} (ha : 0 ≤ a) (hx₀ : |x₀| ≤ a) (hε : |ε| ≤ 1)
    (hL : 1 < L) {u : ℝ → ℝ} (hu : IntervalIntegrable u volume (-a) a) :
    |deriv (suzukiClampedCenteredPolarTrace a u x₀ ε) L| ≤
      suzukiPolarTailConstant a u * Real.exp (-L) := by
  have hL0 : 0 < L := lt_trans zero_lt_one hL
  have heq : suzukiClampedCenteredPolarTrace a u x₀ ε =ᶠ[𝓝 L]
      fun M => suzukiPolarBoundaryTrace a u x₀ ε M - suzukiPolarConvolution a u x₀ := by
    filter_upwards [Ioi_mem_nhds hL0] with M hM
    rw [suzukiClampedCenteredPolarTrace, max_eq_left hM.le]
  rw [heq.deriv_eq, deriv_sub_const]
  simpa [suzukiPolarTailConstant] using
    abs_deriv_suzukiPolarBoundaryTrace_le ha hx₀ hε hL0 hu

/-- Whole-line onset primitive of Suzuki's literal centered polar trace. -/
def suzukiOnsetCenteredPolarPrimitive
    (a : ℝ) (u : ℝ → ℝ) (x₀ ε : ℝ) (L : ℝ) : ℝ :=
  smoothOnsetTail (suzukiClampedCenteredPolarTrace a u x₀ ε) L

theorem memLp_suzukiOnsetCenteredPolarPrimitive
    {a x₀ ε : ℝ} (ha : 0 ≤ a) (hx₀ : |x₀| ≤ a) (hε : |ε| ≤ 1)
    {u : ℝ → ℝ} (hu : IntervalIntegrable u volume (-a) a) :
    MemLp (suzukiOnsetCenteredPolarPrimitive a u x₀ ε) 2 (volume : Measure ℝ) := by
  exact smoothOnsetTail_memLp _
    (lipschitz_suzukiClampedCenteredPolarTrace ha hx₀ hε hu)
    (suzukiPolarTailConstant_nonneg ha u)
    (fun L hL => abs_suzukiClampedCenteredPolarTrace_le_exp ha hx₀ hε hL hu)

theorem memLp_deriv_suzukiOnsetCenteredPolarPrimitive
    {a x₀ ε : ℝ} (ha : 0 ≤ a) (hx₀ : |x₀| ≤ a) (hε : |ε| ≤ 1)
    {u : ℝ → ℝ} (hu : IntervalIntegrable u volume (-a) a) :
    MemLp (deriv (suzukiOnsetCenteredPolarPrimitive a u x₀ ε)) 2
      (volume : Measure ℝ) := by
  obtain ⟨Kp, hpLip⟩ := exists_smoothOnsetTail_lipschitz _
    (lipschitz_suzukiClampedCenteredPolarTrace ha hx₀ hε hu)
    (suzukiPolarTailConstant_nonneg ha u)
    (fun L => abs_suzukiClampedCenteredPolarTrace_le ha hx₀ hε (L := L) hu |>.trans
      (by
        have he : Real.exp (-(max L 0)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_right L 0))
        nlinarith [suzukiPolarTailConstant_nonneg ha u]))
  exact smoothOnsetTail_deriv_memLp _ hpLip
    (fun L hL => abs_deriv_suzukiClampedCenteredPolarTrace_le_exp ha hx₀ hε hL hu)

/-- Literal centered polar primitive and source form an unconditional weak-derivative pair. -/
theorem suzukiOnsetCenteredPolarPrimitive_weakDerivative
    {a x₀ ε : ℝ} (ha : 0 ≤ a) (hx₀ : |x₀| ≤ a) (hε : |ε| ≤ 1)
    {u : ℝ → ℝ} (hu : IntervalIntegrable u volume (-a) a) :
    ∂_{(1 : ℝ)}
        (realToComplexL2 (suzukiOnsetCenteredPolarPrimitive a u x₀ ε)
          (memLp_suzukiOnsetCenteredPolarPrimitive ha hx₀ hε hu) : 𝓢'(ℝ, ℂ)) =
      (realToComplexL2 (deriv (suzukiOnsetCenteredPolarPrimitive a u x₀ ε))
        (memLp_deriv_suzukiOnsetCenteredPolarPrimitive ha hx₀ hε hu) : 𝓢'(ℝ, ℂ)) := by
  apply smoothOnsetTail_weakDerivative
    (q := suzukiClampedCenteredPolarTrace a u x₀ ε)
    (lipschitz_suzukiClampedCenteredPolarTrace ha hx₀ hε hu)
    (suzukiPolarTailConstant_nonneg ha u)
  · intro L
    exact (abs_suzukiClampedCenteredPolarTrace_le ha hx₀ hε (L := L) hu).trans (by
      have he : Real.exp (-(max L 0)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_right L 0))
      nlinarith [suzukiPolarTailConstant_nonneg ha u])
  · intro L hL
    exact abs_suzukiClampedCenteredPolarTrace_le_exp ha hx₀ hε hL hu
  · intro L hL
    exact abs_deriv_suzukiClampedCenteredPolarTrace_le_exp ha hx₀ hε hL hu

end RHTower

end
