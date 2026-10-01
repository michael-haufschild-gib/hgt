import GaloisForLFunctions.RHTower.ReflectedCompactComplementHolomorphy
import GaloisForLFunctions.RHTower.SmoothAFEReflectedComplementTail
import Mathlib.Analysis.Complex.LocallyUniformLimit

open Complex Set Metric
noncomputable section
namespace RHTower

/-- The complete reciprocal-character complement in complex spectral coordinates. -/
def steinhausCompactReflectedComplement (z : ℂ) (N : ℝ) (ω : SteinhausModel.Omega) : ℂ :=
  -zetaChi z * ∑' n : ℕ, reflectedCompactDeepCoefficient z N n *
    starRingEnd ℂ (SteinhausModel.X (n + 1) ω)

/-- Absolute admission of the translated reciprocal-character series holds at
 every positive scale and every point of the closed unit strip. -/
theorem summable_norm_reflectedCompactDeepSeries {N : ℝ} (hN : 0 < N)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) (ω : SteinhausModel.Omega) :
    Summable (fun n : ℕ => ‖reflectedCompactDeepCoefficient z N n *
      starRingEnd ℂ (SteinhausModel.X (n + 1) ω)‖) := by
  obtain ⟨C, _, hC⟩ := exists_reflectedCompactDeepCoefficient_bound hN (abs_nonneg z.im)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_smoothAFEZetaMajorant (p := (9 / 2 : ℝ)) (by norm_num)).mul_left C)
  simpa only [norm_mul, RCLike.norm_conj, SteinhausModel.norm_X, mul_one] using
    hC z hz0 hz1 le_rfl n

/-- The literal deep reciprocal-character sum is holomorphic on the open unit strip. -/
theorem differentiableOn_reflectedCompactDeepSeries {N : ℝ} (hN : 0 < N)
    (ω : SteinhausModel.Omega) :
    DifferentiableOn ℂ (fun z => ∑' n : ℕ, reflectedCompactDeepCoefficient z N n *
      starRingEnd ℂ (SteinhausModel.X (n + 1) ω)) {z : ℂ | 0 < z.re ∧ z.re < 1} := by
  intro z hz
  let B : ℝ := |z.im| + 1
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let U : Set ℂ := {w | 0 < w.re ∧ w.re < 1 ∧ |w.im| < B}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const))
  have hzU : z ∈ U := ⟨hz.1, hz.2, by dsimp only [B]; linarith⟩
  obtain ⟨C, _, hC⟩ := exists_reflectedCompactDeepCoefficient_bound hN hB
  have hsum : DifferentiableOn ℂ (fun w => ∑' n : ℕ,
      reflectedCompactDeepCoefficient w N n * starRingEnd ℂ (SteinhausModel.X (n + 1) ω)) U := by
    apply differentiableOn_tsum_of_summable_norm
      ((summable_smoothAFEZetaMajorant (p := (9 / 2 : ℝ)) (by norm_num)).mul_left C)
    · intro n
      exact ((differentiableOn_reflectedCompactDeepCoefficient hN n).mul_const _).mono
        (fun w hw => ⟨hw.1, hw.2.1⟩)
    · exact hU
    · intro n w hw
      simpa only [norm_mul, RCLike.norm_conj, SteinhausModel.norm_X, mul_one] using
        hC w hw.1.le hw.2.1.le hw.2.2.le n
  exact (hsum.differentiableAt (hU.mem_nhds hzU)).differentiableWithinAt

/-- The original negative chi factor preserves open-strip holomorphy of the
complete reciprocal complement. -/
theorem differentiableOn_steinhausCompactReflectedComplement {N : ℝ} (hN : 0 < N)
    (ω : SteinhausModel.Omega) :
    DifferentiableOn ℂ (fun z => steinhausCompactReflectedComplement z N ω)
      {z : ℂ | 0 < z.re ∧ z.re < 1} := by
  have hchi : DifferentiableOn ℂ zetaChi {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    intro z hz
    apply (zetaChi_analyticAt ?_).differentiableAt.differentiableWithinAt
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.sub_re, Complex.one_re]
    exact sub_pos.mpr hz.2
  exact hchi.neg.mul (differentiableOn_reflectedCompactDeepSeries hN ω)

/-- The holomorphic series retains the exact coefficients of the original full
complement, including conjugate phases and its archimedean prefactor. -/
theorem steinhausFullReflectedComplement_eq_compact {d N : ℝ}
    (hd : 0 < d) (hdhalf : d < 1 / 2) (hN : 0 < N) (tau : ℝ) (ω : SteinhausModel.Omega) :
    steinhausFullReflectedComplement d tau N ω =
      steinhausCompactReflectedComplement (rightDisplacedLinePt d tau) N ω := by
  unfold steinhausFullReflectedComplement steinhausCompactReflectedComplement
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [smoothAFEZetaRightComplementCoefficient_eq_compactIntegral hd hdhalf hN]
  ring

end RHTower

