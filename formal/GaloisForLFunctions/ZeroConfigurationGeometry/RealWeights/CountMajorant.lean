import GaloisForLFunctions.ZeroConfigurationGeometry.RealWeights.PositiveImages
import GaloisForLFunctions.ZeroConfigurationGeometry.RealWeights.IntervalMajorant

/-!
# Positive weighted counts from integrated images

Integrate modulated diagonal camera images over an enlarged interval.
The normalized Fourier kernel majorizes the original interval, so every
finite positive on-line weighted count is bounded by the integrated image.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23

/-- Integrating modulated diagonal images against an enlarged interval bounds every
finite positive on-line weighted count in the original interval. -/
theorem weighted_count_le_integrated_image_bound {w : ℂ → ℝ}
    (hw0 : ∀ z, 0 ≤ w z) (hline : ∀ z, w z ≠ 0 → z.re = 1 / 2)
    (hw : Summable fun z => |w z| / (1 + Complex.normSq (gammaOf z)))
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) (hbc : HasCompactSupport b)
    {x y R : ℝ} (hxy : x ≤ y) (hR : 0 ≤ R)
    (hP : 0 < ∫ v in (-R)..R, ‖paperFT b v‖ ^ 2)
    {U : ℝ → ℝ} (hUi : IntervalIntegrable U volume (x - R) (y + R))
    (hupper : ∀ X ∈ Icc (x - R) (y + R),
      (weightedImage (fun z => (w z : ℂ)) (localWindow X b) (localWindow X b)).re ≤ U X)
    (s : Finset ℂ) (hs : ∀ z ∈ s, z.im ∈ Icc x y) :
    (∑ z ∈ s, w z) ≤
      (∫ X in (x - R)..(y + R), U X) / (∫ v in (-R)..R, ‖paperFT b v‖ ^ 2) := by
  classical
  let K : ℝ → ℝ := fun v => ‖paperFT b v‖ ^ 2
  have hKc : Continuous K :=
    ((_root_.RHTower.EvenSector.differentiable_paperFT_of_compact hb.continuous hbc).continuous.comp
      Complex.continuous_ofReal).norm.pow 2
  have hab : x - R ≤ y + R := by linarith only [hxy, hR]
  have hterm (z : ℂ) : IntervalIntegrable (fun X => w z * K (z.im - X)) volume
      (x - R) (y + R) :=
    (continuous_const.mul (hKc.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _
  have hlocal (X : ℝ) : (∑ z ∈ s, w z * K (z.im - X)) ≤
      (weightedImage (fun z => (w z : ℂ)) (localWindow X b) (localWindow X b)).re := by
    have hbf : ContDiff ℝ 2 (localWindow X b) := by
      change ContDiff ℝ 2 (fun u : ℝ => b u * Complex.exp (-(I * (X : ℂ) * (u : ℂ))))
      have he : ContDiff ℝ 2 (fun u : ℝ => -(I * (X : ℂ) * (u : ℂ))) :=
        (contDiff_const.mul Complex.ofRealCLM.contDiff).neg
      exact hb.mul (Complex.contDiff_exp.comp he)
    have hh := finite_sum_le_re_weightedImage_onLine hw0 hline hw hbf hbc.mul_right s
    simpa only [paperFT_localWindow, ← Complex.ofReal_sub, K] using hh
  have hsum : IntervalIntegrable (fun X => ∑ z ∈ s, w z * K (z.im - X)) volume
      (x - R) (y + R) :=
    ⟨integrable_finsetSum s (fun z _ => (hterm z).1),
      integrable_finsetSum s (fun z _ => (hterm z).2)⟩
  have hmono : (∫ X in (x - R)..(y + R), ∑ z ∈ s, w z * K (z.im - X)) ≤
      ∫ X in (x - R)..(y + R), U X :=
    intervalIntegral.integral_mono_on hab
      hsum hUi
      (fun X hX => (hlocal X).trans (hupper X hX))
  have hlower : (∑ z ∈ s, w z) * (∫ v in (-R)..R, K v) ≤
      ∫ X in (x - R)..(y + R), ∑ z ∈ s, w z * K (z.im - X) := by
    rw [intervalIntegral.integral_finsetSum (fun z _ => hterm z), Finset.sum_mul]
    apply Finset.sum_le_sum
    intro z hz
    have hh := one_le_intervalKernelMajorant hKc (fun _ => sq_nonneg _) hR hP (hs z hz)
    have hc : (∫ v in (-R)..R, K v) ≤ ∫ X in (x - R)..(y + R), K (z.im - X) :=
      (one_le_div hP).mp hh
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hc (hw0 z)
  exact (le_div_iff₀ hP).mpr (hlower.trans hmono)

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.weighted_count_le_integrated_image_bound
