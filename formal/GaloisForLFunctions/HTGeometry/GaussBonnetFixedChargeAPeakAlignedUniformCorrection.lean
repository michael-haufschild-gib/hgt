import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAPeakAlignedProfile
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsOddUniformEnergy

/-!
# Uniform first correction of the peak-aligned reference profile

An exact rational identity removes the vanishing peak coordinate from
the divided profile difference. The remaining two-parameter family is
jointly continuous on a neighborhood of its critical state and the
compact phase interval. Thus its first correction is uniform.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAPeakAlignedCorrectionFamily (s : ℝ × ℝ) (t : ℝ) : ℝ :=
  s.1 * (1 - t ^ 2) ^ 2 *
    (4 * t - s.2 * (2 + 6 * t ^ 2) + 4 * s.2 ^ 2 * t ^ 3 + s.2 ^ 3 * (1 - t ^ 4)) /
      (1 - s.2 * t) ^ 4

theorem egbFixedChargeAPeakAlignedProfile_rational_correction (τ φ ψ : ℝ) :
    (egbFixedChargeAPeakAlignedProfile τ φ ψ - cos ψ ^ 4) / egbCoexistenceASymmetricRatio τ =
      egbFixedChargeAPeakAlignedCorrectionFamily
        (egbFixedChargeAMiddleGapCoordinate τ φ / egbCoexistenceASymmetricRatio τ, egbFixedChargeAMiddleGapCoordinate τ φ)
        (sin ψ) := by
  have hd := egbFixedChargeAPeakAlignedCoordinate_denominator_pos τ φ ψ
  have hd' : 1 - sin ψ * egbFixedChargeAMiddleGapCoordinate τ φ ≠ 0 := by simpa only [mul_comm] using hd.ne'
  have hz := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hs : cos ψ ^ 4 = (1 - sin ψ ^ 2) ^ 2 := by
    have h : 1 - sin ψ ^ 2 = cos ψ ^ 2 := by linarith [sin_sq_add_cos_sq ψ]
    rw [h]
    ring
  unfold egbFixedChargeAPeakAlignedProfile egbFixedChargeAPeakAlignedCoordinate egbFixedChargeAPeakAlignedCorrectionFamily
  dsimp only
  rw [hs]
  field_simp [hd.ne', hd', hz.ne'] <;> ring

theorem egbFixedChargeAPeakAlignedCorrectionFamily_continuousOn :
    ContinuousOn (fun p : (ℝ × ℝ) × Icc (-1 : ℝ) 1 => egbFixedChargeAPeakAlignedCorrectionFamily p.1 p.2)
      ({s : ℝ × ℝ | |s.2| < 1 / 2} ×ˢ univ) := by
  unfold egbFixedChargeAPeakAlignedCorrectionFamily
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro p hp
    have hd : |p.1.2| < 1 / 2 := hp.1
    have ht : |(p.2 : ℝ)| ≤ 1 := abs_le.mpr p.2.property
    have hm : |p.1.2 * (p.2 : ℝ)| < 1 / 2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left ht (abs_nonneg _)).trans_lt (by simpa only [mul_one] using hd)
    have hpos : 0 < 1 - p.1.2 * (p.2 : ℝ) := by linarith [(abs_lt.mp hm).2]
    positivity

theorem egbFixedChargeAPeakAlignedCorrectionFamily_uniform_limit (φ : ℝ) :
    TendstoUniformly (fun s (t : Icc (-1 : ℝ) 1) => egbFixedChargeAPeakAlignedCorrectionFamily s t)
      (fun t => egbFixedChargeAPeakAlignedCorrectionFamily (egbFixedChargeAMiddleMeanCorrection φ, 0) t)
      (𝓝 (egbFixedChargeAMiddleMeanCorrection φ, (0 : ℝ))) := by
  have hU : {s : ℝ × ℝ | |s.2| < 1 / 2} ∈ 𝓝 (egbFixedChargeAMiddleMeanCorrection φ, (0 : ℝ)) := by
    apply (isOpen_lt continuous_snd.abs continuous_const).mem_nhds
    norm_num
  exact egbFixedChargeAPeakAlignedCorrectionFamily_continuousOn.tendstoUniformly hU

theorem egbFixedChargeAPeakAlignedProfile_uniform_first_limit (φ : ℝ) :
    TendstoUniformly (fun τ ψ => (egbFixedChargeAPeakAlignedProfile τ φ ψ - cos ψ ^ 4) / egbCoexistenceASymmetricRatio τ)
      (fun ψ => 4 * egbFixedChargeAMiddleMeanCorrection φ * sin ψ * cos ψ ^ 4) atBot := by
  have hp := (egbFixedChargeAMiddleGapCoordinate_linear_limit φ).prodMk_nhds
    (egbFixedChargeAMiddleGapCoordinate_critical_limit φ)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he := (Metric.tendstoUniformly_iff.mp (egbFixedChargeAPeakAlignedCorrectionFamily_uniform_limit φ)) ε hε
  filter_upwards [hp.eventually he] with τ hτ
  intro ψ
  let t : Icc (-1 : ℝ) 1 := ⟨sin ψ, neg_one_le_sin ψ, sin_le_one ψ⟩
  have hs : (1 - sin ψ ^ 2) ^ 2 = cos ψ ^ 4 := by
    have h : 1 - sin ψ ^ 2 = cos ψ ^ 2 := by linarith [sin_sq_add_cos_sq ψ]
    rw [h]
    ring
  have hc : egbFixedChargeAPeakAlignedCorrectionFamily (egbFixedChargeAMiddleMeanCorrection φ, 0) t =
      4 * egbFixedChargeAMiddleMeanCorrection φ * sin ψ * cos ψ ^ 4 := by
    dsimp [egbFixedChargeAPeakAlignedCorrectionFamily, t]
    rw [hs]
    ring
  rw [egbFixedChargeAPeakAlignedProfile_rational_correction]
  have h := hτ t
  rwa [hc] at h

end GaloisForLFunctions.HTGeometry
