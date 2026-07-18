import GaloisForLFunctions.RHTower.ScaleCovariantBernsteinGibbsCorollary
import GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm
import GaloisForLFunctions.RHTower.XiDivisorSupportedMetric
import GaloisForLFunctions.RHTower.XiZerosInfinite

/-!
# Scale-covariant Xi Bernstein--Abel corollary

This file specializes the confocal radical and free-energy recession to the actual centered
reciprocal-square Xi divisor.  It records in one theorem surface the exact Xi application used by
the scale-covariant Bernstein--Abel tomography paper.
-/

open Complex Filter Topology
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- The occupied centered reciprocal-square Xi source, with multiplicity copies forgotten at the
level of support. -/
def xiScaleCovariantReciprocalSquareSupport : Set ℂ :=
  Set.range xiZeroCopyReciprocalSquare

/-- The scale-covariant Xi Abel radius. -/
def xiScaleCovariantAbelRadius (R : ℝ) : ℝ :=
  HTGeometry.confocalAbelRadius xiScaleCovariantReciprocalSquareSupport R

/-- The intrinsic transverse defect of the centered reciprocal-square Xi source. -/
def xiScaleCovariantTransverseDefect : ℝ :=
  HTGeometry.transverseDefectEnvelope xiScaleCovariantReciprocalSquareSupport

/-- The logarithmic free energy of the scale-covariant Xi Abel radius. -/
def xiScaleCovariantGibbsFreeEnergy (R : ℝ) : ℝ :=
  confocalGibbsFreeEnergy xiScaleCovariantReciprocalSquareSupport R

theorem xiScaleCovariantReciprocalSquareSupport_nonempty :
    xiScaleCovariantReciprocalSquareSupport.Nonempty := by
  obtain ⟨z, hz⟩ := xiDivisorSupport_infinite.nonempty
  let ρ : XiDivisorSupport := ⟨z, hz⟩
  have hpos : 0 < (MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) :=
    xi_divisor_pos_on_support ρ
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨ρ, ⟨0, hn⟩⟩
  exact ⟨xiZeroCopyReciprocalSquare q, ⟨q, rfl⟩⟩

/-- RH is exactly positivity of every occupied centered reciprocal-square Xi coordinate. -/
theorem riemannHypothesis_iff_forall_xiZeroCopyReciprocalSquare_nonnegative :
    RiemannHypothesis ↔
      ∀ q : XiZeroCopy, (0 : ℂ) ≤ xiZeroCopyReciprocalSquare q := by
  constructor
  · intro hRH q
    obtain ⟨x, hx, hcoord⟩ :=
      xiCentralReciprocalSquare_pos_real_of_rh hRH q.1
    rw [xiZeroCopyReciprocalSquare_eq, hcoord]
    exact Complex.nonneg_iff.mpr ⟨hx.le, rfl⟩
  · intro hpositive
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have him : (xiZeroCopyReciprocalSquare q).im = 0 :=
      (Complex.nonneg_iff.mp (hpositive q)).2.symm
    rw [xiZeroCopyReciprocalSquare_eq] at him
    have hre : (q.1 : ℂ).re = 1 / 2 :=
      (xiCentralReciprocalSquare_im_eq_zero_iff q.1).mp him
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [xiSpectralPoint]
    · simp [xiSpectralPoint, hre]

/-- The intrinsic Xi transverse defect vanishes exactly on RH. -/
theorem xiScaleCovariantTransverseDefect_eq_zero_iff_riemannHypothesis
    {M : ℝ} (hbound : ∀ q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ ≤ M) :
    xiScaleCovariantTransverseDefect = 0 ↔ RiemannHypothesis := by
  have hsourceBound : ∀ z ∈ xiScaleCovariantReciprocalSquareSupport, ‖z‖ ≤ M := by
    rintro z ⟨q, rfl⟩
    exact hbound q
  rw [xiScaleCovariantTransverseDefect,
    HTGeometry.transverseDefectEnvelope_eq_zero_iff
      xiScaleCovariantReciprocalSquareSupport_nonempty hsourceBound]
  simpa only [xiScaleCovariantReciprocalSquareSupport, Set.forall_mem_range] using
    riemannHypothesis_iff_forall_xiZeroCopyReciprocalSquare_nonnegative.symm

/-- At every scale beyond a common source bound, unit Xi Abel radius is exactly RH. -/
theorem xiScaleCovariantAbelRadius_eq_one_iff_riemannHypothesis
    {M R : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ ≤ M)
    (hRM : M < R) :
    xiScaleCovariantAbelRadius R = 1 ↔ RiemannHypothesis := by
  have hsourceBound : ∀ z ∈ xiScaleCovariantReciprocalSquareSupport, ‖z‖ ≤ M := by
    rintro z ⟨q, rfl⟩
    exact hbound q
  rw [xiScaleCovariantAbelRadius,
    HTGeometry.confocalAbelRadius_eq_one_iff
      xiScaleCovariantReciprocalSquareSupport_nonempty hM hRM hsourceBound]
  change xiScaleCovariantTransverseDefect = 0 ↔ RiemannHypothesis
  exact xiScaleCovariantTransverseDefect_eq_zero_iff_riemannHypothesis hbound

/-- At every scale beyond a common source bound, vanishing Xi Gibbs free energy is exactly RH. -/
theorem xiScaleCovariantGibbsFreeEnergy_eq_zero_iff_riemannHypothesis
    {M R : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ ≤ M)
    (hRM : M < R) :
    xiScaleCovariantGibbsFreeEnergy R = 0 ↔ RiemannHypothesis := by
  have hsourceBound : ∀ z ∈ xiScaleCovariantReciprocalSquareSupport, ‖z‖ ≤ M := by
    rintro z ⟨q, rfl⟩
    exact hbound q
  rw [xiScaleCovariantGibbsFreeEnergy,
    confocalGibbsFreeEnergy_eq_zero_iff_source_positive
      xiScaleCovariantReciprocalSquareSupport_nonempty hM hRM hsourceBound]
  simpa only [xiScaleCovariantReciprocalSquareSupport, Set.forall_mem_range] using
    riemannHypothesis_iff_forall_xiZeroCopyReciprocalSquare_nonnegative.symm

/-- The Xi Gibbs free energy has first recession twice the intrinsic transverse defect. -/
theorem tendsto_mul_xiScaleCovariantGibbsFreeEnergy
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ ≤ M) :
    Tendsto (fun R : ℝ => R * xiScaleCovariantGibbsFreeEnergy R) atTop
      (nhds (2 * xiScaleCovariantTransverseDefect)) := by
  have hsourceBound : ∀ z ∈ xiScaleCovariantReciprocalSquareSupport, ‖z‖ ≤ M := by
    rintro z ⟨q, rfl⟩
    exact hbound q
  simpa only [xiScaleCovariantGibbsFreeEnergy, xiScaleCovariantTransverseDefect] using
    tendsto_mul_confocalGibbsFreeEnergy
      xiScaleCovariantReciprocalSquareSupport_nonempty hM hsourceBound

/-- One unconditional source bound controls the complete Xi radical chain at every larger scale. -/
theorem exists_xiScaleCovariantRadical_scale :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ ≤ M) ∧
      ∀ R : ℝ, M < R →
        (xiScaleCovariantTransverseDefect = 0 ↔ RiemannHypothesis) ∧
        (xiScaleCovariantAbelRadius R = 1 ↔ RiemannHypothesis) ∧
        (xiScaleCovariantGibbsFreeEnergy R = 0 ↔ RiemannHypothesis) := by
  obtain ⟨M, hM, hbound⟩ := exists_xiZeroCopyReciprocalSquare_norm_bound
  refine ⟨M, zero_le_one.trans hM, hbound, fun R hRM => ?_⟩
  exact ⟨xiScaleCovariantTransverseDefect_eq_zero_iff_riemannHypothesis hbound,
    xiScaleCovariantAbelRadius_eq_one_iff_riemannHypothesis
      (zero_le_one.trans hM) hbound hRM,
    xiScaleCovariantGibbsFreeEnergy_eq_zero_iff_riemannHypothesis
      (zero_le_one.trans hM) hbound hRM⟩

end

end RHTower
