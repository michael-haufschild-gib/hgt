import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainIncompleteIntegral
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainOverlapCusp
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMellinConvergence

/-!
# The height-truncated Narain overlap

On the fundamental domain, incomplete Eisenstein truncation removes
exactly the leading cusp term. Unfolding and subtraction of the vacuum
therefore leave the truncated scalar Mellin transform and an integrable cusp correction.
-/

open Complex RHTower UpperHalfPlane ModularGroup EisensteinSeries Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The literal bilinear overlap over the height-truncated fundamental domain. -/
def narainTruncatedOverlap (ρ σ : D4BMUpperHalfPlaneCoordinate) (s : ℂ) (T : ℝ) : ℂ :=
  ∫ τ in fd, if τ.im ≤ T then
    narainPartitionOnUpperHalfPlane ρ σ τ * narainOverlapEisenstein s τ else 0

theorem narainTruncatedOverlap_eq_setIntegral (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (s : ℂ) (T : ℝ) : narainTruncatedOverlap ρ σ s T =
      ∫ τ in fd ∩ {τ : UpperHalfPlane | τ.im ≤ T},
        narainPartitionOnUpperHalfPlane ρ σ τ * narainOverlapEisenstein s τ := by
  rw [← setIntegral_indicator (measurableSet_le UpperHalfPlane.continuous_im.measurable measurable_const)]
  rfl

/-- On the fundamental domain, incomplete truncation removes exactly the leading cusp term. -/
theorem narainOverlapEisenstein_truncation {s : ℂ} (hs : 1 < s.re)
    {T : ℝ} (hT : 1 ≤ T) {τ : UpperHalfPlane} (hτ : τ ∈ fd) :
    (1 / 2 : ℂ) * truncatedRowSum s T τ =
      narainOverlapEisenstein s τ - (if T < τ.im then (τ.im : ℂ) ^ s else 0) := by
  have hsplit : rowSum s τ = truncatedRowSum s T τ +
      ∑' v : gammaSet 1 1 0, if T < rowHeight v τ then (rowHeight v τ : ℂ) ^ s else 0 := by
    unfold rowSum truncatedRowSum
    rw [← (summable_truncated_term hs T τ).tsum_add (summable_above_term hs T τ)]
    apply tsum_congr
    intro v
    by_cases hv : rowHeight v τ ≤ T
    · simp [hv, not_lt.mpr hv]
    · simp [hv, lt_of_not_ge hv]
  rw [narainOverlapEisenstein, hsplit, tsum_above_eq hτ hT]
  ring

/-- The finite overlap differs from incomplete unfolding by the actual integrable cusp correction. -/
theorem narainTruncatedOverlap_eq_incomplete_sub_tail
    (ρ σ : D4BMUpperHalfPlaneCoordinate) {s : ℂ} (hs : 1 < s.re) {T : ℝ} (hT : 1 ≤ T) :
    narainTruncatedOverlap ρ σ s T =
      (∫ y in Ioc (0 : ℝ) T, (y : ℂ) ^ (s - 1) * (1 + narainScalarHeat ρ σ y)) -
        narainEisensteinCuspTail ρ σ s T := by
  have hi : IntegrableOn (fun τ => ((1 / 2 : ℂ) * truncatedRowSum s T τ) *
      narainPartitionOnUpperHalfPlane ρ σ τ) fd := by
    simpa only [IntegrableOn, mul_assoc] using
      (integrableOn_narainPartition_truncatedRowSum ρ σ hs T).const_mul (1 / 2 : ℂ)
  have hj : IntegrableOn (fun τ : UpperHalfPlane => if T < τ.im then
      narainPartitionOnUpperHalfPlane ρ σ τ *
        (narainOverlapEisenstein s τ - (τ.im : ℂ) ^ s) else 0) fd := by
    have hc : Integrable (fun τ : UpperHalfPlane =>
        narainPartitionOnUpperHalfPlane ρ σ τ *
          (narainOverlapEisenstein s τ - (τ.im : ℂ) ^ s)) (volume.restrict fd) :=
      integrableOn_narainEisenstein_cusp ρ σ hs
    change Integrable ({τ : UpperHalfPlane | T < τ.im}.indicator
      (fun τ => narainPartitionOnUpperHalfPlane ρ σ τ *
        (narainOverlapEisenstein s τ - (τ.im : ℂ) ^ s))) (volume.restrict fd)
    exact hc.indicator
      (measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable)
  rw [narainTruncatedOverlap, ← narainPartition_incomplete_overlap ρ σ hs T, narainEisensteinCuspTail,
    ← integral_sub hi hj]
  apply setIntegral_congr_fun isClosed_fd.measurableSet
  intro τ hτ
  dsimp only
  rw [narainOverlapEisenstein_truncation hs hT hτ]
  by_cases hy : τ.im ≤ T
  · simp only [if_pos hy, if_neg (not_lt.mpr hy), sub_zero]
    ring
  · simp only [if_neg hy, if_pos (lt_of_not_ge hy)]
    ring

private theorem vacuum_integral {s : ℂ} (hs : 1 < s.re) {T : ℝ} (hT : 0 < T) :
    (∫ y in Ioc (0 : ℝ) T, (y : ℂ) ^ (s - 1)) = (T : ℂ) ^ s / s := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  rw [← intervalIntegral.integral_of_le hT.le, integral_cpow (Or.inl (by simp; linarith only [hs])),
    show s - 1 + 1 = s by ring, Complex.ofReal_zero, Complex.zero_cpow hs0, sub_zero]

/-- Subtracting the leading divergent power leaves a truncated actual scalar Mellin transform. -/
theorem narainTruncatedOverlap_sub_vacuum
    (ρ σ : D4BMUpperHalfPlaneCoordinate) {s : ℂ} (hs : 1 < s.re) {T : ℝ} (hT : 1 ≤ T) :
    narainTruncatedOverlap ρ σ s T - (T : ℂ) ^ s / s =
      (∫ y in Ioc (0 : ℝ) T, (y : ℂ) ^ (s - 1) * narainScalarHeat ρ σ y) -
        narainEisensteinCuspTail ρ σ s T := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hv : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s - 1)) (Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0.le).mp
      (intervalIntegral.intervalIntegrable_cpow' (a := (0 : ℝ)) (b := T) (r := s - 1)
        (by simp; linarith only [hs]))
  have hh : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s - 1) * narainScalarHeat ρ σ y) (Ioc 0 T) :=
    (mellinConvergent_narainScalarHeat ρ σ hs).mono_set (fun _ hy => hy.1)
  rw [narainTruncatedOverlap_eq_incomplete_sub_tail ρ σ hs hT]
  simp_rw [mul_add, mul_one]
  rw [integral_add hv hh, vacuum_integral hs hT0]
  ring

#print axioms narainTruncatedOverlap_sub_vacuum
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
