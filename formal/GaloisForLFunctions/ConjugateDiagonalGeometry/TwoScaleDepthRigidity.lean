import GaloisForLFunctions.ConjugateDiagonalGeometry.ZetaDepthDistribution
import GaloisForLFunctions.HTGeometry.PairwiseVarianceIdentity

/-!
# Two translation scales determine depth dispersion

For collided mass `D` and Hecke defect `E`, the quantity
`D(E(2L) − 4E(L)) − E(L)²` is half the weighted pairwise variance of
`2 cosh(2Lδ) − 2`. It is nonnegative. At a nonzero scale, equality says
that all zeros seen by the test have one absolute depth, not necessarily zero.
-/

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

open Zeta23 ArithmeticPolarization

/-- The variance read by collided mass and two Hecke translation scales. -/
def depthDispersion (f : CompactTest) (L : ℝ) : ℝ :=
  collidedForm zetaZeroConfig f.1 * (heckeDefect f (2 * L) - 4 * heckeDefect f L) -
    heckeDefect f L ^ 2

theorem summable_depthDispersion (f : CompactTest) (L : ℝ) :
    Summable fun p : zetaZeroConfig.carrier × zetaZeroConfig.carrier =>
      zetaWeight f p.1 * zetaWeight f p.2 *
        (depthKernel L (zetaDepth p.1) - depthKernel L (zetaDepth p.2)) ^ 2 :=
  HTGeometry.summable_pairwise_dispersion (summable_zetaWeight f)
    (summable_heckeDefect f L) (summable_zeta_kernel_pow f L 2) (zetaWeight_nonneg f)

/-- Exact pairwise identity for the full zeta divisor, with convergence discharged. -/
theorem pairwise_depth_eq_two_mul_dispersion (f : CompactTest) (L : ℝ) :
    (∑' p : zetaZeroConfig.carrier × zetaZeroConfig.carrier,
      zetaWeight f p.1 * zetaWeight f p.2 *
        (depthKernel L (zetaDepth p.1) - depthKernel L (zetaDepth p.2)) ^ 2) =
      2 * depthDispersion f L := by
  rw [HTGeometry.tsum_pairwise_dispersion (summable_zetaWeight f)
    (summable_heckeDefect f L) (summable_zeta_kernel_pow f L 2) (zetaWeight_nonneg f)]
  unfold depthDispersion
  rw [heckeDefect_double]
  change 2 * (collidedForm zetaZeroConfig f.1 *
    (∑' ρ, zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ 2) - heckeDefect f L ^ 2) = _
  ring

theorem depthDispersion_nonneg (f : CompactTest) (L : ℝ) : 0 ≤ depthDispersion f L := by
  have h : 0 ≤ ∑' p : zetaZeroConfig.carrier × zetaZeroConfig.carrier,
      zetaWeight f p.1 * zetaWeight f p.2 *
        (depthKernel L (zetaDepth p.1) - depthKernel L (zetaDepth p.2)) ^ 2 :=
    tsum_nonneg fun p => mul_nonneg
      (mul_nonneg (zetaWeight_nonneg f p.1) (zetaWeight_nonneg f p.2)) (sq_nonneg _)
  rw [pairwise_depth_eq_two_mul_dispersion] at h
  linarith only [h]

/-- A sharp nonlinear constraint on the growth of the Hecke defect between two scales. -/
theorem heckeDefect_sq_le_two_scale (f : CompactTest) (L : ℝ) :
    heckeDefect f L ^ 2 ≤ collidedForm zetaZeroConfig f.1 *
      (heckeDefect f (2 * L) - 4 * heckeDefect f L) :=
  sub_nonneg.mp (depthDispersion_nonneg f L)

/-- Equality is exactly concentration of the weighted divisor on one depth-kernel level. -/
theorem depthDispersion_eq_zero_iff (f : CompactTest) (L : ℝ) :
    depthDispersion f L = 0 ↔
      ∀ ρ σ : zetaZeroConfig.carrier, zetaWeight f ρ ≠ 0 → zetaWeight f σ ≠ 0 →
        |zetaDepth ρ * L| = |zetaDepth σ * L| := by
  constructor
  · intro hzero ρ σ hρ hσ
    apply (depthKernel_eq_iff L (zetaDepth ρ) (zetaDepth σ)).1
    by_contra hne
    have hρpos : 0 < zetaWeight f ρ := lt_of_le_of_ne (zetaWeight_nonneg f ρ) (Ne.symm hρ)
    have hσpos : 0 < zetaWeight f σ := lt_of_le_of_ne (zetaWeight_nonneg f σ) (Ne.symm hσ)
    have hpos := (summable_depthDispersion f L).tsum_pos
      (fun p => mul_nonneg (mul_nonneg (zetaWeight_nonneg f p.1)
        (zetaWeight_nonneg f p.2)) (sq_nonneg _)) (ρ, σ)
      (mul_pos (mul_pos hρpos hσpos) (sq_pos_of_ne_zero (sub_ne_zero.mpr hne)))
    rw [pairwise_depth_eq_two_mul_dispersion, hzero, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  · intro h
    have hz : ∀ p : zetaZeroConfig.carrier × zetaZeroConfig.carrier,
        zetaWeight f p.1 * zetaWeight f p.2 *
          (depthKernel L (zetaDepth p.1) - depthKernel L (zetaDepth p.2)) ^ 2 = 0 := by
      rintro ⟨ρ, σ⟩
      by_cases hρ : zetaWeight f ρ = 0
      · simp only [hρ, zero_mul]
      by_cases hσ : zetaWeight f σ = 0
      · simp only [hσ, mul_zero, zero_mul]
      rw [(depthKernel_eq_iff L (zetaDepth ρ) (zetaDepth σ)).2 (h ρ σ hρ hσ)]
      simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    have heq := pairwise_depth_eq_two_mul_dispersion f L
    rw [tsum_congr hz, tsum_zero] at heq
    linarith only [heq]

/-- At unit translation, equality characterizes a single absolute-depth shell. -/
theorem unit_scale_shell_rigidity (f : CompactTest) :
    depthDispersion f 1 = 0 ↔
      ∀ ρ σ : zetaZeroConfig.carrier, zetaWeight f ρ ≠ 0 → zetaWeight f σ ≠ 0 →
        |zetaDepth ρ| = |zetaDepth σ| := by
  simpa only [mul_one] using depthDispersion_eq_zero_iff f 1

end GaloisForLFunctions.ConjugateDiagonalGeometry
