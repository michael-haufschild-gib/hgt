import GaloisForLFunctions.HTGeometry.AnalyticSquareRoot
import GaloisForLFunctions.HTGeometry.HardyDiskMultiplier
import GaloisForLFunctions.HTGeometry.SmirnovBoundaryQuotient

/-!
# Bounded square roots of zero-free disk multipliers

This packages the existing analytic square-root theorem as a bounded disk multiplier.  It is the
outer-factor half-power needed when an oriented Toeplitz collision must retain one copy of an
inner factor instead of squaring the entire boundary phase.
-/

open Complex Metric Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A zero-free bounded analytic disk multiplier has a bounded analytic square root. -/
theorem DiskMultiplier.exists_squareRoot_of_zeroFree
    (phi : DiskMultiplier)
    (hne : ∀ z ∈ ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    ∃ root : DiskMultiplier,
      ∀ z ∈ ball (0 : ℂ) 1, root.fn z ^ 2 = phi.fn z := by
  obtain ⟨s, hsDiff, hsSq⟩ := exists_sqrt_of_ne_zero phi.diff hne
  let root : DiskMultiplier :=
    { fn := s
      diff := hsDiff
      bd := phi.bd + 1
      bd_nonneg := by linarith [phi.bd_nonneg]
      bd_le := by
        intro z hz
        have hsq : ‖s z‖ ^ 2 = ‖phi.fn z‖ := by
          rw [← norm_pow, hsSq z hz]
        have hsqLe : ‖s z‖ ^ 2 ≤ phi.bd := by
          rw [hsq]
          exact phi.bd_le z hz
        by_cases hsmall : ‖s z‖ ≤ 1
        · linarith [phi.bd_nonneg]
        · have hone : 1 < ‖s z‖ := lt_of_not_ge hsmall
          nlinarith [norm_nonneg (s z)] }
  exact ⟨root, hsSq⟩

/-- A bounded analytic square root of an outer multiplier is outer.  Dense range of multiplication
by the square is contained in the range of multiplication by the root. -/
theorem IsOuterDiskMultiplier.of_square_eq
    {phi root : DiskMultiplier}
    (hphi : IsOuterDiskMultiplier phi)
    (hsq : ∀ z ∈ ball (0 : ℂ) 1, root.fn z ^ 2 = phi.fn z) :
    IsOuterDiskMultiplier root := by
  rw [isOuterDiskMultiplier_iff_denseRange] at hphi ⊢
  rw [denseRange_iff_closure_range] at hphi ⊢
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← hphi]
  apply closure_mono
  rintro _ ⟨f, rfl⟩
  refine ⟨hardyMul root f, ?_⟩
  apply hardyDisk_ext
  intro z hz
  rw [hardyFun_hardyMul root (hardyMul root f) hz,
    hardyFun_hardyMul root f hz, hardyFun_hardyMul phi f hz]
  rw [← hsq z (by simpa [Metric.mem_ball, dist_zero_right] using hz)]
  ring

end

end GaloisForLFunctions.HTGeometry
