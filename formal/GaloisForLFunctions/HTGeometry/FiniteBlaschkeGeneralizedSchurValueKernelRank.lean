import GaloisForLFunctions.HTGeometry.FiniteBlaschkeGeneralizedSchurKernelRank
import GaloisForLFunctions.HTGeometry.FiniteBlaschkeGeneralizedSchurValueKernel

/-!
# Value-kernel rank after finite common-factor cancellation

This transports the exact restricted-adjoint rank from the analytic Hardy realization to the
unreflected generalized-Schur value kernel, both on the full disk and on an exterior uniqueness
annulus avoiding denominator zeros.
-/

open Complex Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Finite generalized-Schur negative index after all common numerator/denominator directions have
been removed. -/
def finiteBlaschkeGeneralizedSchurCancelledIndex
    (F : DiskMultiplier) (B : FiniteBlaschke) : ℕ :=
  Module.finrank ℂ (LinearMap.range
    ((ContinuousLinearMap.adjoint (hardyMul F)).toLinearMap.domRestrict
      (finiteBlaschkeModelSpace B)))

/-- Exact negative-square classification of the unreflected value kernel without coprimality. -/
theorem finiteBlaschkeGeneralizedSchurValueKernel_exactNegativeSquares_rank
    (F : DiskMultiplier) (B : FiniteBlaschke) (hFbd : F.bd ≤ 1) :
    HasFiniteKernelNegativeDimension
        (fun z w : Metric.ball (0 : ℂ) 1 =>
          finiteBlaschkeGeneralizedSchurValueKernel F B z w)
        (finiteBlaschkeGeneralizedSchurCancelledIndex F B) ∧
      ∀ r : ℕ,
        HasFiniteKernelNegativeDimension
          (fun z w : Metric.ball (0 : ℂ) 1 =>
            finiteBlaschkeGeneralizedSchurValueKernel F B z w) r →
          r ≤ finiteBlaschkeGeneralizedSchurCancelledIndex F B := by
  have hexact := finiteBlaschkeGeneralizedSchurKernel_exactNegativeSquares_rank F B hFbd
  constructor
  · rw [hasFiniteKernelNegativeDimension_valueKernel_iff_realization
      F B (Metric.ball 0 1) (fun _ h => h)
      (fun z => by simp [Metric.mem_ball, dist_zero_right])]
    exact (hasFiniteGramNegativeDimensionOn_iff_kernel
      (finiteBlaschkeGeneralizedSchurRealization F B) (Metric.ball 0 1)
      (finiteBlaschkeGeneralizedSchurCancelledIndex F B)).mp hexact.1
  · intro r hr
    apply hexact.2 r
    apply (hasFiniteGramNegativeDimensionOn_iff_kernel
      (finiteBlaschkeGeneralizedSchurRealization F B) (Metric.ball 0 1) r).mpr
    exact (hasFiniteKernelNegativeDimension_valueKernel_iff_realization
      F B (Metric.ball 0 1) (fun _ h => h)
      (fun z => by simp [Metric.mem_ball, dist_zero_right]) r).mp hr

/-- The same exact cancelled rank is visible on every exterior annulus, so the witness avoids all
denominator zeros. -/
theorem finiteBlaschkeGeneralizedSchurValueKernel_hasExteriorNegativeDimension_rank
    (F : DiskMultiplier) (B : FiniteBlaschke) (hFbd : F.bd ≤ 1) :
    HasFiniteKernelNegativeDimension
      (fun z w : B.exteriorDisk =>
        finiteBlaschkeGeneralizedSchurValueKernel F B z w)
      (finiteBlaschkeGeneralizedSchurCancelledIndex F B) := by
  have hglobal :=
    (finiteBlaschkeGeneralizedSchurKernel_exactNegativeSquares_rank F B hFbd).1
  let R := finiteBlaschkeGeneralizedSchurRealization F B
  let V := finiteBlaschkeExteriorOpenRegion F B
  have hext : R.HasFiniteGramNegativeDimensionOn B.exteriorDisk
      (finiteBlaschkeGeneralizedSchurCancelledIndex F B) :=
    (R.hasFiniteGramNegativeDimensionOn_openRegion_iff V
      (finiteBlaschkeGeneralizedSchurCancelledIndex F B)).mpr hglobal
  have hraw := (hasFiniteGramNegativeDimensionOn_iff_kernel
    R B.exteriorDisk (finiteBlaschkeGeneralizedSchurCancelledIndex F B)).mp hext
  exact (hasFiniteKernelNegativeDimension_valueKernel_iff_realization
    F B B.exteriorDisk B.exteriorDisk_subset_ball
      B.exteriorDisk_conj_mem_iff
      (finiteBlaschkeGeneralizedSchurCancelledIndex F B)).mpr hraw

end

end GaloisForLFunctions.HTGeometry
