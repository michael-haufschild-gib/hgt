import GaloisForLFunctions.HTGeometry.ComplexKernelTransfer
import GaloisForLFunctions.HTGeometry.OrthonormalDecayWronskianEscapeLaw
import GaloisForLFunctions.HTGeometry.ChristoffelBoundedKernel

/-!
# Global second-kind escape from one clopen kernel point

Closedness upgrades one bounded complex kernel point to kernel summability everywhere.  On every
real slice this is exactly orthonormal first-kind square summability.  The constant nonzero
orthonormal Wronskian then forces the adjacent recurrence-weighted second-kind coordinates to
escape every bound at every real point.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Clopen-kernel global second-kind escape law.**  If the bounded-kernel locus is closed and
nonempty, no real point admits a uniform simultaneous bound on the two adjacent
recurrence-weighted second-kind coordinates. -/
theorem weightedSecondKind_escape_everywhere_of_isClosed_boundedKernel
    (h : PositiveMomentForm s)
    (hclosed : IsClosed {z : ℂ | BoundedKernel s z})
    {z0 : ℂ} (hz0 : BoundedKernel s z0) :
    ∀ x : ℝ, ∀ C : ℝ, ∃ n : ℕ,
      C < |recurOffSqrt s n * (secondKindNorm s n).eval x| ∨
      C < |recurOffSqrt s n * (secondKindNorm s (n + 1)).eval x| := by
  intro x C
  have hsumComplex :=
    summable_kernel_everywhere_of_isClosed h hclosed hz0 (x : ℂ)
  have hsumReal : Summable fun k => ((monicOrtho s k).eval x) ^ (2 : ℕ) /
      momentInner s (monicOrtho s k) (monicOrtho s k) := by
    convert hsumComplex using 1
    funext k
    rw [normSq_monicOrthoC_ofReal]
  exact orthonormalDecay_forces_weightedSecondKind_escape h x hsumReal C

/-- Equivalently, every proposed global real bound fails somewhere at every real observation
point. -/
theorem not_forall_weightedSecondKind_le_of_isClosed_boundedKernel
    (h : PositiveMomentForm s)
    (hclosed : IsClosed {z : ℂ | BoundedKernel s z})
    {z0 : ℂ} (hz0 : BoundedKernel s z0) (x C : ℝ) :
    ¬ ∀ n : ℕ,
      |recurOffSqrt s n * (secondKindNorm s n).eval x| ≤ C ∧
      |recurOffSqrt s n * (secondKindNorm s (n + 1)).eval x| ≤ C := by
  intro hbounded
  obtain ⟨n, hn | hn⟩ :=
    weightedSecondKind_escape_everywhere_of_isClosed_boundedKernel h hclosed hz0 x C
  · exact (not_lt_of_ge (hbounded n).1) hn
  · exact (not_lt_of_ge (hbounded n).2) hn

end HTGeometry
