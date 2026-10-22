import GaloisForLFunctions.RHTower.Suzuki.SuzukiShiftedXiBoundaryLeakage
import GaloisForLFunctions.HTGeometry.HardyDiskLineMultiplierTransport
import GaloisForLFunctions.HTGeometry.HardyOperatorGramRankProfile

/-!
# Exact negative-Gram rank profile of actual shifted-Xi boundary leakage

The literal patched shifted-Xi compression is pulled back through the exact disk-to-line Hardy
unitary.  Its negative Szegő Gram kernel has precisely the algebraic rank profile of the original
anti-causal operator.  This is operator-theoretic and unconditional; identifying the displayed Gram
with the meromorphic shifted-Xi kernel is a separate scalar boundary identity.
-/

open Complex Metric
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

local instance suzukiShiftedXiBoundaryGramRankLocalInst1 : CompleteSpace UpperHardyL2 :=
  isClosed_hardyL2.completeSpace_coe

local instance suzukiShiftedXiBoundaryGramRankLocalInst2 : CompleteSpace LowerHardyL2 :=
  (Submodule.isClosed_orthogonal hardyL2).completeSpace_coe

/-- Algebraic rank at least `r` for an operator with literal upper-Hardy domain. -/
def UpperHardyOperatorRankAtLeast
    (T : UpperHardyL2 →L[ℂ] LowerHardyL2) (r : ℕ) : Prop :=
  ∃ v : Fin r → UpperHardyL2, LinearIndependent ℂ (fun i => T (v i))

/-- Actual shifted-Xi leakage pulled back to disk Hardy space by the exact Cayley unitary. -/
def suzukiShiftedXiDiskHardyLeakage (omega : ℝ) :
    HardyDisk →L[ℂ] LowerHardyL2 :=
  (suzukiShiftedXiHardyLeakage omega).comp hardyDiskLineCayleyCLM

/-- Literal negative Gram kernel of the actual shifted-Xi boundary compression. -/
def suzukiShiftedXiBoundaryNegativeGramKernel (omega : ℝ) (z w : ℂ) : ℂ :=
  hardyOperatorNegativeGramKernel (suzukiShiftedXiDiskHardyLeakage omega) z w

theorem hardyOperatorRankAtLeast_suzukiShiftedXiDiskHardyLeakage_iff
    (omega : ℝ) (r : ℕ) :
    HardyOperatorRankAtLeast (suzukiShiftedXiDiskHardyLeakage omega) r ↔
      UpperHardyOperatorRankAtLeast (suzukiShiftedXiHardyLeakage omega) r := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨fun i => hardyDiskLineCayleyCLM (v i), ?_⟩
    simpa [suzukiShiftedXiDiskHardyLeakage] using hv
  · rintro ⟨v, hv⟩
    refine ⟨fun i => hardyLineDiskCayleyCLM (v i), ?_⟩
    simpa [suzukiShiftedXiDiskHardyLeakage] using hv

/-- Every finite negative-index level of the actual boundary Gram is exactly an algebraic rank
level of the stated anti-causal shifted-Xi leakage operator. -/
theorem suzukiShiftedXiBoundaryNegativeGramKernel_negativeDimension_iff_rankAtLeast
    (omega : ℝ) (r : ℕ) :
    HasFiniteKernelNegativeDimension
        (fun z w : Metric.ball (0 : ℂ) 1 =>
          suzukiShiftedXiBoundaryNegativeGramKernel omega z.1 w.1) r ↔
      UpperHardyOperatorRankAtLeast (suzukiShiftedXiHardyLeakage omega) r := by
  change HasFiniteKernelNegativeDimension
      (fun z w : Metric.ball (0 : ℂ) 1 =>
        hardyOperatorNegativeGramKernel
          (suzukiShiftedXiDiskHardyLeakage omega) z.1 w.1) r ↔ _
  rw [hardyOperatorNegativeGramKernel_negativeDimension_iff_rankAtLeast,
    hardyOperatorRankAtLeast_suzukiShiftedXiDiskHardyLeakage_iff]

end RHTower
