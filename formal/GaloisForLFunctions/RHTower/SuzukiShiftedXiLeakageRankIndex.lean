import GaloisForLFunctions.RHTower.SuzukiShiftedXiBoundaryFactorization
import GaloisForLFunctions.RHTower.XiShiftEulerCommonDivisorIndex

open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Algebraic operator rank as complete finite-rank profile, with `⊤` for infinite rank. -/
def upperHardyOperatorRankIndex
    (T : UpperHardyL2 →L[ℂ] LowerHardyL2) : WithTop ℕ :=
  ⨆ q : {r : ℕ // UpperHardyOperatorRankAtLeast T r}, (q.1 : WithTop ℕ)

/-- Exact theorem-A rank identity, including exceptional common-divisor cancellation and infinite
rank. -/
theorem suzukiShiftedXiHardyLeakage_rankIndex_eq_uncancelledDivisorIndex
    {omega : ℝ} (homega : 0 ≤ omega) :
    upperHardyOperatorRankIndex (suzukiShiftedXiHardyLeakage omega) =
      xiShiftUncancelledDivisorIndex homega := by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨r, hr⟩
    have hq :=
      (suzukiShiftedXiHardyLeakage_rankAtLeast_iff_uncancelledDivisorQuotient
        homega r).mp hr
    exact le_iSup_of_le
      (⟨r, hq⟩ : {s : ℕ // HasIndependentDimensionAtLeast
        (XiShiftUncancelledDivisorQuotient homega) s}) le_rfl
  · apply iSup_le
    rintro ⟨r, hr⟩
    have hT :=
      (suzukiShiftedXiHardyLeakage_rankAtLeast_iff_uncancelledDivisorQuotient
        homega r).mpr hr
    exact le_iSup_of_le
      (⟨r, hT⟩ : {s : ℕ // UpperHardyOperatorRankAtLeast
        (suzukiShiftedXiHardyLeakage omega) s}) le_rfl

/-- At a nonexceptional shift, literal leakage rank is exactly the multiplicity-copy count of Xi
zeros beyond the transverse line, finite or infinite. -/
theorem suzukiShiftedXiHardyLeakage_rankIndex_nonexceptional_classification
    {omega : ℝ} (homega : 0 < omega)
    (hnon : SuzukiShiftNonexceptional omega) :
    (Finite (XiShiftRightZeroCopy omega) ∧
      upperHardyOperatorRankIndex (suzukiShiftedXiHardyLeakage omega) =
        (Nat.card (XiShiftRightZeroCopy omega) : WithTop ℕ)) ∨
    (Infinite (XiShiftRightZeroCopy omega) ∧
      upperHardyOperatorRankIndex (suzukiShiftedXiHardyLeakage omega) = ⊤) := by
  rw [suzukiShiftedXiHardyLeakage_rankIndex_eq_uncancelledDivisorIndex homega.le]
  exact xiShiftUncancelledDivisorIndex_nonexceptional_classification homega hnon

end

end RHTower
