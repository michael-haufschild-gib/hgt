import GaloisForLFunctions.RHTower.PaperWoldFullKernel
import GaloisForLFunctions.RHTower.PaperWoldNearSignedForm
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import GaloisForLFunctions.HTGeometry.HilbertSchmidtBlockEigenvector

/-! # Compact completion of every bounded selection of Wold interactions

All unwindowed interactions are retained. Arbitrary window schedules and bounded
complex entrywise masks have one common Hilbert–Schmidt norm budget.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped BigOperators ENNReal

def paperWoldMaskedOperator (p : PaperWoldStrictHalf) (m : PaperWoldMask) :
    PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  HilbertSchmidt.toOperator (paperWoldMaskedKernel_isHS p m)

def paperWoldFullOperator (p : PaperWoldStrictHalf) : PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  paperWoldMaskedOperator p paperWoldFullMask

@[simp] theorem paperWoldMaskedOperator_apply (p : PaperWoldStrictHalf) (m : PaperWoldMask)
    (x : PaperWoldHistory) (n : ℕ) :
    paperWoldMaskedOperator p m x n = ∑' j, paperWoldMaskedKernel p m (n,j) * x j := rfl

theorem paperWoldFullOperator_apply (p : PaperWoldStrictHalf) (x : PaperWoldHistory) (n : ℕ) :
    paperWoldFullOperator p x n = ∑' j, paperWoldFullKernel p (n,j) * x j := by
  simp only [paperWoldFullOperator, paperWoldMaskedOperator_apply, paperWoldMaskedKernel_full]

@[simp] theorem paperWoldMaskedOperator_single (p : PaperWoldStrictHalf) (m : PaperWoldMask) (n j : ℕ) :
    paperWoldMaskedOperator p m (lp.single 2 j (1 : ℂ)) n = paperWoldMaskedKernel p m (n,j) :=
  HilbertSchmidt.toOperator_single _ n j

@[simp] theorem paperWoldFullOperator_single (p : PaperWoldStrictHalf) (n j : ℕ) :
    paperWoldFullOperator p (lp.single 2 j (1 : ℂ)) n = paperWoldFullKernel p (n,j) := by
  simp only [paperWoldFullOperator, paperWoldMaskedOperator_single, paperWoldMaskedKernel_full]

theorem paperWoldMaskedOperator_isHilbertSchmidt (p : PaperWoldStrictHalf) (m : PaperWoldMask) :
    (paperWoldMaskedOperator p m).IsHilbertSchmidt :=
  HilbertSchmidt.isHilbertSchmidt_toOperator _

theorem paperWoldMaskedOperator_compact (p : PaperWoldStrictHalf) (m : PaperWoldMask) :
    IsCompactOperator (paperWoldMaskedOperator p m) :=
  (paperWoldMaskedOperator_isHilbertSchmidt p m).isCompactOperator

theorem paperWoldMaskedOperator_norm_le (p : PaperWoldStrictHalf) (m : PaperWoldMask) :
    ‖paperWoldMaskedOperator p m‖ ≤ HilbertSchmidt.hsNorm (paperWoldFullKernel p) :=
  (HilbertSchmidt.norm_toOperator_le _).trans
    (Real.sqrt_le_sqrt (paperWoldMaskedKernel_hsNormSq_le p m))

theorem paperWoldMaskedOperator_traceCost (p : PaperWoldStrictHalf) (m : PaperWoldMask) :
    compactOperatorTraceCost PaperWoldHistory (paperWoldMaskedOperator p m) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (paperWoldMaskedOperator_compact p m)

theorem paperWoldMaskedOperator_distance (p : PaperWoldStrictHalf) (m : PaperWoldMask) :
    compactIdealDistance (paperWoldMaskedOperator p m) = 0 :=
  compactIdealDistance_eq_zero_of_isCompactOperator _ (paperWoldMaskedOperator_compact p m)

theorem paperWoldMaskedOperator_trace_add (p : PaperWoldStrictHalf) (m : PaperWoldMask)
    (T : PaperWoldHistory →L[ℂ] PaperWoldHistory) :
    compactOperatorTraceCost PaperWoldHistory (T + paperWoldMaskedOperator p m) =
      compactOperatorTraceCost PaperWoldHistory T :=
  compactOperatorTraceCost_add_compact T ⟨_, paperWoldMaskedOperator_compact p m⟩

theorem paperWoldMaskedOperator_distance_add (p : PaperWoldStrictHalf) (m : PaperWoldMask)
    (T : PaperWoldHistory →L[ℂ] PaperWoldHistory) :
    compactIdealDistance (T + paperWoldMaskedOperator p m) = compactIdealDistance T :=
  paperCompactIdealDistance_add_compact T ⟨_, paperWoldMaskedOperator_compact p m⟩

/-- Simultaneous finite row-and-column observation of the full masked kernel. -/
def paperWoldMaskedCutoff (p : PaperWoldStrictHalf) (m : PaperWoldMask) (s : Finset ℕ) :
    PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  HilbertSchmidt.toOperator (HilbertSchmidt.isHS_truncKernel (paperWoldMaskedKernel_isHS p m) s)

theorem paperWoldMaskedCutoff_single (p : PaperWoldStrictHalf) (m : PaperWoldMask)
    (s : Finset ℕ) (n j : ℕ) :
    paperWoldMaskedCutoff p m s (lp.single 2 j (1 : ℂ)) n =
      if n ∈ s ∧ j ∈ s then paperWoldMaskedKernel p m (n,j) else 0 := by
  rw [paperWoldMaskedCutoff, HilbertSchmidt.toOperator_single]
  rfl

theorem paperWoldMaskedCutoff_hs_tendsto (p : PaperWoldStrictHalf) (m : PaperWoldMask) :
    Tendsto (fun s : Finset ℕ => HilbertSchmidt.hsNorm
      (paperWoldMaskedKernel p m - HilbertSchmidt.truncKernel (paperWoldMaskedKernel p m) s))
      atTop (𝓝 0) :=
  HilbertSchmidt.tendsto_hsNorm_sub_truncKernel (paperWoldMaskedKernel_isHS p m)

theorem paperWoldMaskedCutoff_norm_tendsto (p : PaperWoldStrictHalf) (m : PaperWoldMask) :
    Tendsto (paperWoldMaskedCutoff p m) atTop (𝓝 (paperWoldMaskedOperator p m)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact HilbertSchmidt.tendsto_norm_toOperator_truncKernel_sub (paperWoldMaskedKernel_isHS p m)

theorem paperWoldMaskedCutoff_compact (p : PaperWoldStrictHalf) (m : PaperWoldMask) (s : Finset ℕ) :
    IsCompactOperator (paperWoldMaskedCutoff p m s) :=
  (HilbertSchmidt.isHilbertSchmidt_toOperator _).isCompactOperator

theorem paperWoldFullOperator_ne_zero (p : PaperWoldStrictHalf) : paperWoldFullOperator p ≠ 0 := by
  intro hz
  have h := paperWoldFullOperator_single p 6 7
  rw [hz] at h
  have hre := congrArg Complex.re h
  simp only [zero_apply, lp.coeFn_zero, Pi.zero_apply, Complex.zero_re,
    paperWoldFullKernel, show (6 : ℕ) < 7 by omega, if_pos, Complex.ofReal_re] at hre
  linarith [paperWoldCompositeInteraction_pos p.nearParameters]

end
end RHTower
