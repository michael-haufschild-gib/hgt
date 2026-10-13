import GaloisForLFunctions.HTGeometry.WalshPowerCompact
import GaloisForLFunctions.RHTower.PaperWoldWalshEnvelope
import GaloisForLFunctions.RHTower.PaperWoldCompactDomain
import GaloisForLFunctions.HTGeometry.PaperCompactIdealTrace

/-! # The actual full Wold operator after Walsh signing

The complete operator exists and is compact throughout `t < 3/4`, including
the strip where its unchanged matrix square energy diverges.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

def paperWoldFullWalshPhase (q : ℕ × ℕ) : {z : ℂ // ‖z‖ = 1} :=
  ⟨dyadicWalshSign q.1 q.2, dyadicWalshSign_norm _ _⟩

def paperWoldWalshDirectedKernel (t : ℝ) (q : ℕ × ℕ) : ℂ :=
  dyadicWalshSign q.1 q.2 * paperWoldDirectedKernel t q

theorem paperWoldWalshDirectedKernel_isHS_iff (t : ℝ) :
    HilbertSchmidt.IsHS (paperWoldWalshDirectedKernel t) ↔ t < 1 / 2 :=
  paperWoldDirectedKernel_phase_isHS_iff t paperWoldFullWalshPhase

theorem paperWoldWalshPowerData_entry (t : PaperWoldWalshBand) (n j : ℕ) :
    (if n < j then (paperWoldWalshPowerData t).row n * (paperWoldWalshPowerData t).column j else 0) =
      paperWoldDirectedKernel t.val (n, j) := by
  change (if n < j then
    ((((n : ℝ) + 1) ^ (2 * t.val) * xiHeatCassiniWoldNatIncrement n : ℝ) : ℂ) *
      (xiHeatCassiniWoldNatIncrement j : ℂ) else 0) = _
  simp only [paperWoldDirectedKernel, Complex.ofReal_mul]

def paperWoldWalshFullOperator (t : {t : ℝ // t < 3 / 4}) : PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  if h : t.val < 1 / 2 then
    HilbertSchmidt.toOperator ((paperWoldWalshDirectedKernel_isHS_iff t).mpr h)
  else (paperWoldWalshPowerData ⟨t.val, le_of_not_gt h, t.property⟩).operator

theorem paperWoldWalshFullOperator_single (t : {t : ℝ // t < 3 / 4}) (n j : ℕ) :
    paperWoldWalshFullOperator t (lp.single 2 j 1) n = paperWoldWalshDirectedKernel t (n, j) := by
  unfold paperWoldWalshFullOperator
  split_ifs with h
  · exact HilbertSchmidt.toOperator_single _ n j
  · rw [WalshPowerKernel.operator_single, paperWoldWalshPowerData_entry]
    rfl

theorem paperWoldWalshFullOperator_compact (t : {t : ℝ // t < 3 / 4}) :
    IsCompactOperator (paperWoldWalshFullOperator t) := by
  unfold paperWoldWalshFullOperator
  split_ifs
  · exact (HilbertSchmidt.isHilbertSchmidt_toOperator _).isCompactOperator
  · exact WalshPowerKernel.operator_compact _

theorem paperWoldWalshFullOperator_abs_entry (t : {t : ℝ // t < 3 / 4}) (n j : ℕ) :
    ‖paperWoldWalshFullOperator t (lp.single 2 j 1) n‖ = ‖paperWoldDirectedKernel t (n, j)‖ := by
  rw [paperWoldWalshFullOperator_single, paperWoldWalshDirectedKernel, norm_mul,
    dyadicWalshSign_norm, one_mul]

theorem paperWoldWalshFullOperator_isHilbertSchmidt_iff (t : {t : ℝ // t < 3 / 4}) :
    (paperWoldWalshFullOperator t).IsHilbertSchmidt ↔ t.val < 1 / 2 := by
  constructor
  · intro h
    have hK := HilbertSchmidt.isHS_matrixOf h
    have he : HilbertSchmidt.matrixOf (paperWoldWalshFullOperator t) =
        paperWoldWalshDirectedKernel t := by
      funext q
      exact paperWoldWalshFullOperator_single t q.1 q.2
    rw [he] at hK
    exact (paperWoldWalshDirectedKernel_isHS_iff t).mp hK
  · intro h
    rw [paperWoldWalshFullOperator, dif_pos h]
    exact HilbertSchmidt.isHilbertSchmidt_toOperator _

theorem paperWoldWalshFullOperator_not_hilbertSchmidt (t : PaperWoldWalshBand) :
    ¬ (paperWoldWalshFullOperator ⟨t.val, t.property.2⟩).IsHilbertSchmidt := by
  rw [paperWoldWalshFullOperator_isHilbertSchmidt_iff]
  exact not_lt_of_ge t.property.1

theorem paperWoldWalshFullOperator_traceCost (t : {t : ℝ // t < 3 / 4}) :
    compactOperatorTraceCost PaperWoldHistory (paperWoldWalshFullOperator t) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (paperWoldWalshFullOperator_compact t)

end
end RHTower
