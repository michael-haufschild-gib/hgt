import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarLaplaceMoments
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaFiniteMeanZeroOffDiagonal
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaCouplingUsesOnlyDetailMass
import GaloisForLFunctions.RHTower.ArchimedeanAnomalyConstantLaws

/-!
# Positive Laplace representation of the Haar Gamma interactions

Each ordered rectangle pairing factors into oppositely signed Laplace
moments. The original rectangle measure controls the absolute series,
including touching cells, so every Gamma off-diagonal entry is nonnegative.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open MeanZeroIntervals BiarithmeticGaugeGeometry

/-- The literal off-diagonal Gamma matrix entry; its diagonal is zero. -/
def haarGammaCoupling (a b : ℕ) : ℝ :=
  -(∫ p : ℝ × ℝ, haarProfile a p.1 * haarProfile b p.2
    ∂gammaRectangleMeasure
      (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
      (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ)))

private theorem haarPair_order {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    Real.log ((2 * a + 2 : ℕ) : ℝ) ≤ Real.log ((2 * b : ℕ) : ℝ) := by
  apply Real.log_le_log (by positivity)
  exact_mod_cast (show 2 * a + 2 ≤ 2 * b by omega)

private theorem haarPair_disjoint {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a ≠ b) :
    Disjoint (Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)))
      (Ioo (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ))) := by
  apply disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hab with h | h
  · have hs := haarPair_order ha h
    linarith only [hs, hx.2, hy.1]
  · have hs := haarPair_order hb h
    linarith only [hs, hy.2, hx.1]

theorem haarGammaCoupling_self (a : ℕ) : haarGammaCoupling a a = 0 := by
  rw [haarGammaCoupling, gammaRectangleMeasure_self, integral_zero_measure, neg_zero]

theorem haarGammaCoupling_symm {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    haarGammaCoupling a b = haarGammaCoupling b a := by
  by_cases hab : a = b
  · subst b
    rfl
  have hd := haarPair_disjoint ha hb hab
  have h := integral_gammaRectangle_swap hd
    (fun p : ℝ × ℝ => haarProfile a p.1 * haarProfile b p.2)
  unfold haarGammaCoupling
  rw [← h]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun _ => mul_comm _ _

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
