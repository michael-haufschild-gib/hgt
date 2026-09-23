import GaloisForLFunctions.RHTower.Sieve.RamareLadderAnnulus
import GaloisForLFunctions.RHTower.Sieve.OmegaBudgetLadderTail

/-!
# The Ramaré bilinear mean square as an affine function of the height

Every term of the cut-window bound is affine in the height `W`: the mean value factor of a ladder
step contributes `5π/2·W`, and so does the ladder discrepancy, while the low-frequency disc and the
diagonal parts of the mean value factors are constants.  Separating the two gives the affine
majorant that Gallagher's dyadic tail consumes.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The height coefficient of one ladder step. -/
def ramareStepSlope (M : ℕ) (Q η : ℝ) (V : ℕ → ℝ) (j : ℕ) : ℝ :=
  V j ^ (2 : ℕ) * (5 * Real.pi / 2 * ((geomCofactorBlock M Q η j).card : ℝ))

/-- The height-free part of one ladder step. -/
def ramareStepConst (M : ℕ) (Q η w₀ : ℝ) (V U Vlow : ℕ → ℝ) (j : ℕ) : ℝ :=
  V j ^ (2 : ℕ) * (5 * Real.exp 1 / 2 * ((⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)
      * ((geomCofactorBlock M Q η j).card : ℝ))
    + Vlow j ^ (2 : ℕ) * U j ^ (2 : ℕ) * (2 * w₀)

/-- The slope of the ladder's affine majorant. -/
def ramareLadderSlope (M L : ℕ) (Q η : ℝ) (V : ℕ → ℝ) : ℝ :=
  2 * (L : ℝ) * ∑ j ∈ Finset.range L, ramareStepSlope M Q η V j
    + 2 * (5 * Real.pi / 2) * ladderDefectSum L M Q η

/-- The constant of the ladder's affine majorant. -/
def ramareLadderConst (M L : ℕ) (Q η w₀ : ℝ) (V U Vlow : ℕ → ℝ) : ℝ :=
  2 * (L : ℝ) * ∑ j ∈ Finset.range L, ramareStepConst M Q η w₀ V U Vlow j
    + 2 * (5 * Real.exp 1 / 2 * ((⌊(M : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ)) * ladderDefectSum L M Q η

theorem ramareStepSlope_nonneg (M : ℕ) (Q η : ℝ) (V : ℕ → ℝ) (j : ℕ) :
    0 ≤ ramareStepSlope M Q η V j := by
  have := Real.pi_pos
  rw [ramareStepSlope]
  positivity

theorem ramareStepConst_nonneg (M : ℕ) (Q η : ℝ) {w₀ : ℝ} (hw₀ : 0 ≤ w₀) (V U Vlow : ℕ → ℝ)
    (j : ℕ) : 0 ≤ ramareStepConst M Q η w₀ V U Vlow j := by
  rw [ramareStepConst]
  positivity

theorem ramareLadderSlope_nonneg {M L : ℕ} {Q η : ℝ} (hQ : 1 < Q) (hη : 0 ≤ η) (V : ℕ → ℝ) :
    0 ≤ ramareLadderSlope M L Q η V := by
  have hd := ladderDefectSum_nonneg (L := L) (B₀ := M) hQ hη
  have hpi := Real.pi_pos
  have h1 : (0 : ℝ) ≤ 2 * (L : ℝ) * ∑ j ∈ Finset.range L, ramareStepSlope M Q η V j := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => ?_)
    exact ramareStepSlope_nonneg M Q η V j
  have h2 : (0 : ℝ) ≤ 2 * (5 * Real.pi / 2) * ladderDefectSum L M Q η := by positivity
  rw [ramareLadderSlope]
  linarith

theorem ramareLadderConst_nonneg {M L : ℕ} {Q η w₀ : ℝ} (hQ : 1 < Q) (hη : 0 ≤ η)
    (hw₀ : 0 ≤ w₀) (V U Vlow : ℕ → ℝ) : 0 ≤ ramareLadderConst M L Q η w₀ V U Vlow := by
  have hd := ladderDefectSum_nonneg (L := L) (B₀ := M) hQ hη
  have h1 : (0 : ℝ) ≤ 2 * (L : ℝ)
      * ∑ j ∈ Finset.range L, ramareStepConst M Q η w₀ V U Vlow j := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => ?_)
    exact ramareStepConst_nonneg M Q η hw₀ V U Vlow j
  have h2 : (0 : ℝ) ≤ 2 * (5 * Real.exp 1 / 2 * ((⌊(M : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
      * ladderDefectSum L M Q η := by positivity
  rw [ramareLadderConst]
  linarith

/-- **The Ramaré bilinear mean square, affine in the height.** -/
theorem integral_normSq_ramareBilinear_affine_le {P : Finset ℕ} (M : ℕ) {Q η w₀ W : ℝ}
    (hQ : 1 < Q) (hη : 0 ≤ η) (hW : 1 ≤ W) (hw₀ : 0 ≤ w₀) (hwW : w₀ ≤ W) {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ q ∈ P, q.Prime) (hPge : ∀ p ∈ P, Q ≤ (p : ℝ))
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    (V U Vlow : ℕ → ℝ) (hV : ∀ j, 0 ≤ V j) (hU : ∀ j, 0 ≤ U j) (hVlow : ∀ j, 0 ≤ Vlow j)
    (hann : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-W) W \ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V j)
    (hlowP : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ Vlow j)
    (hlowC : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ≤ U j) :
    (∫ w in Set.Icc (-W) W, ‖ramareBilinear P M w‖ ^ (2 : ℕ))
      ≤ ramareLadderSlope M L Q η V * W + ramareLadderConst M L Q η w₀ V U Vlow := by
  classical
  have hbase := integral_normSq_ramareBilinear_annulus_le (P := P) M hQ hη hW hw₀ hwW hL
    hPprime hPge hP V U Vlow hV hU hVlow hann hlowP hlowC
  refine hbase.trans (le_of_eq ?_)
  have hterm : ∀ j ∈ Finset.range L,
      (V j ^ (2 : ℕ) * ((5 * Real.pi / 2 * W
              + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
            * ((geomCofactorBlock M Q η j).card : ℝ))
          + Vlow j ^ (2 : ℕ) * U j ^ (2 : ℕ) * (2 * w₀))
      = ramareStepSlope M Q η V j * W + ramareStepConst M Q η w₀ V U Vlow j := by
    intro j _
    rw [ramareStepSlope, ramareStepConst]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ramareLadderSlope, ramareLadderConst,
    ← Finset.sum_mul]
  ring

end

end RHTower.Sieve
