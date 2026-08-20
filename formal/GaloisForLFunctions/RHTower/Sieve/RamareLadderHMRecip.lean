import GaloisForLFunctions.RHTower.Sieve.RamareLadderHM
import GaloisForLFunctions.RHTower.Sieve.LogPolyWindowHMRecip

/-!
# The Ramaré ladder on the exceptional set, with the Kuzmin–Landau mass

`Sieve/RamareLadderHM.ladderHMBound` carries the old kernel constant, whose `3072·N·|E|` term is
never smaller than the trivial bound once `|E| ≥ 1`.  With the reciprocal decay the mass is
`2N + 48π·N·log(2+2T) + C(T,N)·|E|`, so the exceptional half gains as soon as `|E| ≲ N/√T` — a
condition the moment method *can* meet, and the one that makes the low prime range's bottom
polylogarithmic.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The Kuzmin–Landau Halász–Montgomery majorant of one cofactor block over a frequency set. -/
def ladderHMBoundRecip (M : ℕ) (Q η W volE : ℝ) (j : ℕ) : ℝ :=
  (2 * Real.pi)⁻¹
    * (hmMassRecip ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ (2 * Real.pi * W) (2 * Real.pi * volE)
        * ((1 : ℝ) ^ 2 * ((geomCofactorBlock M Q η j).card : ℝ)))

/-- **The cofactor mean square over a frequency set, with reciprocal kernel decay.** -/
theorem setIntegral_normSq_cofactorBlock_le_HM_recip (P : Finset ℕ) (M : ℕ) {Q η W : ℝ}
    (hQ : 0 < Q) (hη : 0 ≤ η) (hW : 1 ≤ W) {j : ℕ}
    (hNj : 1 ≤ ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ 2)
      ≤ ladderHMBoundRecip M Q η W (volume.real E) j := by
  have hsub := geomCofactorBlock_subset_Icc M hQ hη j
  have hbase := setIntegral_normSq_logPoly_le_HM_window_recip (ramareCofactorCoeff P) hNj hsub
    hEm hW hEs (Ω := 1) zero_le_one (norm_ramareCofactorCoeff_le_one P)
  rw [ladderHMBoundRecip]
  exact hbase

/-- **The Ramaré ladder on the exceptional set, with the Kuzmin–Landau mass.** -/
theorem setIntegral_normSq_ramareBilinear_le_ladder_HM_recip {P : Finset ℕ} (M : ℕ)
    {Q η W : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) (hW : 1 ≤ W) {L : ℕ} (hL : 1 ≤ L)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (V : ℕ → ℝ)
    (hNj : ∀ j ∈ Finset.range L, 1 ≤ ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊)
    (hbound : ∀ j ∈ Finset.range L, ∀ w ∈ E,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V j) :
    (∫ w in E, ‖ramareBilinear P M w‖ ^ 2)
      ≤ 2 * (L : ℝ) * ∑ j ∈ Finset.range L,
          V j ^ 2 * ladderHMBoundRecip M Q η W (volume.real E) j
        + 2 * ∫ w in E, ‖ramareLadderError P M Q η L w‖ ^ 2 := by
  refine setIntegral_normSq_ramareBilinear_le_ladder_supMeanSquare (P := P) M hQ hη hL hP
    hEm hEs V (fun j => ladderHMBoundRecip M Q η W (volume.real E) j) hbound ?_
  intro j hj
  exact setIntegral_normSq_cofactorBlock_le_HM_recip P M hQ hη hW (hNj j hj) hEm hEs

end

end RHTower.Sieve
