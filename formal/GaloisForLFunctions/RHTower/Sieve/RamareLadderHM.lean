import GaloisForLFunctions.RHTower.Sieve.RamareLadderSupMeanSquare
import GaloisForLFunctions.RHTower.Sieve.LogPolyWindowHM

/-!
# The Ramaré ladder on the exceptional set

On the part of the annulus where a *first* prime range fails to be small, a *second*, higher range
supplies a pointwise zero-free-region bound on its own prime blocks, and the mean square of the
matching cofactor is bounded by Halász–Montgomery — where the measure of the exceptional set, not
the height of the window, multiplies the oscillation of the kernel.  That asymmetry is the whole
reason the second range may be placed above the window length: it never meets a height term.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Each cofactor block sits inside `[1, ⌊M/Q_j⌋]`. -/
theorem geomCofactorBlock_subset_Icc (M : ℕ) {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) (j : ℕ) :
    geomCofactorBlock M Q η j ⊆ Finset.Icc 1 ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ := by
  intro n hn
  have hbounds := geomCofactorBlockAt_bounds (A₀ := 1) (B₀ := M) (by norm_num) hQ hη j
  have hne : n ≠ 0 := by
    intro h
    exact hbounds.1 (h ▸ hn)
  rw [Finset.mem_Icc]
  exact ⟨Nat.one_le_iff_ne_zero.2 hne, hbounds.2 n hn⟩

/-- The Halász–Montgomery majorant of one cofactor block over a frequency set. -/
def ladderHMBound (M : ℕ) (Q η W volE : ℝ) (j : ℕ) : ℝ :=
  (2 * Real.pi)⁻¹
    * ((2 * ((⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)
          + ((((Nat.log 2 ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ) + 1)
                * (214 * Real.sqrt (2 * (2 * Real.pi * W)))
              + 3072 * ((⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
            * (2 * Real.pi * volE))
        * ((1 : ℝ) ^ 2 * ((geomCofactorBlock M Q η j).card : ℝ)))

/-- **The cofactor mean square over a frequency set, by Halász–Montgomery.** -/
theorem setIntegral_normSq_cofactorBlock_le_HM (P : Finset ℕ) (M : ℕ) {Q η W : ℝ}
    (hQ : 0 < Q) (hη : 0 ≤ η) {j : ℕ} (hNj : 1 ≤ ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ 2)
      ≤ ladderHMBound M Q η W (volume.real E) j := by
  have hsub := geomCofactorBlock_subset_Icc M hQ hη j
  have hbase := setIntegral_normSq_logPoly_le_HM_window (ramareCofactorCoeff P) hNj hsub hEm hEs
    (Ω := 1) zero_le_one (norm_ramareCofactorCoeff_le_one P)
  rw [ladderHMBound]
  exact hbase

/-- **The Ramaré ladder on the exceptional set: prime sup from arithmetic, cofactor from
Halász–Montgomery.** -/
theorem setIntegral_normSq_ramareBilinear_le_ladder_HM {P : Finset ℕ} (M : ℕ)
    {Q η W : ℝ} (hQ : 1 ≤ Q) (hη : 0 ≤ η) (hW : 1 ≤ W) {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ q ∈ P, q.Prime)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (V : ℕ → ℝ)
    (hNj : ∀ j ∈ Finset.range L, 1 ≤ ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊)
    (hbound : ∀ j ∈ Finset.range L, ∀ w ∈ E,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V j) :
    (∫ w in E, ‖ramareBilinear P M w‖ ^ 2)
      ≤ (L : ℝ) * ∑ j ∈ Finset.range L,
          (2 * (V j ^ 2 * ladderHMBound M Q η W (volume.real E) j)
            + 2 * ((geomBlock P Q (1 + η) j).card : ℝ) ^ 2
                * (2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
                    * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / (Q * (1 + η) ^ j) + 4
                      + (((M : ℕ) : ℝ) / (Q * (1 + η) ^ j) ^ 2 + 1)))) := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  refine setIntegral_normSq_ramareBilinear_le_ladder_supMeanSquare (P := P) M hQ hη hW hL
    hPprime hP hEm hEs V (fun j => ladderHMBound M Q η W (volume.real E) j) hbound ?_
  intro j hj
  exact setIntegral_normSq_cofactorBlock_le_HM P M hQ0 hη (hNj j hj) hEm hEs

end

end RHTower.Sieve
