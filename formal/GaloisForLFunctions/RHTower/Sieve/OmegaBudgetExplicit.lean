import GaloisForLFunctions.RHTower.Sieve.OmegaBudgetClosed
import GaloisForLFunctions.RHTower.Sieve.AnnulusRelBound
import GaloisForLFunctions.RHTower.Sieve.RelMoebiusSharp

/-!
# The Route E budget in closed form

Composing the cut-window head bound with the Gallagher split expresses the whole budget through the
ladder's parameters, the annulus constant `ρ` and the disc constant `s`.  Nothing analytic remains:
every quantity below is an elementary function of `x`, `h`, `Q`, `η`, `L`, `B₀`, `G`, `w₀`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The head of the Gallagher split, as a single explicit quantity. -/
def spectralHead (z₀ z L B₀ : ℕ) (Q η w₀ G ρ s : ℝ) : ℝ :=
  2 * ((ρ * Real.sqrt (5 * Real.pi / 2 + 5 * Real.exp 1 / 2)
        * ((L : ℝ) * (B₀ : ℝ) + Q * (((1 + η) ^ L - 1) / η))) ^ (2 : ℕ)
      + (∑ j ∈ Finset.range L, discMajorant (primesRange z₀ z) B₀ Q η s w₀ j) ^ (2 : ℕ))
    + 2 * ((5 * Real.pi / 2 * G
          + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
        * (Real.log ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) / Real.log Q
          * ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j * η + 1)
              * ((1 + (B₀ : ℝ)) * η / (Q * (1 + η) ^ j) + 5
                + (B₀ : ℝ) / (Q * (1 + η) ^ j) ^ (2 : ℕ))))

/-- **The Route E budget in closed form.** -/
theorem omegaBudget_le_explicit {x h : ℝ} {z₀ z L B₀ : ℕ} {Q η w₀ G ρ s : ℝ}
    (hδ : 0 < fibreWidth x h) (hB₀ : B₀ = ⌊Real.sqrt x + h⌋₊)
    (hQ : Q = (z₀ : ℝ)) (hQ1 : 1 < Q) (hη : 0 < η) (hG : 1 ≤ G) (hw₀ : 0 ≤ w₀) (hwG : w₀ ≤ G)
    (hL : 1 ≤ L) (hρ : 0 < ρ) (hs : 0 ≤ s) (hz : z = ⌊Q * (1 + η) ^ L⌋₊)
    (hGle : ∀ j ∈ Finset.range L, G ≤ (B₀ : ℝ) / (Q * (1 + η) ^ j))
    (hV : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-G) G \ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock (primesRange z₀ z) Q (1 + η) j) w‖ ≤ ρ * (Q * (1 + η) ^ j))
    (hU : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly moebiusCoeff (geomCofactorBlockAt 1 B₀ Q η j) w‖
        ≤ s * ((B₀ : ℝ) / (Q * (1 + η) ^ j))) :
    omegaBudget x h z₀ z
      ≤ 16 * Real.sqrt x
          * (2 * (fibreWidth x h) ^ (2 : ℕ) * spectralHead z₀ z L B₀ Q η w₀ G ρ s
            + (4 * (5 * Real.pi / 2
                  * ∑ n ∈ fibreIndex x h, ‖omegaCoeff (primesRange z₀ z) n‖ ^ (2 : ℕ))
                / (Real.pi ^ (2 : ℕ) * G)
              + 4 * (spectralHead z₀ z L B₀ Q η w₀ G ρ s
                    + 5 * Real.exp 1 / 2 * ((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ)
                    * ∑ n ∈ fibreIndex x h, ‖omegaCoeff (primesRange z₀ z) n‖ ^ (2 : ℕ))
                / (3 * Real.pi ^ (2 : ℕ) * G ^ (2 : ℕ))))
        + 204 * (((primesRange z₀ z).card : ℝ) + 1) ^ (2 : ℕ) * (Real.sqrt x + 1)
        + 2 * (h + 1) * (2 * h + 1)
            * (4 * (Real.sqrt x / 2 + h + 1) * mertensS z + 4 * ((Nat.primesLE z).card : ℝ)
              + 8 * ((Nat.primesLE z).card : ℝ) ^ (2 : ℕ)) := by
  classical
  have hhead := integral_normSq_omegaWeighted_head_closed (z₀ := z₀) (z := z) (L := L) (B₀ := B₀)
    hQ hQ1 hη hG hw₀ hwG hL hρ hs hz hGle hV hU
  have hidx : fibreIndex x h = Finset.Icc 1 B₀ := by
    rw [hB₀]
    rfl
  have hhead' : (∫ w in Set.Icc (-G) G,
      ‖omegaWeightedMoebiusPoly (primesRange z₀ z) (fibreIndex x h) w‖ ^ (2 : ℕ))
      ≤ spectralHead z₀ z L B₀ Q η w₀ G ρ s := by
    rw [hidx, spectralHead]
    exact hhead
  exact omegaBudget_le_of_head hδ hG hhead'

end

end RHTower.Sieve
