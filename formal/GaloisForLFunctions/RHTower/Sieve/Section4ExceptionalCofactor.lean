import GaloisForLFunctions.RHTower.Sieve.Section4BlockFull
import GaloisForLFunctions.RHTower.Sieve.Section4ExceptionalMeasure

/-!
# The innermost cofactor on the exceptional set

The last unspecified quantity of `Sieve/Section4BlockFull.section4_block_full` is `I_k`, the mean
square of the innermost cofactor polynomial over the exceptional set of the short prime block.  It
is supplied by Halász–Montgomery (Lemma 2.6) applied on that set, with the measure of the set
supplied by Lemma 2.5 — the two estimates of exposé §4 that the corpus owns.

The bridge is that the exceptional set in the Gallagher variable is the preimage of the exceptional
set in the Dirichlet variable, so both lemmas apply verbatim after the frequency scaling.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The short exceptional set is a scaled preimage. -/
theorem shortExceptional_eq_preimage {B : Finset ℕ} {NA : ℕ} (hB : B ⊆ Finset.Icc 1 NA)
    (W VP : ℝ) :
    shortExceptional B W VP
      = (fun v : ℝ => 2 * Real.pi * v) ⁻¹'
          (blockExceptional B moebiusCoeff NA (2 * Real.pi * W) VP) := by
  have hbase := exceptional_preimage moebiusCoeff hB W VP
  refine Eq.trans ?_ hbase
  ext w
  simp only [shortExceptional, Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [primeBlockPoly_eq_logPoly]

/-- **The innermost cofactor over the exceptional set, with Lemma 2.5 substituted.** -/
theorem setIntegral_normSq_logPoly_shortExceptional_le (a : ℕ → ℂ) {B D : Finset ℕ} {NA ND k : ℕ}
    (hBprime : ∀ p ∈ B, p.Prime) (hB : B ⊆ Finset.Icc 1 NA) (hND : 1 ≤ ND)
    (hD : D ⊆ Finset.Icc 1 ND) (hk : 1 ≤ k) {W VP Ω : ℝ} (hW : 0 ≤ W) (hVP : 0 < VP)
    (hΩ : 0 ≤ Ω) (ha : ∀ n, ‖a n‖ ≤ Ω) :
    (∫ w in shortExceptional B W VP, ‖logPoly a D w‖ ^ 2)
      ≤ (2 * Real.pi)⁻¹
        * ((2 * (ND : ℝ)
            + (((Nat.log 2 ND : ℝ) + 1) * (214 * Real.sqrt (2 * (2 * Real.pi * W)))
                + 3072 * (ND : ℝ))
              * (2 * (((2 * Real.pi * W)
                    + 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ)))
                  * ((k : ℝ) ^ k * (B.card : ℝ) ^ k)) / VP ^ (2 * k)))
          * (Ω ^ 2 * (D.card : ℝ))) := by
  classical
  have hT0 : (0 : ℝ) ≤ 2 * Real.pi * W := by positivity
  have hmeasS : MeasurableSet (blockExceptional B moebiusCoeff NA (2 * Real.pi * W) VP) :=
    measurableSet_blockExceptional B moebiusCoeff NA (2 * Real.pi * W) VP
  have hsubS : blockExceptional B moebiusCoeff NA (2 * Real.pi * W) VP
      ⊆ Set.Icc (-(2 * Real.pi * W)) (2 * Real.pi * W) :=
    blockExceptional_subset B moebiusCoeff NA (2 * Real.pi * W) VP
  rw [shortExceptional_eq_preimage hB W VP]
  refine (setIntegral_normSq_logPoly_le_HM a hND hD hmeasS hsubS hΩ ha).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hEV := volume_blockExceptional_le (B := B) (NA := NA) (k := k) hBprime hk hT0 hVP
  have hC0 : (0 : ℝ) ≤ ((Nat.log 2 ND : ℝ) + 1) * (214 * Real.sqrt (2 * (2 * Real.pi * W)))
      + 3072 * (ND : ℝ) := by
    have h1 : (0 : ℝ) ≤ (Nat.log 2 ND : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ Real.sqrt (2 * (2 * Real.pi * W)) := Real.sqrt_nonneg _
    have h3 : (0 : ℝ) ≤ (ND : ℝ) := Nat.cast_nonneg _
    nlinarith [h1, h2, h3]
  have := mul_le_mul_of_nonneg_left hEV hC0
  linarith [this]

end

end RHTower.Sieve
