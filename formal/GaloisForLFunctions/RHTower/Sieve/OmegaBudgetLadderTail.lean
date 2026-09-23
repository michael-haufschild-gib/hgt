import GaloisForLFunctions.RHTower.Sieve.LadderAffineMajorant
import GaloisForLFunctions.RHTower.Sieve.OmegaBudgetClosed

/-!
# The Gallagher budget with both regimes paid by the ladder

The dyadic tail divides the affine majorant's constant by the square of the cut, so that constant
must come from the ladder.  Only its *slope* may be the trivial one, and only above the height at
which the ladder's analytic input expires — where the trivial constant is absorbed into the slope.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The Gallagher-weighted spectral integral, with both regimes paid by the ladder.** -/
theorem integral_kernel_normSq_omegaWeighted_ladder_le {P : Finset ℕ} {B₀ : ℕ}
    {δ G T₀ αL βL β₀ : ℝ} (hδ : 0 < δ) (hG : 1 ≤ G) (hGT₀ : G ≤ T₀)
    (hαL : 0 ≤ αL) (hβL : 0 ≤ βL)
    (hhead : (∫ w in Set.Icc (-G) G,
        ‖omegaWeightedMoebiusPoly P (Finset.Icc 1 B₀) w‖ ^ (2 : ℕ)) ≤ β₀)
    (hmid : ∀ T : ℝ, G ≤ T → T ≤ T₀ →
      (∫ w in Set.Icc (-T) T, ‖omegaWeightedMoebiusPoly P (Finset.Icc 1 B₀) w‖ ^ (2 : ℕ))
        ≤ αL * T + βL) :
    (∫ w : ℝ, ‖logWindowKernel δ w‖ ^ (2 : ℕ)
        * ‖omegaWeightedMoebiusPoly P (Finset.Icc 1 B₀) w‖ ^ (2 : ℕ))
      ≤ 2 * δ ^ (2 : ℕ) * β₀
        + (4 * (αL + 5 * Real.pi / 2 * (∑ n ∈ Finset.Icc 1 B₀, ‖omegaCoeff P n‖ ^ (2 : ℕ))
              + 5 * Real.exp 1 / 2 * (B₀ : ℝ)
                * (∑ n ∈ Finset.Icc 1 B₀, ‖omegaCoeff P n‖ ^ (2 : ℕ)) / T₀)
            / (Real.pi ^ (2 : ℕ) * G)
          + 4 * βL / (3 * Real.pi ^ (2 : ℕ) * G ^ (2 : ℕ))) := by
  classical
  set S : Finset ℕ := Finset.Icc 1 B₀ with hS
  have hs0 : (0 : ℕ) ∉ S := by
    rw [hS, Finset.mem_Icc]
    omega
  have hsM : ∀ n ∈ S, n ≤ B₀ := by
    intro n hn
    rw [hS, Finset.mem_Icc] at hn
    exact hn.2
  have hconv : ∀ w : ℝ, logPoly (omegaCoeff P) S w = omegaWeightedMoebiusPoly P S w :=
    fun w => logPoly_omegaCoeff_eq P S w
  have hhead' : (∫ w in Set.Icc (-G) G, ‖logPoly (omegaCoeff P) S w‖ ^ (2 : ℕ)) ≤ β₀ := by
    refine le_trans (le_of_eq ?_) hhead
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
    rw [hconv]
  have hmid' : ∀ T : ℝ, G ≤ T → T ≤ T₀ →
      (∫ w in Set.Icc (-T) T, ‖logPoly (omegaCoeff P) S w‖ ^ (2 : ℕ)) ≤ αL * T + βL := by
    intro T h1 h2
    refine le_trans (le_of_eq ?_) (hmid T h1 h2)
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
    rw [hconv]
  have haff := affineMajorant_two_regime (a := omegaCoeff P) hs0 hsM hG hGT₀ hαL hβL hmid'
  have hG0 : (0 : ℝ) < G := lt_of_lt_of_le zero_lt_one hG
  have hgal := gallagher_split_integral_dyadic_head (omegaCoeff P) S hδ hG0 hhead' haff
  rw [integral_normSq_logWindowSum_eq _ _ hδ.le] at hgal
  refine le_trans (le_of_eq ?_) hgal
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [hconv]

/-- **The Route E budget with both Gallagher regimes paid by the ladder.** -/
theorem omegaBudget_le_of_ladder {x h : ℝ} {z₀ z B₀ : ℕ} {G T₀ αL βL β₀ : ℝ}
    (hδ : 0 < fibreWidth x h) (hB₀ : B₀ = ⌊Real.sqrt x + h⌋₊)
    (hG : 1 ≤ G) (hGT₀ : G ≤ T₀) (hαL : 0 ≤ αL) (hβL : 0 ≤ βL)
    (hhead : (∫ w in Set.Icc (-G) G,
        ‖omegaWeightedMoebiusPoly (primesRange z₀ z) (Finset.Icc 1 B₀) w‖ ^ (2 : ℕ)) ≤ β₀)
    (hmid : ∀ T : ℝ, G ≤ T → T ≤ T₀ →
      (∫ w in Set.Icc (-T) T,
        ‖omegaWeightedMoebiusPoly (primesRange z₀ z) (Finset.Icc 1 B₀) w‖ ^ (2 : ℕ)) ≤ αL * T + βL) :
    omegaBudget x h z₀ z
      ≤ 16 * Real.sqrt x
          * (2 * (fibreWidth x h) ^ (2 : ℕ) * β₀
            + (4 * (αL + 5 * Real.pi / 2
                    * (∑ n ∈ Finset.Icc 1 B₀, ‖omegaCoeff (primesRange z₀ z) n‖ ^ (2 : ℕ))
                  + 5 * Real.exp 1 / 2 * (B₀ : ℝ)
                    * (∑ n ∈ Finset.Icc 1 B₀, ‖omegaCoeff (primesRange z₀ z) n‖ ^ (2 : ℕ)) / T₀)
                / (Real.pi ^ (2 : ℕ) * G)
              + 4 * βL / (3 * Real.pi ^ (2 : ℕ) * G ^ (2 : ℕ))))
        + 204 * (((primesRange z₀ z).card : ℝ) + 1) ^ (2 : ℕ) * (Real.sqrt x + 1)
        + 2 * (h + 1) * (2 * h + 1)
            * (4 * (Real.sqrt x / 2 + h + 1) * mertensS z + 4 * ((Nat.primesLE z).card : ℝ)
              + 8 * ((Nat.primesLE z).card : ℝ) ^ (2 : ℕ)) := by
  classical
  have hidx : fibreIndex x h = Finset.Icc 1 B₀ := by
    rw [hB₀]
    rfl
  have hspec := integral_kernel_normSq_omegaWeighted_ladder_le
    (P := primesRange z₀ z) (B₀ := B₀) hδ hG hGT₀ hαL hβL hhead hmid
  rw [omegaBudget, hidx]
  have hsx : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hmul := mul_le_mul_of_nonneg_left hspec (by positivity : (0 : ℝ) ≤ 16 * Real.sqrt x)
  linarith [hmul]

/-- The defect's shape factor is nonnegative. -/
theorem ladderDefectSum_nonneg {L B₀ : ℕ} {Q η : ℝ} (hQ1 : 1 < Q) (hη : 0 ≤ η) :
    0 ≤ ladderDefectSum L B₀ Q η := by
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ1
  have hlogQ : (0 : ℝ) < Real.log Q := Real.log_pos hQ1
  have hlog : (0 : ℝ) ≤ Real.log ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos ⌊(B₀ : ℝ) * (1 + η)⌋₊ with h0 | hpos
    · rw [h0]
      simp
    · refine Real.log_nonneg ?_
      have : (1 : ℕ) ≤ ⌊(B₀ : ℝ) * (1 + η)⌋₊ := hpos
      exact_mod_cast this
  have hsum : (0 : ℝ) ≤ ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j * η + 1)
      * ((1 + (B₀ : ℝ)) * η / (Q * (1 + η) ^ j) + 5 + (B₀ : ℝ) / (Q * (1 + η) ^ j) ^ (2 : ℕ)) := by
    refine Finset.sum_nonneg fun j _ => ?_
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    have h1 : (0 : ℝ) ≤ Q * (1 + η) ^ j * η + 1 := by positivity
    have h2 : (0 : ℝ) ≤ (1 + (B₀ : ℝ)) * η / (Q * (1 + η) ^ j) + 5
        + (B₀ : ℝ) / (Q * (1 + η) ^ j) ^ (2 : ℕ) := by positivity
    exact mul_nonneg h1 h2
  rw [ladderDefectSum]
  exact mul_nonneg (div_nonneg hlog hlogQ.le) hsum

theorem ladderAffineSlope_nonneg {L B₀ : ℕ} {Q η ρ : ℝ} (hQ1 : 1 < Q) (hη : 0 ≤ η) :
    0 ≤ ladderAffineSlope L B₀ Q η ρ := by
  have h1 : (0 : ℝ) ≤ 4 * (5 * Real.pi / 2) * ρ ^ (2 : ℕ)
      * (∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
          * Real.sqrt ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1)) ^ (2 : ℕ) := by positivity
  have h2 : (0 : ℝ) ≤ 2 * (5 * Real.pi / 2) * ladderDefectSum L B₀ Q η :=
    mul_nonneg (by positivity) (ladderDefectSum_nonneg hQ1 hη)
  rw [ladderAffineSlope]
  linarith

theorem ladderAffineConst_nonneg {z₀ z L B₀ : ℕ} {Q η ρ s w₀ : ℝ} (hQ1 : 1 < Q) (hη : 0 ≤ η) :
    0 ≤ ladderAffineConst z₀ z L B₀ Q η ρ s w₀ := by
  have h1 : (0 : ℝ) ≤ 4 * (5 * Real.exp 1 / 2) * ρ ^ (2 : ℕ)
      * (∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
          * Real.sqrt (((B₀ : ℝ) / (Q * (1 + η) ^ j))
              * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1))) ^ (2 : ℕ) := by positivity
  have h2 : (0 : ℝ) ≤ 2 * (∑ j ∈ Finset.range L,
      discMajorant (primesRange z₀ z) B₀ Q η s w₀ j) ^ (2 : ℕ) := by positivity
  have h3 : (0 : ℝ) ≤ 2 * (5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
      * ladderDefectSum L B₀ Q η :=
    mul_nonneg (by positivity) (ladderDefectSum_nonneg hQ1 hη)
  rw [ladderAffineConst]
  linarith

/-- **The Route E budget, fully explicit, with both Gallagher regimes paid by the ladder.** -/
theorem omegaBudget_le_ladder_final {x h : ℝ} {z₀ z L B₀ : ℕ} {Q η w₀ G T₀ ρ s : ℝ}
    (hδ : 0 < fibreWidth x h) (hB₀ : B₀ = ⌊Real.sqrt x + h⌋₊)
    (hQ : Q = (z₀ : ℝ)) (hQ1 : 1 < Q) (hη : 0 < η) (hG : 1 ≤ G) (hGT₀ : G ≤ T₀)
    (hw₀ : 0 ≤ w₀) (hwG : w₀ ≤ G) (hL : 1 ≤ L) (hρ : 0 < ρ) (hs : 0 ≤ s)
    (hz : z = ⌊Q * (1 + η) ^ L⌋₊) (hB : 0 < (B₀ : ℝ))
    (hV : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-T₀) T₀ \ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock (primesRange z₀ z) Q (1 + η) j) w‖ ≤ ρ * (Q * (1 + η) ^ j))
    (hU : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly moebiusCoeff (geomCofactorBlockAt 1 B₀ Q η j) w‖
        ≤ s * ((B₀ : ℝ) / (Q * (1 + η) ^ j))) :
    omegaBudget x h z₀ z
      ≤ 16 * Real.sqrt x
          * (2 * (fibreWidth x h) ^ (2 : ℕ)
              * (ladderAffineSlope L B₀ Q η ρ * G + ladderAffineConst z₀ z L B₀ Q η ρ s w₀)
            + (4 * (ladderAffineSlope L B₀ Q η ρ + 5 * Real.pi / 2
                    * (∑ n ∈ Finset.Icc 1 B₀, ‖omegaCoeff (primesRange z₀ z) n‖ ^ (2 : ℕ))
                  + 5 * Real.exp 1 / 2 * (B₀ : ℝ)
                    * (∑ n ∈ Finset.Icc 1 B₀, ‖omegaCoeff (primesRange z₀ z) n‖ ^ (2 : ℕ)) / T₀)
                / (Real.pi ^ (2 : ℕ) * G)
              + 4 * ladderAffineConst z₀ z L B₀ Q η ρ s w₀ / (3 * Real.pi ^ (2 : ℕ) * G ^ (2 : ℕ))))
        + 204 * (((primesRange z₀ z).card : ℝ) + 1) ^ (2 : ℕ) * (Real.sqrt x + 1)
        + 2 * (h + 1) * (2 * h + 1)
            * (4 * (Real.sqrt x / 2 + h + 1) * mertensS z + 4 * ((Nat.primesLE z).card : ℝ)
              + 8 * ((Nat.primesLE z).card : ℝ) ^ (2 : ℕ)) := by
  classical
  have hmid : ∀ T : ℝ, G ≤ T → T ≤ T₀ →
      (∫ w in Set.Icc (-T) T,
        ‖omegaWeightedMoebiusPoly (primesRange z₀ z) (Finset.Icc 1 B₀) w‖ ^ (2 : ℕ))
        ≤ ladderAffineSlope L B₀ Q η ρ * T + ladderAffineConst z₀ z L B₀ Q η ρ s w₀ := by
    intro T hGT hTT₀
    have hT1 : (1 : ℝ) ≤ T := le_trans hG hGT
    have hwT : w₀ ≤ T := le_trans hwG hGT
    have hVT : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-T) T \ Set.Icc (-w₀) w₀,
        ‖primeBlockPoly (geomBlock (primesRange z₀ z) Q (1 + η) j) w‖
          ≤ ρ * (Q * (1 + η) ^ j) := by
      intro j hj w hw
      refine hV j hj w ?_
      refine ⟨?_, hw.2⟩
      have hwT' : w ∈ Set.Icc (-T) T := hw.1
      rw [Set.mem_Icc] at hwT' ⊢
      exact ⟨by linarith [hwT'.1], by linarith [hwT'.2]⟩
    exact integral_normSq_omegaWeighted_affine_le hQ hQ1 hη hT1 hw₀ hwT hL hρ hs hz hB hVT hU
  have hhead := hmid G le_rfl hGT₀
  exact omegaBudget_le_of_ladder hδ hB₀ hG hGT₀ (ladderAffineSlope_nonneg hQ1 hη.le)
    (ladderAffineConst_nonneg hQ1 hη.le) hhead hmid

end

end RHTower.Sieve
