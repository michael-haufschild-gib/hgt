import GaloisForLFunctions.RHTower.Sieve.LadderBlockMeanSquare

/-!
# The weighted polynomial over the ladder, assembled

The `ω_P`-weighted Möbius polynomial equals the ladder of genuine products minus the defect of
replacing each prime's cofactor range by the common range of its step.  Bounding the two separately
gives a mean-square estimate whose only analytic input is a pointwise bound on each prime
polynomial — that is, cancellation in `∑_{p ∈ P_j} p^{2πiw}`.

Every other quantity is explicit in the parameters `A₀`, `B₀`, `Q`, `η`, `L` and the window `W`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

theorem continuous_omegaWeightedMoebiusPoly (P S : Finset ℕ) :
    Continuous fun w : ℝ => omegaWeightedMoebiusPoly P S w := by
  refine continuous_finsetSum S fun n _ => continuous_const.mul ?_
  exact continuous_moebiusPhase n

theorem continuous_ladderProductPoly (P : Finset ℕ) (A₀ B₀ : ℕ) (Q η : ℝ) (L : ℕ) :
    Continuous fun w : ℝ => ladderProductPoly P A₀ B₀ Q η L w := by
  refine continuous_finsetSum _ fun j _ => ?_
  exact (continuous_primeBlockPoly _).mul (continuous_logPoly _ _)

theorem continuous_ladderProductDefect (P : Finset ℕ) (A₀ B₀ : ℕ) (Q η : ℝ) (L : ℕ) :
    Continuous fun w : ℝ => ladderProductDefect P A₀ B₀ Q η L w := by
  refine continuous_finsetSum _ fun x _ => ?_
  exact (continuous_moebiusPhase _).mul (continuous_logPoly _ _)

/-- **The weighted polynomial, split into the ladder of products and the defect.** -/
theorem integral_normSq_omegaWeighted_le_split {P : Finset ℕ} (A₀ B₀ : ℕ) {Q η : ℝ}
    (hQ : 0 < Q) (hη : 0 ≤ η) {L : ℕ} (hL : 1 ≤ L) (hPprime : ∀ q ∈ P, q.Prime)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L) (W : ℝ) :
    (∫ w in Set.Icc (-W) W, ‖omegaWeightedMoebiusPoly P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ 2 * (∫ w in Set.Icc (-W) W, ‖ladderProductPoly P A₀ B₀ Q η L w‖ ^ 2)
        + 2 * ∫ w in Set.Icc (-W) W, ‖ladderProductDefect P A₀ B₀ Q η L w‖ ^ 2 := by
  classical
  have hcontA : Continuous fun w : ℝ => ‖omegaWeightedMoebiusPoly P (Finset.Icc A₀ B₀) w‖ ^ 2 :=
    ((continuous_omegaWeightedMoebiusPoly _ _).norm).pow 2
  have hcontProd : Continuous fun w : ℝ => ‖ladderProductPoly P A₀ B₀ Q η L w‖ ^ 2 :=
    ((continuous_ladderProductPoly _ _ _ _ _ _).norm).pow 2
  have hcontE : Continuous fun w : ℝ => ‖ladderProductDefect P A₀ B₀ Q η L w‖ ^ 2 :=
    ((continuous_ladderProductDefect _ _ _ _ _ _).norm).pow 2
  have hpt : ∀ w : ℝ, ‖omegaWeightedMoebiusPoly P (Finset.Icc A₀ B₀) w‖ ^ 2
      ≤ 2 * ‖ladderProductPoly P A₀ B₀ Q η L w‖ ^ 2
        + 2 * ‖ladderProductDefect P A₀ B₀ Q η L w‖ ^ 2 := by
    intro w
    have heq := ladderProductPoly_sub_omegaWeighted_eq A₀ B₀ hQ hη hL hPprime hP w
    have hA : omegaWeightedMoebiusPoly P (Finset.Icc A₀ B₀) w
        = ladderProductPoly P A₀ B₀ Q η L w - ladderProductDefect P A₀ B₀ Q η L w := by
      linear_combination -heq
    rw [hA]
    have htri := norm_sub_le (ladderProductPoly P A₀ B₀ Q η L w)
      (ladderProductDefect P A₀ B₀ Q η L w)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [hsq, sq_nonneg (‖ladderProductPoly P A₀ B₀ Q η L w‖
      - ‖ladderProductDefect P A₀ B₀ Q η L w‖)]
  have hint1 : IntegrableOn (fun w : ℝ => ‖omegaWeightedMoebiusPoly P (Finset.Icc A₀ B₀) w‖ ^ 2)
      (Set.Icc (-W) W) volume := hcontA.integrableOn_Icc
  have hint2 : IntegrableOn (fun w : ℝ =>
      2 * ‖ladderProductPoly P A₀ B₀ Q η L w‖ ^ 2
        + 2 * ‖ladderProductDefect P A₀ B₀ Q η L w‖ ^ 2)
      (Set.Icc (-W) W) volume := ((hcontProd.const_mul 2).add (hcontE.const_mul 2)).integrableOn_Icc
  have hmono := setIntegral_mono_on hint1 hint2 measurableSet_Icc (fun w _ => hpt w)
  refine hmono.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_add (hcontProd.const_mul 2).integrableOn_Icc
    (hcontE.const_mul 2).integrableOn_Icc, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]

/-- **The weighted polynomial over the ladder, fully assembled.**  The only analytic input is the
pointwise bound `V j` on each prime polynomial. -/
theorem integral_normSq_omegaWeighted_le {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {Q η W : ℝ} (hQ : 1 < Q) (hη : 0 ≤ η) (hW : 1 ≤ W) {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ q ∈ P, q.Prime) (hPge : ∀ p ∈ P, Q ≤ (p : ℝ))
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    (v V : ℕ → ℝ) (hv : ∀ j ∈ Finset.range L, 0 < v j) (hV : ∀ j, 0 ≤ V j)
    (hbound : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-W) W,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V j) :
    (∫ w in Set.Icc (-W) W, ‖omegaWeightedMoebiusPoly P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ 2 * ((∑ j ∈ Finset.range L, 1 / v j)
            * ∑ j ∈ Finset.range L, v j * (V j ^ 2
                * ((5 * Real.pi / 2 * W
                    + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
                  * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1))))
        + 2 * ((5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
            * (Real.log ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) / Real.log Q
              * ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j * η + 1)
                  * (((A₀ : ℝ) + (B₀ : ℝ)) * η / (Q * (1 + η) ^ j) + 5
                    + (B₀ : ℝ) / (Q * (1 + η) ^ j) ^ 2))) := by
  classical
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ
  have hsplit := integral_normSq_omegaWeighted_le_split A₀ B₀ hQ0 hη hL hPprime hP W
  have hdefect := integral_normSq_ladderProductDefect_le_closed (P := P) (A₀ := A₀) (B₀ := B₀)
    (L := L) hA hQ hη hW hPprime hPge
  have hharm := integral_normSq_ladderProductPoly_le (P := P) A₀ B₀ Q η v hv W
  have hsteps : ∀ j ∈ Finset.range L,
      v j * (∫ w in Set.Icc (-W) W,
          ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2
            * ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ^ 2)
        ≤ v j * (V j ^ 2
            * ((5 * Real.pi / 2 * W
                + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
              * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1))) := by
    intro j hj
    refine mul_le_mul_of_nonneg_left ?_ (hv j hj).le
    refine (integral_normSq_ladderStep_le hA hQ0 hη hW (hV j) j (hbound j hj)).trans ?_
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ ?_) (by positivity)
    · exact card_geomCofactorBlockAt_le hQ0 hη j
    · have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
      have h1 : (0 : ℝ) ≤ 5 * Real.pi / 2 * W := mul_nonneg (by positivity) hW0.le
      have h2 : (0 : ℝ) ≤ 5 * Real.exp 1 / 2
          * ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ) :=
        mul_nonneg (by positivity) (Nat.cast_nonneg _)
      linarith
  have hsum := Finset.sum_le_sum hsteps
  have houter : (0 : ℝ) ≤ ∑ j ∈ Finset.range L, 1 / v j := by
    refine Finset.sum_nonneg fun j hj => ?_
    exact le_of_lt (div_pos one_pos (hv j hj))
  have hprod := mul_le_mul_of_nonneg_left hsum houter
  linarith [hsplit, hharm.trans hprod, hdefect]

end

end RHTower.Sieve
