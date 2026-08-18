import GaloisForLFunctions.RHTower.Sieve.LadderAnnulus
import GaloisForLFunctions.RHTower.Sieve.OmegaWeightedLadderBound

/-!
# The weighted polynomial over a window cut into a disc and an annulus

At zero frequency the prime polynomial of a ladder step is the number of primes of the step, so no
bound uniform on a symmetric window improves on the trivial one, and the harmonic split returns
exactly the trivial mean square.  Cutting the window at a frequency `w₀` repairs this: on the
annulus the prime polynomial carries the saving, on the disc the cofactor polynomial does.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The ladder of products over a cut window.** -/
theorem integral_normSq_ladderProductPoly_annulus_le {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {Q η w₀ G : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) (hG : 1 ≤ G) (hw₀ : 0 ≤ w₀) (hwG : w₀ ≤ G)
    {L : ℕ} (v V U Vlow : ℕ → ℝ)
    (hv : ∀ j ∈ Finset.range L, 0 < v j) (hV : ∀ j, 0 ≤ V j) (hU : ∀ j, 0 ≤ U j)
    (hVlow : ∀ j, 0 ≤ Vlow j)
    (hann : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-G) G \ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V j)
    (hlowP : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ Vlow j)
    (hlowC : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ≤ U j) :
    (∫ w in Set.Icc (-G) G, ‖ladderProductPoly P A₀ B₀ Q η L w‖ ^ 2)
      ≤ (∑ j ∈ Finset.range L, 1 / v j)
        * ∑ j ∈ Finset.range L, v j
            * (V j ^ 2 * ((5 * Real.pi / 2 * G
                  + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
                * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1))
              + Vlow j ^ 2 * U j ^ 2 * (2 * w₀)) := by
  classical
  have hcontZ : Continuous fun w : ℝ => ‖ladderProductPoly P A₀ B₀ Q η L w‖ ^ 2 := by
    refine ((continuous_finsetSum _ fun j _ => ?_).norm).pow 2
    exact (continuous_primeBlockPoly _).mul (continuous_logPoly _ _)
  have hsplit := setIntegral_Icc_split (f := fun w : ℝ =>
    ‖ladderProductPoly P A₀ B₀ Q η L w‖ ^ 2) hcontZ hwG
  have hsubLow : Set.Icc (-w₀) w₀ ⊆ Set.Icc (-G) G := Set.Icc_subset_Icc (by linarith) hwG
  have hsubAnn : Set.Icc (-G) G \ Set.Icc (-w₀) w₀ ⊆ Set.Icc (-G) G := Set.sdiff_subset
  have houter : (0 : ℝ) ≤ ∑ j ∈ Finset.range L, 1 / v j :=
    Finset.sum_nonneg fun j hj => le_of_lt (div_pos one_pos (hv j hj))
  -- the annulus
  have hAnn := integral_normSq_ladderProductPoly_set_le (P := P) A₀ B₀ Q η v hv
    (E := Set.Icc (-G) G \ Set.Icc (-w₀) w₀) (measurableSet_Icc.diff measurableSet_Icc)
    (G := G) hsubAnn
  have hAnnStep : ∀ j ∈ Finset.range L,
      v j * ∫ w in Set.Icc (-G) G \ Set.Icc (-w₀) w₀,
          ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2
            * ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ^ 2
        ≤ v j * (V j ^ 2 * ((5 * Real.pi / 2 * G
              + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
            * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1))) := by
    intro j hj
    refine mul_le_mul_of_nonneg_left ?_ (hv j hj).le
    refine (integral_normSq_ladderStep_set_le hA hQ hη hG (hV j) j
      (measurableSet_Icc.diff measurableSet_Icc) hsubAnn (hann j hj)).trans ?_
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (card_geomCofactorBlockAt_le hQ hη j) ?_) (by positivity)
    have hG0 : (0 : ℝ) < G := lt_of_lt_of_le zero_lt_one hG
    have h1 : (0 : ℝ) ≤ 5 * Real.pi / 2 * G := mul_nonneg (by positivity) hG0.le
    have h2 : (0 : ℝ) ≤ 5 * Real.exp 1 / 2
        * ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ) :=
      mul_nonneg (by positivity) (Nat.cast_nonneg _)
    linarith
  -- the disc
  have hLow := integral_normSq_ladderProductPoly_set_le (P := P) A₀ B₀ Q η v hv
    (E := Set.Icc (-w₀) w₀) measurableSet_Icc (G := G) hsubLow
  have hLowStep : ∀ j ∈ Finset.range L,
      v j * ∫ w in Set.Icc (-w₀) w₀,
          ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2
            * ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ^ 2
        ≤ v j * (Vlow j ^ 2 * U j ^ 2 * (2 * w₀)) := by
    intro j hj
    exact mul_le_mul_of_nonneg_left
      (integral_normSq_ladderStep_low_le hw₀ (hVlow j) (hU j) j (hlowP j hj) (hlowC j hj))
      (hv j hj).le
  have hAnnSum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hAnnStep) houter
  have hLowSum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hLowStep) houter
  have hcomb : (∑ j ∈ Finset.range L, 1 / v j)
        * ∑ j ∈ Finset.range L, v j * (V j ^ 2 * ((5 * Real.pi / 2 * G
              + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
            * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1)))
      + (∑ j ∈ Finset.range L, 1 / v j)
        * ∑ j ∈ Finset.range L, v j * (Vlow j ^ 2 * U j ^ 2 * (2 * w₀))
      = (∑ j ∈ Finset.range L, 1 / v j)
        * ∑ j ∈ Finset.range L, v j
            * (V j ^ 2 * ((5 * Real.pi / 2 * G
                  + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
                * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1))
              + Vlow j ^ 2 * U j ^ 2 * (2 * w₀)) := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit]
  linarith [hAnn, hLow, hAnnSum, hLowSum, hcomb]

/-- **The weighted polynomial over a cut window, fully assembled.**  The analytic inputs are a bound
`V j` on the prime polynomial away from zero frequency and a bound `U j` on the cofactor polynomial
near it. -/
theorem integral_normSq_omegaWeighted_annulus_le {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {Q η w₀ G : ℝ} (hQ : 1 < Q) (hη : 0 ≤ η) (hG : 1 ≤ G) (hw₀ : 0 ≤ w₀) (hwG : w₀ ≤ G)
    {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ q ∈ P, q.Prime) (hPge : ∀ p ∈ P, Q ≤ (p : ℝ))
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    (v V U Vlow : ℕ → ℝ)
    (hv : ∀ j ∈ Finset.range L, 0 < v j) (hV : ∀ j, 0 ≤ V j) (hU : ∀ j, 0 ≤ U j)
    (hVlow : ∀ j, 0 ≤ Vlow j)
    (hann : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-G) G \ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V j)
    (hlowP : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ Vlow j)
    (hlowC : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ≤ U j) :
    (∫ w in Set.Icc (-G) G, ‖omegaWeightedMoebiusPoly P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ 2 * ((∑ j ∈ Finset.range L, 1 / v j)
            * ∑ j ∈ Finset.range L, v j
                * (V j ^ 2 * ((5 * Real.pi / 2 * G
                      + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
                    * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1))
                  + Vlow j ^ 2 * U j ^ 2 * (2 * w₀)))
        + 2 * ((5 * Real.pi / 2 * G
              + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
            * (Real.log ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) / Real.log Q
              * ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j * η + 1)
                  * (((A₀ : ℝ) + (B₀ : ℝ)) * η / (Q * (1 + η) ^ j) + 5
                    + (B₀ : ℝ) / (Q * (1 + η) ^ j) ^ 2))) := by
  classical
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ
  have hsplit := integral_normSq_omegaWeighted_le_split A₀ B₀ hQ0 hη hL hPprime hP G
  have hdefect := integral_normSq_ladderProductDefect_le_closed (P := P) (A₀ := A₀) (B₀ := B₀)
    (L := L) hA hQ hη hG hPprime hPge
  have hprod := integral_normSq_ladderProductPoly_annulus_le hA hQ0 hη hG hw₀ hwG v V U Vlow hv
    hV hU hVlow hann hlowP hlowC
  linarith [hsplit, hprod, hdefect]

/-- The mean value factor of one ladder step. -/
def ladderStepMVT (B₀ : ℕ) (Q η G : ℝ) (j : ℕ) : ℝ :=
  (5 * Real.pi / 2 * G + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
    * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1)

/-- The general cut-window bound, with the mean value factor named. -/
theorem integral_normSq_omegaWeighted_annulus_aux {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {Q η w₀ G : ℝ} (hQ : 1 < Q) (hη : 0 ≤ η) (hG : 1 ≤ G) (hw₀ : 0 ≤ w₀) (hwG : w₀ ≤ G)
    {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ q ∈ P, q.Prime) (hPge : ∀ p ∈ P, Q ≤ (p : ℝ))
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    (v V U Vlow : ℕ → ℝ)
    (hv : ∀ j ∈ Finset.range L, 0 < v j) (hV : ∀ j, 0 ≤ V j) (hU : ∀ j, 0 ≤ U j)
    (hVlow : ∀ j, 0 ≤ Vlow j)
    (hann : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-G) G \ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V j)
    (hlowP : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ Vlow j)
    (hlowC : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ≤ U j) :
    (∫ w in Set.Icc (-G) G, ‖omegaWeightedMoebiusPoly P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ 2 * ((∑ j ∈ Finset.range L, 1 / v j)
            * ∑ j ∈ Finset.range L, v j
                * (V j ^ 2 * ladderStepMVT B₀ Q η G j + Vlow j ^ 2 * U j ^ 2 * (2 * w₀)))
        + 2 * ((5 * Real.pi / 2 * G
              + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
            * (Real.log ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) / Real.log Q
              * ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j * η + 1)
                  * (((A₀ : ℝ) + (B₀ : ℝ)) * η / (Q * (1 + η) ^ j) + 5
                    + (B₀ : ℝ) / (Q * (1 + η) ^ j) ^ 2))) :=
  integral_normSq_omegaWeighted_annulus_le hA hQ hη hG hw₀ hwG hL hPprime hPge hP v V U Vlow
    hv hV hU hVlow hann hlowP hlowC

/-- **The weighted polynomial over a cut window, at the optimal Cauchy--Schwarz weight.**  Taking
`v_j` to be the reciprocal of a `c_j` dominating `V_j √T_j` turns the harmonic split into the square
of a single sum, so no lower bound on the harmonic mass of a ladder step is needed. -/
theorem integral_normSq_omegaWeighted_annulus_optimal_le {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {Q η w₀ G : ℝ} (hQ : 1 < Q) (hη : 0 ≤ η) (hG : 1 ≤ G) (hw₀ : 0 ≤ w₀) (hwG : w₀ ≤ G)
    {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ q ∈ P, q.Prime) (hPge : ∀ p ∈ P, Q ≤ (p : ℝ))
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    (c V U Vlow : ℕ → ℝ)
    (hc : ∀ j ∈ Finset.range L, 0 < c j) (hV : ∀ j, 0 ≤ V j) (hU : ∀ j, 0 ≤ U j)
    (hVlow : ∀ j, 0 ≤ Vlow j)
    (hcT : ∀ j ∈ Finset.range L, V j ^ 2 * ladderStepMVT B₀ Q η G j ≤ c j ^ 2)
    (hann : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-G) G \ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V j)
    (hlowP : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ Vlow j)
    (hlowC : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ≤ U j) :
    (∫ w in Set.Icc (-G) G, ‖omegaWeightedMoebiusPoly P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ 2 * ((∑ j ∈ Finset.range L, c j)
            * ((∑ j ∈ Finset.range L, c j)
              + ∑ j ∈ Finset.range L, Vlow j ^ 2 * U j ^ 2 * (2 * w₀) / c j))
        + 2 * ((5 * Real.pi / 2 * G
              + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
            * (Real.log ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) / Real.log Q
              * ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j * η + 1)
                  * (((A₀ : ℝ) + (B₀ : ℝ)) * η / (Q * (1 + η) ^ j) + 5
                    + (B₀ : ℝ) / (Q * (1 + η) ^ j) ^ 2))) := by
  classical
  have hv : ∀ j ∈ Finset.range L, 0 < 1 / c j := fun j hj => div_pos one_pos (hc j hj)
  have hbase := integral_normSq_omegaWeighted_annulus_aux hA hQ hη hG hw₀ hwG hL
    hPprime hPge hP (fun j => 1 / c j) V U Vlow hv hV hU hVlow hann hlowP hlowC
  have houter : (∑ j ∈ Finset.range L, 1 / (1 / c j)) = ∑ j ∈ Finset.range L, c j :=
    Finset.sum_congr rfl fun j _ => one_div_one_div _
  rw [houter] at hbase
  refine hbase.trans ?_
  have hinner : (∑ j ∈ Finset.range L, (1 / c j)
        * (V j ^ 2 * ladderStepMVT B₀ Q η G j + Vlow j ^ 2 * U j ^ 2 * (2 * w₀)))
      ≤ (∑ j ∈ Finset.range L, c j)
        + ∑ j ∈ Finset.range L, Vlow j ^ 2 * U j ^ 2 * (2 * w₀) / c j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j hj => ?_
    have hcj := hc j hj
    have h1 : (1 / c j) * (V j ^ 2 * ladderStepMVT B₀ Q η G j) ≤ c j := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hcj]
      nlinarith [hcT j hj]
    have h2 : (1 / c j) * (Vlow j ^ 2 * U j ^ 2 * (2 * w₀))
        = Vlow j ^ 2 * U j ^ 2 * (2 * w₀) / c j := by
      rw [div_mul_eq_mul_div, one_mul]
    rw [mul_add, h2]
    linarith [h1]
  have hsum0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range L, c j :=
    Finset.sum_nonneg fun j hj => (hc j hj).le
  have hmul := mul_le_mul_of_nonneg_left hinner hsum0
  linarith [hmul]

/-- **The ladder of products over a cut window, with independent weights on disc and annulus.**
The two ranges have different optimal weights: the annulus is governed by the prime bound, the disc
by the cofactor bound. -/
theorem integral_normSq_ladderProductPoly_annulus_two_le {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {Q η w₀ G : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) (hG : 1 ≤ G) (hw₀ : 0 ≤ w₀) (hwG : w₀ ≤ G)
    {L : ℕ} (vA vD V U Vlow : ℕ → ℝ)
    (hvA : ∀ j ∈ Finset.range L, 0 < vA j) (hvD : ∀ j ∈ Finset.range L, 0 < vD j)
    (hV : ∀ j, 0 ≤ V j) (hU : ∀ j, 0 ≤ U j) (hVlow : ∀ j, 0 ≤ Vlow j)
    (hann : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-G) G \ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V j)
    (hlowP : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ Vlow j)
    (hlowC : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ≤ U j) :
    (∫ w in Set.Icc (-G) G, ‖ladderProductPoly P A₀ B₀ Q η L w‖ ^ 2)
      ≤ (∑ j ∈ Finset.range L, 1 / vA j)
            * (∑ j ∈ Finset.range L, vA j * (V j ^ 2 * ladderStepMVT B₀ Q η G j))
        + (∑ j ∈ Finset.range L, 1 / vD j)
            * ∑ j ∈ Finset.range L, vD j * (Vlow j ^ 2 * U j ^ 2 * (2 * w₀)) := by
  classical
  have hcontZ : Continuous fun w : ℝ => ‖ladderProductPoly P A₀ B₀ Q η L w‖ ^ 2 := by
    refine ((continuous_finsetSum _ fun j _ => ?_).norm).pow 2
    exact (continuous_primeBlockPoly _).mul (continuous_logPoly _ _)
  have hsplit := setIntegral_Icc_split (f := fun w : ℝ =>
    ‖ladderProductPoly P A₀ B₀ Q η L w‖ ^ 2) hcontZ hwG
  have hsubLow : Set.Icc (-w₀) w₀ ⊆ Set.Icc (-G) G := Set.Icc_subset_Icc (by linarith) hwG
  have hsubAnn : Set.Icc (-G) G \ Set.Icc (-w₀) w₀ ⊆ Set.Icc (-G) G := Set.sdiff_subset
  have houterA : (0 : ℝ) ≤ ∑ j ∈ Finset.range L, 1 / vA j :=
    Finset.sum_nonneg fun j hj => le_of_lt (div_pos one_pos (hvA j hj))
  have houterD : (0 : ℝ) ≤ ∑ j ∈ Finset.range L, 1 / vD j :=
    Finset.sum_nonneg fun j hj => le_of_lt (div_pos one_pos (hvD j hj))
  have hAnn := integral_normSq_ladderProductPoly_set_le (P := P) A₀ B₀ Q η vA hvA
    (E := Set.Icc (-G) G \ Set.Icc (-w₀) w₀) (measurableSet_Icc.diff measurableSet_Icc)
    (G := G) hsubAnn
  have hAnnStep : ∀ j ∈ Finset.range L,
      vA j * ∫ w in Set.Icc (-G) G \ Set.Icc (-w₀) w₀,
          ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2
            * ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ^ 2
        ≤ vA j * (V j ^ 2 * ladderStepMVT B₀ Q η G j) := by
    intro j hj
    refine mul_le_mul_of_nonneg_left ?_ (hvA j hj).le
    refine (integral_normSq_ladderStep_set_le hA hQ hη hG (hV j) j
      (measurableSet_Icc.diff measurableSet_Icc) hsubAnn (hann j hj)).trans ?_
    rw [ladderStepMVT]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (card_geomCofactorBlockAt_le hQ hη j) ?_) (by positivity)
    have hG0 : (0 : ℝ) < G := lt_of_lt_of_le zero_lt_one hG
    have h1 : (0 : ℝ) ≤ 5 * Real.pi / 2 * G := mul_nonneg (by positivity) hG0.le
    have h2 : (0 : ℝ) ≤ 5 * Real.exp 1 / 2
        * ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ) :=
      mul_nonneg (by positivity) (Nat.cast_nonneg _)
    linarith
  have hLow := integral_normSq_ladderProductPoly_set_le (P := P) A₀ B₀ Q η vD hvD
    (E := Set.Icc (-w₀) w₀) measurableSet_Icc (G := G) hsubLow
  have hLowStep : ∀ j ∈ Finset.range L,
      vD j * ∫ w in Set.Icc (-w₀) w₀,
          ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2
            * ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ^ 2
        ≤ vD j * (Vlow j ^ 2 * U j ^ 2 * (2 * w₀)) := by
    intro j hj
    exact mul_le_mul_of_nonneg_left
      (integral_normSq_ladderStep_low_le hw₀ (hVlow j) (hU j) j (hlowP j hj) (hlowC j hj))
      (hvD j hj).le
  have hAnnSum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hAnnStep) houterA
  have hLowSum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hLowStep) houterD
  rw [hsplit]
  linarith [hAnn, hLow, hAnnSum, hLowSum]

/-- **The weighted polynomial over a cut window, at the optimal weight on each range.** -/
theorem integral_normSq_omegaWeighted_annulus_optimal_two_le {P : Finset ℕ} {A₀ B₀ : ℕ}
    (hA : 0 < A₀) {Q η w₀ G : ℝ} (hQ : 1 < Q) (hη : 0 ≤ η) (hG : 1 ≤ G) (hw₀ : 0 ≤ w₀)
    (hwG : w₀ ≤ G) {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ q ∈ P, q.Prime) (hPge : ∀ p ∈ P, Q ≤ (p : ℝ))
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    (c d V U Vlow : ℕ → ℝ)
    (hc : ∀ j ∈ Finset.range L, 0 < c j) (hd : ∀ j ∈ Finset.range L, 0 < d j)
    (hV : ∀ j, 0 ≤ V j) (hU : ∀ j, 0 ≤ U j) (hVlow : ∀ j, 0 ≤ Vlow j)
    (hcT : ∀ j ∈ Finset.range L, V j ^ 2 * ladderStepMVT B₀ Q η G j ≤ c j ^ 2)
    (hdT : ∀ j ∈ Finset.range L, Vlow j ^ 2 * U j ^ 2 * (2 * w₀) ≤ d j ^ 2)
    (hann : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-G) G \ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V j)
    (hlowP : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ Vlow j)
    (hlowC : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ≤ U j) :
    (∫ w in Set.Icc (-G) G, ‖omegaWeightedMoebiusPoly P (Finset.Icc A₀ B₀) w‖ ^ 2)
      ≤ 2 * ((∑ j ∈ Finset.range L, c j) ^ 2 + (∑ j ∈ Finset.range L, d j) ^ 2)
        + 2 * ((5 * Real.pi / 2 * G
              + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
            * (Real.log ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) / Real.log Q
              * ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j * η + 1)
                  * (((A₀ : ℝ) + (B₀ : ℝ)) * η / (Q * (1 + η) ^ j) + 5
                    + (B₀ : ℝ) / (Q * (1 + η) ^ j) ^ 2))) := by
  classical
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ
  have hvA : ∀ j ∈ Finset.range L, (0 : ℝ) < 1 / c j := fun j hj => div_pos one_pos (hc j hj)
  have hvD : ∀ j ∈ Finset.range L, (0 : ℝ) < 1 / d j := fun j hj => div_pos one_pos (hd j hj)
  have hprod := integral_normSq_ladderProductPoly_annulus_two_le hA hQ0 hη hG hw₀ hwG
    (fun j => 1 / c j) (fun j => 1 / d j) V U Vlow hvA hvD hV hU hVlow hann hlowP hlowC
  have hsplit := integral_normSq_omegaWeighted_le_split A₀ B₀ hQ0 hη hL hPprime hP G
  have hdefect := integral_normSq_ladderProductDefect_le_closed (P := P) (A₀ := A₀) (B₀ := B₀)
    (L := L) hA hQ hη hG hPprime hPge
  have hA1 : (∑ j ∈ Finset.range L, 1 / (1 / c j)) = ∑ j ∈ Finset.range L, c j :=
    Finset.sum_congr rfl fun j _ => one_div_one_div _
  have hD1 : (∑ j ∈ Finset.range L, 1 / (1 / d j)) = ∑ j ∈ Finset.range L, d j :=
    Finset.sum_congr rfl fun j _ => one_div_one_div _
  have hA2 : (∑ j ∈ Finset.range L, (1 / c j) * (V j ^ 2 * ladderStepMVT B₀ Q η G j))
      ≤ ∑ j ∈ Finset.range L, c j := by
    refine Finset.sum_le_sum fun j hj => ?_
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (hc j hj)]
    nlinarith [hcT j hj]
  have hD2 : (∑ j ∈ Finset.range L, (1 / d j) * (Vlow j ^ 2 * U j ^ 2 * (2 * w₀)))
      ≤ ∑ j ∈ Finset.range L, d j := by
    refine Finset.sum_le_sum fun j hj => ?_
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (hd j hj)]
    nlinarith [hdT j hj]
  have hcs0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range L, c j :=
    Finset.sum_nonneg fun j hj => (hc j hj).le
  have hds0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range L, d j :=
    Finset.sum_nonneg fun j hj => (hd j hj).le
  rw [hA1, hD1] at hprod
  have hbound : (∫ w in Set.Icc (-G) G, ‖ladderProductPoly P A₀ B₀ Q η L w‖ ^ 2)
      ≤ (∑ j ∈ Finset.range L, c j) ^ 2 + (∑ j ∈ Finset.range L, d j) ^ 2 := by
    have e1 := mul_le_mul_of_nonneg_left hA2 hcs0
    have e2 := mul_le_mul_of_nonneg_left hD2 hds0
    nlinarith [hprod, e1, e2]
  linarith [hsplit, hbound, hdefect]

end

end RHTower.Sieve
