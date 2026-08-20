import GaloisForLFunctions.RHTower.Sieve.MoebiusWindowPartition
import GaloisForLFunctions.RHTower.Sieve.RamareLadderHM
import GaloisForLFunctions.RHTower.Sieve.Section4AllBlocksSmall

/-!
# The two halves of the annulus, each with its own designated prime range

On the part of the annulus where every block of a **low** prime range is small — small by definition
of the frequency set, not by any proved estimate — the mean value theorem finishes the ladder.  On
the complement a **high** prime range takes over: its blocks obey a pointwise zero-free-region bound
everywhere on the annulus, and the cofactor is paid by Halász–Montgomery, whose row mass involves
the measure of the exceptional set rather than the height of the window.  Neither half sees the
other's rough class, because the Ramaré decomposition used is set-parametric.
-/

namespace RHTower.Sieve

open Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- The ladder discrepancy over a frequency set is at most its mean square over the window. -/
theorem setIntegral_normSq_ramareLadderError_le_window (P : Finset ℕ) (M : ℕ) (Q η : ℝ) (L : ℕ)
    {W : ℝ} {E : Set ℝ} (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖ramareLadderError P M Q η L w‖ ^ 2)
      ≤ ∫ w in Set.Icc (-W) W, ‖ramareLadderError P M Q η L w‖ ^ 2 := by
  have hcont : Continuous fun w : ℝ => ‖ramareLadderError P M Q η L w‖ ^ 2 :=
    ((continuous_ramareLadderError P M Q η L).norm).pow 2
  exact MeasureTheory.setIntegral_mono_set hcont.integrableOn_Icc
    (Filter.Eventually.of_forall fun w => by positivity)
    (Filter.Eventually.of_forall hEs)

/-- **The small half of the annulus.**  No arithmetic input: the prime bound holds by membership. -/
theorem setIntegral_annulusSmall_normSq_logPoly_moebius_le {P : Finset ℕ} (M : ℕ)
    {R η W w₀ δ : ℝ} (hR : 1 ≤ R) (hη : 0 ≤ η) (hW : 1 ≤ W) {L : ℕ} (hL : 1 ≤ L) (hδ : 0 < δ)
    (hPprime : ∀ q ∈ P, q.Prime)
    (hP : ∀ p ∈ P, R < (p : ℝ) ∧ (p : ℝ) ≤ R * (1 + η) ^ L)
    (V : ℕ → ℝ) (hV0 : ∀ j, 0 ≤ V j) :
    (∫ w in annulusSmall (allBlocksSmall P R η L V W) w₀,
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2)
      ≤ (1 + δ) * (2 * (L : ℝ) * ∑ j ∈ Finset.range L,
              V j ^ 2 * ((5 * Real.pi / 2 * W
                    + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) / (R * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
                  * ((geomCofactorBlock M R η j).card : ℝ))
            + 2 * ∫ w in Set.Icc (-W) W, ‖ramareLadderError P M R η L w‖ ^ 2)
        + (1 + 1 / δ)
            * (∫ w in Set.Icc (-W) W,
                ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet P M) w‖ ^ 2) := by
  set E : Set ℝ := annulusSmall (allBlocksSmall P R η L V W) w₀ with hE
  have hTm : MeasurableSet (allBlocksSmall P R η L V W) := measurableSet_allBlocksSmall P R η L V W
  have hTs : allBlocksSmall P R η L V W ⊆ Set.Icc (-W) W := allBlocksSmall_subset P R η L V W
  have hEm : MeasurableSet E := measurableSet_annulusSmall hTm w₀
  have hEs : E ⊆ Set.Icc (-W) W := annulusSmall_subset hTs w₀
  have hbound : ∀ j ∈ Finset.range L, ∀ w ∈ E,
      ‖primeBlockPoly (geomBlock P R (1 + η) j) w‖ ≤ V j := by
    intro j hj w hw
    exact norm_primeBlockPoly_le_of_mem_allBlocksSmall hj hw.1
  have hlad := setIntegral_normSq_ramareBilinear_le_ladder_sup (P := P) M hR hη hW hL
    hP hEm hEs V hV0 hbound
  have herr := setIntegral_normSq_ramareLadderError_le_window P M R η L hEs
  have hsplit := setIntegral_normSq_logPoly_moebius_le_ramare_rough (P := P) hPprime M
    (W := W) hδ hEm hEs
  have hrough := setIntegral_normSq_logPoly_moebius_roughSet_le (P := P) M (W := W) hEs
  have hδ0 : (0 : ℝ) ≤ 1 + δ := by linarith
  have hδ1 : (0 : ℝ) ≤ 1 + 1 / δ := by positivity
  have hlad' := hlad.trans (by linarith [herr] :
    2 * (L : ℝ) * ∑ j ∈ Finset.range L,
        V j ^ 2 * ((5 * Real.pi / 2 * W
              + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) / (R * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
            * ((geomCofactorBlock M R η j).card : ℝ))
      + 2 * ∫ w in E, ‖ramareLadderError P M R η L w‖ ^ 2
      ≤ 2 * (L : ℝ) * ∑ j ∈ Finset.range L,
          V j ^ 2 * ((5 * Real.pi / 2 * W
                + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) / (R * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
              * ((geomCofactorBlock M R η j).card : ℝ))
        + 2 * ∫ w in Set.Icc (-W) W, ‖ramareLadderError P M R η L w‖ ^ 2)
  have h1 := mul_le_mul_of_nonneg_left hlad' hδ0
  have h2 := mul_le_mul_of_nonneg_left hrough hδ1
  linarith

/-- **The large half of the annulus.**  The pointwise prime bound is supplied by the caller — a
zero-free-region estimate for the high range — and the cofactor is paid by Halász–Montgomery. -/
theorem setIntegral_annulusLarge_normSq_logPoly_moebius_le {P' : Finset ℕ} (M : ℕ)
    {R' η' W w₀ δ : ℝ} (hR' : 0 < R') (hη' : 0 ≤ η') {L' : ℕ} (hL' : 1 ≤ L')
    (hδ : 0 < δ) (hP'prime : ∀ q ∈ P', q.Prime)
    (hP' : ∀ p ∈ P', R' < (p : ℝ) ∧ (p : ℝ) ≤ R' * (1 + η') ^ L')
    {T : Set ℝ} (hTm : MeasurableSet T)
    (V' : ℕ → ℝ)
    (hNj : ∀ j ∈ Finset.range L', 1 ≤ ⌊(M : ℝ) / (R' * (1 + η') ^ j)⌋₊)
    (hbound : ∀ j ∈ Finset.range L', ∀ w ∈ annulusLarge T W w₀,
      ‖primeBlockPoly (geomBlock P' R' (1 + η') j) w‖ ≤ V' j) :
    (∫ w in annulusLarge T W w₀,
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2)
      ≤ (1 + δ) * (2 * (L' : ℝ) * ∑ j ∈ Finset.range L',
              V' j ^ 2
                * ladderHMBound M R' η' W (volume.real (annulusLarge T W w₀)) j
            + 2 * ∫ w in Set.Icc (-W) W, ‖ramareLadderError P' M R' η' L' w‖ ^ 2)
        + (1 + 1 / δ)
            * (∫ w in Set.Icc (-W) W,
                ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet P' M) w‖ ^ 2) := by
  set E : Set ℝ := annulusLarge T W w₀ with hE
  have hEm : MeasurableSet E := measurableSet_annulusLarge hTm W w₀
  have hEs : E ⊆ Set.Icc (-W) W := annulusLarge_subset T W w₀
  have hlad := setIntegral_normSq_ramareBilinear_le_ladder_HM (P := P') M hR' hη' hL'
    hP' hEm hEs V' hNj hbound
  have herr := setIntegral_normSq_ramareLadderError_le_window P' M R' η' L' hEs
  have hsplit := setIntegral_normSq_logPoly_moebius_le_ramare_rough (P := P') hP'prime M
    (W := W) hδ hEm hEs
  have hrough := setIntegral_normSq_logPoly_moebius_roughSet_le (P := P') M (W := W) hEs
  have hδ0 : (0 : ℝ) ≤ 1 + δ := by linarith
  have hδ1 : (0 : ℝ) ≤ 1 + 1 / δ := by positivity
  have hlad' := hlad.trans (by linarith [herr] :
    2 * (L' : ℝ) * ∑ j ∈ Finset.range L',
        V' j ^ 2 * ladderHMBound M R' η' W (volume.real E) j
      + 2 * ∫ w in E, ‖ramareLadderError P' M R' η' L' w‖ ^ 2
      ≤ 2 * (L' : ℝ) * ∑ j ∈ Finset.range L',
          V' j ^ 2 * ladderHMBound M R' η' W (volume.real E) j
        + 2 * ∫ w in Set.Icc (-W) W, ‖ramareLadderError P' M R' η' L' w‖ ^ 2)
  have h1 := mul_le_mul_of_nonneg_left hlad' hδ0
  have h2 := mul_le_mul_of_nonneg_left hrough hδ1
  linarith

/-- **The Möbius mean square over the whole window, from the two-range partition.**  The disc bound
is a parameter: it is supplied by the Route-T twisted Möbius rate, whose import closure is heavy and
irrelevant to the structure here. -/
theorem integral_Icc_normSq_logPoly_moebius_le_twoRange {P P' : Finset ℕ} (M : ℕ)
    {R η R' η' W w₀ δ Bdisc : ℝ} (hR : 1 ≤ R) (hη : 0 ≤ η) (hR' : 0 < R') (hη' : 0 ≤ η')
    (hW : 1 ≤ W) (hwW : w₀ ≤ W) {L L' : ℕ} (hL : 1 ≤ L) (hL' : 1 ≤ L') (hδ : 0 < δ)
    (hPprime : ∀ q ∈ P, q.Prime) (hP : ∀ p ∈ P, R < (p : ℝ) ∧ (p : ℝ) ≤ R * (1 + η) ^ L)
    (hP'prime : ∀ q ∈ P', q.Prime)
    (hP' : ∀ p ∈ P', R' < (p : ℝ) ∧ (p : ℝ) ≤ R' * (1 + η') ^ L')
    (V V' : ℕ → ℝ) (hV0 : ∀ j, 0 ≤ V j)
    (hNj : ∀ j ∈ Finset.range L', 1 ≤ ⌊(M : ℝ) / (R' * (1 + η') ^ j)⌋₊)
    (hbound' : ∀ j ∈ Finset.range L', ∀ w ∈ annulusLarge (allBlocksSmall P R η L V W) W w₀,
      ‖primeBlockPoly (geomBlock P' R' (1 + η') j) w‖ ≤ V' j)
    (hdisc : (∫ w in Set.Icc (-w₀) w₀,
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2) ≤ Bdisc) :
    (∫ w in Set.Icc (-W) W,
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2)
      ≤ Bdisc
        + ((1 + δ) * (2 * (L : ℝ) * ∑ j ∈ Finset.range L,
                V j ^ 2 * ((5 * Real.pi / 2 * W
                      + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) / (R * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
                    * ((geomCofactorBlock M R η j).card : ℝ))
              + 2 * ∫ w in Set.Icc (-W) W, ‖ramareLadderError P M R η L w‖ ^ 2)
          + (1 + 1 / δ)
              * (∫ w in Set.Icc (-W) W,
                  ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet P M) w‖ ^ 2))
        + ((1 + δ) * (2 * (L' : ℝ) * ∑ j ∈ Finset.range L',
                V' j ^ 2 * ladderHMBound M R' η' W
                    (volume.real (annulusLarge (allBlocksSmall P R η L V W) W w₀)) j
              + 2 * ∫ w in Set.Icc (-W) W, ‖ramareLadderError P' M R' η' L' w‖ ^ 2)
          + (1 + 1 / δ)
              * (∫ w in Set.Icc (-W) W,
                  ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet P' M) w‖ ^ 2)) := by
  refine integral_Icc_normSq_logPoly_moebius_le_partition M hwW
    (measurableSet_allBlocksSmall P R η L V W) (allBlocksSmall_subset P R η L V W) hdisc ?_ ?_
  · exact setIntegral_annulusSmall_normSq_logPoly_moebius_le M hR hη hW hL hδ hPprime hP V hV0
  · exact setIntegral_annulusLarge_normSq_logPoly_moebius_le M hR' hη' hL' hδ hP'prime hP'
      (measurableSet_allBlocksSmall P R η L V W) V' hNj hbound'

/-- The large half of the annulus sits inside the ladder's exceptional set. -/
theorem annulusLarge_subset_someBlockLarge (P : Finset ℕ) (R η : ℝ) (L : ℕ) (V : ℕ → ℝ)
    (W w₀ : ℝ) :
    annulusLarge (allBlocksSmall P R η L V W) W w₀ ⊆ someBlockLarge P R η L V W :=
  fun _ hu => ⟨hu.1.1, hu.1.2⟩

/-- **The measure of the large half, by the moment method.**  Each summand is what
`Sieve/Section4RelativeThreshold.volume_blockExceptional_le_relative` controls. -/
theorem measureReal_annulusLarge_le (P : Finset ℕ) (R η : ℝ) (L : ℕ) (V : ℕ → ℝ) (W w₀ : ℝ) :
    volume.real (annulusLarge (allBlocksSmall P R η L V W) W w₀)
      ≤ ∑ k ∈ Finset.range L,
          volume.real (shortExceptional (geomBlock P R (1 + η) k) W (V k)) := by
  classical
  have hfin : ∀ k ∈ Finset.range L,
      volume (shortExceptional (geomBlock P R (1 + η) k) W (V k)) ≠ ⊤ := by
    intro k _
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (shortExceptional_subset _ W (V k))) ?_)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hsub := annulusLarge_subset_someBlockLarge P R η L V W w₀
  have hmono : volume (annulusLarge (allBlocksSmall P R η L V W) W w₀)
      ≤ ∑ k ∈ Finset.range L, volume (shortExceptional (geomBlock P R (1 + η) k) W (V k)) :=
    le_trans (measure_mono hsub) (volume_someBlockLarge_le P R η L V W)
  have hsumfin : (∑ k ∈ Finset.range L,
      volume (shortExceptional (geomBlock P R (1 + η) k) W (V k))) ≠ ⊤ :=
    (ENNReal.sum_lt_top.2 fun k hk => lt_top_iff_ne_top.2 (hfin k hk)).ne
  have hcast : (∑ k ∈ Finset.range L,
        volume (shortExceptional (geomBlock P R (1 + η) k) W (V k))).toReal
      = ∑ k ∈ Finset.range L,
          volume.real (shortExceptional (geomBlock P R (1 + η) k) W (V k)) := by
    rw [ENNReal.toReal_sum hfin]
    rfl
  rw [MeasureTheory.measureReal_def, ← hcast]
  exact ENNReal.toReal_mono hsumfin hmono

end

end RHTower.Sieve
