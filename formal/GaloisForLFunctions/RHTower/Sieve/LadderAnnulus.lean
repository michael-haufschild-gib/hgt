import GaloisForLFunctions.RHTower.Sieve.LadderBlockMeanSquare

/-!
# The ladder on a frequency annulus

Cancellation in a twisted prime sum degrades as the frequency approaches zero — at zero frequency
the prime polynomial *is* the number of primes of the block, so no bound uniform on a symmetric
window can beat the trivial one.  The window must therefore be cut into a low-frequency disc, where
the *cofactor* polynomial carries the saving, and an annulus, where the prime polynomial does.

Everything below is the set-indexed form of the ladder estimates.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **Splitting a symmetric window into a disc and an annulus.** -/
theorem setIntegral_Icc_split {f : ℝ → ℝ} (hf : Continuous f) {w₀ G : ℝ} (hwG : w₀ ≤ G) :
    (∫ w in Set.Icc (-G) G, f w)
      = (∫ w in Set.Icc (-w₀) w₀, f w)
        + ∫ w in Set.Icc (-G) G \ Set.Icc (-w₀) w₀, f w := by
  have hsub : Set.Icc (-w₀) w₀ ⊆ Set.Icc (-G) G := Set.Icc_subset_Icc (by linarith) hwG
  have hunion : Set.Icc (-w₀) w₀ ∪ (Set.Icc (-G) G \ Set.Icc (-w₀) w₀) = Set.Icc (-G) G :=
    Set.union_sdiff_cancel hsub
  calc (∫ w in Set.Icc (-G) G, f w)
      = ∫ w in Set.Icc (-w₀) w₀ ∪ (Set.Icc (-G) G \ Set.Icc (-w₀) w₀), f w := by rw [hunion]
    _ = (∫ w in Set.Icc (-w₀) w₀, f w)
          + ∫ w in Set.Icc (-G) G \ Set.Icc (-w₀) w₀, f w :=
        MeasureTheory.setIntegral_union Set.disjoint_sdiff_right
          (measurableSet_Icc.diff measurableSet_Icc)
          (hf.integrableOn_Icc (a := -w₀) (b := w₀) (μ := (volume : Measure ℝ)))
          ((hf.integrableOn_Icc (a := -G) (b := G) (μ := (volume : Measure ℝ))).mono_set
            Set.sdiff_subset)

/-- **The harmonic split of the ladder of products, over an arbitrary frequency set.** -/
theorem integral_normSq_ladderProductPoly_set_le {P : Finset ℕ} (A₀ B₀ : ℕ) (Q η : ℝ) {L : ℕ}
    (v : ℕ → ℝ) (hv : ∀ j ∈ Finset.range L, 0 < v j) {E : Set ℝ} (hEm : MeasurableSet E)
    {G : ℝ} (hEG : E ⊆ Set.Icc (-G) G) :
    (∫ w in E, ‖ladderProductPoly P A₀ B₀ Q η L w‖ ^ 2)
      ≤ (∑ j ∈ Finset.range L, 1 / v j)
        * ∑ j ∈ Finset.range L, v j
            * ∫ w in E,
                ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2
                  * ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ^ 2 := by
  classical
  set F : ℕ → ℝ → ℝ := fun j w =>
    ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2
      * ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ^ 2 with hF
  have hcontF : ∀ j : ℕ, Continuous (F j) := by
    intro j
    exact (((continuous_primeBlockPoly _).norm).pow 2).mul
      (((continuous_logPoly _ _).norm).pow 2)
  have hcontZ : Continuous fun w : ℝ => ‖ladderProductPoly P A₀ B₀ Q η L w‖ ^ 2 := by
    refine ((continuous_finsetSum _ fun j _ => ?_).norm).pow 2
    exact (continuous_primeBlockPoly _).mul (continuous_logPoly _ _)
  have hcontR : Continuous fun w : ℝ =>
      (∑ j ∈ Finset.range L, 1 / v j) * ∑ j ∈ Finset.range L, v j * F j w :=
    (continuous_finsetSum _ fun j _ => (hcontF j).const_mul _).const_mul _
  have hintZ : IntegrableOn (fun w : ℝ => ‖ladderProductPoly P A₀ B₀ Q η L w‖ ^ 2) E volume :=
    (hcontZ.integrableOn_Icc (a := -G) (b := G)).mono_set hEG
  have hintR : IntegrableOn (fun w : ℝ =>
      (∑ j ∈ Finset.range L, 1 / v j) * ∑ j ∈ Finset.range L, v j * F j w) E volume :=
    (hcontR.integrableOn_Icc (a := -G) (b := G)).mono_set hEG
  have hmono := setIntegral_mono_on hintZ hintR hEm
    (fun w _ => normSq_ladderProductPoly_le A₀ B₀ Q η v hv w)
  refine hmono.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [integral_finsetSum _ fun j _ =>
    (((hcontF j).const_mul (v j)).integrableOn_Icc (a := -G) (b := G)).mono_set hEG]
  exact Finset.sum_congr rfl fun j _ => MeasureTheory.integral_const_mul _ _

/-- **One step of the ladder over a frequency set, with the prime polynomial bounded there.** -/
theorem integral_normSq_ladderStep_set_le {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀) {Q η G V : ℝ}
    (hQ : 0 < Q) (hη : 0 ≤ η) (hG : 1 ≤ G) (hV : 0 ≤ V) (j : ℕ)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEG : E ⊆ Set.Icc (-G) G)
    (hbound : ∀ w ∈ E, ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V) :
    (∫ w in E,
        ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2
          * ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ^ 2)
      ≤ V ^ 2 * ((5 * Real.pi / 2 * G
            + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
          * ((geomCofactorBlockAt A₀ B₀ Q η j).card : ℝ)) := by
  classical
  set D : Finset ℕ := geomCofactorBlockAt A₀ B₀ Q η j with hD
  have hcontR : Continuous fun w : ℝ => ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2 :=
    ((continuous_primeBlockPoly _).norm).pow 2
  have hcontS : Continuous fun w : ℝ => ‖logPoly moebiusCoeff D w‖ ^ 2 :=
    ((continuous_logPoly _ _).norm).pow 2
  have hint1 : IntegrableOn (fun w : ℝ =>
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2 * ‖logPoly moebiusCoeff D w‖ ^ 2)
      E volume := ((hcontR.mul hcontS).integrableOn_Icc (a := -G) (b := G)).mono_set hEG
  have hint2 : IntegrableOn (fun w : ℝ => V ^ 2 * ‖logPoly moebiusCoeff D w‖ ^ 2) E volume :=
    (((hcontS.const_mul _)).integrableOn_Icc (a := -G) (b := G)).mono_set hEG
  have hpt : ∀ w ∈ E,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2 * ‖logPoly moebiusCoeff D w‖ ^ 2
        ≤ V ^ 2 * ‖logPoly moebiusCoeff D w‖ ^ 2 := by
    intro w hw
    have hb := hbound w hw
    have h0 : (0 : ℝ) ≤ ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ := norm_nonneg _
    have hsq : ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2 ≤ V ^ 2 := by nlinarith [hb, h0]
    exact mul_le_mul_of_nonneg_right hsq (by positivity)
  have hmono := setIntegral_mono_on hint1 hint2 hEm hpt
  rw [MeasureTheory.integral_const_mul] at hmono
  refine hmono.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hwiden : (∫ w in E, ‖logPoly moebiusCoeff D w‖ ^ 2)
      ≤ ∫ w in Set.Icc (-G) G, ‖logPoly moebiusCoeff D w‖ ^ 2 := by
    refine MeasureTheory.setIntegral_mono_set hcontS.integrableOn_Icc ?_
      (Filter.Eventually.of_forall hEG)
    exact Filter.Eventually.of_forall fun w => by positivity
  refine hwiden.trans ?_
  obtain ⟨h0, hle⟩ := geomCofactorBlockAt_bounds (A₀ := A₀) (B₀ := B₀) hA hQ hη j
  exact integral_Icc_normSq_logPoly_le_support moebiusCoeff h0 hle norm_moebiusCoeff_le_one hG

/-- **One step of the ladder on the low-frequency disc, with the cofactor polynomial bounded.** -/
theorem integral_normSq_ladderStep_low_le {P : Finset ℕ} {A₀ B₀ : ℕ} {Q η w₀ V U : ℝ}
    (hw₀ : 0 ≤ w₀) (hV : 0 ≤ V) (hU : 0 ≤ U) (j : ℕ)
    (hprime : ∀ w ∈ Set.Icc (-w₀) w₀, ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V)
    (hcof : ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ≤ U) :
    (∫ w in Set.Icc (-w₀) w₀,
        ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2
          * ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ^ 2)
      ≤ V ^ 2 * U ^ 2 * (2 * w₀) := by
  classical
  set D : Finset ℕ := geomCofactorBlockAt A₀ B₀ Q η j with hD
  have hcontR : Continuous fun w : ℝ => ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2 :=
    ((continuous_primeBlockPoly _).norm).pow 2
  have hcontS : Continuous fun w : ℝ => ‖logPoly moebiusCoeff D w‖ ^ 2 :=
    ((continuous_logPoly _ _).norm).pow 2
  have hint1 : IntegrableOn (fun w : ℝ =>
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2 * ‖logPoly moebiusCoeff D w‖ ^ 2)
      (Set.Icc (-w₀) w₀) volume := (hcontR.mul hcontS).integrableOn_Icc
  have hint2 : IntegrableOn (fun _ : ℝ => V ^ 2 * U ^ 2) (Set.Icc (-w₀) w₀) volume :=
    (continuous_const.integrableOn_Icc)
  have hpt : ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2 * ‖logPoly moebiusCoeff D w‖ ^ 2
        ≤ V ^ 2 * U ^ 2 := by
    intro w hw
    have hb := hprime w hw
    have hc := hcof w hw
    have h0 : (0 : ℝ) ≤ ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ := norm_nonneg _
    have h1 : (0 : ℝ) ≤ ‖logPoly moebiusCoeff D w‖ := norm_nonneg _
    have hsq1 : ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2 ≤ V ^ 2 := by nlinarith [hb, h0]
    have hsq2 : ‖logPoly moebiusCoeff D w‖ ^ 2 ≤ U ^ 2 := by nlinarith [hc, h1]
    have hs1 : (0 : ℝ) ≤ ‖logPoly moebiusCoeff D w‖ ^ 2 := by positivity
    nlinarith [hsq1, hsq2, hs1, hV, hU]
  have hmono := setIntegral_mono_on hint1 hint2 measurableSet_Icc hpt
  refine hmono.trans (le_of_eq ?_)
  rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
  ring

end

end RHTower.Sieve
