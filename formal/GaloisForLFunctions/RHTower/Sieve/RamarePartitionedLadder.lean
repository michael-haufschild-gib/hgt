import GaloisForLFunctions.RHTower.Sieve.RamareBlockSplitOn
import GaloisForLFunctions.RHTower.Sieve.SetIntegralBlockSplit
import GaloisForLFunctions.RHTower.Sieve.BlockProductAnnulus

/-!
# The Ramaré ladder against a frequency partition

`Sieve/RamareLadderAffine.integral_normSq_ramareBilinear_affine_le` needs one pointwise bound `V j`
for the prime block valid on the **whole** annulus.  Matomäki–Radziwiłł's partition supplies such a
bound only on a part `𝒯` of the annulus — there by definition — and on the complement the roles of
the two factors are exchanged: the cofactor is bounded pointwise (by the zero-free region) and the
prime block is integrated.

This module splits the window into the low disc, the part of the annulus inside `𝒯`, and the part
outside, and applies the block ladder of `Sieve/RamareBlockSplitOn` on each.  The three pieces are
disjoint and cover, so nothing is lost but a threefold copy of the ladder defect.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- The ladder defect of one step, as it appears in the block bound. -/
def ramareStepDefect (P : Finset ℕ) (M : ℕ) (Q η W : ℝ) (j : ℕ) : ℝ :=
  2 * ((geomBlock P Q (1 + η) j).card : ℝ) ^ 2
      * (2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
          * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / (Q * (1 + η) ^ j) + 4
            + (((M : ℕ) : ℝ) / (Q * (1 + η) ^ j) ^ 2 + 1)))

/-- The block ladder over a measurable set, with the defect named. -/
theorem setIntegral_normSq_ramareBilinear_le_ladder_defect {P : Finset ℕ} (M : ℕ) {Q η W : ℝ}
    (hQ : 1 ≤ Q) (hη : 0 ≤ η) (hW : 1 ≤ W) {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ q ∈ P, q.Prime)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖ramareBilinear P M w‖ ^ 2)
      ≤ (L : ℝ) * ∑ j ∈ Finset.range L,
          (2 * (∫ w in E, ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2
                * ‖logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ 2)
            + ramareStepDefect P M Q η W j) := by
  have h := setIntegral_normSq_ramareBilinear_le_ladder_assembled (P := P) M hQ hη hW hL
    hPprime hP hEm hEs
  refine h.trans (le_of_eq ?_)
  refine congrArg (fun t => (L : ℝ) * t) (Finset.sum_congr rfl fun j _ => ?_)
  rw [ramareStepDefect]
  congr 2
  refine MeasureTheory.setIntegral_congr_fun hEm fun w _ => ?_
  rw [norm_mul, mul_pow]

/-- **The three-piece split of the window.** -/
theorem setIntegral_split_three {f : ℝ → ℝ} (hf : Continuous f) {W w₀ : ℝ}
    (hwW : w₀ ≤ W) {T : Set ℝ} (hTm : MeasurableSet T)
    (hTs : T ⊆ Set.Icc (-W) W) :
    (∫ w in Set.Icc (-W) W, f w)
      = (∫ w in Set.Icc (-w₀) w₀, f w) + (∫ w in T \ Set.Icc (-w₀) w₀, f w)
        + ∫ w in (Set.Icc (-W) W \ T) \ Set.Icc (-w₀) w₀, f w := by
  classical
  have hint : IntegrableOn f (Set.Icc (-W) W) volume := hf.integrableOn_Icc
  have hsub : Set.Icc (-w₀) w₀ ⊆ Set.Icc (-W) W := by
    intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hinter : Set.Icc (-W) W ∩ Set.Icc (-w₀) w₀ = Set.Icc (-w₀) w₀ :=
    Set.inter_eq_self_of_subset_right hsub
  have h1 := integral_inter_add_sdiff (μ := volume) (measurableSet_Icc (a := -w₀) (b := w₀)) hint
  rw [hinter] at h1
  have hintR : IntegrableOn f (Set.Icc (-W) W \ Set.Icc (-w₀) w₀) volume :=
    hint.mono_set Set.sdiff_subset
  have h2 := integral_inter_add_sdiff (μ := volume) hTm hintR
  have hA : (Set.Icc (-W) W \ Set.Icc (-w₀) w₀) ∩ T = T \ Set.Icc (-w₀) w₀ := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_sdiff]
    constructor
    · rintro ⟨⟨-, hu2⟩, hu3⟩
      exact ⟨hu3, hu2⟩
    · rintro ⟨hu1, hu2⟩
      exact ⟨⟨hTs hu1, hu2⟩, hu1⟩
  have hB : (Set.Icc (-W) W \ Set.Icc (-w₀) w₀) \ T
      = (Set.Icc (-W) W \ T) \ Set.Icc (-w₀) w₀ := by
    ext u
    simp only [Set.mem_sdiff]
    tauto
  rw [hA, hB] at h2
  linarith [h1, h2]

end

end RHTower.Sieve

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- **One block over a frequency set, with the COFACTOR bounded there.**  The dual of
`Sieve/BlockProductAnnulus.integral_normSq_blockProduct_set_le`: on the exceptional part of the
annulus the prime polynomial is large by definition, so the supremum must be taken on the cofactor
and the prime polynomial's mean square supplied from outside. -/
theorem integral_normSq_blockProduct_set_cofactorSup_le (a : ℕ → ℂ) (B D : Finset ℕ)
    {G U J : ℝ} {E : Set ℝ} (hEm : MeasurableSet E) (hEG : E ⊆ Set.Icc (-G) G)
    (hcof : ∀ w ∈ E, ‖logPoly a D w‖ ≤ U)
    (hJ : (∫ w in E, ‖primeBlockPoly B w‖ ^ 2) ≤ J) :
    (∫ w in E, ‖primeBlockPoly B w * logPoly a D w‖ ^ 2) ≤ U ^ 2 * J := by
  classical
  have hcomm : (∫ w in E, ‖primeBlockPoly B w * logPoly a D w‖ ^ 2)
      = ∫ w in E, ‖logPoly a D w‖ ^ 2 * ‖primeBlockPoly B w‖ ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun hEm fun w _ => ?_
    rw [norm_mul, mul_pow]
    ring
  rw [hcomm]
  have hb := setIntegral_normSq_mul_le_of_bound (F := fun w => logPoly a D w)
    (G := fun w => primeBlockPoly B w) (continuous_logPoly a D) (continuous_primeBlockPoly B)
    hEm hEG hcof
  exact hb.trans (mul_le_mul_of_nonneg_left hJ (sq_nonneg _))

/-- **One block over the whole window, split by a frequency partition.**  The low disc is paid by
two pointwise bounds, the part of the annulus inside `T` by the prime bound and the cofactor's mean
value theorem, and the part outside by the cofactor bound and the prime polynomial's mean square. -/
theorem integral_normSq_blockProduct_partitioned_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (B D : Finset ℕ) (hD0 : (0 : ℕ) ∉ D) {MD : ℕ} (hDM : ∀ n ∈ D, n ≤ MD)
    {w₀ G V Vlow U Us J : ℝ} (hG : 1 ≤ G) (hw₀ : 0 ≤ w₀) (hwG : w₀ ≤ G)
    (hV : 0 ≤ V) (hVlow : 0 ≤ Vlow) (hU : 0 ≤ U)
    {T : Set ℝ} (hTm : MeasurableSet T) (hTs : T ⊆ Set.Icc (-G) G)
    (hann : ∀ w ∈ T \ Set.Icc (-w₀) w₀, ‖primeBlockPoly B w‖ ≤ V)
    (hcof : ∀ w ∈ (Set.Icc (-G) G \ T) \ Set.Icc (-w₀) w₀, ‖logPoly a D w‖ ≤ Us)
    (hJ : (∫ w in (Set.Icc (-G) G \ T) \ Set.Icc (-w₀) w₀,
        ‖primeBlockPoly B w‖ ^ 2) ≤ J)
    (hlowP : ∀ w ∈ Set.Icc (-w₀) w₀, ‖primeBlockPoly B w‖ ≤ Vlow)
    (hlowC : ∀ w ∈ Set.Icc (-w₀) w₀, ‖logPoly a D w‖ ≤ U) :
    (∫ w in Set.Icc (-G) G, ‖primeBlockPoly B w * logPoly a D w‖ ^ 2)
      ≤ V ^ 2 * ((5 * Real.pi / 2 * G + 5 * Real.exp 1 / 2 * (MD : ℝ)) * (D.card : ℝ))
        + Us ^ 2 * J
        + Vlow ^ 2 * U ^ 2 * (2 * w₀) := by
  classical
  have hcont : Continuous fun w : ℝ => ‖primeBlockPoly B w * logPoly a D w‖ ^ 2 :=
    (((continuous_primeBlockPoly B).mul (continuous_logPoly a D)).norm).pow 2
  have hsplit := setIntegral_split_three (f := fun w : ℝ =>
    ‖primeBlockPoly B w * logPoly a D w‖ ^ 2) hcont hwG hTm hTs
  have hsubT : T \ Set.Icc (-w₀) w₀ ⊆ Set.Icc (-G) G := fun u hu => hTs hu.1
  have hsubU : (Set.Icc (-G) G \ T) \ Set.Icc (-w₀) w₀ ⊆ Set.Icc (-G) G := fun u hu => hu.1.1
  have hT := integral_normSq_blockProduct_set_le a ha B D hD0 hDM hG hV
    (hTm.diff measurableSet_Icc) hsubT hann
  have hUpart := integral_normSq_blockProduct_set_cofactorSup_le a B D
    ((measurableSet_Icc.diff hTm).diff measurableSet_Icc) hsubU hcof hJ
  have hLow := integral_normSq_blockProduct_low_le a B D hw₀ hVlow hU hlowP hlowC
  rw [hsplit]
  linarith

end

end RHTower.Sieve
