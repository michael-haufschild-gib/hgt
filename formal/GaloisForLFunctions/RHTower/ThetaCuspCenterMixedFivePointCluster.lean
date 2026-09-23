import GaloisForLFunctions.HTGeometry.PrefixDividedDifferenceGram
import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedFivePointCusp

/-!
# Uniform positivity of arbitrary five-point theta clusters

Every critical aperture has one cluster-diameter radius for every five distinct real nodes,
without ordering, minimum-gap, or spacing-ratio assumptions. The literal factorial-normalized
jet matrix is strictly positive, and the prefix divided-difference theorem transfers its sign
to all small clusters. Translation and permutation invariance give the final physical form.
-/

open Set Matrix
namespace RHTower
open GaloisForLFunctions.HTGeometry
noncomputable section

/-- Actual five-point theta Gram matrix at arbitrary real nodes. -/
def thetaCuspCenterMixedGramFive (a : ℝ) (t : Fin 5 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  translationSampleGram (thetaCuspCenterMixedDensity a) t

/-- The literal theta derivative matrix is strictly positive after factorial normalization. -/
theorem thetaCuspCenterMixed_translationJetMatrix_five_posDef
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    (translationJetMatrix 5 (thetaCuspCenterMixedDensity a)).PosDef := by
  let f := thetaCuspCenterMixedDensity a
  have heven : Function.Even f := thetaCuspCenterMixedDensity_even a
  have h1 : iteratedDeriv 1 f 0 = 0 := iteratedDeriv_zero_of_even_real_of_odd heven (by norm_num)
  have h3 : iteratedDeriv 3 f 0 = 0 := iteratedDeriv_zero_of_even_real_of_odd heven (by norm_num)
  have h5 : iteratedDeriv 5 f 0 = 0 := iteratedDeriv_zero_of_even_real_of_odd heven (by norm_num)
  have h7 : iteratedDeriv 7 f 0 = 0 := iteratedDeriv_zero_of_even_real_of_odd heven (by norm_num)
  have h2 : iteratedDeriv 2 f 0 < 0 := by
    rw [iteratedDeriv_two_thetaCuspCenterMixedDensity ha0.le ha]
    exact thetaCuspCenterMixedDensitySecondJet_zero_neg ha0 ha
  have h4 : 0 < f 0*iteratedDeriv 4 f 0-(iteratedDeriv 2 f 0)^(2 : ℕ) := by
    rw [iteratedDeriv_four_thetaCuspCenterMixedDensity ha0.le ha,
      iteratedDeriv_two_thetaCuspCenterMixedDensity ha0.le ha]
    exact thetaCuspCenterMixedDensity_fourthHankel_pos ha0 ha
  have hH := HilbertMetric.fivePointJetMatrix_posDef
    (thetaCuspCenterMixedDensity_pos ha0 ha 0) h2 h4
    (thetaCuspCenterMixedDensity_iteratedDeriv_secondSixthHankel_pos ha0 ha)
    (thetaCuspCenterMixedDensity_iteratedDeriv_eighthHankel_pos ha0 ha)
  let S : Matrix (Fin 5) (Fin 5) ℝ := diagonal (fun i => (i.val.factorial : ℝ)⁻¹)
  have hS : Function.Injective S.mulVec := by
    intro v w hvw
    funext i
    have hi := congrFun hvw i
    simp only [S, Matrix.mulVec_diagonal] at hi
    have hn : (i.val.factorial : ℝ)⁻¹ ≠ 0 := by
      exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero i.val)
    exact (mul_left_cancel₀ hn) hi
  have heq : translationJetMatrix 5 f =
      Sᴴ * HilbertMetric.fivePointJetMatrix (f 0) (iteratedDeriv 2 f 0)
        (iteratedDeriv 4 f 0) (iteratedDeriv 6 f 0) (iteratedDeriv 8 f 0) * S := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [translationJetMatrix, S, Matrix.diagonal, HilbertMetric.fivePointJetMatrix,
        Matrix.mul_apply, Fin.sum_univ_succ, h1, h3, h5, h7] <;> ring
  rw [heq]
  exact hH.conjTranspose_mul_mul_same hS

/-- One theta cluster radius works for every ordered shape, however unequal its gaps. -/
theorem exists_thetaCuspCenterMixedGramFive_posDef_radius
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : Fin 5 → ℝ, StrictMono t → ‖t‖ < δ →
      (thetaCuspCenterMixedGramFive a t).PosDef := by
  exact exists_translationSampleGram_posDef_radius
    (contDiff_eight_thetaCuspCenterMixedDensity ha0.le ha)
    (thetaCuspCenterMixedDensity_even a)
    (thetaCuspCenterMixed_translationJetMatrix_five_posDef ha0 ha)

/-- Every ordered five-point cluster of sufficiently small diameter is strictly positive. -/
theorem exists_thetaCuspCenterMixedGramFive_posDef_diameter
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : Fin 5 → ℝ, StrictMono t → t 4-t 0 < δ →
      (thetaCuspCenterMixedGramFive a t).PosDef := by
  obtain ⟨δ, hδ, hpos⟩ := exists_thetaCuspCenterMixedGramFive_posDef_radius ha0 ha
  refine ⟨δ, hδ, fun t ht hdiam => ?_⟩
  let u : Fin 5 → ℝ := fun i => t i-t 0
  have hu : StrictMono u := fun i j hij => sub_lt_sub_right (ht hij) (t 0)
  have hunorm : ‖u‖ < δ := by
    rw [pi_norm_lt_iff hδ]
    intro i
    have hlo : 0 ≤ t i-t 0 := sub_nonneg.mpr (ht.monotone (Fin.zero_le i))
    have hhi : t i-t 0 ≤ t 4-t 0 := sub_le_sub_right (ht.monotone (Fin.le_last i)) _
    simpa only [u, Real.norm_eq_abs, abs_of_nonneg hlo] using hhi.trans_lt hdiam
  have hM := hpos u hu hunorm
  have heq : thetaCuspCenterMixedGramFive a u = thetaCuspCenterMixedGramFive a t := by
    ext i j
    unfold thetaCuspCenterMixedGramFive translationSampleGram
    dsimp only [u]
    congr 1
    ring
  rw [heq] at hM
  exact hM


/-- Arbitrary distinct five-point clusters are positive without ordering or spacing restrictions. -/
theorem exists_thetaCuspCenterMixedGramFive_posDef_cluster
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : Fin 5 → ℝ, Function.Injective t →
      (∀ i j, |t i-t j| < δ) → (thetaCuspCenterMixedGramFive a t).PosDef := by
  classical
  obtain ⟨δ, hδ, hpos⟩ := exists_thetaCuspCenterMixedGramFive_posDef_diameter ha0 ha
  refine ⟨δ, hδ, fun t ht hsmall => ?_⟩
  have hcard : (Finset.image t Finset.univ).card = 5 :=
    (Finset.card_image_of_injective Finset.univ ht).trans (Finset.card_fin 5)
  let σ : Equiv.Perm (Fin 5) :=
    (Finset.orderIsoOfFin (Finset.image t Finset.univ) hcard).toEquiv.trans
      ((Equiv.setCongr Fintype.coe_image_univ).trans (Equiv.ofInjective t ht).symm)
  have heq (i : Fin 5) : t (σ i) =
      ((Finset.orderIsoOfFin (Finset.image t Finset.univ) hcard i) : ℝ) := by
    simp [σ, Equiv.apply_ofInjective_symm]
    rfl
  have hmono : StrictMono (t ∘ σ) := by
    intro i j hij
    change t (σ i) < t (σ j)
    rw [heq i, heq j]
    exact (Finset.orderIsoOfFin (Finset.image t Finset.univ) hcard).strictMono hij
  have hdiam : (t ∘ σ) 4-(t ∘ σ) 0 < δ :=
    (le_abs_self _).trans_lt (hsmall (σ 4) (σ 0))
  have hM := (hpos (t ∘ σ) hmono hdiam).submatrix σ.symm.injective
  have heqM : (thetaCuspCenterMixedGramFive a (t ∘ σ)).submatrix σ.symm σ.symm =
      thetaCuspCenterMixedGramFive a t := by
    ext i j
    simp [thetaCuspCenterMixedGramFive, translationSampleGram, Matrix.submatrix]
  rw [heqM] at hM
  exact hM

end
end RHTower
