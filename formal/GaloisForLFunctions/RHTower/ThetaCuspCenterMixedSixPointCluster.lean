import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedSixthRank

/-! # Uniform positivity of arbitrary six-point theta clusters -/
open Set Matrix
namespace RHTower
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option maxHeartbeats 2000000

/-- Actual six-point theta Gram matrix at arbitrary real nodes. -/
def thetaCuspCenterMixedGramSix (a : ℝ) (t : Fin 6 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  translationSampleGram (thetaCuspCenterMixedDensity a) t

/-- The literal factorial-normalized sixth jet section is strictly positive. -/
theorem thetaCuspCenterMixed_translationJetMatrix_six_posDef
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    (translationJetMatrix 6 (thetaCuspCenterMixedDensity a)).PosDef := by
  let f := thetaCuspCenterMixedDensity a
  have heven : Function.Even f := thetaCuspCenterMixedDensity_even a
  have h1 : iteratedDeriv 1 f 0 = 0 := iteratedDeriv_zero_of_even_real_of_odd heven (by norm_num)
  have h3 : iteratedDeriv 3 f 0 = 0 := iteratedDeriv_zero_of_even_real_of_odd heven (by norm_num)
  have h5 : iteratedDeriv 5 f 0 = 0 := iteratedDeriv_zero_of_even_real_of_odd heven (by norm_num)
  have h7 : iteratedDeriv 7 f 0 = 0 := iteratedDeriv_zero_of_even_real_of_odd heven (by norm_num)
  have h9 : iteratedDeriv 9 f 0 = 0 := iteratedDeriv_zero_of_even_real_of_odd heven (by norm_num)
  have hH := thetaCuspCenterMixedSignedHankel_six_posDef ha0 ha
  rw [thetaCuspCenterMixedSignedHankel_six_eq] at hH
  let S : Matrix (Fin 6) (Fin 6) ℝ := diagonal
    (fun i => (-1 : ℝ)^(i.val/2)/(i.val.factorial : ℝ))
  have hS : Function.Injective S.mulVec := by
    intro v w hvw
    funext i
    have hi := congrFun hvw i
    simp only [S, Matrix.mulVec_diagonal] at hi
    have hn : (-1 : ℝ)^(i.val/2)/(i.val.factorial : ℝ) ≠ 0 :=
      div_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero i.val)
    exact (mul_left_cancel₀ hn) hi
  have heq : translationJetMatrix 6 f = Sᴴ *
      sixPointSignedHankel (f 0) (-iteratedDeriv 2 f 0) (iteratedDeriv 4 f 0)
        (-iteratedDeriv 6 f 0) (iteratedDeriv 8 f 0) (-iteratedDeriv 10 f 0) * S := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [translationJetMatrix, S, Matrix.diagonal, sixPointSignedHankel,
        Matrix.mul_apply, Fin.sum_univ_succ, h1, h3, h5, h7, h9] <;> ring
  rw [heq]
  exact hH.conjTranspose_mul_mul_same hS

/-- One theta cluster radius works for every ordered shape, however unequal its gaps. -/
theorem exists_thetaCuspCenterMixedGramSix_posDef_radius
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : Fin 6 → ℝ, StrictMono t → ‖t‖ < δ →
      (thetaCuspCenterMixedGramSix a t).PosDef := by
  exact exists_translationSampleGram_posDef_radius
    (show ContDiff ℝ 10 (thetaCuspCenterMixedDensity a) from
      (contDiff_infty_thetaCuspCenterMixedDensity a (by rw [abs_of_pos ha0]; linarith)).of_le (by exact WithTop.coe_le_coe.mpr (le_top : (10 : ℕ∞) ≤ ⊤)))
    (thetaCuspCenterMixedDensity_even a)
    (thetaCuspCenterMixed_translationJetMatrix_six_posDef ha0 ha)

/-- Every ordered six-point cluster of sufficiently small diameter is strictly positive. -/
theorem exists_thetaCuspCenterMixedGramSix_posDef_diameter
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : Fin 6 → ℝ, StrictMono t → t 5-t 0 < δ →
      (thetaCuspCenterMixedGramSix a t).PosDef := by
  obtain ⟨δ, hδ, hpos⟩ := exists_thetaCuspCenterMixedGramSix_posDef_radius ha0 ha
  refine ⟨δ, hδ, fun t ht hdiam => ?_⟩
  let u : Fin 6 → ℝ := fun i => t i-t 0
  have hu : StrictMono u := fun i j hij => sub_lt_sub_right (ht hij) (t 0)
  have hunorm : ‖u‖ < δ := by
    rw [pi_norm_lt_iff hδ]
    intro i
    have hlo : 0 ≤ t i-t 0 := sub_nonneg.mpr (ht.monotone (Fin.zero_le i))
    have hhi : t i-t 0 ≤ t 5-t 0 := sub_le_sub_right (ht.monotone (Fin.le_last i)) _
    simpa only [u, Real.norm_eq_abs, abs_of_nonneg hlo] using hhi.trans_lt hdiam
  have hM := hpos u hu hunorm
  have heq : thetaCuspCenterMixedGramSix a u = thetaCuspCenterMixedGramSix a t := by
    ext i j
    unfold thetaCuspCenterMixedGramSix translationSampleGram
    dsimp only [u]
    congr 1
    ring
  rw [heq] at hM
  exact hM


/-- Arbitrary distinct six-point clusters are positive without ordering or spacing restrictions. -/
theorem exists_thetaCuspCenterMixedGramSix_posDef_cluster
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : Fin 6 → ℝ, Function.Injective t →
      (∀ i j, |t i-t j| < δ) → (thetaCuspCenterMixedGramSix a t).PosDef := by
  classical
  obtain ⟨δ, hδ, hpos⟩ := exists_thetaCuspCenterMixedGramSix_posDef_diameter ha0 ha
  refine ⟨δ, hδ, fun t ht hsmall => ?_⟩
  have hcard : (Finset.image t Finset.univ).card = 6 :=
    (Finset.card_image_of_injective Finset.univ ht).trans (Finset.card_fin 6)
  let σ : Equiv.Perm (Fin 6) :=
    (Finset.orderIsoOfFin (Finset.image t Finset.univ) hcard).toEquiv.trans
      ((Equiv.setCongr Fintype.coe_image_univ).trans (Equiv.ofInjective t ht).symm)
  have heq (i : Fin 6) : t (σ i) =
      ((Finset.orderIsoOfFin (Finset.image t Finset.univ) hcard i) : ℝ) := by
    simp [σ, Equiv.apply_ofInjective_symm]
    rfl
  have hmono : StrictMono (t ∘ σ) := by
    intro i j hij
    change t (σ i) < t (σ j)
    rw [heq i, heq j]
    exact (Finset.orderIsoOfFin (Finset.image t Finset.univ) hcard).strictMono hij
  have hdiam : (t ∘ σ) 5-(t ∘ σ) 0 < δ :=
    (le_abs_self _).trans_lt (hsmall (σ 5) (σ 0))
  have hM := (hpos (t ∘ σ) hmono hdiam).submatrix σ.symm.injective
  have heqM : (thetaCuspCenterMixedGramSix a (t ∘ σ)).submatrix σ.symm σ.symm =
      thetaCuspCenterMixedGramSix a t := by
    ext i j
    simp [thetaCuspCenterMixedGramSix, translationSampleGram, Matrix.submatrix]
  rw [heqM] at hM
  exact hM

end
end RHTower
