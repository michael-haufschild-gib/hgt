import GaloisForLFunctions.RHTower.Deninger.DeningerHasseHilbertPairing
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHassePaugamBlocks

/-! # A global continuous, nondegenerate Paugam form on literal Meyer cohomology

Native Hasse admission makes the full complementary-block sum convergent.
Exact finite causal sources detect every coordinate, so the form has zero
radical without simplicity, positivity, or a spectral admission premise.
-/

noncomputable section
open Complex Set Topology
open scoped Classical

namespace RHTower
open scoped DeningerMeyerNaturalTopology

def deningerHasseHilbertPaugamLM :
    DeningerArithmeticJetHilbert →ₗ[ℂ] DeningerArithmeticJetHilbert →ₗ[ℂ] ℂ :=
  deningerHasseHalfPairingLM.compl₂ deningerHasseHilbertReflectLM -
    (deningerHasseHalfPairingLM.compl₂ deningerHasseHilbertReflectLM).flip

@[simp] theorem deningerHasseHilbertPaugamLM_apply (x y : DeningerArithmeticJetHilbert) :
    deningerHasseHilbertPaugamLM x y =
      deningerHasseHalfPairing x (deningerHasseHilbertReflectCLM y) -
        deningerHasseHalfPairing y (deningerHasseHilbertReflectCLM x) := rfl

private theorem hasseHilbertPaugam_bound (x y : DeningerArithmeticJetHilbert) :
    ‖deningerHasseHilbertPaugamLM x y‖ ≤ 2 * ‖x‖ * ‖y‖ := by
  rw [deningerHasseHilbertPaugamLM_apply]
  calc
    _ ≤ ‖deningerHasseHalfPairing x (deningerHasseHilbertReflectCLM y)‖ +
        ‖deningerHasseHalfPairing y (deningerHasseHilbertReflectCLM x)‖ := norm_sub_le _ _
    _ ≤ ‖x‖ * ‖y‖ + ‖y‖ * ‖x‖ := add_le_add
      ((deningerHasseHalfPairing_bound _ _).trans
        (mul_le_mul_of_nonneg_left (deningerHasseHilbertReflectLM_norm_le y) (norm_nonneg x)))
      ((deningerHasseHalfPairing_bound _ _).trans
        (mul_le_mul_of_nonneg_left (deningerHasseHilbertReflectLM_norm_le x) (norm_nonneg y)))
    _ = _ := by ring

def deningerHasseHilbertPaugamCLM :
    DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert →L[ℂ] ℂ :=
  deningerHasseHilbertPaugamLM.mkContinuous₂ 2 hasseHilbertPaugam_bound

@[simp] theorem deningerHasseHilbertPaugamCLM_apply (x y : DeningerArithmeticJetHilbert) :
    deningerHasseHilbertPaugamCLM x y = deningerHasseHilbertPaugamLM x y := rfl

private theorem hasseHilbertPaugam_detect (x : DeningerArithmeticJetHilbert)
    (q : DeningerArithmeticJetCoordinate)
    (h : deningerHasseHilbertPaugamLM x
      (lp.single 2 (deningerHasseJetReflect (deningerHasseJetReverse q)) 1) = 0) :
    x q = 0 := by
  have hk : deningerHasseJetReverse (deningerHasseJetReflect (deningerHasseJetReverse q)) =
      deningerHasseJetReflect q := by
    rw [deningerHasseJetReverse_reflect, deningerHasseJetReverse_sq]
  rw [deningerHasseHilbertPaugamLM_apply, deningerHasseHilbertReflect_single,
    deningerHasseHalfPairing_single_right, deningerHasseHalfPairing_single_left,
    deningerHasseJetReflect_sq, deningerHasseJetReverse_sq, hk] at h
  change (if 0 < (q.1 : ℂ).im then
      ((-1 : ℂ)^q.2.rev.val * 1) * x q else 0) -
      (if 0 < (1-(q.1 : ℂ)).im then
        1 * ((-1 : ℂ)^q.2.val * x (deningerHasseJetReflect (deningerHasseJetReflect q)))
        else 0) = 0 at h
  rw [deningerHasseJetReflect_sq] at h
  have hn := xi_divisor_support_im_ne_zero q.1
  by_cases hp : 0 < (q.1 : ℂ).im
  · have hm : ¬0 < (1-(q.1 : ℂ)).im := by simp only [sub_im, one_im]; linarith
    simp only [if_pos hp, if_neg hm, mul_one, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (by norm_num))
  · have hm : 0 < (1-(q.1 : ℂ)).im := by simp only [sub_im, one_im]; rcases hn.lt_or_gt with hlt | hgt <;> linarith
    simp only [if_neg hp, if_pos hm, one_mul, zero_sub, neg_eq_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (by norm_num))

def deningerMeyerGlobalHassePaugamPairing :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ] DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ :=
  deningerHasseHilbertPaugamLM.compl₁₂ deningerMeyerHasseHilbertLM deningerMeyerHasseHilbertLM

theorem deningerMeyerGlobalHassePaugamPairing_apply
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerGlobalHassePaugamPairing u v =
      deningerHasseHalfPairing (deningerMeyerHasseHilbertLM u)
        (deningerMeyerHasseHilbertLM (deningerMeyerStrongLogCohomologyJ v)) -
      deningerHasseHalfPairing (deningerMeyerHasseHilbertLM v)
        (deningerMeyerHasseHilbertLM (deningerMeyerStrongLogCohomologyJ u)) := by
  simp only [deningerMeyerGlobalHassePaugamPairing, LinearMap.compl₁₂_apply,
    deningerHasseHilbertPaugamLM_apply, deningerMeyerHasseHilbert_J]

/-- Joint continuity holds for the original strong Poisson-quotient topology. -/
theorem deningerMeyerGlobalHassePaugamPairing_continuous :
    Continuous (fun p : DeningerMeyerStrongLogCohomology × DeningerMeyerStrongLogCohomology =>
      deningerMeyerGlobalHassePaugamPairing p.1 p.2) := by
  have h₁ : Continuous (fun p : DeningerMeyerStrongLogCohomology ×
      DeningerMeyerStrongLogCohomology => deningerMeyerHasseHilbertLM p.1) :=
    deningerMeyerHasseHilbertLM_continuous.comp continuous_fst
  have h₂ : Continuous (fun p : DeningerMeyerStrongLogCohomology ×
      DeningerMeyerStrongLogCohomology => deningerMeyerHasseHilbertLM p.2) :=
    deningerMeyerHasseHilbertLM_continuous.comp continuous_snd
  have hc := deningerHasseHilbertPaugamCLM.continuous₂.comp (h₁.prodMk h₂)
  simpa only [Function.comp_def, Function.uncurry_apply_pair,
    deningerHasseHilbertPaugamCLM_apply, deningerMeyerGlobalHassePaugamPairing,
    LinearMap.compl₁₂_apply] using hc

@[simp] theorem deningerMeyerGlobalHassePaugamPairing_self
    (u : DeningerMeyerStrongLogCohomology) : deningerMeyerGlobalHassePaugamPairing u u = 0 := by
  rw [deningerMeyerGlobalHassePaugamPairing_apply, sub_self]

theorem deningerMeyerGlobalHassePaugamPairing_skew
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerGlobalHassePaugamPairing u v = -deningerMeyerGlobalHassePaugamPairing v u := by
  simp only [deningerMeyerGlobalHassePaugamPairing_apply]
  ring

/-- Exact finite causal sources annihilate the entire radical. -/
theorem deningerMeyerGlobalHassePaugamPairing_ker :
    LinearMap.ker deningerMeyerGlobalHassePaugamPairing = ⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  apply (injective_iff_map_eq_zero _).mpr
  intro u hu
  apply deningerMeyerHasseHilbertLM_injective
  rw [map_zero]
  apply lp.ext
  funext q
  apply hasseHilbertPaugam_detect
  obtain ⟨v, hv⟩ := deningerMeyerHasseHilbert_single
    (deningerHasseJetReflect (deningerHasseJetReverse q)) 1
  have h := congrArg (fun L : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ => L v) hu
  change deningerHasseHilbertPaugamLM (deningerMeyerHasseHilbertLM u)
    (deningerMeyerHasseHilbertLM v) = 0 at h
  rwa [hv] at h

def deningerMeyerGlobalHassePaugamTerm (u v : DeningerMeyerStrongLogCohomology)
    (q : DeningerArithmeticJetCoordinate) : ℂ :=
  deningerHasseHalfTerm (deningerMeyerHasseHilbertLM u)
      (deningerMeyerHasseHilbertLM (deningerMeyerStrongLogCohomologyJ v)) q -
    deningerHasseHalfTerm (deningerMeyerHasseHilbertLM v)
      (deningerMeyerHasseHilbertLM (deningerMeyerStrongLogCohomologyJ u)) q

theorem deningerMeyerGlobalHassePaugamTerm_summable
    (u v : DeningerMeyerStrongLogCohomology) :
    Summable (deningerMeyerGlobalHassePaugamTerm u v) :=
  (deningerHasseHalfTerm_summable _ _).sub (deningerHasseHalfTerm_summable _ _)

/-- The complete original-source pairing is absolutely convergent. -/
theorem deningerMeyerGlobalHassePaugamTerm_norm_summable
    (u v : DeningerMeyerStrongLogCohomology) :
    Summable (fun q => ‖deningerMeyerGlobalHassePaugamTerm u v q‖) := by
  apply Summable.of_norm_bounded
    ((deningerHasseHalfTerm_norm_summable (deningerMeyerHasseHilbertLM u)
      (deningerMeyerHasseHilbertLM (deningerMeyerStrongLogCohomologyJ v))).add
      (deningerHasseHalfTerm_norm_summable (deningerMeyerHasseHilbertLM v)
        (deningerMeyerHasseHilbertLM (deningerMeyerStrongLogCohomologyJ u))))
  intro q
  rw [norm_norm]
  exact norm_sub_le _ _

theorem deningerMeyerGlobalHassePaugamPairing_tsum
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerGlobalHassePaugamPairing u v = ∑' q, deningerMeyerGlobalHassePaugamTerm u v q := by
  rw [deningerMeyerGlobalHassePaugamPairing_apply]
  exact ((deningerHasseHalfTerm_summable _ _).tsum_sub
    (deningerHasseHalfTerm_summable _ _)).symm

private theorem hassePaugam_block_sum (rho : XiDivisorSupport)
    (u v : DeningerMeyerStrongLogCohomology) :
    (∑' j : DeningerArithmeticJetIndex rho, deningerMeyerGlobalHassePaugamTerm u v ⟨rho, j⟩) =
      if 0 < (rho : ℂ).im then deningerMeyerHassePaugamBlock rho u v else 0 := by
  rw [tsum_fintype]
  by_cases hp : 0 < (rho : ℂ).im
  · simp only [deningerMeyerGlobalHassePaugamTerm, deningerHasseHalfTerm,
      deningerHasseJetReverse_apply, if_pos hp, deningerMeyerHasseHilbertLM_apply,
      deningerMeyerHassePaugamBlock]
  · simp only [deningerMeyerGlobalHassePaugamTerm, deningerHasseHalfTerm,
      if_neg hp, sub_self, Finset.sum_const_zero]

theorem deningerMeyerGlobalHassePaugamBlocks_summable
    (u v : DeningerMeyerStrongLogCohomology) :
    Summable (fun rho : XiDivisorSupport =>
      if 0 < (rho : ℂ).im then deningerMeyerHassePaugamBlock rho u v else 0) := by
  simpa only [hassePaugam_block_sum] using (deningerMeyerGlobalHassePaugamTerm_summable u v).sigma

/-- One global form combines every full local Paugam block with its forced
factorial normalization, rather than replacing repeated zeros by simple ones. -/
theorem deningerMeyerGlobalHassePaugamPairing_blocks
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerGlobalHassePaugamPairing u v =
      ∑' rho : XiDivisorSupport,
        if 0 < (rho : ℂ).im then deningerMeyerHassePaugamBlock rho u v else 0 := by
  rw [deningerMeyerGlobalHassePaugamPairing_tsum,
    (deningerMeyerGlobalHassePaugamTerm_summable u v).tsum_sigma]
  exact tsum_congr fun rho => hassePaugam_block_sum rho u v

/-- The global nondegenerate form has the original Meyer weight-one dynamics. -/
theorem deningerMeyerGlobalHassePaugamPairing_flow (c : ℝ)
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerGlobalHassePaugamPairing
        (deningerMeyerStrongLogCohomologyFlow c u) (deningerMeyerStrongLogCohomologyFlow c v) =
      (Real.exp c : ℂ) * deningerMeyerGlobalHassePaugamPairing u v := by
  rw [deningerMeyerGlobalHassePaugamPairing_blocks,
    deningerMeyerGlobalHassePaugamPairing_blocks, ← tsum_mul_left]
  apply tsum_congr
  intro rho
  split_ifs
  · exact deningerMeyerHassePaugamBlock_flow rho c u v
  · simp

theorem deningerMeyerGlobalHassePaugamPairing_J
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerGlobalHassePaugamPairing
        (deningerMeyerStrongLogCohomologyJ u) (deningerMeyerStrongLogCohomologyJ v) =
      -deningerMeyerGlobalHassePaugamPairing u v := by
  rw [deningerMeyerGlobalHassePaugamPairing_blocks,
    deningerMeyerGlobalHassePaugamPairing_blocks, ← tsum_neg]
  apply tsum_congr
  intro rho
  split_ifs
  · exact deningerMeyerHassePaugamBlock_J rho u v
  · simp

end RHTower
