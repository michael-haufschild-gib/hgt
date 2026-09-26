import GaloisForLFunctions.RHTower.EtaHighHeightReflectionRecovery

set_option autoImplicit false

/-!
# Analytic eta reflection separation from height two pi

The stronger Euler-prefactor estimate absorbs the digamma error already
at height `2*pi`.  A positive first-term logarithm bound supplies a fixed
margin, without a numerical grid.  A square coordinate includes the
endpoint and covers the entire closed height range.
-/

namespace RiemannGaussian

open Complex RHTower GaloisForLFunctions Set
open scoped ComplexConjugate

noncomputable section

def etaTransitionHeight (t : ℝ) : ℝ := 2 * Real.pi * (1 + t ^ 2)

theorem etaTransitionHeight_half_ge_pi (t : ℝ) :
    Real.pi ≤ etaTransitionHeight t / 2 := by
  unfold etaTransitionHeight
  nlinarith [sq_nonneg t, Real.pi_pos]

theorem range_etaTransitionHeight :
    Set.range etaTransitionHeight = Set.Ici (2 * Real.pi) := by
  ext b
  constructor
  · rintro ⟨t, rfl⟩
    change 2 * Real.pi ≤ etaTransitionHeight t
    linarith [etaTransitionHeight_half_ge_pi t]
  · intro hb
    have hc : 0 < 2 * Real.pi := by positivity
    have hq : 1 ≤ b / (2 * Real.pi) := by
      apply (le_div_iff₀ hc).mpr
      simpa using hb
    refine ⟨Real.sqrt (b / (2 * Real.pi) - 1), ?_⟩
    rw [etaTransitionHeight, Real.sq_sqrt (sub_nonneg.mpr hq)]
    field_simp
    ring

/-- The first positive term of the analytic logarithm expansion suffices
for the drift margin. -/
theorem etaPrefactor_log_two_lower : (2 : ℝ) / 3 ≤ Real.log 2 := by
  have h := Real.sum_range_le_log_div (x := (1 : ℝ) / 3)
    (by norm_num) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem etaTransitionHeight_digamma_error (t : ℝ) :
    1 / (etaTransitionHeight t / 2) ^ 2 +
      Real.pi / (2 * (etaTransitionHeight t / 2)) < 3 / 4 := by
  let y := etaTransitionHeight t / 2
  have hy : Real.pi ≤ y := etaTransitionHeight_half_ge_pi t
  have hy0 : 0 < y := lt_of_lt_of_le Real.pi_pos hy
  have hy2 : 2 < y := by linarith [Real.pi_gt_three]
  have hfirst : 1 / y ^ 2 < (1 : ℝ) / 4 := by
    apply (div_lt_div_iff₀ (sq_pos_of_pos hy0) (by norm_num : (0 : ℝ) < 4)).mpr
    nlinarith
  have hsecond : Real.pi / (2 * y) ≤ (1 : ℝ) / 2 := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hy0) (by norm_num : (0 : ℝ) < 2)).mpr
    linarith
  change 1 / y ^ 2 + Real.pi / (2 * y) < 3 / 4
  linarith

/-- A modest upper bound on chi's drift is sufficient; chi itself need
not have negative drift in the transition range. -/
theorem re_logDeriv_zetaChi_etaTransitionHeight (x t : ℝ) :
    (logDeriv zetaChi (etaReflectionStripPoint x (etaTransitionHeight t))).re < 3 / 4 := by
  let y := etaTransitionHeight t / 2
  have hy : Real.pi ≤ y := etaTransitionHeight_half_ge_pi t
  have hy0 : 0 < y := lt_of_lt_of_le Real.pi_pos hy
  have hu := re_digamma_ge (x := sigmoid x / 2) (y := y)
    (by positivity [sigmoid_pos x]) hy0
  have hv := re_digamma_ge (x := (1 - sigmoid x) / 2) (y := y)
    (by linarith [sigmoid_lt_one x]) hy0
  have hlog : Real.log Real.pi ≤ Real.log y := Real.log_le_log Real.pi_pos hy
  have herr := etaTransitionHeight_digamma_error t
  change 1 / y ^ 2 + Real.pi / (2 * y) < 3 / 4 at herr
  rw [re_logDeriv_zetaChi_strip]
  linarith

/-- A uniform negative margin for the literal multiplier, including the
transition endpoint, follows from two analytic inequalities. -/
theorem re_logDeriv_etaElementaryReflectionMultiplier_transition (x t : ℝ) :
    (logDeriv etaElementaryReflectionMultiplier
      (etaReflectionStripPoint x (etaTransitionHeight t))).re < -(1 / 36) := by
  rw [re_logDeriv_etaElementaryReflectionMultiplier]
  have hp := pairedEtaFactorLogDerivative_sum_lt_seven_sixths x (etaTransitionHeight t)
  have hχ := re_logDeriv_zetaChi_etaTransitionHeight x t
  have hl := etaPrefactor_log_two_lower
  nlinarith

theorem deriv_log_norm_etaElementaryReflectionMultiplier_transition_neg (x t : ℝ) :
    deriv (fun σ : ℝ => Real.log ‖etaElementaryReflectionMultiplier
      ((σ : ℂ) + (etaTransitionHeight t : ℂ) * I)‖) (sigmoid x) < 0 := by
  rw [deriv_log_norm_etaElementaryReflectionMultiplier]
  exact lt_trans (re_logDeriv_etaElementaryReflectionMultiplier_transition x t) (by norm_num)

theorem strictAntiOn_log_norm_etaElementaryReflectionMultiplier_transition (t : ℝ) :
    StrictAntiOn (fun σ : ℝ => Real.log ‖etaElementaryReflectionMultiplier
      ((σ : ℂ) + (etaTransitionHeight t : ℂ) * I)‖) (Ioo 0 1) := by
  have hneg (σ : ℝ) (hσ : σ ∈ Ioo (0 : ℝ) 1) :
      deriv (fun a : ℝ => Real.log ‖etaElementaryReflectionMultiplier
        ((a : ℂ) + (etaTransitionHeight t : ℂ) * I)‖) σ < 0 := by
    have hrange : σ ∈ Set.range sigmoid := by rw [sigmoid_range]; exact hσ
    obtain ⟨x, rfl⟩ := hrange
    exact deriv_log_norm_etaElementaryReflectionMultiplier_transition_neg x t
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
  · intro σ hσ
    exact (differentiableAt_of_deriv_ne_zero (hneg σ hσ).ne).continuousAt.continuousWithinAt
  · intro σ hσ
    exact hneg σ (interior_subset hσ)

theorem norm_etaElementaryReflectionMultiplier_transition_eq_one_iff (x t : ℝ) :
    ‖etaElementaryReflectionMultiplier (etaReflectionStripPoint x (etaTransitionHeight t))‖ = 1 ↔
      sigmoid x = 1 / 2 := by
  constructor
  · intro h
    have hcenter := norm_etaElementaryReflectionMultiplier_half (etaTransitionHeight t)
    apply (strictAntiOn_log_norm_etaElementaryReflectionMultiplier_transition t).injOn
      ⟨sigmoid_pos x, sigmoid_lt_one x⟩ (by constructor <;> norm_num)
    change Real.log ‖etaElementaryReflectionMultiplier
        (etaReflectionStripPoint x (etaTransitionHeight t))‖ = _
    rw [h]
    simpa using congrArg Real.log hcenter.symm
  · intro h
    simpa [etaReflectionStripPoint, h] using
      norm_etaElementaryReflectionMultiplier_half (etaTransitionHeight t)

/-- The source-retaining mirror classification now holds throughout the
closed tail from `2*pi`, with no transitional numerical certificate. -/
theorem pairedEtaCore_transition_mirror_eq_iff (x t : ℝ) :
    let s := etaReflectionStripPoint x (etaTransitionHeight t)
    pairedEtaCore s = pairedEtaCore (1 - conj s) ↔
      sigmoid x = 1 / 2 ∨ pairedEtaCore s = 0 := by
  dsimp only
  let s := etaReflectionStripPoint x (etaTransitionHeight t)
  have hbalance := norm_pairedEtaCore_mirror_balance x (etaTransitionHeight t)
  change ‖pairedEtaCore s‖ = ‖etaElementaryReflectionMultiplier s‖ *
    ‖pairedEtaCore (1 - conj s)‖ at hbalance
  constructor
  · intro h
    by_cases hcenter : sigmoid x = 1 / 2
    · exact Or.inl hcenter
    · right
      have hmod : ‖etaElementaryReflectionMultiplier s‖ ≠ 1 := by
        exact fun hm => hcenter ((norm_etaElementaryReflectionMultiplier_transition_eq_one_iff x t).mp hm)
      have hnorm : ‖pairedEtaCore s‖ = ‖pairedEtaCore (1 - conj s)‖ := congrArg norm h
      have hprod : (1 - ‖etaElementaryReflectionMultiplier s‖) * ‖pairedEtaCore s‖ = 0 := by
        rw [← hnorm] at hbalance
        linear_combination hbalance
      exact norm_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left
        (sub_ne_zero.mpr hmod.symm))
  · rintro (hcenter | hzero)
    · have hs : 1 - conj s = s := by
        dsimp [s, etaReflectionStripPoint]
        rw [hcenter]
        apply Complex.ext <;> simp
        ring
      change pairedEtaCore s = pairedEtaCore (1 - conj s)
      rw [hs]
    · have hmod : ‖etaElementaryReflectionMultiplier s‖ ≠ 0 :=
        norm_ne_zero_iff.mpr (etaElementaryReflectionMultiplier_ne_zero x (etaTransitionHeight t))
      rw [hzero, norm_zero] at hbalance
      have hp : pairedEtaCore (1 - conj s) = 0 := norm_eq_zero.mp
        ((mul_eq_zero.mp hbalance.symm).resolve_left hmod)
      exact hzero.trans hp.symm

end

end RiemannGaussian
