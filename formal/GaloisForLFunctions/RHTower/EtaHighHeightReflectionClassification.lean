import GaloisForLFunctions.RHTower.EtaPrefactorArchimedeanDrift

set_option autoImplicit false

/-!
# What a strictly monotone eta reflection multiplier actually proves

At analytically controlled high heights, the multiplier log-modulus is
strictly decreasing across the open strip and is zero exactly on its
midline.  The resulting eta reflection classification retains common
zeros: equality at mirror points occurs exactly on the midline or at an
eta zero.  Thus multiplier monotonicity separates nonzero mirror values
without asserting that the common-zero alternative is absent.
-/

namespace RiemannGaussian

open Complex RHTower GaloisForLFunctions Set
open scoped ComplexConjugate

noncomputable section

/-- The height coordinate covers exactly the open analytic tail; it does
not select a discrete set of checked heights. -/
theorem range_etaArchimedeanHeight :
    Set.range etaArchimedeanHeight = Set.Ioi (2 * Real.pi * Real.exp 1) := by
  ext b
  constructor
  · rintro ⟨t, rfl⟩
    change 2 * Real.pi * Real.exp 1 < 2 * Real.pi * Real.exp (1 + Real.exp t)
    exact mul_lt_mul_of_pos_left
      (Real.exp_lt_exp.mpr (by linarith [Real.exp_pos t])) (by positivity)
  · intro hb
    have hc : 0 < 2 * Real.pi := by positivity
    have hq : Real.exp 1 < b / (2 * Real.pi) := by
      apply (lt_div_iff₀ hc).mpr
      simpa [mul_comm] using hb
    have hq0 : 0 < b / (2 * Real.pi) := lt_trans (Real.exp_pos 1) hq
    have hl : 1 < Real.log (b / (2 * Real.pi)) :=
      (Real.lt_log_iff_exp_lt hq0).mpr hq
    refine ⟨Real.log (Real.log (b / (2 * Real.pi)) - 1), ?_⟩
    rw [etaArchimedeanHeight, Real.exp_log (sub_pos.mpr hl),
      show 1 + (Real.log (b / (2 * Real.pi)) - 1) =
        Real.log (b / (2 * Real.pi)) by ring, Real.exp_log hq0]
    field_simp

/-- The elementary reflection multiplier has unit modulus on the midline. -/
theorem norm_etaElementaryReflectionMultiplier_half (b : ℝ) :
    ‖etaElementaryReflectionMultiplier ((1 / 2 : ℂ) + (b : ℂ) * I)‖ = 1 := by
  let s : ℂ := 1 / 2 + (b : ℂ) * I
  have hs : s.re = 1 / 2 := by simp [s]
  have hsym : 1 - s = conj s := by
    dsimp [s]
    apply Complex.ext <;> simp
    ring
  have hg : pairedEtaFactor s ≠ 0 := pairedEtaFactor_ne_zero_of_re_lt_one (by linarith)
  change ‖etaElementaryReflectionMultiplier s‖ = 1
  rw [etaElementaryReflectionMultiplier, norm_div, norm_mul,
    zetaChi_norm_on_line hs, hsym, pairedEtaFactor_conj, Complex.norm_conj, mul_one]
  exact div_self (norm_ne_zero_iff.mpr hg)

/-- Strict horizontal monotonicity of the actual multiplier norm, proved
analytically on the entire open strip at each admitted height. -/
theorem strictAntiOn_log_norm_etaElementaryReflectionMultiplier (t : ℝ) :
    StrictAntiOn (fun σ : ℝ => Real.log ‖etaElementaryReflectionMultiplier
      ((σ : ℂ) + (etaArchimedeanHeight t : ℂ) * I)‖) (Ioo 0 1) := by
  have hneg (σ : ℝ) (hσ : σ ∈ Ioo (0 : ℝ) 1) :
      deriv (fun a : ℝ => Real.log ‖etaElementaryReflectionMultiplier
        ((a : ℂ) + (etaArchimedeanHeight t : ℂ) * I)‖) σ < 0 := by
    have hrange : σ ∈ Set.range sigmoid := by rw [sigmoid_range]; exact hσ
    obtain ⟨x, rfl⟩ := hrange
    exact deriv_log_norm_etaElementaryReflectionMultiplier_neg x t
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
  · intro σ hσ
    exact (differentiableAt_of_deriv_ne_zero (hneg σ hσ).ne).continuousAt.continuousWithinAt
  · intro σ hσ
    exact hneg σ (interior_subset hσ)

/-- Unit multiplier modulus is equivalent to the midline at high heights. -/
theorem norm_etaElementaryReflectionMultiplier_eq_one_iff (x t : ℝ) :
    ‖etaElementaryReflectionMultiplier (etaReflectionStripPoint x (etaArchimedeanHeight t))‖ = 1 ↔
      sigmoid x = 1 / 2 := by
  constructor
  · intro h
    have hcenter := norm_etaElementaryReflectionMultiplier_half (etaArchimedeanHeight t)
    apply (strictAntiOn_log_norm_etaElementaryReflectionMultiplier t).injOn
      ⟨sigmoid_pos x, sigmoid_lt_one x⟩ (by constructor <;> norm_num)
    change Real.log ‖etaElementaryReflectionMultiplier
        (etaReflectionStripPoint x (etaArchimedeanHeight t))‖ = _
    rw [h]
    simpa using congrArg Real.log hcenter.symm
  · intro h
    simpa [etaReflectionStripPoint, h] using
      norm_etaElementaryReflectionMultiplier_half (etaArchimedeanHeight t)

/-- The actual eta functional equation with its elementary reflection
multiplier, including points where eta vanishes. -/
theorem pairedEtaCore_elementary_reflection (x b : ℝ) :
    let s := etaReflectionStripPoint x b
    pairedEtaCore s = etaElementaryReflectionMultiplier s * pairedEtaCore (1 - s) := by
  dsimp only
  let s := etaReflectionStripPoint x b
  have hs : 0 < s.re := etaReflectionStripPoint_re_pos x b
  have ht : s.re < 1 := etaReflectionStripPoint_re_lt_one x b
  have hp : 0 < (1 - s).re := by simpa using sub_pos.mpr ht
  have hpt : (1 - s).re < 1 := by simp; linarith
  have hs0 : s ≠ 0 := by intro h; rw [h, zero_re] at hs; linarith
  have hs1 : s ≠ 1 := by intro h; rw [h, one_re] at ht; linarith
  have hp1 : 1 - s ≠ 1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hfactor : pairedEtaFactor (1 - s) ≠ 0 :=
    pairedEtaFactor_ne_zero_of_re_lt_one hpt
  change pairedEtaCore s = etaElementaryReflectionMultiplier s * pairedEtaCore (1 - s)
  rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one hs hs1,
    pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one hp hp1,
    zeta_eq_zetaChi_mul hs0 hs1 (Complex.Gammaℝ_ne_zero_of_re_pos hp)]
  change pairedEtaFactor s * (zetaChi s * riemannZeta (1 - s)) =
    etaElementaryReflectionMultiplier s * (pairedEtaFactor (1 - s) * riemannZeta (1 - s))
  unfold etaElementaryReflectionMultiplier
  field_simp

/-- Source-retaining norm balance between actual mirror eta values. -/
theorem norm_pairedEtaCore_mirror_balance (x b : ℝ) :
    let s := etaReflectionStripPoint x b
    ‖pairedEtaCore s‖ = ‖etaElementaryReflectionMultiplier s‖ *
      ‖pairedEtaCore (1 - conj s)‖ := by
  dsimp only
  have h := congrArg norm (pairedEtaCore_elementary_reflection x b)
  rw [norm_mul] at h
  rw [show 1 - conj (etaReflectionStripPoint x b) =
    conj (1 - etaReflectionStripPoint x b) by simp,
    pairedEtaCore_conj, Complex.norm_conj]
  exact h

/-- The exact surviving alternative: high-height mirror collisions are
midline points or common eta zeros.  No zero-free assertion is used. -/
theorem pairedEtaCore_highHeight_mirror_eq_iff (x t : ℝ) :
    let s := etaReflectionStripPoint x (etaArchimedeanHeight t)
    pairedEtaCore s = pairedEtaCore (1 - conj s) ↔
      sigmoid x = 1 / 2 ∨ pairedEtaCore s = 0 := by
  dsimp only
  let s := etaReflectionStripPoint x (etaArchimedeanHeight t)
  have hbalance := norm_pairedEtaCore_mirror_balance x (etaArchimedeanHeight t)
  change ‖pairedEtaCore s‖ = ‖etaElementaryReflectionMultiplier s‖ *
    ‖pairedEtaCore (1 - conj s)‖ at hbalance
  constructor
  · intro h
    by_cases hcenter : sigmoid x = 1 / 2
    · exact Or.inl hcenter
    · right
      have hmod : ‖etaElementaryReflectionMultiplier s‖ ≠ 1 := by
        exact fun hm => hcenter ((norm_etaElementaryReflectionMultiplier_eq_one_iff x t).mp hm)
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
        norm_ne_zero_iff.mpr (etaElementaryReflectionMultiplier_ne_zero x (etaArchimedeanHeight t))
      rw [hzero, norm_zero] at hbalance
      have hp : pairedEtaCore (1 - conj s) = 0 := norm_eq_zero.mp
        ((mul_eq_zero.mp hbalance.symm).resolve_left hmod)
      exact hzero.trans hp.symm

end

end RiemannGaussian
