import GaloisForLFunctions.HTGeometry.LongitudinalTransverseFormationMechanics
import GaloisForLFunctions.HTGeometry.ConstitutiveGlobalFormationProperness
import GaloisForLFunctions.RHTower.CompleteResolutionSummableLanding

/-!
# Constitutive formation-depth properness

This module certifies the source-level global formation/properness mechanism from
`source-depth-graph-properness-and-cofinal-mixer-selection-law.md`.
-/

open scoped BigOperators
open Complex Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

/-- Depth generator on a source history. -/
def formationDepthSequence (x : ℕ → ℂ) : ℕ → ℂ :=
  fun n => (n : ℂ) * x n

/-- Source codiagonal. -/
def formationMass (x : ℕ → ℂ) : ℂ := ∑' n, x n

/-- Absolute graph work of the depth generator. -/
def formationDepthWork (x : ℕ → ℂ) : ℝ :=
  ∑' n, ‖formationDepthSequence x n‖

/-- Formation gauge coupling longitudinal mass and depth work. -/
def formationGauge (x : ℕ → ℂ) : ℝ :=
  ‖formationMass x‖ + 2 * formationDepthWork x

/-- The formation gauge controls the full source norm. -/
theorem tsum_norm_le_formationGauge
    (x : ℕ → ℂ) (hx : Summable x)
    (hDx : Summable (formationDepthSequence x)) :
    (∑' n, ‖x n‖) ≤ formationGauge x := by
  have hxnorm : Summable (fun n => ‖x n‖) := hx.norm
  have hDnorm : Summable (fun n => ‖formationDepthSequence x n‖) := hDx.norm
  have hmassSplit : formationMass x = x 0 + ∑' n, x (n + 1) := by
    simpa [formationMass] using (hx.sum_add_tsum_nat_add 1).symm
  have hnormSplit : (∑' n, ‖x n‖) = ‖x 0‖ + ∑' n, ‖x (n + 1)‖ := by
    simpa using (hxnorm.sum_add_tsum_nat_add 1).symm
  have hdepthSplit :
      formationDepthWork x = ∑' n, ‖formationDepthSequence x (n + 1)‖ := by
    have h := (hDnorm.sum_add_tsum_nat_add 1).symm
    simpa [formationDepthWork, formationDepthSequence] using h
  have htailSummable : Summable (fun n => ‖x (n + 1)‖) :=
    (summable_nat_add_iff 1).2 hxnorm
  have hdepthTailSummable :
      Summable (fun n => ‖formationDepthSequence x (n + 1)‖) :=
    (summable_nat_add_iff 1).2 hDnorm
  have htail :
      (∑' n, ‖x (n + 1)‖) ≤ formationDepthWork x := by
    rw [hdepthSplit]
    apply Summable.tsum_le_tsum _ htailSummable hdepthTailSummable
    intro n
    simp only [formationDepthSequence, norm_mul, norm_natCast]
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    calc
      ‖x (n + 1)‖ = 1 * ‖x (n + 1)‖ := by ring
      _ ≤ ((n + 1 : ℕ) : ℝ) * ‖x (n + 1)‖ :=
        mul_le_mul_of_nonneg_right hn (norm_nonneg _)
  have hx0 : ‖x 0‖ ≤ ‖formationMass x‖ + ∑' n, ‖x (n + 1)‖ := by
    have hsub : x 0 = formationMass x - ∑' n, x (n + 1) := by
      rw [hmassSplit]
      abel
    rw [hsub]
    have htri := norm_sub_le (formationMass x) (∑' n, x (n + 1))
    have hnormTail :=
      norm_tsum_le_tsum_norm ((summable_nat_add_iff 1).2 hx).norm
    linarith
  rw [hnormSplit, formationGauge]
  linarith

/-- Codiagonal and depth generator are jointly faithful. -/
theorem formation_joint_kernel
    (x : ℕ → ℂ) (hx : Summable x) :
    (formationMass x = 0 ∧ formationDepthSequence x = 0) ↔ x = 0 := by
  constructor
  · rintro ⟨hmass, hdepth⟩
    have hsucc : ∀ n : ℕ, x (n + 1) = 0 := by
      intro n
      have h := congrFun hdepth (n + 1)
      simp only [formationDepthSequence, Pi.zero_apply] at h
      exact (mul_eq_zero.mp h).resolve_left (by
        exact_mod_cast Nat.succ_ne_zero n)
    have hmassSplit : formationMass x = x 0 + ∑' n, x (n + 1) := by
      simpa [formationMass] using (hx.sum_add_tsum_nat_add 1).symm
    have hx0 : x 0 = 0 := by
      rw [hmassSplit, tsum_congr hsucc, tsum_zero, add_zero] at hmass
      exact hmass
    funext n
    cases n with
    | zero => simpa using hx0
    | succ n => simpa using hsucc n
  · rintro rfl
    constructor
    · simp [formationMass]
    · funext n
      simp [formationDepthSequence]

theorem formationGauge_nonneg (x : ℕ → ℂ) : 0 ≤ formationGauge x := by
  apply add_nonneg (norm_nonneg _)
  exact mul_nonneg (by norm_num) (tsum_nonneg fun _ => norm_nonneg _)

/-- Formation gauge vanishes exactly on neutral source history. -/
theorem formationGauge_eq_zero_iff
    (x : ℕ → ℂ) (hx : Summable x)
    (hDx : Summable (formationDepthSequence x)) :
    formationGauge x = 0 ↔ x = 0 := by
  constructor
  · intro hzero
    have hnorm := tsum_norm_le_formationGauge x hx hDx
    rw [hzero] at hnorm
    have hsumZero : (∑' n, ‖x n‖) = 0 :=
      le_antisymm hnorm (tsum_nonneg fun _ => norm_nonneg _)
    funext n
    have hnle : ‖x n‖ ≤ ∑' j, ‖x j‖ := by
      simpa using hx.norm.sum_le_tsum {n} (fun _ _ => norm_nonneg _)
    rw [hsumZero] at hnle
    exact norm_eq_zero.mp (le_antisymm hnle (norm_nonneg _))
  · rintro rfl
    simp [formationGauge, formationMass, formationDepthWork,
      formationDepthSequence]

theorem formationMass_smul (a : ℂ) (x : ℕ → ℂ) :
    formationMass (fun n => a * x n) = a * formationMass x := by
  simp [formationMass, tsum_mul_left]

theorem formationDepthWork_smul (a : ℂ) (x : ℕ → ℂ) :
    formationDepthWork (fun n => a * x n) = ‖a‖ * formationDepthWork x := by
  calc
    formationDepthWork (fun n => a * x n) =
        ∑' n, ‖a‖ * ‖formationDepthSequence x n‖ := by
          apply tsum_congr
          intro n
          simp only [formationDepthSequence, norm_mul, norm_natCast]
          ring
    _ = ‖a‖ * formationDepthWork x := by
      rw [formationDepthWork, tsum_mul_left]

/-- Formation gauge is absolutely homogeneous. -/
theorem formationGauge_smul (a : ℂ) (x : ℕ → ℂ) :
    formationGauge (fun n => a * x n) = ‖a‖ * formationGauge x := by
  unfold formationGauge
  rw [formationMass_smul, formationDepthWork_smul, norm_mul]
  ring

/-- Expanding scalar formation orbit. -/
def formationScaleOrbit (d : ℝ) (n : ℕ) (x : ℕ → ℂ) : ℕ → ℂ :=
  fun j => ((d ^ n : ℝ) : ℂ) * x j

def BoundedFormationGaugeOrbit (d : ℝ) (x : ℕ → ℂ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, formationGauge (formationScaleOrbit d n x) ≤ C

theorem formationGauge_scaleOrbit (d : ℝ) (n : ℕ) (x : ℕ → ℂ)
    (hd : 0 ≤ d) :
    formationGauge (formationScaleOrbit d n x) = d ^ n * formationGauge x := by
  change formationGauge (fun j => ((d ^ n : ℝ) : ℂ) * x j) = _
  rw [formationGauge_smul]
  simp [Real.norm_eq_abs, abs_of_nonneg hd]

/-- Global properness/selection: bounded work on an expanding formation orbit is equivalent to
neutral source history. -/
theorem boundedFormationGaugeOrbit_iff
    {d : ℝ} (hd : 1 < d) (x : ℕ → ℂ)
    (hx : Summable x) (hDx : Summable (formationDepthSequence x)) :
    BoundedFormationGaugeOrbit d x ↔ x = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hxne
    have hgauge : 0 < formationGauge x :=
      lt_of_le_of_ne (formationGauge_nonneg x)
        (Ne.symm (mt (formationGauge_eq_zero_iff x hx hDx).mp hxne))
    have hescape := scaleOrbit_tendsto hd hgauge
    obtain ⟨n, hn⟩ := (hescape.eventually_gt_atTop C).exists
    have hbound := hC n
    rw [formationGauge_scaleOrbit d n x (le_trans (by norm_num) hd.le)] at hbound
    linarith
  · rintro rfl
    refine ⟨0, ?_⟩
    intro n
    simp [formationScaleOrbit, formationGauge, formationMass,
      formationDepthWork, formationDepthSequence]

/-- Cofinal source tail. -/
def formationTail (x : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑' n, ‖x (n + N)‖

/-- Depth work controls every cofinal tail with the sharp factor `N`. -/
theorem formationTail_mul_le_depthWork
    (x : ℕ → ℂ) (hx : Summable x)
    (hDx : Summable (formationDepthSequence x)) (N : ℕ) :
    (N : ℝ) * formationTail x N ≤ formationDepthWork x := by
  have hxnorm : Summable (fun n => ‖x n‖) := hx.norm
  have hDnorm : Summable (fun n => ‖formationDepthSequence x n‖) := hDx.norm
  have htailx : Summable (fun n => ‖x (n + N)‖) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff N).2 hxnorm
  have htailD : Summable (fun n => ‖formationDepthSequence x (n + N)‖) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff N).2 hDnorm
  have hweightedTail :
      (N : ℝ) * formationTail x N ≤
        ∑' n, ‖formationDepthSequence x (n + N)‖ := by
    rw [formationTail, ← tsum_mul_left]
    apply Summable.tsum_le_tsum _ (htailx.mul_left (N : ℝ)) htailD
    intro n
    simp only [formationDepthSequence, norm_mul, norm_natCast]
    have hN : (N : ℝ) ≤ ((n + N : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left N n
    exact mul_le_mul_of_nonneg_right hN (norm_nonneg _)
  have htail_le_full :
      (∑' n, ‖formationDepthSequence x (n + N)‖) ≤ formationDepthWork x := by
    have hsplit := hDnorm.sum_add_tsum_nat_add N
    have hfinite :
        0 ≤ ∑ n ∈ Finset.range N, ‖formationDepthSequence x n‖ := by
      positivity
    rw [formationDepthWork]
    linarith
  exact hweightedTail.trans htail_le_full

theorem formationTail_le_depthWork_div
    (x : ℕ → ℂ) (hx : Summable x)
    (hDx : Summable (formationDepthSequence x)) {N : ℕ} (hN : 0 < N) :
    formationTail x N ≤ formationDepthWork x / N := by
  have h := formationTail_mul_le_depthWork x hx hDx N
  exact (le_div_iff₀ (by exact_mod_cast hN)).2 (by simpa [mul_comm] using h)

/-! ## Literal complete-resolution formation mixer -/

/-- Complete-resolution vector lies in the depth-generator graph domain. -/
theorem summable_weighted_completeResolutionMultiplier
    (K : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun j : ℕ => (j : ℂ) * RHTower.completeResolutionMultiplier K j s) := by
  let b : ℕ → ℂ := fun n =>
    ((n + 1 : ℕ) : ℂ) * RHTower.completeResolutionMultiplier K (n + 1) s
  have hscaled_ne :
      ∀ᶠ n : ℕ in atTop,
        (2 : ℂ) ^ ((n : ℂ) * s) * RHTower.shellMultiplier n s ≠ 0 :=
    (RHTower.tendsto_two_cpow_nat_mul_shellMultiplier hs).eventually_ne
      (RHTower.one_sub_two_cpow_neg_ne_zero hs)
  have hshell_ne : ∀ᶠ n : ℕ in atTop, RHTower.shellMultiplier n s ≠ 0 := by
    filter_upwards [hscaled_ne] with n hn
    exact (mul_ne_zero_iff.mp hn).2
  have hshift_ne :
      ∀ᶠ n : ℕ in atTop, RHTower.shellMultiplier (K + n) s ≠ 0 := by
    have hK : Tendsto (fun n : ℕ => K + n) atTop atTop := by
      simpa [Nat.add_comm] using tendsto_add_atTop_nat K
    exact hK.eventually hshell_ne
  have hb_ne : ∀ᶠ n : ℕ in atTop, b n ≠ 0 := by
    filter_upwards [hshift_ne] with n hn
    exact mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero n) (by
      simpa [b, RHTower.completeResolutionMultiplier] using hn)
  have hlinear :
      Tendsto (fun n : ℕ => (((n + 2 : ℕ) : ℂ) / ((n + 1 : ℕ) : ℂ)))
        atTop (nhds 1) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (tendsto_add_mul_div_add_mul_atTop_nhds
        (2 : ℂ) 1 1 (d := 1) one_ne_zero)
  have hshellRatio :
      Tendsto (fun n : ℕ => RHTower.shellAdjacentTransfer (K + n) s)
        atTop (nhds ((2 : ℂ) ^ (-s))) := by
    have hK : Tendsto (fun n : ℕ => K + n) atTop atTop := by
      simpa [Nat.add_comm] using tendsto_add_atTop_nat K
    exact (RHTower.tendsto_shellAdjacentTransfer hs).comp hK
  have hratio :
      Tendsto (fun n : ℕ => b (n + 1) / b n)
        atTop (nhds ((2 : ℂ) ^ (-s))) := by
    have hmul := hlinear.mul hshellRatio
    have heq :
        (fun n : ℕ => b (n + 1) / b n) =ᶠ[atTop]
          (fun n : ℕ =>
            (((n + 2 : ℕ) : ℂ) / ((n + 1 : ℕ) : ℂ)) *
              RHTower.shellAdjacentTransfer (K + n) s) := by
      filter_upwards [hshift_ne] with n hn
      simp only [b, RHTower.completeResolutionMultiplier,
        RHTower.shellAdjacentTransfer]
      field_simp
      ring
    have hraw := hmul.congr' heq.symm
    simpa using hraw
  have hnorm_lt : ‖(2 : ℂ) ^ (-s)‖ < 1 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (by simp only [Complex.neg_re]; linarith)
  have hb : Summable b := by
    apply summable_of_ratio_test_tendsto_lt_one hnorm_lt hb_ne
    simpa [norm_div] using hratio.norm
  apply (summable_nat_add_iff 1).1
  simpa [b] using hb

/-- Terminal finite-aperture flux vanishes cofinally. -/
theorem tendsto_completeResolution_boundary_zero
    (K : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun N : ℕ =>
        (N : ℂ) *
          ((riemannZeta (((K + N : ℕ) : ℂ) * s))⁻¹ - 1))
      atTop (nhds 0) := by
  let q : ℂ := (2 : ℂ) ^ (-s)
  have hqnorm : ‖q‖ < 1 := by
    dsimp [q]
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (by simp only [Complex.neg_re]; linarith)
  have hdecayNorm :
      Tendsto (fun n : ℕ => ‖((n : ℂ) * q ^ n)‖) atTop (nhds 0) := by
    simpa [norm_mul, norm_pow, Complex.norm_natCast] using
      (tendsto_self_mul_const_pow_of_lt_one (norm_nonneg q) hqnorm)
  have hdecay : Tendsto (fun n : ℕ => (n : ℂ) * q ^ n) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hdecayNorm
  have hKdecay :
      Tendsto
        (fun n : ℕ => (2 : ℂ) ^ (-((K : ℂ) * s)) * ((n : ℂ) * q ^ n))
        atTop (nhds 0) := by
    simpa using hdecay.const_mul ((2 : ℂ) ^ (-((K : ℂ) * s)))
  have hnormalized :
      Tendsto
        (fun n : ℕ =>
          (2 : ℂ) ^ (((K + n : ℕ) : ℂ) * s) *
            ((riemannZeta (((K + n : ℕ) : ℂ) * s))⁻¹ - 1))
        atTop (nhds (-1)) := by
    have hK : Tendsto (fun n : ℕ => K + n) atTop atTop := by
      simpa [Nat.add_comm] using tendsto_add_atTop_nat K
    exact
      (RHTower.tendsto_two_cpow_nat_mul_inv_riemannZeta_sub_one hs).comp hK
  have hprod := hKdecay.mul hnormalized
  have heq :
      (fun N : ℕ =>
        (N : ℂ) * ((riemannZeta (((K + N : ℕ) : ℂ) * s))⁻¹ - 1)) =ᶠ[atTop]
      (fun N : ℕ =>
        ((2 : ℂ) ^ (-((K : ℂ) * s)) * ((N : ℂ) * q ^ N)) *
          ((2 : ℂ) ^ (((K + N : ℕ) : ℂ) * s) *
            ((riemannZeta (((K + N : ℕ) : ℂ) * s))⁻¹ - 1))) := by
    filter_upwards [] with n
    dsimp [q]
    rw [← Complex.cpow_nat_mul]
    have hpow :
        (2 : ℂ) ^ (-((K : ℂ) * s)) *
            (2 : ℂ) ^ ((n : ℂ) * (-s)) *
            (2 : ℂ) ^ (((K + n : ℕ) : ℂ) * s) = 1 := by
      rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0),
        ← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
      have hexp :
          -((K : ℂ) * s) + (n : ℂ) * (-s) +
              ((K + n : ℕ) : ℂ) * s = 0 := by
        push_cast
        ring
      rw [hexp, Complex.cpow_zero]
    calc
      (n : ℂ) * ((riemannZeta (((K + n : ℕ) : ℂ) * s))⁻¹ - 1) =
          (n : ℂ) * 1 *
            ((riemannZeta (((K + n : ℕ) : ℂ) * s))⁻¹ - 1) := by ring
      _ = _ := by rw [← hpow]; ring
  have hraw := hprod.congr' heq.symm
  simpa using hraw

/-- Accumulated reciprocal-zeta deficit. -/
def completeResolutionDeficit (K : ℕ) (s : ℂ) (j : ℕ) : ℂ :=
  1 - (riemannZeta (((K + j : ℕ) : ℂ) * s))⁻¹

theorem summable_completeResolutionDeficit
    (K : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Summable (completeResolutionDeficit K s) := by
  let B : ℕ → ℂ := fun n =>
    (2 : ℂ) ^ (((K + n : ℕ) : ℂ) * s) * completeResolutionDeficit K s n
  have hK : Tendsto (fun n : ℕ => K + n) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat K
  have hB : Tendsto B atTop (nhds 1) := by
    have h :=
      (RHTower.tendsto_two_cpow_nat_mul_inv_riemannZeta_sub_one hs).comp hK
    convert h.neg using 1
    · funext n
      dsimp [B, completeResolutionDeficit]
      ring
    · norm_num
  have hB_ne : ∀ᶠ n : ℕ in atTop, B n ≠ 0 := hB.eventually_ne one_ne_zero
  have hf_ne : ∀ᶠ n : ℕ in atTop, completeResolutionDeficit K s n ≠ 0 := by
    filter_upwards [hB_ne] with n hn
    exact (mul_ne_zero_iff.mp hn).2
  have hBsucc : Tendsto (fun n : ℕ => B (n + 1)) atTop (nhds 1) :=
    hB.comp (by simpa [Nat.add_comm] using tendsto_add_atTop_nat 1)
  have hBratio : Tendsto (fun n : ℕ => B (n + 1) / B n) atTop (nhds 1) := by
    change Tendsto ((fun n : ℕ => B (n + 1)) / B) atTop (nhds 1)
    simpa using hBsucc.div hB one_ne_zero
  let q : ℂ := (2 : ℂ) ^ (-s)
  have hratioRaw :
      Tendsto (fun n : ℕ => q * (B (n + 1) / B n)) atTop (nhds q) := by
    simpa using tendsto_const_nhds.mul hBratio
  have hratio :
      Tendsto
        (fun n : ℕ =>
          completeResolutionDeficit K s (n + 1) /
            completeResolutionDeficit K s n)
        atTop (nhds q) := by
    have heq :
        (fun n : ℕ =>
          completeResolutionDeficit K s (n + 1) /
            completeResolutionDeficit K s n) =ᶠ[atTop]
        (fun n : ℕ => q * (B (n + 1) / B n)) := by
      filter_upwards [hf_ne] with n hn
      dsimp [B, q]
      have hpow :
          (2 : ℂ) ^ (-s) *
              (2 : ℂ) ^ (((K + (n + 1) : ℕ) : ℂ) * s) =
            (2 : ℂ) ^ (((K + n : ℕ) : ℂ) * s) := by
        rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
        congr 2
        push_cast
        ring
      field_simp [hn]
      rw [mul_comm s (((K + n : ℕ) : ℂ)),
        mul_comm s (((K + (n + 1) : ℕ) : ℂ))]
      calc
        completeResolutionDeficit K s (n + 1) *
            (2 : ℂ) ^ (((K + n : ℕ) : ℂ) * s) =
          completeResolutionDeficit K s (n + 1) *
            ((2 : ℂ) ^ (-s) *
              (2 : ℂ) ^ (((K + (n + 1) : ℕ) : ℂ) * s)) := by rw [hpow]
        _ = _ := by ring
    exact hratioRaw.congr' heq.symm
  have hqnorm : ‖q‖ < 1 := by
    dsimp [q]
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (by simp only [Complex.neg_re]; linarith)
  apply summable_of_ratio_test_tendsto_lt_one hqnorm hf_ne
  simpa [norm_div] using hratio.norm

/-- Infinite formation-generation conservation: depth-weighted source formation equals the
cofinal accumulated reciprocal-zeta deficit. -/
theorem hasSum_completeResolutionDeficit_eq_weighted
    (K : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasSum (completeResolutionDeficit K s)
      (∑' j : ℕ, (j : ℂ) * RHTower.completeResolutionMultiplier K j s) := by
  have hdef := summable_completeResolutionDeficit K hs
  refine hdef.hasSum_iff_tendsto_nat.mpr ?_
  have hweighted :=
    (summable_weighted_completeResolutionMultiplier K hs).hasSum_iff_tendsto_nat.mp
      (summable_weighted_completeResolutionMultiplier K hs).hasSum
  have hweightedSucc :
      Tendsto
        (fun N : ℕ => ∑ i ∈ Finset.range (N + 1),
          (i : ℂ) * RHTower.completeResolutionMultiplier K i s)
        atTop
        (nhds (∑' j : ℕ,
          (j : ℂ) * RHTower.completeResolutionMultiplier K j s)) := by
    exact hweighted.comp (by simpa [Nat.add_comm] using tendsto_add_atTop_nat 1)
  have hboundary := tendsto_completeResolution_boundary_zero K hs
  have hdiff := hweightedSucc.sub hboundary
  have heq :
      (fun N : ℕ =>
        ∑ i ∈ Finset.range N, completeResolutionDeficit K s i) =ᶠ[atTop]
      (fun N : ℕ =>
        (∑ i ∈ Finset.range (N + 1),
          (i : ℂ) * RHTower.completeResolutionMultiplier K i s) -
          (N : ℂ) *
            ((riemannZeta (((K + N : ℕ) : ℂ) * s))⁻¹ - 1)) := by
    filter_upwards [] with N
    rw [completeResolution_weightedFusion_conservation]
    simp only [completeResolutionDeficit]
    ring
  have hraw := hdiff.congr' heq.symm
  simpa using hraw

end

end GaloisForLFunctions.HTGeometry
