import GaloisForLFunctions.RHTower.HardyZThetaTrace
import GaloisForLFunctions.RHTower.HardySignChange

/-!
# Hardy-Z sign and moment gaps produce actual critical-line zeta zeros

The generic moment-gap theorem produces only a two-height sign bracket.  Hardy Z is now known to
be continuous and to have exactly the critical-line zeta zeros, so that abstract bracket can be
closed into an actual zeta zero in the same interval.  The positive-theta pair law supplies the
same conclusion from a source-side cosine bracket.
-/

open Complex Real MeasureTheory Set Filter Topology HurwitzZeta
open scoped ENNReal Topology FourierTransform

noncomputable section

namespace RHTower

/-- **Actual finite-carrier zero from the continuous Gamma-oriented sign bracket.**  This is the
branch-free sign interface that the principal-log finite amplitude could not supply before its
square-root ambiguity was resolved. -/
theorem exists_gN_line_zero_of_gammaHardyCarrier_sign_bracket
    {N : ℕ} {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂)
    (hsign : gammaHardyCarrier N t₁ * gammaHardyCarrier N t₂ ≤ 0) :
    ∃ τ ∈ Icc t₁ t₂, gN N (linePt τ) = 0 := by
  have hzero : ∃ τ ∈ Icc t₁ t₂, gammaHardyCarrier N τ = 0 := by
    rcases mul_nonpos_iff.mp hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨τ, hτ, hτzero⟩ :=
        intermediate_value_Icc' h12 (continuous_gammaHardyCarrier N).continuousOn ⟨h2, h1⟩
      exact ⟨τ, hτ, hτzero⟩
    · obtain ⟨τ, hτ, hτzero⟩ :=
        intermediate_value_Icc h12 (continuous_gammaHardyCarrier N).continuousOn ⟨h1, h2⟩
      exact ⟨τ, hτ, hτzero⟩
  obtain ⟨τ, hτ, hτzero⟩ := hzero
  exact ⟨τ, hτ, (gN_line_eq_zero_iff_gammaHardyCarrier N τ).2 hτzero⟩

/-- **Finite-carrier moment gap to an actual on-line zero.**  The Gamma-oriented amplitude
discharges the continuity premise and converts the generic moment bracket into a genuine zero of
the finite Riemann--Siegel carrier. -/
theorem exists_gN_line_zero_of_gammaHardyCarrier_moment_gap
    {N : ℕ} {α β S M_line : ℝ} (hαβ : α ≤ β) (hS : 0 < S)
    (hsupply : S ≤ ∫ u in α..β, (gammaHardyCarrier N u) ^ 2)
    (hsup : ∀ u ∈ Icc α β, |gammaHardyCarrier N u| ≤ M_line)
    (hfm : M_line * |∫ u in α..β, gammaHardyCarrier N u| < S) :
    ∃ τ ∈ Icc α β, gN N (linePt τ) = 0 := by
  obtain ⟨t₁, t₂, ht₁, ht₂, h12, hsign⟩ :=
    exists_sign_bracket_of_moment_gap hαβ (continuous_gammaHardyCarrier N).continuousOn
      hS hsupply hsup hfm
  obtain ⟨τ, hτ, hzero⟩ :=
    exists_gN_line_zero_of_gammaHardyCarrier_sign_bracket h12 hsign
  exact ⟨τ, ⟨le_trans ht₁.1 hτ.1, le_trans hτ.2 ht₂.2⟩, hzero⟩

/-- **Actual critical-line zeta zero from a Hardy-Z sign bracket.** -/
theorem exists_riemannZeta_line_zero_of_hardyZ_sign_bracket
    {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂) (hsign : hardyZ t₁ * hardyZ t₂ ≤ 0) :
    ∃ τ ∈ Icc t₁ t₂, riemannZeta (linePt τ) = 0 := by
  have hzero : ∃ τ ∈ Icc t₁ t₂, hardyZ τ = 0 := by
    rcases mul_nonpos_iff.mp hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨τ, hτ, hZτ⟩ :=
        intermediate_value_Icc' h12 continuous_hardyZ.continuousOn ⟨h2, h1⟩
      exact ⟨τ, hτ, hZτ⟩
    · obtain ⟨τ, hτ, hZτ⟩ :=
        intermediate_value_Icc h12 continuous_hardyZ.continuousOn ⟨h1, h2⟩
      exact ⟨τ, hτ, hZτ⟩
  obtain ⟨τ, hτ, hZτ⟩ := hzero
  exact ⟨τ, hτ, (riemannZeta_line_eq_zero_iff_hardyZ τ).2 hZτ⟩

/-- **Actual critical-line zeta zero from a positive-theta source bracket.**  No continuity
hypothesis on the integral expression is required: the positive scale transfers the bracket to
the already-continuous Hardy Z function. -/
theorem exists_riemannZeta_line_zero_of_thetaCuspCosine_sign_bracket
    {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂)
    (hsign :
      (∫ x : ℝ in Ioi 0, thetaCuspFullSource x * Real.cos (t₁ * x)) *
        (∫ x : ℝ in Ioi 0, thetaCuspFullSource x * Real.cos (t₂ * x)) ≤ 0) :
    ∃ τ ∈ Icc t₁ t₂, riemannZeta (linePt τ) = 0 := by
  exact exists_riemannZeta_line_zero_of_hardyZ_sign_bracket h12
    ((hardyZ_mul_nonpos_iff_thetaCuspCosine_mul_nonpos t₁ t₂).2 hsign)

/-- **Hardy moment gap to an actual zeta zero.**  This closes the generic sign-bracket output of
`exists_sign_bracket_of_moment_gap` through continuity and the exact Hardy-Z/zeta zero interface.
The only remaining premises are the analytic moment supply, line sup, and first-moment gap. -/
theorem exists_riemannZeta_line_zero_of_hardyZ_moment_gap
    {α β S M_line : ℝ} (hαβ : α ≤ β) (hS : 0 < S)
    (hsupply : S ≤ ∫ u in α..β, (hardyZ u) ^ 2)
    (hsup : ∀ u ∈ Icc α β, |hardyZ u| ≤ M_line)
    (hfm : M_line * |∫ u in α..β, hardyZ u| < S) :
    ∃ τ ∈ Icc α β, riemannZeta (linePt τ) = 0 := by
  obtain ⟨t₁, t₂, ht₁, ht₂, h12, hsign⟩ :=
    exists_sign_bracket_of_moment_gap hαβ continuous_hardyZ.continuousOn
      hS hsupply hsup hfm
  obtain ⟨τ, hτ, hzeta⟩ :=
    exists_riemannZeta_line_zero_of_hardyZ_sign_bracket h12 hsign
  exact ⟨τ, ⟨le_trans ht₁.1 hτ.1, le_trans hτ.2 ht₂.2⟩, hzeta⟩

/-! ## Finite symmetrized Euler--Maclaurin sign certificates -/

/-- **One-height certified sign transfer.**  If the finite real symmetrized-EM value clears its
explicit error budget, it has the same strict sign as the actual Hardy Z value. -/
theorem hardyZ_mul_hardySEM_pos_of_error_lt_abs
    {N : ℕ} (hN : 1 ≤ N) {τ : ℝ}
    (hmargin : hardySEMError N τ < |hardySEM N τ|) :
    0 < hardyZ τ * hardySEM N τ := by
  have hbound := abs_hardyZ_sub_hardySEM_le hN τ
  have hE : 0 ≤ hardySEMError N τ := le_trans (abs_nonneg _) hbound
  rcases lt_trichotomy (hardySEM N τ) 0 with hneg | hzero | hpos
  · rw [abs_of_neg hneg] at hmargin
    have hupper : hardyZ τ - hardySEM N τ ≤ hardySEMError N τ :=
      le_trans (le_abs_self _) hbound
    have hzneg : hardyZ τ < 0 := by nlinarith
    exact mul_pos_of_neg_of_neg hzneg hneg
  · rw [hzero, abs_zero] at hmargin
    linarith
  · rw [abs_of_pos hpos] at hmargin
    have hlower : -hardySEMError N τ ≤ hardyZ τ - hardySEM N τ :=
      le_trans (neg_le_neg hbound) (neg_abs_le _)
    have hzpos : 0 < hardyZ τ := by nlinarith
    exact mul_pos hzpos hpos

/-- Two certified finite values have opposite signs exactly when the corresponding actual Hardy-Z
values do.  This is the orientation-free pair interface for finite zero certificates. -/
theorem hardyZ_pair_neg_iff_hardySEM_pair_neg_of_error_margins
    {N : ℕ} (hN : 1 ≤ N) {t₁ t₂ : ℝ}
    (hmargin₁ : hardySEMError N t₁ < |hardySEM N t₁|)
    (hmargin₂ : hardySEMError N t₂ < |hardySEM N t₂|) :
    hardyZ t₁ * hardyZ t₂ < 0 ↔ hardySEM N t₁ * hardySEM N t₂ < 0 := by
  have hsame₁ := hardyZ_mul_hardySEM_pos_of_error_lt_abs hN hmargin₁
  have hsame₂ := hardyZ_mul_hardySEM_pos_of_error_lt_abs hN hmargin₂
  have hpair : 0 <
      (hardyZ t₁ * hardyZ t₂) * (hardySEM N t₁ * hardySEM N t₂) := by
    calc
      0 < (hardyZ t₁ * hardySEM N t₁) *
          (hardyZ t₂ * hardySEM N t₂) := mul_pos hsame₁ hsame₂
      _ = (hardyZ t₁ * hardyZ t₂) *
          (hardySEM N t₁ * hardySEM N t₂) := by ring
  constructor <;> intro h <;> nlinarith

/-- **Exact finite certificate for a strict Hardy sign bracket.**  Two actual Hardy values have
opposite signs exactly when one common finite symmetrized-EM level clears both explicit error
budgets and has opposite signs.  Completeness follows from pointwise convergence at the two
nonzero endpoints; no cutoff is computed. -/
theorem hardyZ_pair_neg_iff_exists_hardySEM_certified_pair (t₁ t₂ : ℝ) :
    hardyZ t₁ * hardyZ t₂ < 0 ↔
      ∃ N : ℕ, 1 ≤ N ∧
        hardySEMError N t₁ < |hardySEM N t₁| ∧
        hardySEMError N t₂ < |hardySEM N t₂| ∧
        hardySEM N t₁ * hardySEM N t₂ < 0 := by
  constructor
  · intro hsign
    have hZ₁ : hardyZ t₁ ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hsign
      exact (lt_irrefl 0) hsign
    have hZ₂ : hardyZ t₂ ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hsign
      exact (lt_irrefl 0) hsign
    have hcert : ∀ᶠ N : ℕ in atTop,
        1 ≤ N ∧ hardySEMError N t₁ < |hardySEM N t₁| ∧
          hardySEMError N t₂ < |hardySEM N t₂| :=
      (eventually_ge_atTop 1).and
        ((eventually_hardySEMError_lt_abs_of_hardyZ_ne_zero hZ₁).and
          (eventually_hardySEMError_lt_abs_of_hardyZ_ne_zero hZ₂))
    obtain ⟨N, hN, hmargin₁, hmargin₂⟩ := hcert.exists
    exact ⟨N, hN, hmargin₁, hmargin₂,
      (hardyZ_pair_neg_iff_hardySEM_pair_neg_of_error_margins
        hN hmargin₁ hmargin₂).mp hsign⟩
  · rintro ⟨N, hN, hmargin₁, hmargin₂, hsign⟩
    exact (hardyZ_pair_neg_iff_hardySEM_pair_neg_of_error_margins
      hN hmargin₁ hmargin₂).mpr hsign

/-- **Exact positive-source finite sign certificate.**  A pair of positive-theta cosine traces
has opposite signs exactly when one common finite symmetrized-EM level certifies the bracket. -/
theorem thetaCuspCosine_pair_neg_iff_exists_hardySEM_certified_pair (t₁ t₂ : ℝ) :
    ( ∫ x : ℝ in Ioi 0, thetaCuspFullSource x * Real.cos (t₁ * x)) *
        (∫ x : ℝ in Ioi 0, thetaCuspFullSource x * Real.cos (t₂ * x)) < 0 ↔
      ∃ N : ℕ, 1 ≤ N ∧
        hardySEMError N t₁ < |hardySEM N t₁| ∧
        hardySEMError N t₂ < |hardySEM N t₂| ∧
        hardySEM N t₁ * hardySEM N t₂ < 0 := by
  exact (hardyZ_mul_neg_iff_thetaCuspCosine_mul_neg t₁ t₂).symm.trans
    (hardyZ_pair_neg_iff_exists_hardySEM_certified_pair t₁ t₂)

/-- **Finite symmetrized-EM certificate for an actual critical-line zeta zero.**  Two finite
real approximant values of opposite sign, each clearing the explicit pointwise error budget,
force a genuine zeta zero between their heights. -/
theorem exists_riemannZeta_line_zero_of_hardySEM_certified_sign_bracket
    {N : ℕ} (hN : 1 ≤ N) {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂)
    (hmargin₁ : hardySEMError N t₁ < |hardySEM N t₁|)
    (hmargin₂ : hardySEMError N t₂ < |hardySEM N t₂|)
    (hsign : hardySEM N t₁ * hardySEM N t₂ < 0) :
    ∃ τ ∈ Icc t₁ t₂, riemannZeta (linePt τ) = 0 := by
  apply exists_riemannZeta_line_zero_of_hardyZ_sign_bracket h12
  exact (hardyZ_pair_neg_iff_hardySEM_pair_neg_of_error_margins
    hN hmargin₁ hmargin₂).2 hsign |>.le

end RHTower
