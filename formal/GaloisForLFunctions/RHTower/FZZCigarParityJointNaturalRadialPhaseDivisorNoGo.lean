import GaloisForLFunctions.RHTower.FZZCigarParityIndependentRadialPhaseIncidenceClassification
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem

/-!
# Canonical radial-phase no-go for the joint FZZ parity source encoding

The pair-valued FZZ source survivor combines the strict Fermi radial clock and fixed-quintic phase
at one positive physical scale. This module compares that report with the canonical polar
decomposition of the centered dyadic Mellin character.

The radial comparison is sharp: a natural target radius occurs at a positive source scale exactly
in the strict left chamber `Re rho < 1/2`, and then the scale is unique. Hence the joint report is a
one-sided horizontal-chamber chart, not a neutral lost-scale repair.

Hardy's unconditional dyadic-window theorem then supplies, above every height, an actual
critical-line zeta zero. Exact FZZ/zeta divisor comparison makes it a literal parity-Mellin mode.
Its natural target radius is one, while every positive-scale source radius is strictly below one.
Thus cofinally many actual modes miss the full joint source report at every positive scale, even
when each mode may choose its scale independently.

This kills the canonical pair-valued landing arrow in the chain

`literal FZZ parity-delay source -> joint radial/phase divisor landing -> FZZ-P -> RH`.

`[NEW] [FZZ-P ROUTE-CLASS KILL] [COFINAL DIVISOR ESCAPE]
[POSITIVE CHAMBER SURVIVOR] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Canonical polar decomposition of the centered dyadic Mellin character. -/
def fzzCigarParityNaturalMellinRadialPhaseTarget (rho : ℂ) : ℝ × ℂ :=
  (‖fzzCigarParityDyadicMellinCharacter rho‖,
    fzzCigarParityDyadicMellinCharacter rho /
      (‖fzzCigarParityDyadicMellinCharacter rho‖ : ℂ))

theorem norm_fzzCigarParityNaturalMellinRadialPhaseTarget_phase
    (rho : ℂ) :
    ‖(fzzCigarParityNaturalMellinRadialPhaseTarget rho).2‖ = 1 := by
  rw [fzzCigarParityNaturalMellinRadialPhaseTarget, norm_div,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (norm_fzzCigarParityDyadicMellinCharacter_pos rho)]
  exact div_self (norm_fzzCigarParityDyadicMellinCharacter_pos rho).ne'

theorem fzzCigarParityNaturalMellinRadialPhaseTarget_reconstructs
    (rho : ℂ) :
    ((fzzCigarParityNaturalMellinRadialPhaseTarget rho).1 : ℂ) *
        (fzzCigarParityNaturalMellinRadialPhaseTarget rho).2 =
      fzzCigarParityDyadicMellinCharacter rho := by
  change (‖fzzCigarParityDyadicMellinCharacter rho‖ : ℂ) *
      (fzzCigarParityDyadicMellinCharacter rho /
        (‖fzzCigarParityDyadicMellinCharacter rho‖ : ℂ)) =
    fzzCigarParityDyadicMellinCharacter rho
  have hn : (‖fzzCigarParityDyadicMellinCharacter rho‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_fzzCigarParityDyadicMellinCharacter_pos rho).ne'
  field_simp [hn]

/-- First-coordinate incidence of the literal joint source report with the natural Mellin radius. -/
def FZZCigarParityJointQuinticNaturalRadialIncident (rho : ℂ) : Prop :=
  ∃ beta : ℝ, 0 < beta ∧
    (fzzCigarParityJointQuinticRadialEncoding beta).1 =
      (fzzCigarParityNaturalMellinRadialPhaseTarget rho).1

/-- Full pair-valued incidence of the literal joint source report with the natural Mellin target. -/
def FZZCigarParityJointQuinticNaturalRadialPhaseIncident (rho : ℂ) : Prop :=
  ∃ beta : ℝ, 0 < beta ∧
    fzzCigarParityJointQuinticRadialEncoding beta =
      fzzCigarParityNaturalMellinRadialPhaseTarget rho

/-- Sharp positive survivor: the joint source radius lands exactly in the left Mellin chamber. -/
theorem fzzCigarParityJointQuinticNaturalRadialIncident_iff (rho : ℂ) :
    FZZCigarParityJointQuinticNaturalRadialIncident rho ↔ rho.re < 1 / 2 := by
  constructor
  · rintro ⟨beta, hbeta, hmatch⟩
    change fzzCigarParityIndependentFermiRadial beta =
      ‖fzzCigarParityDyadicMellinCharacter rho‖ at hmatch
    have hlt : ‖fzzCigarParityDyadicMellinCharacter rho‖ < 1 := by
      rw [← hmatch]
      exact fzzCigarParityIndependentFermiRadial_lt_one hbeta
    rw [norm_fzzCigarParityDyadicMellinCharacter, Real.exp_lt_one_iff] at hlt
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  · intro hre
    have hnormlt : ‖fzzCigarParityDyadicMellinCharacter rho‖ < 1 := by
      rw [norm_fzzCigarParityDyadicMellinCharacter, Real.exp_lt_one_iff]
      have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
      nlinarith
    obtain ⟨beta, ⟨hbeta, hradial⟩, _⟩ :=
      existsUnique_pos_fzzCigarParityKreinEigenline_neg_re_eq
        (norm_fzzCigarParityDyadicMellinCharacter_pos rho) hnormlt
    refine ⟨beta, hbeta, ?_⟩
    exact hradial

/-- The left-chamber target radius determines one unique positive physical source scale. -/
theorem existsUnique_fzzCigarParityJointQuinticNaturalRadialIncident
    {rho : ℂ} (hre : rho.re < 1 / 2) :
    ∃! beta : ℝ, 0 < beta ∧
      (fzzCigarParityJointQuinticRadialEncoding beta).1 =
        (fzzCigarParityNaturalMellinRadialPhaseTarget rho).1 := by
  have hnormlt : ‖fzzCigarParityDyadicMellinCharacter rho‖ < 1 := by
    rw [norm_fzzCigarParityDyadicMellinCharacter, Real.exp_lt_one_iff]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  simpa [fzzCigarParityJointQuinticRadialEncoding,
    fzzCigarParityNaturalMellinRadialPhaseTarget] using
    (existsUnique_pos_fzzCigarParityKreinEigenline_neg_re_eq
      (norm_fzzCigarParityDyadicMellinCharacter_pos rho) hnormlt)

theorem fzzCigarParityJointQuinticNaturalRadialPhaseIncident_forces_left
    {rho : ℂ} (hincident :
      FZZCigarParityJointQuinticNaturalRadialPhaseIncident rho) :
    rho.re < 1 / 2 := by
  apply (fzzCigarParityJointQuinticNaturalRadialIncident_iff rho).mp
  obtain ⟨beta, hbeta, hmatch⟩ := hincident
  exact ⟨beta, hbeta, congrArg Prod.fst hmatch⟩

theorem not_fzzCigarParityJointQuinticNaturalRadialPhaseIncident_of_re_eq_half
    {rho : ℂ} (hre : rho.re = 1 / 2) :
    ¬FZZCigarParityJointQuinticNaturalRadialPhaseIncident rho := by
  intro hincident
  have hleft :=
    fzzCigarParityJointQuinticNaturalRadialPhaseIncident_forces_left hincident
  linarith

/-- Every sufficiently high range contains an actual critical divisor mode escaping the joint
source report at every positive physical scale. -/
theorem exists_fzzCigarParityMellinMode_not_jointQuinticNaturalRadialPhase_above
    (H : ℝ) :
    ∃ rho : ℂ,
      riemannZeta rho = 0 ∧ 0 < rho.re ∧ rho.re < 1 ∧ H < rho.im ∧
        FZZCigarParityMellinMode rho ∧
          ∀ beta : ℝ, 0 < beta →
            fzzCigarParityJointQuinticRadialEncoding beta ≠
              fzzCigarParityNaturalMellinRadialPhaseTarget rho := by
  obtain ⟨T0, hT0, hwindow⟩ := exists_riemannZeta_line_zero_dyadic
  let T := max T0 (H + 1)
  have hT0le : T0 ≤ T := le_max_left _ _
  obtain ⟨tau, htau, hzero⟩ := hwindow T hT0le
  have hHtau : H < tau := by
    have hHT : H + 1 ≤ T := le_max_right _ _
    exact lt_of_lt_of_le (by linarith) htau.1
  refine ⟨linePt tau, hzero, linePt_re_pos tau, linePt_re_lt_one tau, ?_, ?_, ?_⟩
  · simpa [linePt_im] using hHtau
  · exact (fzzCigarParityMellin_eq_zero_iff_riemannZeta_eq_zero
      (linePt_re_pos tau) (linePt_re_lt_one tau)).2 hzero
  · intro beta hbeta hmatch
    exact not_fzzCigarParityJointQuinticNaturalRadialPhaseIncident_of_re_eq_half
      (linePt_re tau) ⟨beta, hbeta, hmatch⟩

/-- Proposed pointwise landing of every literal open-strip FZZ parity-Mellin mode. -/
def FZZCigarParityJointQuinticNaturalRadialPhaseDivisorLanding : Prop :=
  ∀ rho : ℂ, 0 < rho.re → rho.re < 1 → FZZCigarParityMellinMode rho →
    FZZCigarParityJointQuinticNaturalRadialPhaseIncident rho

/-- Closed route kill: arbitrary mode-dependent positive scales cannot land the complete literal
FZZ divisor on the canonical pair-valued radial-phase target. -/
theorem fzzCigarParityJointQuinticNaturalRadialPhaseRouteKilled :
    ¬FZZCigarParityJointQuinticNaturalRadialPhaseDivisorLanding := by
  intro hlanding
  obtain ⟨rho, _, h0, h1, _, hmode, hmiss⟩ :=
    exists_fzzCigarParityMellinMode_not_jointQuinticNaturalRadialPhase_above 0
  obtain ⟨beta, hbeta, hmatch⟩ := hlanding rho h0 h1 hmode
  exact hmiss beta hbeta hmatch

end

end RHTower
