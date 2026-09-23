import GaloisForLFunctions.RHTower.FZZCigarParityJointQuinticRadialScaleEncoding

/-!
# Independent Fermi-radial/quintic-phase incidence classification

HC27 supplies a literal Fermi radial clock with image `(0,1)`; HC25 supplies a fixed quintic phase
covering the unit circle. This module permits those two positive source scales to vary
independently and adds the reciprocal radial sector forced by Mellin reflection.

The resulting source family has an exact classification. Contracting incidence is equivalent to
`Re rho < 1/2`, unit incidence to `Re rho = 1/2`, and expanding incidence to `Re rho > 1/2`.
Every dyadic Mellin character lies in exactly one sector. Hence selectable independent radial and
phase scales are universally nonselective, even though the sector itself records transverse sign
exactly. Remaining viable FZZ-P dynamics must force the unit sector or couple the two scales before
target specialization.

`[NEW] [EXACT INCIDENCE TRICHOTOMY] [UNIVERSAL NONSELECTION] [SHARP NO-GO]
[POSITIVE SECTOR SURVIVOR] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

def fzzCigarParityIndependentFermiRadial (beta : ℝ) : ℝ :=
  -(fzzCigarParityDilatedKreinEigenlineBalancedCoordinate beta).re

def fzzCigarParityIndependentContractingQuinticEncoding
    (radialScale phaseScale : ℝ) : ℂ :=
  (fzzCigarParityIndependentFermiRadial radialScale : ℂ) *
    fzzCigarParityFixedQuinticEigenphase phaseScale

def fzzCigarParityIndependentExpandingQuinticEncoding
    (radialScale phaseScale : ℝ) : ℂ :=
  ((fzzCigarParityIndependentFermiRadial radialScale)⁻¹ : ℂ) *
    fzzCigarParityFixedQuinticEigenphase phaseScale

theorem fzzCigarParityIndependentFermiRadial_pos
    {beta : ℝ} (hbeta : 0 < beta) :
    0 < fzzCigarParityIndependentFermiRadial beta := by
  exact neg_pos.mpr
    (fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_re_neg hbeta)

theorem fzzCigarParityIndependentFermiRadial_lt_one
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityIndependentFermiRadial beta < 1 := by
  have hnorm :=
    norm_fzzCigarParityDilatedKreinEigenlineBalancedCoordinate hbeta
  have hnormsq := congrArg (fun x : ℝ => x ^ (2 : ℕ)) hnorm
  rw [Complex.sq_norm, Complex.normSq_apply] at hnormsq
  have him :=
    fzzCigarParityDilatedKreinEigenlineBalancedCoordinate_im_pos hbeta
  dsimp [fzzCigarParityIndependentFermiRadial]
  nlinarith [sq_pos_of_pos him]

theorem norm_fzzCigarParityIndependentContractingQuinticEncoding
    {radialScale phaseScale : ℝ}
    (hradial : 0 < radialScale) (hphase : 0 < phaseScale) :
    ‖fzzCigarParityIndependentContractingQuinticEncoding radialScale phaseScale‖ =
      fzzCigarParityIndependentFermiRadial radialScale := by
  rw [fzzCigarParityIndependentContractingQuinticEncoding, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (fzzCigarParityIndependentFermiRadial_pos hradial),
    norm_fzzCigarParityFixedQuinticEigenphase hphase, mul_one]

theorem norm_fzzCigarParityIndependentExpandingQuinticEncoding
    {radialScale phaseScale : ℝ}
    (hradial : 0 < radialScale) (hphase : 0 < phaseScale) :
    ‖fzzCigarParityIndependentExpandingQuinticEncoding radialScale phaseScale‖ =
      (fzzCigarParityIndependentFermiRadial radialScale)⁻¹ := by
  rw [fzzCigarParityIndependentExpandingQuinticEncoding, norm_mul,
    norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (fzzCigarParityIndependentFermiRadial_pos hradial),
    norm_fzzCigarParityFixedQuinticEigenphase hphase, mul_one]

theorem exists_pos_fzzCigarParityIndependentContractingQuinticEncoding_eq
    {z : ℂ} (hz : z ≠ 0) (hnorm : ‖z‖ < 1) :
    ∃ radialScale phaseScale : ℝ,
      0 < radialScale ∧ 0 < phaseScale ∧
        fzzCigarParityIndependentContractingQuinticEncoding radialScale phaseScale = z := by
  have hnpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  obtain ⟨radialScale, hradial, hr⟩ :=
    exists_pos_fzzCigarParityKreinEigenline_neg_re_eq hnpos hnorm
  have hphaseNorm : ‖z / (‖z‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos]
    exact div_self hnpos.ne'
  obtain ⟨phaseScale, hphase, hp⟩ :=
    exists_pos_fzzCigarParityFixedQuinticEigenphase_eq_of_norm_one hphaseNorm
  refine ⟨radialScale, phaseScale, hradial, hphase, ?_⟩
  rw [fzzCigarParityIndependentContractingQuinticEncoding,
    fzzCigarParityIndependentFermiRadial, hr, hp]
  exact mul_div_cancel₀ z (by exact_mod_cast hnpos.ne')

theorem exists_pos_fzzCigarParityIndependentExpandingQuinticEncoding_eq
    {z : ℂ} (hnorm : 1 < ‖z‖) :
    ∃ radialScale phaseScale : ℝ,
      0 < radialScale ∧ 0 < phaseScale ∧
        fzzCigarParityIndependentExpandingQuinticEncoding radialScale phaseScale = z := by
  have hnpos : 0 < ‖z‖ := lt_trans zero_lt_one hnorm
  have hinvpos : 0 < ‖z‖⁻¹ := inv_pos.mpr hnpos
  have hinvlt : ‖z‖⁻¹ < 1 := (inv_lt_one₀ hnpos).2 hnorm
  obtain ⟨radialScale, hradial, hr⟩ :=
    exists_pos_fzzCigarParityKreinEigenline_neg_re_eq hinvpos hinvlt
  have hphaseNorm : ‖z / (‖z‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos]
    exact div_self hnpos.ne'
  obtain ⟨phaseScale, hphase, hp⟩ :=
    exists_pos_fzzCigarParityFixedQuinticEigenphase_eq_of_norm_one hphaseNorm
  refine ⟨radialScale, phaseScale, hradial, hphase, ?_⟩
  rw [fzzCigarParityIndependentExpandingQuinticEncoding,
    fzzCigarParityIndependentFermiRadial, hr, hp]
  push_cast
  rw [inv_inv]
  exact mul_div_cancel₀ z (by exact_mod_cast hnpos.ne')

def FZZCigarParityIndependentContractingQuinticIncident (rho : ℂ) : Prop :=
  ∃ radialScale phaseScale : ℝ,
    0 < radialScale ∧ 0 < phaseScale ∧
      fzzCigarParityIndependentContractingQuinticEncoding radialScale phaseScale =
        fzzCigarParityDyadicMellinCharacter rho

def FZZCigarParityIndependentExpandingQuinticIncident (rho : ℂ) : Prop :=
  ∃ radialScale phaseScale : ℝ,
    0 < radialScale ∧ 0 < phaseScale ∧
      fzzCigarParityIndependentExpandingQuinticEncoding radialScale phaseScale =
        fzzCigarParityDyadicMellinCharacter rho

theorem fzzCigarParityIndependentContractingQuinticIncident_iff
    (rho : ℂ) :
    FZZCigarParityIndependentContractingQuinticIncident rho ↔
      rho.re < 1 / 2 := by
  constructor
  · rintro ⟨radialScale, phaseScale, hradial, hphase, hmatch⟩
    have hnorm := congrArg norm hmatch
    rw [norm_fzzCigarParityIndependentContractingQuinticEncoding hradial hphase,
      norm_fzzCigarParityDyadicMellinCharacter] at hnorm
    have hlt : Real.exp (Real.log 2 * (rho.re - 1 / 2)) < 1 := by
      rw [← hnorm]
      exact fzzCigarParityIndependentFermiRadial_lt_one hradial
    rw [Real.exp_lt_one_iff] at hlt
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  · intro hre
    apply exists_pos_fzzCigarParityIndependentContractingQuinticEncoding_eq
      (fzzCigarParityDyadicMellinCharacter_ne_zero rho)
    rw [norm_fzzCigarParityDyadicMellinCharacter, Real.exp_lt_one_iff]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith

theorem fzzCigarParityIndependentExpandingQuinticIncident_iff
    (rho : ℂ) :
    FZZCigarParityIndependentExpandingQuinticIncident rho ↔
      1 / 2 < rho.re := by
  constructor
  · rintro ⟨radialScale, phaseScale, hradial, hphase, hmatch⟩
    have hnorm := congrArg norm hmatch
    rw [norm_fzzCigarParityIndependentExpandingQuinticEncoding hradial hphase,
      norm_fzzCigarParityDyadicMellinCharacter] at hnorm
    have hgt : 1 < Real.exp (Real.log 2 * (rho.re - 1 / 2)) := by
      rw [← hnorm]
      exact (one_lt_inv₀ (fzzCigarParityIndependentFermiRadial_pos hradial)).2
        (fzzCigarParityIndependentFermiRadial_lt_one hradial)
    rw [Real.one_lt_exp_iff] at hgt
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  · intro hre
    apply exists_pos_fzzCigarParityIndependentExpandingQuinticEncoding_eq
      
    rw [norm_fzzCigarParityDyadicMellinCharacter, Real.one_lt_exp_iff]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith

inductive FZZCigarParityIndependentRadialPhaseSector
  | contracting
  | unit
  | expanding
  deriving DecidableEq

def FZZCigarParityIndependentRadialPhaseSectorIncident
    (sector : FZZCigarParityIndependentRadialPhaseSector) (rho : ℂ) : Prop :=
  match sector with
  | .contracting => FZZCigarParityIndependentContractingQuinticIncident rho
  | .unit => ∃ phaseScale : ℝ, 0 < phaseScale ∧
      fzzCigarParityFixedQuinticEigenphase phaseScale =
        fzzCigarParityDyadicMellinCharacter rho
  | .expanding => FZZCigarParityIndependentExpandingQuinticIncident rho

theorem fzzCigarParityIndependentRadialPhaseSectorIncident_contracting_iff
    (rho : ℂ) :
    FZZCigarParityIndependentRadialPhaseSectorIncident .contracting rho ↔
      rho.re < 1 / 2 :=
  fzzCigarParityIndependentContractingQuinticIncident_iff rho

theorem fzzCigarParityIndependentRadialPhaseSectorIncident_unit_iff
    (rho : ℂ) :
    FZZCigarParityIndependentRadialPhaseSectorIncident .unit rho ↔
      rho.re = 1 / 2 :=
  exists_pos_fzzCigarParityFixedQuinticEigenphase_eq_dyadicMellinCharacter_iff rho

theorem fzzCigarParityIndependentRadialPhaseSectorIncident_expanding_iff
    (rho : ℂ) :
    FZZCigarParityIndependentRadialPhaseSectorIncident .expanding rho ↔
      1 / 2 < rho.re :=
  fzzCigarParityIndependentExpandingQuinticIncident_iff rho

theorem fzzCigarParityIndependentRadialPhaseIncidenceTrichotomy
    (rho : ℂ) :
    (FZZCigarParityIndependentRadialPhaseSectorIncident .contracting rho ↔
        rho.re < 1 / 2) ∧
      (FZZCigarParityIndependentRadialPhaseSectorIncident .unit rho ↔
        rho.re = 1 / 2) ∧
      (FZZCigarParityIndependentRadialPhaseSectorIncident .expanding rho ↔
        1 / 2 < rho.re) := by
  exact ⟨fzzCigarParityIndependentRadialPhaseSectorIncident_contracting_iff rho,
    fzzCigarParityIndependentRadialPhaseSectorIncident_unit_iff rho,
    fzzCigarParityIndependentRadialPhaseSectorIncident_expanding_iff rho⟩

theorem existsUnique_fzzCigarParityIndependentRadialPhaseSectorIncident
    (rho : ℂ) :
    ∃! sector : FZZCigarParityIndependentRadialPhaseSector,
      FZZCigarParityIndependentRadialPhaseSectorIncident sector rho := by
  rcases lt_trichotomy rho.re (1 / 2) with hre | hre | hre
  · refine ⟨.contracting,
      (fzzCigarParityIndependentContractingQuinticIncident_iff rho).2 hre, ?_⟩
    intro sector hsector
    cases sector with
    | contracting => rfl
    | unit =>
        exfalso
        have heq :=
          (exists_pos_fzzCigarParityFixedQuinticEigenphase_eq_dyadicMellinCharacter_iff
            rho).1 hsector
        linarith
    | expanding =>
        exfalso
        have hgt :=
          (fzzCigarParityIndependentExpandingQuinticIncident_iff rho).1 hsector
        linarith
  · refine ⟨.unit,
      (exists_pos_fzzCigarParityFixedQuinticEigenphase_eq_dyadicMellinCharacter_iff
        rho).2 hre, ?_⟩
    intro sector hsector
    cases sector with
    | contracting =>
        exfalso
        have hlt :=
          (fzzCigarParityIndependentContractingQuinticIncident_iff rho).1 hsector
        linarith
    | unit => rfl
    | expanding =>
        exfalso
        have hgt :=
          (fzzCigarParityIndependentExpandingQuinticIncident_iff rho).1 hsector
        linarith
  · refine ⟨.expanding,
      (fzzCigarParityIndependentExpandingQuinticIncident_iff rho).2 hre, ?_⟩
    intro sector hsector
    cases sector with
    | contracting =>
        exfalso
        have hlt :=
          (fzzCigarParityIndependentContractingQuinticIncident_iff rho).1 hsector
        linarith
    | unit =>
        exfalso
        have heq :=
          (exists_pos_fzzCigarParityFixedQuinticEigenphase_eq_dyadicMellinCharacter_iff
            rho).1 hsector
        linarith
    | expanding => rfl

def FZZCigarParityIndependentRadialPhaseDivisorSectorComplete : Prop :=
  ∀ rho : ℂ, riemannZeta rho = 0 → 0 < rho.re → rho.re < 1 →
    ∃ sector : FZZCigarParityIndependentRadialPhaseSector,
      FZZCigarParityIndependentRadialPhaseSectorIncident sector rho

theorem fzzCigarParityIndependentRadialPhaseDivisorSectorComplete :
    FZZCigarParityIndependentRadialPhaseDivisorSectorComplete := by
  intro rho _ _ _
  exact (existsUnique_fzzCigarParityIndependentRadialPhaseSectorIncident rho).exists

def FZZCigarParityIndependentRadialPhaseAnySectorIncident (rho : ℂ) : Prop :=
  ∃ sector : FZZCigarParityIndependentRadialPhaseSector,
    FZZCigarParityIndependentRadialPhaseSectorIncident sector rho

theorem fzzCigarParityIndependentRadialPhaseAnySectorIncident_all
    (rho : ℂ) :
    FZZCigarParityIndependentRadialPhaseAnySectorIncident rho :=
  (existsUnique_fzzCigarParityIndependentRadialPhaseSectorIncident rho).exists

theorem not_fzzCigarParityIndependentRadialPhaseAnySectorIncident_iff_criticalLine :
    ¬ ∀ rho : ℂ,
      FZZCigarParityIndependentRadialPhaseAnySectorIncident rho ↔
        rho.re = 1 / 2 := by
  intro hselect
  have hfalse :=
    (hselect 0).mp (fzzCigarParityIndependentRadialPhaseAnySectorIncident_all 0)
  norm_num at hfalse

theorem exists_noncritical_fzzCigarParityIndependentRadialPhaseSectorIncident :
    ∃ rho : ℂ, rho.re ≠ 1 / 2 ∧
      ∃ sector : FZZCigarParityIndependentRadialPhaseSector,
        FZZCigarParityIndependentRadialPhaseSectorIncident sector rho := by
  refine ⟨0, by norm_num, ?_⟩
  exact (existsUnique_fzzCigarParityIndependentRadialPhaseSectorIncident 0).exists

end

end RHTower
