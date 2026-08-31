import GaloisForLFunctions.RHTower.FZZCigarParityIndependentRadialPhaseIncidenceClassification

/-!
# FZZ same-scale Laurent radial critical-sector no-go

The literal FZZ parity source supplies two observables at one positive scale:

* the strictly subunit Fermi radial coordinate, and
* the unit-modulus fixed-quintic Krein phase.

The pair-valued joint encoding is phase-complete and scale-injective.  This
file tests the coefficient-faithful scalar fusion obtained by multiplying the
quintic phase by a fixed positive or negative Laurent power of the radial
coordinate.

There is an exact trichotomy.  A positive radial exponent can meet only the
strict left half of the dyadic Mellin character, a negative exponent only the
strict right half, and exponent zero only the critical line.  Consequently
every nonzero exponent misses every unit target.  Exponent zero recovers the
complete quintic phase, but its explicit two-scale collision destroys scale
determinism.

Thus no fixed same-scale Laurent fusion is both critical-sector complete and
scale-injective.  This kills that FZZ-P producer class before divisor
specialization.  The positive survivor is genuinely pair-valued or
non-Laurent dynamics retaining the radial coordinate separately.

No Xi or zeta zero, RH, numerical computation, or divisor-placement premise
is used.
-/

open Complex

namespace RHTower

noncomputable section

/-- Fixed Laurent sectors for fusing the same-scale radial and quintic phase
observables.  The natural number in a nonneutral constructor represents
absolute exponent `degree + 1`, so those exponents are genuinely nonzero. -/
inductive FZZCigarParitySameScaleLaurentSector
  | neutral
  | contracting (degree : ℕ)
  | expanding (degree : ℕ)
  deriving DecidableEq

/-- Scalar same-scale Laurent fusion of the literal Fermi radial coordinate
and the fixed-quintic source phase. -/
def fzzCigarParitySameScaleLaurentEncoding
    (sector : FZZCigarParitySameScaleLaurentSector) (beta : ℝ) : ℂ :=
  match sector with
  | .neutral => fzzCigarParityFixedQuinticEigenphase beta
  | .contracting degree =>
      ((fzzCigarParityIndependentFermiRadial beta ^ (degree + 1) : ℝ) : ℂ) *
        fzzCigarParityFixedQuinticEigenphase beta
  | .expanding degree =>
      (((fzzCigarParityIndependentFermiRadial beta)⁻¹ ^
          (degree + 1) : ℝ) : ℂ) *
        fzzCigarParityFixedQuinticEigenphase beta

theorem norm_fzzCigarParitySameScaleLaurentEncoding_neutral
    {beta : ℝ} (hbeta : 0 < beta) :
    ‖fzzCigarParitySameScaleLaurentEncoding .neutral beta‖ = 1 := by
  exact norm_fzzCigarParityFixedQuinticEigenphase hbeta

theorem norm_fzzCigarParitySameScaleLaurentEncoding_contracting
    {degree : ℕ} {beta : ℝ} (hbeta : 0 < beta) :
    ‖fzzCigarParitySameScaleLaurentEncoding (.contracting degree) beta‖ =
      fzzCigarParityIndependentFermiRadial beta ^ (degree + 1) := by
  rw [fzzCigarParitySameScaleLaurentEncoding, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (pow_pos (fzzCigarParityIndependentFermiRadial_pos hbeta) _),
    norm_fzzCigarParityFixedQuinticEigenphase hbeta, mul_one]

theorem norm_fzzCigarParitySameScaleLaurentEncoding_expanding
    {degree : ℕ} {beta : ℝ} (hbeta : 0 < beta) :
    ‖fzzCigarParitySameScaleLaurentEncoding (.expanding degree) beta‖ =
      (fzzCigarParityIndependentFermiRadial beta)⁻¹ ^ (degree + 1) := by
  rw [fzzCigarParitySameScaleLaurentEncoding, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (pow_pos (inv_pos.mpr
      (fzzCigarParityIndependentFermiRadial_pos hbeta)) _),
    norm_fzzCigarParityFixedQuinticEigenphase hbeta, mul_one]

/-- Every genuinely contracting same-scale Laurent fusion has strict subunit
modulus. -/
theorem norm_fzzCigarParitySameScaleLaurentEncoding_contracting_lt_one
    {degree : ℕ} {beta : ℝ} (hbeta : 0 < beta) :
    ‖fzzCigarParitySameScaleLaurentEncoding (.contracting degree) beta‖ < 1 := by
  rw [norm_fzzCigarParitySameScaleLaurentEncoding_contracting hbeta]
  exact pow_lt_one₀
    (fzzCigarParityIndependentFermiRadial_pos hbeta).le
    (fzzCigarParityIndependentFermiRadial_lt_one hbeta)
    (by omega)

/-- Every genuinely expanding same-scale Laurent fusion has strict superunit
modulus. -/
theorem one_lt_norm_fzzCigarParitySameScaleLaurentEncoding_expanding
    {degree : ℕ} {beta : ℝ} (hbeta : 0 < beta) :
    1 < ‖fzzCigarParitySameScaleLaurentEncoding (.expanding degree) beta‖ := by
  rw [norm_fzzCigarParitySameScaleLaurentEncoding_expanding hbeta]
  exact one_lt_pow₀
    ((one_lt_inv₀ (fzzCigarParityIndependentFermiRadial_pos hbeta)).2
      (fzzCigarParityIndependentFermiRadial_lt_one hbeta))
    (by omega)

/-- Critical completeness asks one fixed scalar fusion sector to realize every
unit Mellin character from a positive physical scale. -/
def FZZCigarParitySameScaleLaurentCriticalComplete
    (sector : FZZCigarParitySameScaleLaurentSector) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 →
    ∃ beta : ℝ, 0 < beta ∧
      fzzCigarParitySameScaleLaurentEncoding sector beta = z

/-- Scale determinism of one scalar same-scale Laurent fusion. -/
def FZZCigarParitySameScaleLaurentScaleInjective
    (sector : FZZCigarParitySameScaleLaurentSector) : Prop :=
  Set.InjOn (fzzCigarParitySameScaleLaurentEncoding sector) (Set.Ioi 0)

/-- Horizontal chamber selected by the sign of the radial Laurent exponent. -/
def FZZCigarParitySameScaleLaurentHorizontalSector
    (sector : FZZCigarParitySameScaleLaurentSector) (rho : ℂ) : Prop :=
  match sector with
  | .neutral => rho.re = 1 / 2
  | .contracting _ => rho.re < 1 / 2
  | .expanding _ => 1 / 2 < rho.re

/-- **Laurent/chamber rigidity.**  Any exact same-scale scalar match to the
dyadic Mellin character forces the horizontal chamber determined by exponent
sign. -/
theorem
    fzzCigarParitySameScaleLaurentEncoding_eq_dyadicMellinCharacter_forces_sector
    {sector : FZZCigarParitySameScaleLaurentSector}
    {beta : ℝ} (hbeta : 0 < beta) {rho : ℂ}
    (hmatch : fzzCigarParitySameScaleLaurentEncoding sector beta =
      fzzCigarParityDyadicMellinCharacter rho) :
    FZZCigarParitySameScaleLaurentHorizontalSector sector rho := by
  cases sector with
  | neutral =>
      exact fzzCigarParityDyadicMellinCharacter_eq_fixedQuintic_forces_critical
        hbeta (by
          simpa [fzzCigarParitySameScaleLaurentEncoding] using hmatch.symm)
  | contracting degree =>
      change rho.re < 1 / 2
      have hnorm := congrArg norm hmatch
      have hlt :=
        norm_fzzCigarParitySameScaleLaurentEncoding_contracting_lt_one
          (degree := degree) hbeta
      rw [norm_fzzCigarParityDyadicMellinCharacter] at hnorm
      have hexp : Real.exp (Real.log 2 * (rho.re - 1 / 2)) < 1 := by
        rw [← hnorm]
        exact hlt
      rw [Real.exp_lt_one_iff] at hexp
      have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
      nlinarith
  | expanding degree =>
      change 1 / 2 < rho.re
      have hnorm := congrArg norm hmatch
      have hgt :=
        one_lt_norm_fzzCigarParitySameScaleLaurentEncoding_expanding
          (degree := degree) hbeta
      rw [norm_fzzCigarParityDyadicMellinCharacter] at hnorm
      have hexp : 1 < Real.exp (Real.log 2 * (rho.re - 1 / 2)) := by
        rw [← hnorm]
        exact hgt
      rw [Real.one_lt_exp_iff] at hexp
      have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
      nlinarith

/-- Neutral exponent recovers full unit-circle capacity. -/
theorem fzzCigarParitySameScaleLaurentCriticalComplete_neutral :
    FZZCigarParitySameScaleLaurentCriticalComplete .neutral := by
  intro z hnorm
  simpa [fzzCigarParitySameScaleLaurentEncoding] using
    exists_pos_fzzCigarParityFixedQuinticEigenphase_eq_of_norm_one hnorm

theorem not_fzzCigarParitySameScaleLaurentCriticalComplete_contracting
    (degree : ℕ) :
    ¬FZZCigarParitySameScaleLaurentCriticalComplete (.contracting degree) := by
  intro hcomplete
  obtain ⟨beta, hbeta, hmatch⟩ := hcomplete 1 (by simp)
  have hnorm := congrArg norm hmatch
  have hlt :=
    norm_fzzCigarParitySameScaleLaurentEncoding_contracting_lt_one
      (degree := degree) hbeta
  simp at hnorm
  linarith

theorem not_fzzCigarParitySameScaleLaurentCriticalComplete_expanding
    (degree : ℕ) :
    ¬FZZCigarParitySameScaleLaurentCriticalComplete (.expanding degree) := by
  intro hcomplete
  obtain ⟨beta, hbeta, hmatch⟩ := hcomplete 1 (by simp)
  have hnorm := congrArg norm hmatch
  have hgt := one_lt_norm_fzzCigarParitySameScaleLaurentEncoding_expanding
    (degree := degree) hbeta
  simp at hnorm
  linarith

/-- Neutral exponent cannot determine scale: degree-five phase capacity has
an explicit collision at two distinct positive source scales. -/
theorem not_fzzCigarParitySameScaleLaurentScaleInjective_neutral :
    ¬FZZCigarParitySameScaleLaurentScaleInjective .neutral := by
  intro hinjective
  obtain ⟨beta₁, beta₂, hbeta₁, hbeta₂, hne, heq⟩ :=
    exists_distinct_pos_fzzCigarParityFixedMonomialEigenphase_eq
      (n := 5) (by norm_num)
  apply hne
  apply hinjective hbeta₁ hbeta₂
  simpa [fzzCigarParitySameScaleLaurentEncoding,
    fzzCigarParityFixedQuinticEigenphase] using heq

/-- Every fixed same-scale Laurent sector fails critical completeness or
scale determinism. -/
theorem fzzCigarParitySameScaleLaurentCriticalRouteKilled
    (sector : FZZCigarParitySameScaleLaurentSector) :
    ¬(FZZCigarParitySameScaleLaurentCriticalComplete sector ∧
      FZZCigarParitySameScaleLaurentScaleInjective sector) := by
  cases sector with
  | neutral =>
      rintro ⟨_, hinjective⟩
      exact not_fzzCigarParitySameScaleLaurentScaleInjective_neutral hinjective
  | contracting degree =>
      rintro ⟨hcomplete, _⟩
      exact
        not_fzzCigarParitySameScaleLaurentCriticalComplete_contracting degree
          hcomplete
  | expanding degree =>
      rintro ⟨hcomplete, _⟩
      exact not_fzzCigarParitySameScaleLaurentCriticalComplete_expanding degree
        hcomplete

/-- Closed route certificate for the terminal dependency audit. -/
def FZZCigarParitySameScaleLaurentCriticalRouteKilled : Prop :=
  ∀ sector : FZZCigarParitySameScaleLaurentSector,
    ¬(FZZCigarParitySameScaleLaurentCriticalComplete sector ∧
      FZZCigarParitySameScaleLaurentScaleInjective sector)

/-- **FZZ-P route-class kill.**  No coefficient-faithful scalar Laurent
fusion of the same-scale radial and quintic source observables can retain
both critical-sector capacity and physical-scale determinism. -/
theorem fzzCigarParitySameScaleLaurentCriticalRouteKilled_all :
    FZZCigarParitySameScaleLaurentCriticalRouteKilled := by
  exact fzzCigarParitySameScaleLaurentCriticalRouteKilled

end

end RHTower
