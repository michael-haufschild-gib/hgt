import GaloisForLFunctions.RHTower.FermiMellinPhaseProperness
import GaloisForLFunctions.RHTower.FZZCigarParityDelaySourceContinuation

/-!
# Reflected Fermi information gradient flow for literal FZZ parity modes

The literal Fermi--Mellin source carries a nonlinear reflected information force.  Its unique
equilibrium is the critical center, and its negative-gradient velocity points strictly inward on
the whole open strip.
-/

open Complex MeasureTheory Set InformationTheory
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Symmetric reflected information work in source coordinates. -/
def fzzCigarParityReflectedFermiInformationWork (sigma : ℝ) : ℝ :=
  (2 * sigma - 1) * (fermiLogMean sigma - fermiLogMean (1 - sigma))

/-- Exact nonlinear gradient force of reflected Fermi information work. -/
def fzzCigarParityReflectedFermiInformationForce (sigma : ℝ) : ℝ :=
  2 * (fermiLogMean sigma - fermiLogMean (1 - sigma)) +
    (2 * sigma - 1) * (fermiLogVariance sigma + fermiLogVariance (1 - sigma))

/-- Reflected information work is the Jeffreys divergence of the two Fermi source laws. -/
theorem fzzCigarParityReflectedFermiInformationWork_eq_jeffreys
    {sigma : ℝ} (h0 : 0 < sigma) (h1 : sigma < 1) :
    fzzCigarParityReflectedFermiInformationWork sigma =
      (klDiv (fermiMellinMeasure sigma) (fermiMellinMeasure (1 - sigma))).toReal +
        (klDiv (fermiMellinMeasure (1 - sigma)) (fermiMellinMeasure sigma)).toReal := by
  have hr : 0 < 1 - sigma := by linarith
  rw [jeffreys_fermiMellinMeasure h0 hr]
  rw [fzzCigarParityReflectedFermiInformationWork]
  ring

/-- Exact derivative identity: full nonlinear force is gradient of reflected source work. -/
theorem hasDerivAt_fzzCigarParityReflectedFermiInformationWork
    {sigma : ℝ} (h0 : 0 < sigma) (h1 : sigma < 1) :
    HasDerivAt fzzCigarParityReflectedFermiInformationWork
      (fzzCigarParityReflectedFermiInformationForce sigma) sigma := by
  have hr : 0 < 1 - sigma := by linarith
  have hleft := hasDerivAt_fermiLogMean h0
  have hrightBase := hasDerivAt_fermiLogMean hr
  have hinner : HasDerivAt (fun x : ℝ => 1 - x) (-1) sigma := by
    have hsub := (hasDerivAt_const sigma (1 : ℝ)).sub (hasDerivAt_id sigma)
    have hfun : ((fun _ : ℝ => (1 : ℝ)) - id) = fun x : ℝ => 1 - x := by
      funext x
      rfl
    rw [hfun, zero_sub] at hsub
    exact hsub
  have hright := hrightBase.comp sigma hinner
  have hdiff := hleft.sub hright
  have hfactor : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 sigma := by
    have htwo : HasDerivAt (fun x : ℝ => 2 * x) 2 sigma := by
      simpa using (HasDerivAt.const_mul (2 : ℝ) (hasDerivAt_id sigma))
    exact htwo.sub_const 1
  have hmul := hfactor.mul hdiff
  have hfun :
      ((fun x : ℝ => 2 * x - 1) *
          (fermiLogMean - fermiLogMean ∘ fun x : ℝ => 1 - x)) =
        fun x : ℝ => (2 * x - 1) * (fermiLogMean x - fermiLogMean (1 - x)) := by
    funext x
    rfl
  rw [hfun] at hmul
  have hderiv :
      2 * (fermiLogMean - fermiLogMean ∘ fun x : ℝ => 1 - x) sigma +
          (2 * sigma - 1) *
            (fermiLogVariance sigma - fermiLogVariance (1 - sigma) * -1) =
        fzzCigarParityReflectedFermiInformationForce sigma := by
    simp [fzzCigarParityReflectedFermiInformationForce]
  rw [hderiv] at hmul
  change HasDerivAt
    (fun x : ℝ => (2 * x - 1) * (fermiLogMean x - fermiLogMean (1 - x)))
    (fzzCigarParityReflectedFermiInformationForce sigma) sigma
  exact hmul

theorem fzzCigarParityReflectedFermiInformationForce_neg_of_lt_half
    {sigma : ℝ} (h0 : 0 < sigma) (hhalf : sigma < 1 / 2) :
    fzzCigarParityReflectedFermiInformationForce sigma < 0 := by
  have hr : 0 < 1 - sigma := by linarith
  have horder : sigma < 1 - sigma := by linarith
  have hm := fermiLogMean_strictMonoOn h0 hr horder
  have hv := fermiLogVariance_pos h0
  have hvr := fermiLogVariance_pos hr
  rw [fzzCigarParityReflectedFermiInformationForce]
  nlinarith

theorem fzzCigarParityReflectedFermiInformationForce_pos_of_half_lt
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (h1 : sigma < 1) :
    0 < fzzCigarParityReflectedFermiInformationForce sigma := by
  have h0 : 0 < sigma := by linarith
  have hr : 0 < 1 - sigma := by linarith
  have horder : 1 - sigma < sigma := by linarith
  have hm := fermiLogMean_strictMonoOn hr h0 horder
  have hv := fermiLogVariance_pos h0
  have hvr := fermiLogVariance_pos hr
  rw [fzzCigarParityReflectedFermiInformationForce]
  nlinarith

@[simp] theorem fzzCigarParityReflectedFermiInformationForce_half :
    fzzCigarParityReflectedFermiInformationForce (1 / 2) = 0 := by
  norm_num [fzzCigarParityReflectedFermiInformationForce]

/-- Unique equilibrium of nonlinear reflected Fermi source force. -/
theorem fzzCigarParityReflectedFermiInformationForce_eq_zero_iff
    {sigma : ℝ} (h0 : 0 < sigma) (h1 : sigma < 1) :
    fzzCigarParityReflectedFermiInformationForce sigma = 0 ↔ sigma = 1 / 2 := by
  constructor
  · intro hforce
    rcases lt_trichotomy sigma (1 / 2) with hlt | heq | hgt
    · exact False.elim ((ne_of_lt
        (fzzCigarParityReflectedFermiInformationForce_neg_of_lt_half h0 hlt)) hforce)
    · exact heq
    · exact False.elim ((ne_of_gt
        (fzzCigarParityReflectedFermiInformationForce_pos_of_half_lt hgt h1)) hforce)
  · rintro rfl
    exact fzzCigarParityReflectedFermiInformationForce_half

/-- Negative-gradient source velocity. -/
def fzzCigarParityReflectedFermiInformationVelocity (sigma : ℝ) : ℝ :=
  -fzzCigarParityReflectedFermiInformationForce sigma

/-- Global strict inward orientation of nonlinear source dynamics. -/
theorem fzzCigarParityReflectedFermiInformationVelocity_inward
    {sigma : ℝ} (h0 : 0 < sigma) (h1 : sigma < 1) (hne : sigma ≠ 1 / 2) :
    (sigma - 1 / 2) * fzzCigarParityReflectedFermiInformationVelocity sigma < 0 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hf := fzzCigarParityReflectedFermiInformationForce_neg_of_lt_half h0 hlt
    rw [fzzCigarParityReflectedFermiInformationVelocity]
    nlinarith
  · have hf := fzzCigarParityReflectedFermiInformationForce_pos_of_half_lt hgt h1
    rw [fzzCigarParityReflectedFermiInformationVelocity]
    nlinarith

/-- Reflected information work is nonnegative and vanishes only at critical center. -/
theorem fzzCigarParityReflectedFermiInformationWork_eq_zero_iff
    {sigma : ℝ} (h0 : 0 < sigma) (h1 : sigma < 1) :
    fzzCigarParityReflectedFermiInformationWork sigma = 0 ↔ sigma = 1 / 2 := by
  rw [fzzCigarParityReflectedFermiInformationWork_eq_jeffreys h0 h1]
  exact jeffreys_fermiMellinMeasure_eq_zero_iff_center h0 h1

theorem fzzCigarParityReflectedFermiInformationWork_pos_of_ne_half
    {sigma : ℝ} (h0 : 0 < sigma) (h1 : sigma < 1) (hne : sigma ≠ 1 / 2) :
    0 < fzzCigarParityReflectedFermiInformationWork sigma := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hr : 0 < 1 - sigma := by linarith
    have hm := fermiLogMean_strictMonoOn h0 hr (by linarith : sigma < 1 - sigma)
    rw [fzzCigarParityReflectedFermiInformationWork]
    nlinarith
  · have hr : 0 < 1 - sigma := by linarith
    have hm := fermiLogMean_strictMonoOn hr h0 (by linarith : 1 - sigma < sigma)
    rw [fzzCigarParityReflectedFermiInformationWork]
    nlinarith

/-- Work derivative along negative-gradient dynamics is a strict negative square off center. -/
theorem fzzCigarParityReflectedFermiInformationDissipation_neg
    {sigma : ℝ} (h0 : 0 < sigma) (h1 : sigma < 1) (hne : sigma ≠ 1 / 2) :
    fzzCigarParityReflectedFermiInformationForce sigma *
        fzzCigarParityReflectedFermiInformationVelocity sigma < 0 := by
  have hf : fzzCigarParityReflectedFermiInformationForce sigma ≠ 0 := by
    intro hz
    exact hne ((fzzCigarParityReflectedFermiInformationForce_eq_zero_iff h0 h1).mp hz)
  rw [fzzCigarParityReflectedFermiInformationVelocity]
  nlinarith [sq_pos_of_ne_zero hf]

/-- A source-first FZZ Mellin mode that is stationary for reflected information dynamics. -/
def FZZCigarParityReflectedFermiInformationStationaryMode (rho : ℂ) : Prop :=
  FZZCigarParityMellinMode rho ∧
    fzzCigarParityReflectedFermiInformationForce rho.re = 0

theorem fzzCigarParityReflectedFermiInformationStationaryMode_iff
    {rho : ℂ} (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    FZZCigarParityReflectedFermiInformationStationaryMode rho ↔
      FZZCigarParityMellinMode rho ∧ rho.re = 1 / 2 := by
  rw [FZZCigarParityReflectedFermiInformationStationaryMode,
    fzzCigarParityReflectedFermiInformationForce_eq_zero_iff h0 h1]

/-- Every open-strip FZZ parity Mellin mode is stationary for literal reflected information
dynamics. -/
def FZZCigarParityReflectedFermiInformationStationarity : Prop :=
  ∀ rho : ℂ, 0 < rho.re → rho.re < 1 → FZZCigarParityMellinMode rho →
    fzzCigarParityReflectedFermiInformationForce rho.re = 0

theorem fzzCigarParityReflectedFermiInformationStationarity_iff_complete :
    FZZCigarParityReflectedFermiInformationStationarity ↔
      FZZCigarParityMellinComplete := by
  constructor
  · intro hstationary rho h0 h1 hmode
    have hre := (fzzCigarParityReflectedFermiInformationForce_eq_zero_iff h0 h1).mp
      (hstationary rho h0 h1 hmode)
    refine ⟨rho.im, ?_⟩
    apply Complex.ext
    · rw [fzzPunctureHorizonDilationSpectralParameter_re, hre]
    · rw [fzzPunctureHorizonDilationSpectralParameter_im]
  · intro hcomplete rho h0 h1 hmode
    obtain ⟨E, hE⟩ := hcomplete rho h0 h1 hmode
    apply (fzzCigarParityReflectedFermiInformationForce_eq_zero_iff h0 h1).2
    rw [hE, fzzPunctureHorizonDilationSpectralParameter_re]

/-- Exact nonlinear source endpoint: universal stationarity is RH-strength. -/
theorem fzzCigarParityReflectedFermiInformationStationarity_iff_riemannHypothesis :
    FZZCigarParityReflectedFermiInformationStationarity ↔ RiemannHypothesis :=
  fzzCigarParityReflectedFermiInformationStationarity_iff_complete.trans
    fzzCigarParityMellinComplete_iff_riemannHypothesis

theorem riemannHypothesis_iff_fzzCigarParityReflectedFermiInformationStationarity :
    RiemannHypothesis ↔ FZZCigarParityReflectedFermiInformationStationarity :=
  fzzCigarParityReflectedFermiInformationStationarity_iff_riemannHypothesis.symm

end

end RHTower
