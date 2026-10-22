import GaloisForLFunctions.RHTower.FZZCigarPunctureDilationCompletenessEndpoint
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceCompressedInverseDeterminant
import GaloisForLFunctions.RHTower.XiExplicitFormulaLogDeriv

/-!
# FZZ puncture to theta-source infinite-occurrence bridge

The protected scalar FZZ delay has no real-energy `L²` point mode, while every fixed finite regular
polynomial pencil is too rigid to carry the completed Xi divisor. This file records the strongest
survivor after those no-go results: the corpus's fixed, source-derived Hedenmalm compact operator
does provide an honest infinite-dimensional Fredholm occurrence for every nontrivial puncture
Mellin zero.

The affine rotation

`rho ↦ (rho - 1/2)(-i)`

sends the FZZ critical line to the real source-pencilled coordinate. Lean proves exact divisor,
eigenvector, real-energy, completeness, and nonzero-spectrum equivalences.

This is a cross-route compatibility theorem, not an independent FZZ proof of the divisor law:
`fzzCigarContinuumMellinDivisor` is definitionally `riemannZeta`. The remaining physical burden is
to construct the complex continuation and occurrence operator from literal FZZ/GFZZ source data,
rather than importing the completed divisor through this interface.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

/-- Center the FZZ puncture Mellin parameter and rotate the critical line to the real axis. -/
def fzzPunctureThetaSourceCoordinate (rho : ℂ) : ℂ :=
  (rho - 1 / 2) * (-Complex.I)

/-- Infinite-dimensional occurrence of a puncture Mellin point in the fixed theta-source pencil. -/
def FZZPunctureThetaSourceOccurrence (rho : ℂ) : Prop :=
  ¬ IsUnit (HedenmalmThetaSource.thetaSourcePencil
    (fzzPunctureThetaSourceCoordinate rho))

theorem fzzPunctureThetaSourceCoordinate_re (rho : ℂ) :
    (fzzPunctureThetaSourceCoordinate rho).re = rho.im := by
  simp [fzzPunctureThetaSourceCoordinate, Complex.mul_re]

theorem fzzPunctureThetaSourceCoordinate_im (rho : ℂ) :
    (fzzPunctureThetaSourceCoordinate rho).im = 1 / 2 - rho.re := by
  simp [fzzPunctureThetaSourceCoordinate, Complex.mul_im]

/-- A theta-source coordinate is a real energy exactly when the original Mellin point is the
corresponding horizon-dilation spectral parameter. -/
theorem fzzPunctureThetaSourceCoordinate_eq_real_iff (rho : ℂ) (E : ℝ) :
    fzzPunctureThetaSourceCoordinate rho = (E : ℂ) ↔
      rho = fzzPunctureHorizonDilationSpectralParameter E := by
  constructor
  · intro h
    apply Complex.ext
    · have him := congrArg Complex.im h
      rw [fzzPunctureThetaSourceCoordinate_im, Complex.ofReal_im] at him
      rw [fzzPunctureHorizonDilationSpectralParameter_re]
      linarith
    · have hre := congrArg Complex.re h
      rw [fzzPunctureThetaSourceCoordinate_re, Complex.ofReal_re] at hre
      rw [fzzPunctureHorizonDilationSpectralParameter_im]
      exact hre
  · intro h
    rw [h]
    apply Complex.ext
    · rw [fzzPunctureThetaSourceCoordinate_re, Complex.ofReal_re,
        fzzPunctureHorizonDilationSpectralParameter_im]
    · rw [fzzPunctureThetaSourceCoordinate_im, Complex.ofReal_im,
        fzzPunctureHorizonDilationSpectralParameter_re]
      norm_num

theorem exists_real_fzzPunctureThetaSourceCoordinate_iff (rho : ℂ) :
    (∃ E : ℝ, fzzPunctureThetaSourceCoordinate rho = (E : ℂ)) ↔
      rho.re = 1 / 2 := by
  constructor
  · rintro ⟨E, hE⟩
    rw [(fzzPunctureThetaSourceCoordinate_eq_real_iff rho E).mp hE,
      fzzPunctureHorizonDilationSpectralParameter_re]
  · intro hre
    refine ⟨rho.im, ?_⟩
    apply (fzzPunctureThetaSourceCoordinate_eq_real_iff rho rho.im).2
    apply Complex.ext
    · rw [fzzPunctureHorizonDilationSpectralParameter_re, hre]
    · rw [fzzPunctureHorizonDilationSpectralParameter_im]

/-- Exact infinite-dimensional occurrence law in centered coordinates. -/
theorem fzzPunctureThetaSourceOccurrence_iff_XiC_eq_zero (rho : ℂ) :
    FZZPunctureThetaSourceOccurrence rho ↔
      XiC (fzzPunctureThetaSourceCoordinate rho) = 0 := by
  exact HedenmalmThetaSource.thetaSourcePencil_not_isUnit_iff_XiC_eq_zero _

theorem fzzPunctureThetaSourceOccurrence_iff_xi_eq_zero (rho : ℂ) :
    FZZPunctureThetaSourceOccurrence rho ↔ xi rho = 0 := by
  rw [fzzPunctureThetaSourceOccurrence_iff_XiC_eq_zero,
    xi_eq_XiC_comp]
  rfl

/-- Source-pencil occurrences are exactly the nontrivial zeros of the FZZ-labelled Mellin
divisor. -/
theorem fzzPunctureThetaSourceOccurrence_iff_nontrivialMellinZero (rho : ℂ) :
    FZZPunctureThetaSourceOccurrence rho ↔
      fzzCigarContinuumMellinDivisor rho = 0 ∧
        ∀ n : ℕ, rho ≠ -2 * ((n : ℂ) + 1) := by
  rw [fzzPunctureThetaSourceOccurrence_iff_xi_eq_zero,
    xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial]
  simp only [fzzCigarContinuumMellinDivisor, neg_mul]

/-- Every FZZ-labelled source-pencil occurrence supplies an actual nonzero vector of the fixed
theta-source Hilbert space at the reciprocal eigenvalue. -/
theorem exists_thetaSource_eigenvector_of_fzzPunctureOccurrence
    {rho : ℂ} (h : FZZPunctureThetaSourceOccurrence rho) :
    ∃ f : Lp ℂ 2 unitIntervalMeasure, f ≠ 0 ∧
      HedenmalmThetaSource.thetaKernelOperator f =
        (-(fzzPunctureThetaSourceCoordinate rho)⁻¹) • f := by
  have hXi : XiC (fzzPunctureThetaSourceCoordinate rho) = 0 :=
    (fzzPunctureThetaSourceOccurrence_iff_XiC_eq_zero rho).mp h
  exact ((HedenmalmThetaSource.XiC_eq_zero_iff_sourcePencil_not_isUnit_iff_eigenvector
    (fzzPunctureThetaSourceCoordinate rho)).mp hXi).2

theorem fzzPunctureHorizonDilationSpectralParameter_not_trivial
    (E : ℝ) (n : ℕ) :
    fzzPunctureHorizonDilationSpectralParameter E ≠
      -2 * ((n : ℂ) + 1) := by
  intro h
  have hre := congrArg Complex.re h
  rw [fzzPunctureHorizonDilationSpectralParameter_re] at hre
  norm_num at hre
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- A real-energy FZZ horizon mode is exactly a theta-source pencil occurrence at the associated
critical-line parameter. -/
theorem fzzPunctureHorizonDilationMode_iff_thetaSourceOccurrence (E : ℝ) :
    fzzPunctureHorizonDilationMode E ↔
      FZZPunctureThetaSourceOccurrence
        (fzzPunctureHorizonDilationSpectralParameter E) := by
  rw [fzzPunctureThetaSourceOccurrence_iff_nontrivialMellinZero]
  constructor
  · intro h
    exact ⟨h, fzzPunctureHorizonDilationSpectralParameter_not_trivial E⟩
  · exact fun h => h.1

/-- On real energy, the FZZ-labelled mode equation is literally noninvertibility of the fixed
theta-source Fredholm pencil. -/
theorem fzzPunctureHorizonDilationMode_iff_thetaSourcePencil_not_isUnit (E : ℝ) :
    fzzPunctureHorizonDilationMode E ↔
      ¬ IsUnit (HedenmalmThetaSource.thetaSourcePencil (E : ℂ)) := by
  have hcoordinate :
      fzzPunctureThetaSourceCoordinate
          (fzzPunctureHorizonDilationSpectralParameter E) = (E : ℂ) :=
    (fzzPunctureThetaSourceCoordinate_eq_real_iff _ E).2 rfl
  simpa only [FZZPunctureThetaSourceOccurrence, hcoordinate] using
    fzzPunctureHorizonDilationMode_iff_thetaSourceOccurrence E

/-- Completeness expressed entirely as reality of every source-pencilled FZZ occurrence. -/
def FZZPunctureThetaSourceCoordinateReal : Prop :=
  ∀ rho : ℂ, FZZPunctureThetaSourceOccurrence rho →
    ∃ E : ℝ, fzzPunctureThetaSourceCoordinate rho = (E : ℂ)

theorem fzzPunctureHorizonDilationComplete_iff_thetaSourceCoordinateReal :
    FZZPunctureHorizonDilationComplete ↔
      FZZPunctureThetaSourceCoordinateReal := by
  constructor
  · intro hcomplete rho hocc
    obtain ⟨hz, htriv⟩ :=
      (fzzPunctureThetaSourceOccurrence_iff_nontrivialMellinZero rho).mp hocc
    obtain ⟨E, hρ, _⟩ := hcomplete rho hz (not_exists.mpr htriv)
    exact ⟨E, (fzzPunctureThetaSourceCoordinate_eq_real_iff rho E).2 hρ⟩
  · intro hreal rho hz htriv
    have hocc : FZZPunctureThetaSourceOccurrence rho :=
      (fzzPunctureThetaSourceOccurrence_iff_nontrivialMellinZero rho).2
        ⟨hz, not_exists.mp htriv⟩
    obtain ⟨E, hE⟩ := hreal rho hocc
    have hρ := (fzzPunctureThetaSourceCoordinate_eq_real_iff rho E).1 hE
    refine ⟨E, hρ, ?_⟩
    rw [fzzPunctureHorizonDilationMode, ← hρ]
    exact hz

theorem riemannHypothesis_iff_fzzPunctureThetaSourceCoordinateReal :
    RiemannHypothesis ↔ FZZPunctureThetaSourceCoordinateReal := by
  rw [riemannHypothesis_iff_fzzPunctureHorizonDilationComplete,
    fzzPunctureHorizonDilationComplete_iff_thetaSourceCoordinateReal]

/-- Exact cross-route endpoint: FZZ-labelled dilation completeness is the reality of the nonzero
spectrum of the fixed theta-source operator. It is an equivalence of RH-strength criteria, not a
proof of either side. -/
theorem fzzPunctureHorizonDilationComplete_iff_thetaKernelOperator_nonzero_spectrum_real :
    FZZPunctureHorizonDilationComplete ↔
      ∀ mu : ℂ,
        mu ∈ spectrum ℂ HedenmalmThetaSource.thetaKernelOperator → mu ≠ 0 →
          ∃ t : ℝ, mu = (t : ℂ) := by
  calc
    FZZPunctureHorizonDilationComplete ↔ RiemannHypothesis :=
      riemannHypothesis_iff_fzzPunctureHorizonDilationComplete.symm
    _ ↔ _ :=
      HedenmalmThetaSource.riemannHypothesis_iff_thetaKernelOperator_nonzero_spectrum_real

end

end RHTower
