import GaloisForLFunctions.HTGeometry.FZZCigarScatteringSpectralAsymmetry
import GaloisForLFunctions.RHTower.FZZCigarPunctureDilationCompletenessEndpoint
import GaloisForLFunctions.RHTower.SalemFermiModeIntegral

/-!
# Source-first complex continuation of the FZZ cigar parity delay

The exact FZZ long-string reflection deficit produces the Bose delay

`B(t) = 1 / (exp t - 1)`.

Its dyadic parity subtraction `B(t) - 2 B(2t)` is exactly the Fermi kernel
`1 / (exp t + 1)` on positive delay. Consequently its complex Mellin transform is defined directly
from literal FZZ source data and is holomorphic on the full half-plane `Re s > 0`. In the open
critical strip its zeros are exactly the nontrivial zeta/Xi divisor: Gamma and the dyadic factor
`1 - 2^(1-s)` are nonzero there.

This repairs the circularity of `fzzCigarContinuumMellinDivisor`, which labels `riemannZeta` as the
continued divisor by definition. No zeta, Xi, or enumerated zero set occurs in
`fzzCigarParityMellin`; the divisor comparison is a theorem. The resulting completeness statement
is still exactly RH-strength. The remaining FZZ-P burden is dynamical orientation: prove from
literal interacting FZZ/GFZZ physics that every source mode has critical real part `1/2`.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Dyadic parity subtraction of the literal FZZ long-string continuum delay. -/
def fzzCigarParityDelay (t : ℝ) : ℝ :=
  HTGeometry.fzzCigarContinuumDelay t -
    2 * HTGeometry.fzzCigarContinuumDelay (2 * t)

/-- Exact Bose-to-Fermi identity for the FZZ delay source. -/
theorem fzzCigarParityDelay_eq_fermi {t : ℝ} (ht : 0 < t) :
    fzzCigarParityDelay t = (Real.exp t + 1)⁻¹ := by
  have he : 1 < Real.exp t := Real.one_lt_exp_iff.mpr ht
  have hminus : Real.exp t - 1 ≠ 0 := ne_of_gt (sub_pos.mpr he)
  have hplus : Real.exp t + 1 ≠ 0 := by positivity
  have hsquare : Real.exp t * Real.exp t - 1 ≠ 0 := by nlinarith
  rw [fzzCigarParityDelay, HTGeometry.fzzCigarContinuumDelay,
    HTGeometry.fzzCigarContinuumDelay]
  rw [show Real.exp (2 * t) = Real.exp t * Real.exp t by
    rw [show 2 * t = t + t by ring, Real.exp_add]]
  rw [show Real.exp t * Real.exp t - 1 =
    (Real.exp t - 1) * (Real.exp t + 1) by ring]
  field_simp [hminus, hplus, hsquare]
  ring

theorem ofReal_fzzCigarParityDelay_eq_salemFermiKernel {t : ℝ} (ht : 0 < t) :
    ((fzzCigarParityDelay t : ℝ) : ℂ) = salemFermiKernel t := by
  rw [fzzCigarParityDelay_eq_fermi ht, salemFermiKernel]
  push_cast
  rfl

/-- The parity-subtracted source is literally the alternating supertrace of the FZZ charge-delay
tower: odd/even charge sectors carry opposite signs. -/
theorem hasSum_fzzCigarParityChargeDelay {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ =>
      (-1 : ℂ) ^ n * HTGeometry.fzzCigarChargeDelay n t)
      ((fzzCigarParityDelay t : ℝ) : ℂ) := by
  have h := salemFermiKernel_hasSum ht
  rw [← ofReal_fzzCigarParityDelay_eq_salemFermiKernel ht] at h
  simpa only [HTGeometry.fzzCigarChargeDelay, Nat.cast_add, Nat.cast_one,
    Complex.ofReal_exp, neg_mul] using h

/-- Complex Mellin transform defined directly from the parity-subtracted FZZ delay source. -/
def fzzCigarParityMellin (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => ((fzzCigarParityDelay t : ℝ) : ℂ)) s

/-- The FZZ parity-delay Mellin transform is the Fermi Mellin transform because their source
kernels agree at every positive delay. -/
theorem fzzCigarParityMellin_eq_salemFermiMellin (s : ℂ) :
    fzzCigarParityMellin s = mellin salemFermiKernel s := by
  rw [fzzCigarParityMellin, mellin]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change (t : ℂ) ^ (s - 1) • ((fzzCigarParityDelay t : ℝ) : ℂ) =
    (t : ℂ) ^ (s - 1) • salemFermiKernel t
  rw [ofReal_fzzCigarParityDelay_eq_salemFermiKernel ht]

/-- Source-first complex continuation: the literal FZZ parity-delay Mellin transform is
holomorphic throughout `Re s > 0`, including the whole critical strip. -/
theorem analyticOnNhd_fzzCigarParityMellin :
    AnalyticOnNhd ℂ fzzCigarParityMellin {s : ℂ | 0 < s.re} := by
  have hfun : fzzCigarParityMellin = mellin salemFermiKernel := by
    funext s
    exact fzzCigarParityMellin_eq_salemFermiMellin s
  rw [hfun]
  exact analyticOnNhd_mellin_salemFermiKernel

theorem fzzCigarParityMellin_eq_closedForm
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    fzzCigarParityMellin s =
      Complex.Gamma s * (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  rw [fzzCigarParityMellin_eq_salemFermiMellin]
  exact mellin_salemFermiKernel_eq_closedForm hs0 hs1

/-- Exact divisor comparison on the open critical strip. This is a theorem about the
FZZ-defined source integral, not a definition by zeta. -/
theorem fzzCigarParityMellin_eq_zero_iff_riemannZeta_eq_zero
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    fzzCigarParityMellin s = 0 ↔ riemannZeta s = 0 := by
  have hsne : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs1
  rw [fzzCigarParityMellin_eq_closedForm hs0 hsne]
  have hGamma : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
  have hdyadic : 1 - (2 : ℂ) ^ (1 - s) ≠ 0 := by
    simpa only [salemSpectralParameter_re_im] using
      (salemDyadicFactor_ne_zero (delta := s.re) (gamma := s.im) hs1)
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hGamma hdyadic)
  · intro h
    rw [h, mul_zero]

theorem fzzCigarParityMellin_eq_zero_iff_xi_eq_zero
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    fzzCigarParityMellin s = 0 ↔ xi s = 0 := by
  have hsne : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs1
  exact (fzzCigarParityMellin_eq_zero_iff_riemannZeta_eq_zero hs0 hs1).trans
    (xi_eq_zero_iff hs0 hsne).symm

/-- A complex mode of the source-defined FZZ parity-delay Mellin transform. -/
def FZZCigarParityMellinMode (rho : ℂ) : Prop :=
  fzzCigarParityMellin rho = 0

/-- The old real-energy FZZ-labelled mode equation agrees exactly with the new source-first
parity-delay mode equation. -/
theorem fzzPunctureHorizonDilationMode_iff_parityMellinMode (E : ℝ) :
    fzzPunctureHorizonDilationMode E ↔
      FZZCigarParityMellinMode
        (fzzPunctureHorizonDilationSpectralParameter E) := by
  have h0 : 0 < (fzzPunctureHorizonDilationSpectralParameter E).re := by
    rw [fzzPunctureHorizonDilationSpectralParameter_re]
    norm_num
  have h1 : (fzzPunctureHorizonDilationSpectralParameter E).re < 1 := by
    rw [fzzPunctureHorizonDilationSpectralParameter_re]
    norm_num
  simpa only [fzzPunctureHorizonDilationMode,
    fzzCigarContinuumMellinDivisor, FZZCigarParityMellinMode] using
      (fzzCigarParityMellin_eq_zero_iff_riemannZeta_eq_zero h0 h1).symm

/-- Every open-strip mode of the FZZ source continuation is carried by a real horizon energy. -/
def FZZCigarParityMellinComplete : Prop :=
  ∀ rho : ℂ, 0 < rho.re → rho.re < 1 → FZZCigarParityMellinMode rho →
    ∃ E : ℝ, rho = fzzPunctureHorizonDilationSpectralParameter E

/-- The repaired, source-native FZZ completeness endpoint is exactly RH-strength. Unlike the old
endpoint, its defining source contains no zeta/Xi divisor. -/
theorem fzzCigarParityMellinComplete_iff_riemannHypothesis :
    FZZCigarParityMellinComplete ↔ RiemannHypothesis := by
  constructor
  · intro hcomplete
    rw [riemannHypothesis_iff_forall_nontrivial_zero]
    intro rho hz htriv
    have htriv' : ∀ n : ℕ, rho ≠ -(2 * ((n : ℂ) + 1)) := by
      intro n hn
      apply htriv
      refine ⟨n, ?_⟩
      simpa only [neg_mul] using hn
    obtain ⟨h0, h1⟩ := riemannZeta_zero_re_mem_Ioo hz htriv'
    have hmode : FZZCigarParityMellinMode rho :=
      (fzzCigarParityMellin_eq_zero_iff_riemannZeta_eq_zero h0 h1).2 hz
    obtain ⟨E, hE⟩ := hcomplete rho h0 h1 hmode
    rw [hE, fzzPunctureHorizonDilationSpectralParameter_re]
  · intro hRH rho h0 h1 hmode
    have hxi : xi rho = 0 :=
      (fzzCigarParityMellin_eq_zero_iff_xi_eq_zero h0 h1).1 hmode
    have hre : rho.re = 1 / 2 := xi_zero_re_eq_half_of_RH hRH hxi
    refine ⟨rho.im, ?_⟩
    apply Complex.ext
    · rw [fzzPunctureHorizonDilationSpectralParameter_re, hre]
    · rw [fzzPunctureHorizonDilationSpectralParameter_im]

theorem riemannHypothesis_iff_fzzCigarParityMellinComplete :
    RiemannHypothesis ↔ FZZCigarParityMellinComplete :=
  fzzCigarParityMellinComplete_iff_riemannHypothesis.symm

end

end RHTower
