import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingFZZJostDelayIncidenceNoGo
import GaloisForLFunctions.HTGeometry.BlackHoleDressedLogSpectralClock

/-!
# FZZ-cigar delay incidence with the Schwarzschild dressed logarithm

Two exact black-hole scattering constructions contain the same Bose delay kernel.

* Ashok--Troost's protected two-dimensional cigar reflection asymmetry Fourier-transforms, after
  summing positive charge sectors, to `B(t) = 1 / (exp(t) - 1)`.  Its Mellin moments are
  `Gamma(s) * zeta(s)`.
* Solon's all-order four-dimensional Schwarzschild dynamical response contains the universal
  far-zone dressed logarithm

  `tau_L(eta) = L + 2 * (digamma(1 - eta) + gamma_E)`.

The exact cross-dimensional incidence proved here is

`tau_L^(m+1)(0) = -2 * integral_0^infinity t^(m+1) B(t) dt`.

Equivalently, the factorial-normalized FZZ delay moments are precisely the normalized all-order
Schwarzschild response jet.  This is stronger than observing that both formulas contain zeta
values: it identifies every physical integer Mellin moment of the protected cigar continuum with
one response derivative of the four-dimensional black hole.

The positive survivor is an infinite-memory necessity theorem.  The collective FZZ delay moment
sequence obeys no positive-order linear recurrence and has no fixed-dimensional linear
state-space realization.  Therefore no finite oscillator palette, finite local response circuit,
or finite-mode Cayley block can supply the full black-hole delay tomography relevant to the zeta
divisor.

**[FALSIFIED]** Positivity and moment determinacy of the Bose delay measure do not prove RH.  They
recover the physical measure but do not constrain zeros of its complex Mellin continuation.

**[LITERATURE]** The protected cigar spectral asymmetry is from Ashok--Troost,
arXiv:1101.1059.  The all-order Schwarzschild dressed logarithm is from Solon,
arXiv:2606.19281.

**[BRIDGE] [PAPER-PROVED] [NOVELTY UNVERIFIED]** The incidence and infinite-memory consequences
are exact, unconditional consequences of the two imported theorem surfaces.  A targeted priority
search found no published FZZ--dynamical-Love incidence, but this is not an independent novelty
claim.

**[OPEN CORE]** Derive the complex-order interpolation of this all-order response jet from one
theta-dependent nonlinear black-hole influence functional, then obtain a time-orientation or
horizon-flux law strong enough to constrain its Mellin zeros.  Generic KMS, passivity, or finite
sector mixing cannot do this.

`[SCOPE]` This theorem identifies exact observables of two black-hole models; it does not assert a
physical dimensional reduction or a dynamical coupling between the two theories.
-/

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

open HTGeometry

/-! ## Natural Gamma normalization -/

/-- Gamma at the positive integer required by the FZZ moment normalization. -/
private theorem complexGamma_nat_succ_eq_factorial (m : ℕ) :
    Complex.Gamma (((m + 2 : ℕ) : ℂ)) = ((m + 1).factorial : ℂ) := by
  induction m with
  | zero =>
      rw [show (((0 + 2 : ℕ) : ℂ)) = (1 : ℂ) + 1 by norm_num,
        Complex.Gamma_add_one _ (by norm_num), Complex.Gamma_one]
      norm_num
  | succ m ih =>
      rw [show (((Nat.succ m + 2 : ℕ) : ℂ)) =
          (((m + 2 : ℕ) : ℂ)) + 1 by push_cast; ring,
        Complex.Gamma_add_one _ (by exact_mod_cast (by omega : m + 2 ≠ 0)), ih]
      have hfac : (Nat.succ m + 1).factorial =
          (m + 2) * (m + 1).factorial := by
        rw [show Nat.succ m + 1 = (m + 1) + 1 by omega, Nat.factorial_succ]
      rw [hfac]
      push_cast
      ring

/-! ## Exact 2D--4D black-hole scattering incidence -/

/-- Every physical integer FZZ delay moment is the corresponding factorial-scaled normalized
Schwarzschild far-zone response jet. -/
theorem fzzCigarContinuumMellin_natSucc_eq_factorial_mul_blackHoleFarZoneJet
    (scaleLog : ℂ) (m : ℕ) :
    ((HTGeometry.fzzCigarContinuumMellin ((m : ℝ) + 1) : ℝ) : ℂ) =
      ((m + 1).factorial : ℂ) *
        (HTGeometry.normalizedBlackHoleFarZoneJet scaleLog m : ℂ) := by
  rw [HTGeometry.ofReal_fzzCigarContinuumMellin (by positivity),
    HTGeometry.normalizedBlackHoleFarZoneJet_ofReal_eq_riemannZeta]
  rw [show (((((m : ℝ) + 1) + 1 : ℝ) : ℂ)) = ((m + 2 : ℕ) : ℂ) by
    push_cast
    ring]
  rw [complexGamma_nat_succ_eq_factorial]

/-- **Exact all-order black-hole incidence.**  The `(m+1)`-st four-dimensional Schwarzschild
dressed-log response derivative is minus twice the corresponding physical Mellin moment of the
two-dimensional FZZ long-string delay. -/
theorem iteratedDeriv_blackHoleFarZoneDressedLog_eq_neg_two_fzzCigarMellin
    (scaleLog : ℂ) (m : ℕ) :
    iteratedDeriv (m + 1) (HTGeometry.blackHoleFarZoneDressedLog scaleLog) 0 =
      -2 *
        ((HTGeometry.fzzCigarContinuumMellin ((m : ℝ) + 1) : ℝ) : ℂ) := by
  rw [HTGeometry.iteratedDeriv_blackHoleFarZoneDressedLog_succ,
    HTGeometry.ofReal_fzzCigarContinuumMellin (by positivity)]
  rw [HTGeometry.gammaBoseMoment_one_ofReal_eq_riemannZeta]
  have hgamma := complexGamma_nat_succ_eq_factorial m
  rw [show (((((m : ℝ) + 1) + 1 : ℝ) : ℂ)) = ((m + 2 : ℕ) : ℂ) by
    push_cast
    ring]
  rw [hgamma]
  ring

/-! ## Infinite-memory necessity -/

/-- Factorial-normalized physical moments of the protected FZZ continuum delay. -/
def fzzCigarNormalizedDelayMoment (m : ℕ) : ℝ :=
  HTGeometry.fzzCigarContinuumMellin ((m : ℝ) + 1) /
    (m + 1).factorial

/-- The collective cigar delay clock and the all-order Schwarzschild response clock are the same
sequence, independently of far-zone scale convention. -/
theorem fzzCigarNormalizedDelayMoment_eq_blackHoleFarZoneJet
    (scaleLog : ℂ) (m : ℕ) :
    fzzCigarNormalizedDelayMoment m =
      HTGeometry.normalizedBlackHoleFarZoneJet scaleLog m := by
  have hcomplex :=
    fzzCigarContinuumMellin_natSucc_eq_factorial_mul_blackHoleFarZoneJet
      scaleLog m
  have hreal := congrArg Complex.re hcomplex
  simp only [ofReal_re, mul_re, ofReal_im, mul_zero, sub_zero] at hreal
  unfold fzzCigarNormalizedDelayMoment
  have hfac : (((m + 1).factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (m + 1)
  exact (div_eq_iff hfac).2 (by simpa [mul_comm] using hreal)

/-- **No finite recurrence.**  Collective protected black-hole delay cannot be generated by any
positive-order constant-coefficient linear recurrence. -/
theorem fzzCigarNormalizedDelayMoment_not_linearRecurrence
    (E : LinearRecurrence ℝ) (horder : E.order ≠ 0) :
    ¬ E.IsSolution fzzCigarNormalizedDelayMoment := by
  have hseq : fzzCigarNormalizedDelayMoment =
      HTGeometry.normalizedBlackHoleFarZoneJet 0 := by
    funext m
    exact fzzCigarNormalizedDelayMoment_eq_blackHoleFarZoneJet 0 m
  rw [hseq]
  exact HTGeometry.normalizedBlackHoleFarZoneJet_not_linearRecurrence 0 E horder

/-- **No finite-dimensional response realization.**  No fixed-dimensional linear hidden-state
model reproduces arbitrarily long windows of the collective FZZ/Schwarzschild delay clock. -/
theorem fzzCigarNormalizedDelayMoment_not_fixedStateSpaceDimensionLocalClosure
    (d : ℕ) :
    ¬ FixedStateSpaceDimensionLocalClosure d fzzCigarNormalizedDelayMoment := by
  have hseq : fzzCigarNormalizedDelayMoment =
      HTGeometry.normalizedBlackHoleFarZoneJet 0 := by
    funext m
    exact fzzCigarNormalizedDelayMoment_eq_blackHoleFarZoneJet 0 m
  rw [hseq]
  exact HTGeometry.normalizedBlackHoleFarZoneJet_not_fixedStateSpaceDimensionLocalClosure 0 d

end RHTower
