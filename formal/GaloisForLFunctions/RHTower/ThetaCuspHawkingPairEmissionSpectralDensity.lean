import GaloisForLFunctions.RHTower.ThetaCuspHawkingBogoliubovCCRCompletionEndpoint

/-!
# Theta-cusp Hawking pair-emission spectral density

This endpoint uses the Hawking mechanism at amplitude level.  The theta-cusp moving-mirror Born
kernel creates an exterior/partner pair with frequencies `u,v`:

`K(u,v) = 2 i u v XiC(u+v)`.

Fixing total positive frequency `w` and integrating the emitted pair intensity over every physical
split `u + v = w` gives an exact continuum spectral law.  No KMS, passivity, minimum-phase, or RH
hypothesis enters the calculation:

`integral from 0 to w of normSq(K(u,w-u)) du = (2/15) w^(5 : ℕ) Xi(w)^(2 : ℕ)`.

**[LITERATURE]** Perturbative moving-mirror influence-functional calculations derive particle
creation, colored noise, and nonlocal dissipation from quadratic convolution integrals over two
environmental frequency channels at the pair resonance `w = u + v`; see Butera,
*Noise and dissipation on a moving mirror induced by the dynamical Casimir emission*,
arXiv:2306.03813.
The density below is the coefficient-faithful specialization of that pair-frequency structure to
the exact theta source.

**[PAPER-PROVED] [LEAN-PROVED]** The physical density is nonnegative at positive frequency and is
dark exactly at real zeros of `Xi`.

**[FALSIFIED] [OPEN CORE]** Hawking particle flux cannot by itself locate nonreal zeros.  Multiplying
the pair amplitude by any unit-norm total-frequency phase leaves the complete density unchanged.
Thus particle number, and any FDT noise law depending only on this density, erases the all-pass
sector.  A viable Hawking endpoint must derive a phase-sensitive exterior/partner correlator,
causal clock, or equivalent source-calibrated observable rather than postulate minimum phase.
-/

open Complex Real MeasureTheory
open scoped Interval

noncomputable section

namespace RHTower

/-- Continuum Hawking pair-emission density at fixed total frequency.  The interval integral is
oriented for arbitrary real `w`; physical emission uses `0 ≤ w`. -/
def thetaCuspHawkingBornPairEmissionDensity (w : ℝ) : ℝ :=
  ∫ u in 0..w, Complex.normSq
    (thetaCuspHawkingBornPairKernel (u : ℂ) ((w - u : ℝ) : ℂ))

/-- Pair-emission density after a total-frequency phase dressing of the Born kernel. -/
def thetaCuspHawkingPhaseDressedPairEmissionDensity
    (phase : ℝ → ℂ) (w : ℝ) : ℝ :=
  ∫ u in 0..w, Complex.normSq
    (phase w *
      thetaCuspHawkingBornPairKernel (u : ℂ) ((w - u : ℝ) : ℂ))

/-- Entire form factor continuing the exact physical pair-emission density.  The fifth-order zero
at the origin is universal pair phase space; every other zero comes from the theta source. -/
def thetaCuspHawkingAnalyticPairEmissionFormFactor (z : ℂ) : ℂ :=
  (2 / 15 : ℂ) * z ^ (5 : ℕ) * XiC z ^ (2 : ℕ)

/-- The continued theta Hawking pair-emission form factor is entire. -/
theorem thetaCuspHawkingAnalyticPairEmissionFormFactor_differentiable :
    Differentiable ℂ thetaCuspHawkingAnalyticPairEmissionFormFactor := by
  unfold thetaCuspHawkingAnalyticPairEmissionFormFactor
  exact ((differentiable_const (c := (2 / 15 : ℂ))).mul
    (differentiable_id.pow 5)).mul (XiC_differentiable.pow 2)

/-- **[PAPER-PROVED] [LEAN-PROVED] Pair-shell intensity.**  On the total-frequency shell
`u + (w-u) = w`, the exact theta Hawking kernel has polynomial split weight and coefficient
`Xi(w)^(2 : ℕ)`. -/
theorem thetaCuspHawkingBornPairKernel_normSq_totalSplit (w u : ℝ) :
    Complex.normSq
        (thetaCuspHawkingBornPairKernel (u : ℂ) ((w - u : ℝ) : ℂ)) =
      4 * u ^ (2 : ℕ) * (w - u) ^ (2 : ℕ) * Xi w ^ (2 : ℕ) := by
  rw [thetaCuspHawkingBornPairKernel]
  push_cast
  rw [show (u : ℂ) + ((w : ℂ) - (u : ℂ)) = (w : ℂ) by ring,
    XiC_ofReal]
  simp only [Complex.normSq_mul, Complex.normSq_ofReal]
  norm_num [Complex.normSq_apply]
  ring

/-- Exact beta-function integral of the theta Hawking pair-shell intensity. -/
private theorem integral_thetaCuspHawkingBornPairKernel_normSq (w : ℝ) :
    ∫ u in 0..w, 4 * u ^ (2 : ℕ) * (w - u) ^ (2 : ℕ) * Xi w ^ (2 : ℕ) =
      (2 / 15 : ℝ) * w ^ (5 : ℕ) * Xi w ^ (2 : ℕ) := by
  have h2 := integral_pow (a := (0 : ℝ)) (b := w) (n := 2)
  have h3 := integral_pow (a := (0 : ℝ)) (b := w) (n := 3)
  have h4 := integral_pow (a := (0 : ℝ)) (b := w) (n := 4)
  have hi2 : IntervalIntegrable
      (fun u : ℝ => (4 * w ^ (2 : ℕ) * Xi w ^ (2 : ℕ)) * u ^ (2 : ℕ)) volume 0 w :=
    (by fun_prop : Continuous
      (fun u : ℝ => (4 * w ^ (2 : ℕ) * Xi w ^ (2 : ℕ)) * u ^ (2 : ℕ))).intervalIntegrable _ _
  have hi3 : IntervalIntegrable
      (fun u : ℝ => (-8 * w * Xi w ^ (2 : ℕ)) * u ^ (3 : ℕ)) volume 0 w :=
    (by fun_prop : Continuous
      (fun u : ℝ => (-8 * w * Xi w ^ (2 : ℕ)) * u ^ (3 : ℕ))).intervalIntegrable _ _
  have hi4 : IntervalIntegrable
      (fun u : ℝ => (4 * Xi w ^ (2 : ℕ)) * u ^ (4 : ℕ)) volume 0 w :=
    (by fun_prop : Continuous
      (fun u : ℝ => (4 * Xi w ^ (2 : ℕ)) * u ^ (4 : ℕ))).intervalIntegrable _ _
  rw [show (fun u : ℝ => 4 * u ^ (2 : ℕ) * (w - u) ^ (2 : ℕ) * Xi w ^ (2 : ℕ)) =
      fun u : ℝ => (4 * w ^ (2 : ℕ) * Xi w ^ (2 : ℕ)) * u ^ (2 : ℕ) +
        (-8 * w * Xi w ^ (2 : ℕ)) * u ^ (3 : ℕ) +
        (4 * Xi w ^ (2 : ℕ)) * u ^ (4 : ℕ) by
    funext u
    ring]
  rw [intervalIntegral.integral_add (hi2.add hi3) hi4,
    intervalIntegral.integral_add hi2 hi3,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    h2, h3, h4]
  ring

/-- **[PAPER-PROVED] [LEAN-PROVED] Exact theta Hawking emission law.** -/
theorem thetaCuspHawkingBornPairEmissionDensity_eq (w : ℝ) :
    thetaCuspHawkingBornPairEmissionDensity w =
      (2 / 15 : ℝ) * w ^ (5 : ℕ) * Xi w ^ (2 : ℕ) := by
  rw [thetaCuspHawkingBornPairEmissionDensity]
  calc
    (∫ u in 0..w, Complex.normSq
        (thetaCuspHawkingBornPairKernel (u : ℂ) ((w - u : ℝ) : ℂ))) =
        ∫ u in 0..w, 4 * u ^ (2 : ℕ) * (w - u) ^ (2 : ℕ) * Xi w ^ (2 : ℕ) := by
      apply intervalIntegral.integral_congr
      intro u _hu
      exact thetaCuspHawkingBornPairKernel_normSq_totalSplit w u
    _ = _ := integral_thetaCuspHawkingBornPairKernel_normSq w

/-- Physical theta Hawking pair-emission density is nonnegative. -/
theorem thetaCuspHawkingBornPairEmissionDensity_nonneg {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ thetaCuspHawkingBornPairEmissionDensity w := by
  rw [thetaCuspHawkingBornPairEmissionDensity_eq]
  positivity

/-- **[PAPER-PROVED] [LEAN-PROVED] Hawking dark-frequency law.**  At positive total frequency,
zero emitted pair flux is equivalent to a real zero of the completed Xi function. -/
theorem thetaCuspHawkingBornPairEmissionDensity_eq_zero_iff {w : ℝ} (hw : 0 < w) :
    thetaCuspHawkingBornPairEmissionDensity w = 0 ↔ Xi w = 0 := by
  rw [thetaCuspHawkingBornPairEmissionDensity_eq]
  have hfac : (2 / 15 : ℝ) * w ^ (5 : ℕ) ≠ 0 := by positivity
  constructor
  · intro h
    have hs : Xi w ^ (2 : ℕ) = 0 := (mul_eq_zero.mp h).resolve_left hfac
    exact sq_eq_zero_iff.mp hs
  · intro h
    simp [h]

/-- **[FALSIFIED] [LEAN-PROVED] All-pass blindness.**  Every unit-norm total-frequency phase
dressing is invisible to the entire pair-emission density, not merely to one sampled intensity. -/
theorem thetaCuspHawkingPhaseDressedPairEmissionDensity_eq
    (phase : ℝ → ℂ) (w : ℝ) (hphase : Complex.normSq (phase w) = 1) :
    thetaCuspHawkingPhaseDressedPairEmissionDensity phase w =
      thetaCuspHawkingBornPairEmissionDensity w := by
  rw [thetaCuspHawkingPhaseDressedPairEmissionDensity,
    thetaCuspHawkingBornPairEmissionDensity]
  apply intervalIntegral.integral_congr
  intro u _hu
  change Complex.normSq
      (phase w *
        thetaCuspHawkingBornPairKernel (u : ℂ) ((w - u : ℝ) : ℂ)) = _
  rw [Complex.normSq_mul, hphase, one_mul]

/-- **[PAPER-PROVED] [LEAN-PROVED] Source-calibrated continuation law.**  On real frequency, the
entire form factor is exactly the complexification of measured pair-emission density. -/
theorem thetaCuspHawkingAnalyticPairEmissionFormFactor_ofReal (w : ℝ) :
    thetaCuspHawkingAnalyticPairEmissionFormFactor (w : ℂ) =
      (thetaCuspHawkingBornPairEmissionDensity w : ℂ) := by
  rw [thetaCuspHawkingAnalyticPairEmissionFormFactor,
    thetaCuspHawkingBornPairEmissionDensity_eq, XiC_ofReal]
  push_cast
  norm_num

/-- Analytic pair-density dark resonances are the universal zero-frequency edge or completed-Xi
zeros. -/
theorem thetaCuspHawkingAnalyticPairEmissionFormFactor_eq_zero_iff (z : ℂ) :
    thetaCuspHawkingAnalyticPairEmissionFormFactor z = 0 ↔
      z = 0 ∨ XiC z = 0 := by
  simp [thetaCuspHawkingAnalyticPairEmissionFormFactor]

/-- **[BRIDGE] Theta Hawking pair-emission endpoint.**  RH is equivalent to physical-sheet
confinement of every dark resonance of the source-calibrated analytic pair-density form factor.
This is a coefficient-faithful Hawking reduction, not a proof of the confinement law. -/
theorem riemannHypothesis_iff_thetaCuspHawkingAnalyticPairEmissionDarkPhysical :
    RiemannHypothesis ↔
      ∀ z : ℂ,
        thetaCuspHawkingAnalyticPairEmissionFormFactor z = 0 → z.im = 0 := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  constructor
  · intro hreal z hdark
    rcases
        (thetaCuspHawkingAnalyticPairEmissionFormFactor_eq_zero_iff z).mp hdark with
      rfl | hXi
    · simp
    · exact hreal z hXi
  · intro hphysical z hXi
    exact hphysical z
      ((thetaCuspHawkingAnalyticPairEmissionFormFactor_eq_zero_iff z).mpr
        (Or.inr hXi))

end RHTower
