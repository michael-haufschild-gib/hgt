import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingPairEmissionSpectralDensity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingPartnerCorrelationEndpoint

/-!
# Theta-cusp Hawking partner-coherence rigidity

The theta Hawking Born pair kernel defines, on every positive total-frequency shell, both an
incoherent particle density and a coherent exterior/partner amplitude.  They are not independent:

`6 * normSq(integral K) = 5 * w * integral normSq(K)`.

Equivalently, the Gram determinant of the constant shell mode and the emitted pair mode is

`w * integral normSq(K) - normSq(integral K) = (1/45) * w^(6 : ℕ) * Xi(w)^(2 : ℕ)`.

Thus every bright shell has the same normalized coherent fraction `5/6`; its remaining `1/6` is
the exact continuum split-mode coherence defect.  This relation is invariant under arbitrary
unit-norm total-frequency phase dressing.  More generally, every detector weight whose geometric
split moment is nonzero has the same nonkinematic dark frequencies.

**[LITERATURE]** Lin--Chen--Good--Nambu, *Squeezed quantum states and partner modes in the moving
mirror model of black hole evaporation*, arXiv:2608.11957, show that mirror-history squeezing
redistributes mutual Hawking/partner correlations into additional self-correlations even when the
frequency spectrum is approximately thermal.  Tomitsuka--Yamaguchi--Hotta, arXiv:1906.05009,
show that partner modes depend strongly on detector design.  These facts make a phase-invariant
shell Gram law and an explicit detector-nondegeneracy condition physically necessary, rather than
optional presentation choices.

**[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [PAPER-PROVED] [LEAN-PROVED]** The
coefficient-faithful theta source has the exact `5/6` coherent fraction, `1/45` Gram defect, and
detector-universal dark divisor proved below.

**[BRIDGE] [OPEN CORE]** The entire continuation of the Gram defect is
`(1/45) z^(6 : ℕ) XiC(z)^(2 : ℕ)`; hence RH is exactly confinement of its nonkinematic degeneracy resonances
to the physical-frequency sheet.  Real-shell Gram positivity is automatic and therefore does not
prove this confinement.  A producer must derive an independent complex-frequency positivity or
backreaction stability law for this same Hawking covariance object.
-/

open Complex Real MeasureTheory
open scoped Interval

noncomputable section

namespace RHTower

/-- Geometric split moment selected by a complex detector weight on a total-frequency shell. -/
def thetaCuspHawkingDetectorSplitMoment
    (weight : ℝ → ℂ) (w : ℝ) : ℂ :=
  ∫ u in 0..w, weight u * ((u * (w - u) : ℝ) : ℂ)

/-- Coherent theta Hawking partner shell seen by a complex detector weight. -/
def thetaCuspHawkingWeightedAnomalousPairShellAmplitude
    (weight : ℝ → ℂ) (w : ℝ) : ℂ :=
  ∫ u in 0..w, weight u *
    thetaCuspHawkingBornPairKernel (u : ℂ) ((w - u : ℝ) : ℂ)

/-- **[PAPER-PROVED] [LEAN-PROVED] Detector factorization.** Every shell detector separates into
one geometric split moment and the same total-frequency theta-source coefficient. -/
theorem thetaCuspHawkingWeightedAnomalousPairShellAmplitude_eq
    (weight : ℝ → ℂ) (w : ℝ) :
    thetaCuspHawkingWeightedAnomalousPairShellAmplitude weight w =
      (2 * Complex.I * XiC (w : ℂ)) *
        thetaCuspHawkingDetectorSplitMoment weight w := by
  rw [thetaCuspHawkingWeightedAnomalousPairShellAmplitude,
    thetaCuspHawkingDetectorSplitMoment]
  calc
    (∫ u in 0..w, weight u *
        thetaCuspHawkingBornPairKernel (u : ℂ) ((w - u : ℝ) : ℂ)) =
        ∫ u in 0..w,
          (2 * Complex.I * XiC (w : ℂ)) *
            (weight u * ((u * (w - u) : ℝ) : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro u _hu
      change weight u *
        (2 * Complex.I * (u : ℂ) * ((w - u : ℝ) : ℂ) *
          XiC ((u : ℂ) + ((w - u : ℝ) : ℂ))) = _
      push_cast
      rw [show (u : ℂ) + ((w : ℂ) - (u : ℂ)) = (w : ℂ) by ring]
      ring
    _ = _ := by rw [intervalIntegral.integral_const_mul]

/-- Every detector with nonzero split moment sees exactly the real Xi dark frequencies. -/
theorem thetaCuspHawkingWeightedAnomalousPairShellAmplitude_eq_zero_iff
    (weight : ℝ → ℂ) (w : ℝ)
    (hmoment : thetaCuspHawkingDetectorSplitMoment weight w ≠ 0) :
    thetaCuspHawkingWeightedAnomalousPairShellAmplitude weight w = 0 ↔
      XiC (w : ℂ) = 0 := by
  rw [thetaCuspHawkingWeightedAnomalousPairShellAmplitude_eq]
  simp [hmoment]

/-- Gram determinant of the constant shell mode and the emitted theta Hawking pair mode. -/
def thetaCuspHawkingBornPairShellCoherenceDefect (w : ℝ) : ℝ :=
  w * thetaCuspHawkingBornPairEmissionDensity w -
    Complex.normSq (thetaCuspHawkingBornAnomalousPairShellAmplitude w)

/-- Entire continuation of the exact Hawking shell-coherence Gram defect. -/
def thetaCuspHawkingAnalyticPairShellCoherenceDefect (z : ℂ) : ℂ :=
  (1 / 45 : ℂ) * z ^ (6 : ℕ) * XiC z ^ (2 : ℕ)

/-- Squared norm of the coherent anomalous shell amplitude. -/
theorem normSq_thetaCuspHawkingBornAnomalousPairShellAmplitude (w : ℝ) :
    Complex.normSq (thetaCuspHawkingBornAnomalousPairShellAmplitude w) =
      (1 / 9 : ℝ) * w ^ (6 : ℕ) * Xi w ^ (2 : ℕ) := by
  have hpow : Complex.normSq ((w : ℂ) ^ (3 : ℕ)) = w ^ (6 : ℕ) := by
    norm_num [Complex.normSq_apply, pow_succ]
    ring
  have hI : Complex.normSq (Complex.I / 3) = (1 / 9 : ℝ) := by
    norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im]
  rw [thetaCuspHawkingBornAnomalousPairShellAmplitude_eq, XiC_ofReal]
  rw [Complex.normSq_mul, Complex.normSq_mul, hI, hpow,
    Complex.normSq_ofReal]
  ring

/-- **[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] Exact `5/6` Hawking coherence law.** -/
theorem thetaCuspHawkingBornPairShell_coherence_five_sixths (w : ℝ) :
    6 * Complex.normSq (thetaCuspHawkingBornAnomalousPairShellAmplitude w) =
      5 * w * thetaCuspHawkingBornPairEmissionDensity w := by
  rw [normSq_thetaCuspHawkingBornAnomalousPairShellAmplitude,
    thetaCuspHawkingBornPairEmissionDensity_eq]
  ring

/-- **[PAPER-PROVED] [LEAN-PROVED] Exact shell Gram defect.** -/
theorem thetaCuspHawkingBornPairShellCoherenceDefect_eq (w : ℝ) :
    thetaCuspHawkingBornPairShellCoherenceDefect w =
      (1 / 45 : ℝ) * w ^ (6 : ℕ) * Xi w ^ (2 : ℕ) := by
  rw [thetaCuspHawkingBornPairShellCoherenceDefect,
    thetaCuspHawkingBornPairEmissionDensity_eq,
    normSq_thetaCuspHawkingBornAnomalousPairShellAmplitude]
  ring

/-- Physical shell-coherence defect is nonnegative. -/
theorem thetaCuspHawkingBornPairShellCoherenceDefect_nonneg (w : ℝ) :
    0 ≤ thetaCuspHawkingBornPairShellCoherenceDefect w := by
  rw [thetaCuspHawkingBornPairShellCoherenceDefect_eq]
  positivity

/-- At nonzero physical frequency, Gram degeneracy is exactly a real Xi zero. -/
theorem thetaCuspHawkingBornPairShellCoherenceDefect_eq_zero_iff
    {w : ℝ} (hw : w ≠ 0) :
    thetaCuspHawkingBornPairShellCoherenceDefect w = 0 ↔ Xi w = 0 := by
  rw [thetaCuspHawkingBornPairShellCoherenceDefect_eq]
  have hfac : (1 / 45 : ℝ) * w ^ (6 : ℕ) ≠ 0 := by positivity
  constructor
  · intro h
    have hs : Xi w ^ (2 : ℕ) = 0 := (mul_eq_zero.mp h).resolve_left hfac
    exact sq_eq_zero_iff.mp hs
  · intro h
    simp [h]

/-- Unit-norm total-frequency phase dressing leaves the full Hawking Gram defect unchanged. -/
theorem thetaCuspHawkingPhaseDressedPairShellCoherenceDefect_eq
    (phase : ℝ → ℂ) (w : ℝ) (hphase : Complex.normSq (phase w) = 1) :
    w * thetaCuspHawkingPhaseDressedPairEmissionDensity phase w -
        Complex.normSq
          (thetaCuspHawkingPhaseDressedAnomalousPairShellAmplitude phase w) =
      thetaCuspHawkingBornPairShellCoherenceDefect w := by
  rw [thetaCuspHawkingPhaseDressedPairEmissionDensity_eq phase w hphase,
    thetaCuspHawkingPhaseDressedAnomalousPairShellAmplitude_eq,
    Complex.normSq_mul, hphase, one_mul]
  rfl

/-- Entire analyticity of the shell-coherence defect. -/
theorem thetaCuspHawkingAnalyticPairShellCoherenceDefect_differentiable :
    Differentiable ℂ thetaCuspHawkingAnalyticPairShellCoherenceDefect := by
  unfold thetaCuspHawkingAnalyticPairShellCoherenceDefect
  exact ((differentiable_const (c := (1 / 45 : ℂ))).mul
    (differentiable_id.pow 6)).mul (XiC_differentiable.pow 2)

/-- Physical shell Gram defect is the real boundary value of its entire continuation. -/
theorem thetaCuspHawkingAnalyticPairShellCoherenceDefect_ofReal (w : ℝ) :
    thetaCuspHawkingAnalyticPairShellCoherenceDefect (w : ℂ) =
      (thetaCuspHawkingBornPairShellCoherenceDefect w : ℂ) := by
  rw [thetaCuspHawkingAnalyticPairShellCoherenceDefect,
    thetaCuspHawkingBornPairShellCoherenceDefect_eq, XiC_ofReal]
  push_cast
  norm_num

/-- Analytic shell Gram degeneracies are the kinematic zero-frequency edge or Xi zeros. -/
theorem thetaCuspHawkingAnalyticPairShellCoherenceDefect_eq_zero_iff (z : ℂ) :
    thetaCuspHawkingAnalyticPairShellCoherenceDefect z = 0 ↔
      z = 0 ∨ XiC z = 0 := by
  simp [thetaCuspHawkingAnalyticPairShellCoherenceDefect]

/-- **[BRIDGE] Hawking partner-coherence endpoint.** RH is exactly physical-sheet confinement of
all analytic degeneracy resonances of the theta Hawking pair-shell Gram determinant. -/
theorem riemannHypothesis_iff_thetaCuspHawkingPairShellCoherenceDegeneracyPhysical :
    RiemannHypothesis ↔
      ∀ z : ℂ,
        thetaCuspHawkingAnalyticPairShellCoherenceDefect z = 0 → z.im = 0 := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  constructor
  · intro hreal z hdegenerate
    rcases
        (thetaCuspHawkingAnalyticPairShellCoherenceDefect_eq_zero_iff z).mp
          hdegenerate with rfl | hXi
    · simp
    · exact hreal z hXi
  · intro hphysical z hXi
    exact hphysical z
      ((thetaCuspHawkingAnalyticPairShellCoherenceDefect_eq_zero_iff z).mpr
        (Or.inr hXi))

end RHTower
