import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBogoliubovCCRCompletionEndpoint

/-!
# Theta-cusp Hawking partner-correlation endpoint

Hawking pair creation has a phase-sensitive observable beyond particle number: the anomalous
exterior/partner correlator.  At Born order its pair amplitude is the Bogoliubov kernel itself,
not its modulus square.  Coherently wavepacketizing every positive-frequency split at fixed total
frequency `w` therefore gives the source-calibrated shell amplitude

`integral from 0 to w of K(u,w-u) du = (i/3) w^(3 : ℕ) Xi(w)`.

This differs materially from the pair-emission density in
`ThetaCuspHawkingPairEmissionSpectralDensity`: the density is quadratic and all-pass blind, while
the anomalous shell amplitude retains the complex Bogoliubov phase linearly.

**[LITERATURE]** Hawking/partner density correlations are expressed through the anomalous
correlator `⟨a_ext a_int⟩` in Dudley--Fabbri--Anderson--Balbinot, arXiv:2008.01433.  Partner modes
for moving mirrors depend on detector wavepacket design and can retain pre-thermal trajectory
information; see Tomitsuka--Yamaguchi--Hotta, arXiv:1906.05009.  These results motivate the
coherent shell observable, but do not impose a canonical phase convention for it.

**[PAPER-PROVED] [LEAN-PROVED]** The exact theta Born shell amplitude is linear in `Xi`, and its
entire continuation has only the universal cubic zero at zero plus the completed-Xi divisor.

**[OPEN CORE] [NOVELTY UNVERIFIED]** A joint exterior/partner homodyne reference can observe this
phase, but generic Hawking thermality, Gaussian purity, and CCR leave the squeeze angle free.
Causality also permits non-minimum-phase all-pass response (Bechhoefer, arXiv:1107.0071).
Therefore the endpoint below is a source-faithful phase-tomography reduction, not a proof that its
dark resonances lie on the physical sheet.  A producer must derive a canonical source-locked
partner quadrature together with an independent rigidity law; it may not assume minimum phase.
-/

open Complex Real MeasureTheory
open scoped Interval

noncomputable section

namespace RHTower

/-- Coherent Born anomalous-correlation amplitude at fixed total pair frequency. -/
def thetaCuspHawkingBornAnomalousPairShellAmplitude (w : ℝ) : ℂ :=
  ∫ u in 0..w,
    thetaCuspHawkingBornPairKernel (u : ℂ) ((w - u : ℝ) : ℂ)

/-- Same coherent shell amplitude after a total-frequency phase dressing. -/
def thetaCuspHawkingPhaseDressedAnomalousPairShellAmplitude
    (phase : ℝ → ℂ) (w : ℝ) : ℂ :=
  ∫ u in 0..w,
    phase w *
      thetaCuspHawkingBornPairKernel (u : ℂ) ((w - u : ℝ) : ℂ)

/-- Entire continuation of the coherent theta Hawking partner-correlation shell. -/
def thetaCuspHawkingAnalyticAnomalousPairShellAmplitude (z : ℂ) : ℂ :=
  Complex.I / 3 * z ^ (3 : ℕ) * XiC z

/-- The analytic anomalous partner shell is entire. -/
theorem thetaCuspHawkingAnalyticAnomalousPairShellAmplitude_differentiable :
    Differentiable ℂ thetaCuspHawkingAnalyticAnomalousPairShellAmplitude := by
  unfold thetaCuspHawkingAnalyticAnomalousPairShellAmplitude
  exact ((differentiable_const (c := Complex.I / 3)).mul
    (differentiable_id.pow 3)).mul XiC_differentiable

/-- **[PAPER-PROVED] [LEAN-PROVED] Exact Hawking partner-correlation law.**  Coherent integration
over the full pair shell retains completed Xi linearly. -/
theorem thetaCuspHawkingBornAnomalousPairShellAmplitude_eq (w : ℝ) :
    thetaCuspHawkingBornAnomalousPairShellAmplitude w =
      Complex.I / 3 * (w : ℂ) ^ (3 : ℕ) * XiC (w : ℂ) := by
  have h1 : (∫ u in 0..w, u) = w ^ (2 : ℕ) / 2 := by
    convert integral_pow (a := (0 : ℝ)) (b := w) (n := 1) using 1
    all_goals norm_num
  have h2 : (∫ u in 0..w, u ^ (2 : ℕ)) = w ^ (3 : ℕ) / 3 := by
    convert integral_pow (a := (0 : ℝ)) (b := w) (n := 2) using 1
    all_goals norm_num
  have hi1 : IntervalIntegrable (fun u : ℝ => w * u) volume 0 w :=
    (by fun_prop : Continuous (fun u : ℝ => w * u)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun u : ℝ => u ^ (2 : ℕ)) volume 0 w :=
    (by fun_prop : Continuous (fun u : ℝ => u ^ (2 : ℕ))).intervalIntegrable _ _
  have hreal : (∫ u in 0..w, u * (w - u)) = w ^ (3 : ℕ) / 6 := by
    rw [show (fun u : ℝ => u * (w - u)) = fun u : ℝ => w * u - u ^ (2 : ℕ) by
      funext u
      ring]
    rw [intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_const_mul, h1, h2]
    ring
  rw [thetaCuspHawkingBornAnomalousPairShellAmplitude]
  calc
    (∫ u in 0..w,
        thetaCuspHawkingBornPairKernel (u : ℂ) ((w - u : ℝ) : ℂ)) =
        ∫ u in 0..w,
          (2 * Complex.I * XiC (w : ℂ)) * ((u * (w - u) : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro u _hu
      change thetaCuspHawkingBornPairKernel
          (u : ℂ) ((w - u : ℝ) : ℂ) = _
      rw [thetaCuspHawkingBornPairKernel]
      push_cast
      rw [show (u : ℂ) + ((w : ℂ) - (u : ℂ)) = (w : ℂ) by ring]
      ring
    _ = (2 * Complex.I * XiC (w : ℂ)) *
        ∫ u in 0..w, ((u * (w - u) : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_const_mul]
    _ = _ := by
      rw [intervalIntegral.integral_ofReal, hreal]
      push_cast
      ring

/-- Phase dressing acts observably and linearly on the anomalous Hawking partner shell. -/
theorem thetaCuspHawkingPhaseDressedAnomalousPairShellAmplitude_eq
    (phase : ℝ → ℂ) (w : ℝ) :
    thetaCuspHawkingPhaseDressedAnomalousPairShellAmplitude phase w =
      phase w * thetaCuspHawkingBornAnomalousPairShellAmplitude w := by
  rw [thetaCuspHawkingPhaseDressedAnomalousPairShellAmplitude,
    thetaCuspHawkingBornAnomalousPairShellAmplitude,
    intervalIntegral.integral_const_mul]

/-- The physical coherent shell is the real-frequency boundary of its entire continuation. -/
theorem thetaCuspHawkingAnalyticAnomalousPairShellAmplitude_ofReal (w : ℝ) :
    thetaCuspHawkingAnalyticAnomalousPairShellAmplitude (w : ℂ) =
      thetaCuspHawkingBornAnomalousPairShellAmplitude w := by
  rw [thetaCuspHawkingAnalyticAnomalousPairShellAmplitude,
    thetaCuspHawkingBornAnomalousPairShellAmplitude_eq]

/-- At positive total frequency, a dark anomalous Hawking partner shell is exactly a real
completed-Xi zero. -/
theorem thetaCuspHawkingBornAnomalousPairShellAmplitude_eq_zero_iff
    {w : ℝ} (hw : 0 < w) :
    thetaCuspHawkingBornAnomalousPairShellAmplitude w = 0 ↔ Xi w = 0 := by
  rw [← thetaCuspHawkingAnalyticAnomalousPairShellAmplitude_ofReal,
    thetaCuspHawkingAnalyticAnomalousPairShellAmplitude,
    XiC_ofReal]
  simp [ne_of_gt hw]

/-- Analytic dark partner shells are the universal zero-frequency edge or completed-Xi zeros. -/
theorem thetaCuspHawkingAnalyticAnomalousPairShellAmplitude_eq_zero_iff (z : ℂ) :
    thetaCuspHawkingAnalyticAnomalousPairShellAmplitude z = 0 ↔
      z = 0 ∨ XiC z = 0 := by
  simp [thetaCuspHawkingAnalyticAnomalousPairShellAmplitude]

/-- **[BRIDGE] Theta Hawking partner-correlation endpoint.**  RH is equivalent to physical-sheet
confinement of every dark resonance of the source-calibrated anomalous partner correlator. -/
theorem riemannHypothesis_iff_thetaCuspHawkingAnomalousPairShellDarkPhysical :
    RiemannHypothesis ↔
      ∀ z : ℂ,
        thetaCuspHawkingAnalyticAnomalousPairShellAmplitude z = 0 → z.im = 0 := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  constructor
  · intro hreal z hdark
    rcases
        (thetaCuspHawkingAnalyticAnomalousPairShellAmplitude_eq_zero_iff z).mp hdark with
      rfl | hXi
    · simp
    · exact hreal z hXi
  · intro hphysical z hXi
    exact hphysical z
      ((thetaCuspHawkingAnalyticAnomalousPairShellAmplitude_eq_zero_iff z).mpr
        (Or.inr hXi))

end RHTower
