import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftAveragedEnergies

/-!
# The shift-averaged variation inequality

Integrating the two-sided ground-state representation over the shift `a > 0` gives, for every
even `u ∈ C²_c(ℝ)`, the shift-free identity

    ∫_0^∞ markovEnergy(Φ(ω_a u)) da
      = 2 ∫ dm(t) ∫_{x>0} [G(t) − G(2x+t)] (u(x) − u(x+t))² dx
        − ∫ dm(t) ∫_0^t [G(2x−t) − G(t)] (u(x) − u(t−x))² dx
        + 2 ∫_{x>0} u(x)² sinh²(x/2) dx,

where `G = Φ ∗ Φ` is the autocorrelation of Riemann's kernel and
`dm = archLevyDensity dt + Σ Λ(n) n^{−1/2} δ_{log n}`. Under the Riemann Hypothesis every
shifted Markov energy is nonnegative, so the averaged reflected variation is dominated by twice
the averaged same-side variation plus the hyperbolic source: the **shift-averaged variation
inequality**.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The averaged kernels in autocorrelation form -/

theorem averagedKernel_reflected (x t : ℝ) :
    averagedKernel x (t - x) = riemannAutocorr (2 * x - t) - riemannAutocorr t := by
  unfold averagedKernel
  rw [show x - (t - x) = 2 * x - t by ring, show x + (t - x) = t by ring]

theorem averagedKernel_sameSide (x t : ℝ) :
    averagedKernel x (x + t) = riemannAutocorr t - riemannAutocorr (2 * x + t) := by
  unfold averagedKernel
  rw [show x - (x + t) = -t by ring, riemannAutocorr_neg, show x + (x + t) = 2 * x + t by ring]

/-! ### The shift-averaged Markov energy -/

/-- **Shift average of the Markov energy of the shifted ground states.** For every even
`u ∈ C²_c(ℝ)`,

    ∫_0^∞ markovEnergy(Φ(ω_a u)) da = 2 S̄(u) − D̄(u) + 2 ∫_{x>0} u² sinh²(x/2). -/
theorem integral_Ioi_markovEnergy_phiDoob_shiftedGroundState {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    (∫ a in Ioi (0 : ℝ),
        markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ))) =
      2 * averagedSameSideEnergy u - averagedReflectedEnergy u +
        2 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * Real.sinh (x / 2) ^ 2 := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have e : Set.EqOn
      (fun a => markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)))
      (fun a => 2 * sameSideEnergy (shiftedGroundState a) u -
        reflectedDifferenceEnergy (shiftedGroundState a) u +
        4 * Real.sinh (a / 2) *
          ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) (Ioi 0) :=
    fun a ha => markovEnergy_phiDoob_shiftedGroundState_eq_twoSided ha hu huc heven
  have hS := integrableOn_sameSideEnergy_shiftedGroundState hu1 huc
  have hD := integrableOn_reflectedDifferenceEnergy_shiftedGroundState hu.continuous huc
  have hsrc := integrableOn_source_shiftedGroundState hu.continuous huc
  have hSD : IntegrableOn (fun a => 2 * sameSideEnergy (shiftedGroundState a) u -
      reflectedDifferenceEnergy (shiftedGroundState a) u) (Ioi 0) := (hS.const_mul 2).sub hD
  have hS2 : IntegrableOn (fun a => 2 * sameSideEnergy (shiftedGroundState a) u) (Ioi 0) :=
    hS.const_mul 2
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_add hSD hsrc, integral_sub hS2 hD,
    integral_const_mul,
    integral_Ioi_sameSideEnergy_shiftedGroundState hu1 huc,
    integral_Ioi_reflectedDifferenceEnergy_shiftedGroundState hu.continuous huc,
    integral_Ioi_source_shiftedGroundState hu.continuous huc]

/-! ### The shift-averaged variation inequality under RH -/

/-- **The Riemann Hypothesis implies the shift-averaged variation inequality.** For every even
`u ∈ C²_c(ℝ)`,

    ∫ dm(t) ∫_0^t K(x,t−x) (u(x) − u(t−x))² dx
      ≤ 2 ∫ dm(t) ∫_{x>0} K(x,x+t) (u(x) − u(x+t))² dx + 2 ∫_{x>0} u(x)² sinh²(x/2) dx,

with `K(x,y) = G(x−y) − G(x+y)`. -/
theorem averagedReflectedEnergy_le_of_riemannHypothesis (hRH : RiemannHypothesis) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    averagedReflectedEnergy u ≤
      2 * averagedSameSideEnergy u + 2 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * Real.sinh (x / 2) ^ 2 := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have h := integral_Ioi_markovEnergy_phiDoob_shiftedGroundState hu huc heven
  have hnn : 0 ≤ ∫ a in Ioi (0 : ℝ),
      markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) := by
    refine setIntegral_nonneg measurableSet_Ioi fun a ha => ?_
    rw [markovEnergy_phiDoob_shiftedGroundState_nonneg_iff_variation ha hu huc heven]
    exact reflectedDifferenceEnergy_le_of_riemannHypothesis hRH ha hu huc heven
  linarith

/-- The shift-averaged variation inequality in autocorrelation form: under RH, for every even
`u ∈ C²_c(ℝ)`,

    ∫ dm(t) ∫_0^t [G(2x−t) − G(t)] (u(x) − u(t−x))² dx
      ≤ 2 ∫ dm(t) ∫_{x>0} [G(t) − G(2x+t)] (u(x) − u(x+t))² dx + 2 ∫_{x>0} u(x)² sinh²(x/2) dx. -/
theorem averaged_variation_inequality_autocorr_of_riemannHypothesis (hRH : RiemannHypothesis)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioo (0 : ℝ) t,
        (riemannAutocorr (2 * x - t) - riemannAutocorr t) * (u x - u (t - x)) ^ 2) +
      (∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
        (riemannAutocorr (2 * x - Real.log n) - riemannAutocorr (Real.log n)) *
          (u x - u (Real.log n - x)) ^ 2) ≤
    2 * ((∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioi (0 : ℝ),
        (riemannAutocorr t - riemannAutocorr (2 * x + t)) * (u x - u (x + t)) ^ 2) +
      ∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioi (0 : ℝ),
        (riemannAutocorr (Real.log n) - riemannAutocorr (2 * x + Real.log n)) *
          (u x - u (x + Real.log n)) ^ 2) +
      2 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * Real.sinh (x / 2) ^ 2 := by
  have h := averagedReflectedEnergy_le_of_riemannHypothesis hRH hu huc heven
  unfold averagedReflectedEnergy averagedSameSideEnergy averagedReflectedShift
    averagedSameSideShift at h
  simp only [averagedKernel_reflected, averagedKernel_sameSide] at h
  exact h

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
