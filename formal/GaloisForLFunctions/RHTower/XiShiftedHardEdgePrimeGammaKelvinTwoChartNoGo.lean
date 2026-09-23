import GaloisForLFunctions.RHTower.XiShiftedHardEdgePrimeGammaKelvinLaplaceDetailedBalance

/-!
# Route U: two-chart obstruction to scalar Gamma renormalization

The normalized Gamma phase rate has incompatible defects in two asymptotic charts selected by the
hard-edge Kelvin geometry.  A fixed logarithmic interior chart has finite defect `-1`, whereas the
fixed physical boundary chart carries one logarithmic unit.  Consequently no scalar counterterm,
with no regularity assumptions whatsoever, can give finite limits in both charts.

This is an unconditional terminal no-go for scalar completion of the Route U Gamma correction.  It
does not assert positivity of the prime/polar source or the Riemann hypothesis.
-/

noncomputable section

open Complex Filter Topology

namespace RHTower

/-- Gamma-rate difference in the fixed logarithmic interior chart. -/
def routeUHardEdgeKelvinGammaInteriorChart (a : ℝ) : ℝ :=
  gammaHardyPhaseRate (a * Real.exp (-1)) -
    gammaHardyPhaseRate (a * Real.exp 1)

/-- Gamma-rate difference in the fixed physical boundary chart. -/
def routeUHardEdgeKelvinGammaPhysicalBoundaryChart (a : ℝ) : ℝ :=
  gammaHardyPhaseRate 1 - gammaHardyPhaseRate (a ^ (2 : ℕ))

/-- The interior Kelvin chart has finite Gamma-rate defect `-1`. -/
theorem routeUHardEdgeKelvinGammaInteriorChart_tendsto :
    Tendsto routeUHardEdgeKelvinGammaInteriorChart atTop (nhds (-1)) := by
  let e : ℝ → ℝ := fun t =>
    gammaHardyPhaseRate t - Real.log (t / (2 * Real.pi)) / 2
  have hminusScale : Tendsto (fun a : ℝ => a * Real.exp (-1)) atTop atTop :=
    tendsto_id.atTop_mul_const (Real.exp_pos (-1))
  have hplusScale : Tendsto (fun a : ℝ => a * Real.exp 1) atTop atTop :=
    tendsto_id.atTop_mul_const (Real.exp_pos 1)
  have hminus : Tendsto (fun a : ℝ => e (a * Real.exp (-1))) atTop (nhds 0) :=
    gammaHardyPhaseRate_sub_log_conductor_tendsto_zero.comp hminusScale
  have hplus : Tendsto (fun a : ℝ => e (a * Real.exp 1)) atTop (nhds 0) :=
    gammaHardyPhaseRate_sub_log_conductor_tendsto_zero.comp hplusScale
  have hmain : Tendsto
      (fun a : ℝ => e (a * Real.exp (-1)) - e (a * Real.exp 1) - 1)
      atTop (nhds (-1)) := by
    simpa using (hminus.sub hplus).sub (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1))
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  dsimp only [routeUHardEdgeKelvinGammaInteriorChart, e]
  rw [Real.log_div (mul_ne_zero ha.ne' (Real.exp_ne_zero (-1)))
      (by positivity : (2 * Real.pi : ℝ) ≠ 0),
    Real.log_div (mul_ne_zero ha.ne' (Real.exp_ne_zero 1))
      (by positivity : (2 * Real.pi : ℝ) ≠ 0),
    Real.log_mul ha.ne' (Real.exp_ne_zero (-1)),
    Real.log_mul ha.ne' (Real.exp_ne_zero 1),
    Real.log_exp, Real.log_exp]
  ring

/-- The physical boundary chart has a logarithmic Gamma-rate defect. -/
theorem routeUHardEdgeKelvinGammaPhysicalBoundaryChart_tendsto :
    Tendsto
      (fun a : ℝ => routeUHardEdgeKelvinGammaPhysicalBoundaryChart a + Real.log a)
      atTop
      (nhds (gammaHardyPhaseRate 1 + Real.log (2 * Real.pi) / 2)) := by
  let e : ℝ → ℝ := fun t =>
    gammaHardyPhaseRate t - Real.log (t / (2 * Real.pi)) / 2
  have hsq : Tendsto (fun a : ℝ => a ^ (2 : ℕ)) atTop atTop :=
    tendsto_pow_atTop (n := 2) (by norm_num)
  have he : Tendsto (fun a : ℝ => e (a ^ (2 : ℕ))) atTop (nhds 0) :=
    gammaHardyPhaseRate_sub_log_conductor_tendsto_zero.comp hsq
  have hmain : Tendsto
      (fun a : ℝ => gammaHardyPhaseRate 1 - e (a ^ (2 : ℕ)) +
        Real.log (2 * Real.pi) / 2)
      atTop
      (nhds (gammaHardyPhaseRate 1 + Real.log (2 * Real.pi) / 2)) := by
    have hconst1 : Tendsto (fun _ : ℝ => gammaHardyPhaseRate 1) atTop
        (nhds (gammaHardyPhaseRate 1)) := tendsto_const_nhds
    have hconst2 : Tendsto (fun _ : ℝ => Real.log (2 * Real.pi) / 2) atTop
        (nhds (Real.log (2 * Real.pi) / 2)) := tendsto_const_nhds
    simpa using (hconst1.sub he).add hconst2
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  dsimp only [routeUHardEdgeKelvinGammaPhysicalBoundaryChart, e]
  rw [Real.log_div (pow_ne_zero 2 ha.ne')
      (by positivity : (2 * Real.pi : ℝ) ≠ 0),
    Real.log_pow]
  ring

/-- No scalar counterterm can simultaneously renormalize the interior and physical-boundary
Kelvin charts to finite limits. -/
theorem not_exists_routeUHardEdgeKelvinGammaGlobalScalarRenormalization :
    ¬ ∃ r : ℝ → ℝ, ∃ LInterior LBoundary : ℝ,
      Tendsto
          (fun a : ℝ => routeUHardEdgeKelvinGammaInteriorChart a + r a)
          atTop (nhds LInterior) ∧
        Tendsto
          (fun a : ℝ => routeUHardEdgeKelvinGammaPhysicalBoundaryChart a + r a)
          atTop (nhds LBoundary) := by
  rintro ⟨r, LInterior, LBoundary, hInterior, hBoundary⟩
  have hr : Tendsto r atTop (nhds (LInterior + 1)) := by
    have h := hInterior.sub routeUHardEdgeKelvinGammaInteriorChart_tendsto
    convert h using 1
    · funext a
      ring
    · ring
  have hrSubLog : Tendsto (fun a : ℝ => r a - Real.log a) atTop
      (nhds (LBoundary -
        (gammaHardyPhaseRate 1 + Real.log (2 * Real.pi) / 2))) := by
    have h := hBoundary.sub
      routeUHardEdgeKelvinGammaPhysicalBoundaryChart_tendsto
    convert h using 1
    · funext a
      ring
  have hrTop : Tendsto r atTop atTop := by
    have h := Real.tendsto_log_atTop.atTop_add hrSubLog
    exact h.congr' (Eventually.of_forall fun a => by ring)
  have hfinite := hr.eventually (Iio_mem_nhds (lt_add_one (LInterior + 1)))
  have hlarge := hrTop.eventually_ge_atTop (LInterior + 2)
  obtain ⟨a, ha, hge⟩ := (hfinite.and hlarge).exists
  exact (not_lt_of_ge hge) (by linarith)

end RHTower
