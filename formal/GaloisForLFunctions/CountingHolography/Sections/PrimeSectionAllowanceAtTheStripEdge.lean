import GaloisForLFunctions.CountingHolography.Sections.SmallSectionsOnPrimePairs
import GaloisForLFunctions.FloorFreeArithmetic.TheTopTraceDeterminesTheTopLayer

/-!
# An unconditional allowance for the two-graph sections

For the effective pair of degrees one and p, the discrepancy between the
logarithmic modulus and radius is smaller than ε√p times the squared
multiplicity at every sufficiently large degree and then every sufficiently
large multiplicity. The open strip has no zeros on its right edge, so the
spline trace normalized at that edge tends to zero.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology Zeta23 SurfaceOfSpecZ ArithmeticOrientationGeometry
open ArithmeticScatteringHolography RenormalizedIntersectionTheory

/-- The signed degree per squared multiplicity is little-o of the square
root of the second conductor. This applies to every positive degree. -/
theorem tendsto_primePair_degree_div_sqrt :
    Tendsto (fun p : ℕ => integerProbe (p+1) (primePair p) / Real.sqrt p) atTop (𝓝 0) := by
  have hstrip (ρ : ℂ) (hρ : ρ ∈ zetaZeroConfig.carrier) : ρ.re < 1/2 + 1/2 := by
    linarith only [(zetaZeroConfig.strip ρ hρ).2]
  have htop : TopDepth zetaZeroConfig (1/2) := fun z hz =>
    (le_abs_self _).trans (abs_re_le_of_traceCoeff_ne_zero_of_re_le
      (fun ρ hρ => (hstrip ρ hρ).le) (r := 3) hz)
  have ht := (FloorFreeArithmetic.tendsto_normTrace_zeta_zero_iff (by norm_num) htop).mpr
    (fun ρ hρ => (hstrip ρ hρ).ne)
  have hl := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hs := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun p : ℕ => 2*(splineSeries 0).re / Real.sqrt p) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hs
  have hh := hc.add (ht.comp hl)
  rw [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with p hp
  have hp' : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  change _ + normTrace zetaZeroConfig (1/2) (Real.log p) = _
  rw [integerProbe_primePair hp, add_div, normTrace, ← orbitCorr_eq_re_lagStructure_spline,
    orbitCorr_splineCycle_eq, Real.exp_neg, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp']
  ring

/-- On each sufficiently large pair, every sufficiently high multiple has
absolute degree below any prescribed positive multiple of √p times m². -/
theorem eventually_primePair_degree_allowance (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      |radius (m • primePair p) - Real.log (generator (m • primePair p) : ℝ)| <
        ε * Real.sqrt p * (m : ℝ)^2 := by
  have ht := tendsto_primePair_degree_div_sqrt.abs
  rw [abs_zero] at ht
  filter_upwards [ht.eventually_lt_const hε, eventually_ge_atTop 1] with p hp hp1
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos_of_pos (Nat.cast_pos.mpr hp1)
  rw [abs_div, abs_of_pos hsp, div_lt_iff₀ hsp] at hp
  have hm := (tendsto_splineDegree (primePair p)).abs.eventually_lt_const hp
  filter_upwards [hm, eventually_ge_atTop 1] with m hm hm1
  have hm2 : 0 < (m : ℝ)^2 := by positivity
  rwa [abs_div, abs_of_pos hm2, div_lt_iff₀ hm2] at hm

#print axioms eventually_primePair_degree_allowance

end GaloisForLFunctions.CountingHolography.Sections
