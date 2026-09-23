import GaloisForLFunctions.HTGeometry.FokasLenellsRawTaylorFifth

/-!
# Fifth-order expansion of both genuine infinite scattering endpoints

Exact divided equations survive the two oriented half-line integrals.
The fifth endpoint remainder converges by the proved whole-line majorant,
so no endpoint regularity or formal series is assumed.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawOrientedFourthIntegrand (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) (x : ℝ) : SpectralVector :=
  if left then -rawFourthIntegrand q k v (-x) else rawFourthIntegrand q k v x

theorem rawOrientedFourthIntegrand_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) :
    Integrable (rawOrientedFourthIntegrand q k v left) := by
  cases left
  · exact rawFourthIntegrand_integrable q k v
  · exact (rawFourthIntegrand_integrable q k v).comp_neg.neg

def rawFourthEndpoint (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) : SpectralVector :=
  ∫ x in Set.Ioi (0 : ℝ), rawOrientedFourthIntegrand q k v left x

def rawOrientedFifthIntegrand (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) (x : ℝ) : SpectralVector :=
  if left then -rawFifthIntegrand q k v (-x) else rawFifthIntegrand q k v x

theorem rawOrientedFifthIntegrand_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) :
    Integrable (rawOrientedFifthIntegrand q k v left) := by
  cases left
  · exact rawFifthIntegrand_integrable q k v
  · exact (rawFifthIntegrand_integrable q k v).comp_neg.neg

def rawFifthEndpoint (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) : SpectralVector :=
  ∫ x in Set.Ioi (0 : ℝ), rawOrientedFifthIntegrand q k v left x

theorem rawOrientedThirdIntegrand_fourth_factor (q : SchwartzMap ℝ ℂ) (k : ℝ)
    (v : SpectralVector) (left : Bool) (x : ℝ) :
    rawOrientedThirdIntegrand q k v left x = rawOrientedThirdIntegrand q 0 v left x+
      (k : ℂ) • rawOrientedFourthIntegrand q k v left x := by
  cases left
  · exact rawThirdIntegrand_fourth_factor q k v x
  · change -rawThirdIntegrand q k v (-x) = -rawThirdIntegrand q 0 v (-x)+
      (k : ℂ) • (-rawFourthIntegrand q k v (-x))
    rw [rawThirdIntegrand_fourth_factor,neg_add,smul_neg]

theorem rawThirdEndpoint_fourth_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) :
    rawThirdEndpoint q k v left = rawThirdEndpoint q 0 v left+(k : ℂ) • rawFourthEndpoint q k v left := by
  have he : (fun x => rawOrientedThirdIntegrand q k v left x) = fun x =>
      rawOrientedThirdIntegrand q 0 v left x+(k : ℂ) • rawOrientedFourthIntegrand q k v left x := by
    funext x
    exact rawOrientedThirdIntegrand_fourth_factor q k v left x
  have hz : IntegrableOn (fun x => rawOrientedThirdIntegrand q 0 v left x) (Set.Ioi (0 : ℝ)) :=
    (rawOrientedThirdIntegrand_integrable q 0 v left).integrableOn
  have hs : IntegrableOn (fun x => (k : ℂ) • rawOrientedFourthIntegrand q k v left x) (Set.Ioi (0 : ℝ)) :=
    ((rawOrientedFourthIntegrand_integrable q k v left).smul (k : ℂ)).integrableOn
  rw [rawThirdEndpoint,he,integral_add hz hs,integral_smul]
  rfl

theorem rawOrientedFourthIntegrand_fifth_factor (q : SchwartzMap ℝ ℂ) (k : ℝ)
    (v : SpectralVector) (left : Bool) (x : ℝ) :
    rawOrientedFourthIntegrand q k v left x = rawOrientedFourthIntegrand q 0 v left x+
      (k : ℂ) • rawOrientedFifthIntegrand q k v left x := by
  cases left
  · exact rawFourthIntegrand_fifth_factor q k v x
  · change -rawFourthIntegrand q k v (-x) = -rawFourthIntegrand q 0 v (-x)+
      (k : ℂ) • (-rawFifthIntegrand q k v (-x))
    rw [rawFourthIntegrand_fifth_factor,neg_add,smul_neg]

theorem rawFourthEndpoint_fifth_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) :
    rawFourthEndpoint q k v left = rawFourthEndpoint q 0 v left+(k : ℂ) • rawFifthEndpoint q k v left := by
  have he : (fun x => rawOrientedFourthIntegrand q k v left x) = fun x =>
      rawOrientedFourthIntegrand q 0 v left x+(k : ℂ) • rawOrientedFifthIntegrand q k v left x := by
    funext x
    exact rawOrientedFourthIntegrand_fifth_factor q k v left x
  have hz : IntegrableOn (fun x => rawOrientedFourthIntegrand q 0 v left x) (Set.Ioi (0 : ℝ)) :=
    (rawOrientedFourthIntegrand_integrable q 0 v left).integrableOn
  have hs : IntegrableOn (fun x => (k : ℂ) • rawOrientedFifthIntegrand q k v left x) (Set.Ioi (0 : ℝ)) :=
    ((rawOrientedFifthIntegrand_integrable q k v left).smul (k : ℂ)).integrableOn
  rw [rawFourthEndpoint,he,integral_add hz hs,integral_smul]
  rfl

/-- The actual local flow has five exact spectral orders and a constructed remainder. -/
theorem rawInteractionSolution_fifth_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    rawInteractionSolution q k v x = v+(k : ℂ) • rawLinearCoefficient q v x+
      (k : ℂ)^(2 : ℕ) • rawSecondSlope q 0 v x+(k : ℂ)^(3 : ℕ) • rawThirdSlope q 0 v x+
      (k : ℂ)^(4 : ℕ) • rawFourthSlope q 0 v x+(k : ℂ)^(5 : ℕ) • rawFifthSlope q k v x := by
  rw [rawInteractionSolution_third_factor,rawThirdSlope_fourth_factor,rawFourthSlope_fifth_factor]
  module

/-- The true infinite Jost endpoints have the same five exact spectral orders. -/
theorem rawAsymptoticVector_fifth_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) :
    rawAsymptoticVector q k v left = v+(k : ℂ) • rawFirstCoefficient q v+
      (k : ℂ)^(2 : ℕ) • rawSecondEndpoint q 0 v left+(k : ℂ)^(3 : ℕ) • rawThirdEndpoint q 0 v left+
      (k : ℂ)^(4 : ℕ) • rawFourthEndpoint q 0 v left+(k : ℂ)^(5 : ℕ) • rawFifthEndpoint q k v left := by
  rw [rawAsymptoticVector_third_factor,rawThirdEndpoint_fourth_factor,rawFourthEndpoint_fifth_factor]
  module

/-- The genuine fifth endpoint remainder converges at zero frequency on both half-lines. -/
theorem rawFifthEndpoint_tendsto_zero (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (left : Bool) :
    Tendsto (fun k => rawFifthEndpoint q k v left) (𝓝 0) (𝓝 (rawFifthEndpoint q 0 v left)) := by
  have hb : Integrable (fun x : ℝ => (‖v‖*Real.exp (rawInteractionMass q))*
      rawFifthDensity q 1 (if left then -x else x)) := by
    cases left
    · exact (rawFifthDensity_integrable q 1).const_mul _
    · exact (rawFifthDensity_integrable q 1).comp_neg.const_mul _
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => (‖v‖*Real.exp (rawInteractionMass q))*rawFifthDensity q 1 (if left then -x else x))
    (Eventually.of_forall fun k => (rawOrientedFifthIntegrand_integrable q k v left).aestronglyMeasurable.restrict)
    ?_ hb.integrableOn ?_
  · filter_upwards [rawFifthIntegrand_eventually_bound q v] with k hk
    apply Eventually.of_forall
    intro x
    have hh := hk (if left then -x else x)
    cases left <;> simpa only [rawOrientedFifthIntegrand,↓reduceIte,Bool.false_eq_true,norm_neg] using hh
  · apply Eventually.of_forall
    intro x
    cases left
    · exact rawFifthIntegrand_tendsto_zero q v x
    · exact (rawFifthIntegrand_tendsto_zero q v (-x)).neg

theorem rawFourthEndpoint_tendsto_zero (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (left : Bool) :
    Tendsto (fun k => rawFourthEndpoint q k v left) (𝓝 0) (𝓝 (rawFourthEndpoint q 0 v left)) := by
  have hc : Tendsto (fun _ : ℝ => rawFourthEndpoint q 0 v left) (𝓝 0) (𝓝 (rawFourthEndpoint q 0 v left)) := tendsto_const_nhds
  have hh := hc.add ((Complex.continuous_ofReal.tendsto 0).smul (rawFifthEndpoint_tendsto_zero q v left))
  simpa only [← rawFourthEndpoint_fifth_factor,Complex.ofReal_zero,zero_smul,add_zero] using hh

end
end GaloisForLFunctions.HTGeometry.FokasLenells
