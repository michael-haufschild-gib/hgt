import GaloisForLFunctions.HTGeometry.FokasLenellsRawTaylorThird

/-!
# Cubic expansion of the actual infinite scattering endpoints

Every coefficient is obtained by integrating the constructed original
solution and its exact divided equations. Uniform whole-line majorants
justify the zero-frequency limits on both half-lines. The expansion has an
actual convergent cubic remainder and imposes no compatibility condition.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawOrientedSecondIntegrand (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) (x : ℝ) : SpectralVector :=
  if left then -rawSecondIntegrand q k v (-x) else rawSecondIntegrand q k v x

def rawOrientedThirdIntegrand (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) (x : ℝ) : SpectralVector :=
  if left then -rawThirdIntegrand q k v (-x) else rawThirdIntegrand q k v x

theorem rawOrientedSecondIntegrand_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) :
    Integrable (rawOrientedSecondIntegrand q k v left) := by
  cases left
  · exact rawSecondIntegrand_integrable q k v
  · exact (rawSecondIntegrand_integrable q k v).comp_neg.neg

theorem rawOrientedThirdIntegrand_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) :
    Integrable (rawOrientedThirdIntegrand q k v left) := by
  cases left
  · exact rawThirdIntegrand_integrable q k v
  · exact (rawThirdIntegrand_integrable q k v).comp_neg.neg

theorem rawOrientedDividedDerivative_second_factor (q : SchwartzMap ℝ ℂ) (k : ℝ)
    (v : SpectralVector) (left : Bool) (x : ℝ) :
    rawOrientedDividedDerivative q k v left x = rawOrientedDividedDerivative q 0 v left x+
      (k : ℂ) • rawOrientedSecondIntegrand q k v left x := by
  cases left
  · exact rawDividedDerivative_second_factor q k v x
  · change -rawDividedDerivative q k v (-x) = -rawDividedDerivative q 0 v (-x)+
      (k : ℂ) • (-rawSecondIntegrand q k v (-x))
    rw [rawDividedDerivative_second_factor,neg_add,smul_neg]

theorem rawOrientedSecondIntegrand_third_factor (q : SchwartzMap ℝ ℂ) (k : ℝ)
    (v : SpectralVector) (left : Bool) (x : ℝ) :
    rawOrientedSecondIntegrand q k v left x = rawOrientedSecondIntegrand q 0 v left x+
      (k : ℂ) • rawOrientedThirdIntegrand q k v left x := by
  cases left
  · exact rawSecondIntegrand_third_factor q k v x
  · change -rawSecondIntegrand q k v (-x) = -rawSecondIntegrand q 0 v (-x)+
      (k : ℂ) • (-rawThirdIntegrand q k v (-x))
    rw [rawSecondIntegrand_third_factor,neg_add,smul_neg]

def rawSecondEndpoint (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) : SpectralVector :=
  ∫ x in Set.Ioi (0 : ℝ), rawOrientedSecondIntegrand q k v left x

def rawThirdEndpoint (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) : SpectralVector :=
  ∫ x in Set.Ioi (0 : ℝ), rawOrientedThirdIntegrand q k v left x

/-- The exact second divided equation survives integration to either spatial infinity. -/
theorem rawFirstSlope_second_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) :
    rawFirstSlope q k v left = rawFirstCoefficient q v+(k : ℂ) • rawSecondEndpoint q k v left := by
  have he : (fun x => rawOrientedDividedDerivative q k v left x) = fun x =>
      rawOrientedDividedDerivative q 0 v left x+(k : ℂ) • rawOrientedSecondIntegrand q k v left x := by
    funext x
    exact rawOrientedDividedDerivative_second_factor q k v left x
  have hz : IntegrableOn (fun x => rawOrientedDividedDerivative q 0 v left x) (Set.Ioi (0 : ℝ)) :=
    (rawOrientedDividedDerivative_integrable q 0 v left).integrableOn
  have hs : IntegrableOn (fun x => (k : ℂ) • rawOrientedSecondIntegrand q k v left x) (Set.Ioi (0 : ℝ)) :=
    ((rawOrientedSecondIntegrand_integrable q k v left).smul (k : ℂ)).integrableOn
  rw [rawFirstSlope,he,integral_add hz hs,integral_smul]
  exact congrArg (fun w => w+(k : ℂ) • rawSecondEndpoint q k v left) (rawFirstSlope_zero q v left)

/-- The cubic divided equation also survives integration to both infinite endpoints. -/
theorem rawSecondEndpoint_third_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) :
    rawSecondEndpoint q k v left = rawSecondEndpoint q 0 v left+(k : ℂ) • rawThirdEndpoint q k v left := by
  have he : (fun x => rawOrientedSecondIntegrand q k v left x) = fun x =>
      rawOrientedSecondIntegrand q 0 v left x+(k : ℂ) • rawOrientedThirdIntegrand q k v left x := by
    funext x
    exact rawOrientedSecondIntegrand_third_factor q k v left x
  have hz : IntegrableOn (fun x => rawOrientedSecondIntegrand q 0 v left x) (Set.Ioi (0 : ℝ)) :=
    (rawOrientedSecondIntegrand_integrable q 0 v left).integrableOn
  have hs : IntegrableOn (fun x => (k : ℂ) • rawOrientedThirdIntegrand q k v left x) (Set.Ioi (0 : ℝ)) :=
    ((rawOrientedThirdIntegrand_integrable q k v left).smul (k : ℂ)).integrableOn
  rw [rawSecondEndpoint,he,integral_add hz hs,integral_smul]
  rfl

/-- This is an exact cubic expansion of the genuine Jost endpoint, at every real frequency. -/
theorem rawAsymptoticVector_third_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) :
    rawAsymptoticVector q k v left = v+(k : ℂ) • rawFirstCoefficient q v+
      (k : ℂ)^2 • rawSecondEndpoint q 0 v left+(k : ℂ)^3 • rawThirdEndpoint q k v left := by
  rw [rawAsymptoticVector_first_factor,rawFirstSlope_second_factor,rawSecondEndpoint_third_factor]
  simp only [smul_add,smul_smul,pow_succ,pow_zero,one_mul,mul_assoc,add_assoc]

/-- Dominated convergence controls the genuine cubic endpoint remainder across zero. -/
theorem rawThirdEndpoint_tendsto_zero (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (left : Bool) :
    Tendsto (fun k => rawThirdEndpoint q k v left) (𝓝 0) (𝓝 (rawThirdEndpoint q 0 v left)) := by
  have hb : Integrable (fun x : ℝ => (‖v‖*Real.exp (rawInteractionMass q))*
      rawThirdDensity q 1 (if left then -x else x)) := by
    cases left
    · exact (rawThirdDensity_integrable q 1).const_mul _
    · exact (rawThirdDensity_integrable q 1).comp_neg.const_mul _
  have hk : ∀ᶠ k : ℝ in 𝓝 0, |k| < 1 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simp)
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => (‖v‖*Real.exp (rawInteractionMass q))*rawThirdDensity q 1 (if left then -x else x))
    (Eventually.of_forall fun k => (rawOrientedThirdIntegrand_integrable q k v left).aestronglyMeasurable.restrict)
    ?_ hb.integrableOn ?_
  · filter_upwards [hk] with k hk
    apply Eventually.of_forall
    intro x
    let y := if left then -x else x
    have hm : |k| * rawInteractionMass q ≤ rawInteractionMass q := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hk.le (rawInteractionMass_nonneg q)
    have hd : rawThirdDensity q k y ≤ rawThirdDensity q 1 y := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hk.le.trans_eq (abs_one.symm)) (rawCubicMass_nonneg q)))
          (rawInteractionDensity_nonneg q y)) le_rfl
    have hh := (rawThirdIntegrand_bound q k v y).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hm) (norm_nonneg v)) hd
        (rawThirdDensity_nonneg q k y) (mul_nonneg (norm_nonneg v) (Real.exp_pos _).le))
    cases left <;> simpa only [rawOrientedThirdIntegrand,↓reduceIte,Bool.false_eq_true,norm_neg,y] using hh
  · apply Eventually.of_forall
    intro x
    cases left
    · exact rawThirdIntegrand_tendsto_zero q v x
    · exact (rawThirdIntegrand_tendsto_zero q v (-x)).neg

theorem rawSecondEndpoint_tendsto_zero (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (left : Bool) :
    Tendsto (fun k => rawSecondEndpoint q k v left) (𝓝 0) (𝓝 (rawSecondEndpoint q 0 v left)) := by
  have hconst : Tendsto (fun _ : ℝ => rawSecondEndpoint q 0 v left) (𝓝 0) (𝓝 (rawSecondEndpoint q 0 v left)) := tendsto_const_nhds
  have hh := hconst.add ((Complex.continuous_ofReal.tendsto 0).smul
    (rawThirdEndpoint_tendsto_zero q v left))
  simpa only [← rawSecondEndpoint_third_factor,Complex.ofReal_zero,zero_smul,add_zero] using hh

end
end GaloisForLFunctions.HTGeometry.FokasLenells
