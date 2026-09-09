import GaloisForLFunctions.HTGeometry.FokasLenellsRawTaylorSecond

/-!
# An exact cubic expansion of the original scattering flow

A second iteration of the divided integral equation yields a cubic
remainder with a whole-line integrable bound and a proved zero-frequency
limit. This expands the actual solution, not a formally postulated series.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawThirdIntegrand (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) : SpectralVector :=
  rawDividedOperator q 0 x (rawSecondSlope q k v x)+
    rawCubicOperator q k x (rawInteractionSolution q k v x)

def rawThirdDensity (q : SchwartzMap ℝ ℂ) (k x : ℝ) : ℝ :=
  (rawInteractionMass q^2+|k| * rawCubicMass q)*rawInteractionDensity q x+rawCubicDensity q x

theorem rawThirdDensity_nonneg (q : SchwartzMap ℝ ℂ) (k x : ℝ) : 0 ≤ rawThirdDensity q k x :=
  add_nonneg (mul_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg (abs_nonneg k) (rawCubicMass_nonneg q)))
    (rawInteractionDensity_nonneg q x)) (rawCubicDensity_nonneg q x)

theorem rawThirdDensity_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) : Integrable (rawThirdDensity q k) :=
  ((rawInteractionDensity_integrable q).const_mul (rawInteractionMass q^2+|k| * rawCubicMass q)).add
    (rawCubicDensity_integrable q)

theorem continuous_rawThirdIntegrand (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Continuous (rawThirdIntegrand q k v) :=
  ((continuous_rawDividedOperator q 0).clm_apply (continuous_rawSecondSlope q k v)).add
    ((continuous_rawCubicOperator q k).clm_apply (continuous_rawInteractionSolution q k v))

theorem rawThirdIntegrand_bound (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    ‖rawThirdIntegrand q k v x‖ ≤
      (‖v‖*Real.exp (|k| * rawInteractionMass q))*rawThirdDensity q k x := by
  have hL := ((rawDividedOperator q 0 x).le_opNorm (rawSecondSlope q k v x)).trans
    (mul_le_mul (rawDividedOperator_bound q 0 x) (rawSecondSlope_bound q k v x)
      (norm_nonneg _) (rawInteractionDensity_nonneg q x))
  have hC := ((rawCubicOperator q k x).le_opNorm (rawInteractionSolution q k v x)).trans
    (mul_le_mul (rawCubicOperator_bound q k x) (rawInteractionSolution_global_bound q k v x)
      (norm_nonneg _) (rawCubicDensity_nonneg q x))
  exact (norm_add_le _ _).trans ((add_le_add hL hC).trans_eq (by unfold rawThirdDensity; ring))

theorem rawThirdIntegrand_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Integrable (rawThirdIntegrand q k v) :=
  ((rawThirdDensity_integrable q k).const_mul (‖v‖*Real.exp (|k| * rawInteractionMass q))).mono'
    (continuous_rawThirdIntegrand q k v).aestronglyMeasurable
    (Eventually.of_forall (rawThirdIntegrand_bound q k v))

/-- Exact factorization after subtracting the actual second coefficient. -/
theorem rawSecondIntegrand_third_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    rawSecondIntegrand q k v x = rawSecondIntegrand q 0 v x+(k : ℂ) • rawThirdIntegrand q k v x := by
  unfold rawSecondIntegrand rawThirdIntegrand
  rw [rawSolutionSlope_second_factor,rawSolutionSlope_zero]
  simp only [Complex.ofReal_zero,zero_smul,add_zero,map_add,map_smul,smul_add,add_assoc]

def rawThirdSlope (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) : SpectralVector :=
  ∫ s in (0 : ℝ)..x, rawThirdIntegrand q k v s

theorem continuous_rawThirdSlope (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Continuous (rawThirdSlope q k v) := (rawThirdIntegrand_integrable q k v).continuous_primitive 0

theorem rawSecondSlope_third_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    rawSecondSlope q k v x = rawSecondSlope q 0 v x+(k : ℂ) • rawThirdSlope q k v x := by
  have he : (fun s => rawSecondIntegrand q k v s) =
      fun s => rawSecondIntegrand q 0 v s+(k : ℂ) • rawThirdIntegrand q k v s := by
    funext s
    exact rawSecondIntegrand_third_factor q k v s
  rw [rawSecondSlope,he]
  have hz : IntervalIntegrable (fun s => rawSecondIntegrand q 0 v s) volume 0 x :=
    (rawSecondIntegrand_integrable q 0 v).intervalIntegrable
  have hs : IntervalIntegrable (fun s => (k : ℂ) • rawThirdIntegrand q k v s) volume 0 x :=
    ((rawThirdIntegrand_integrable q k v).smul (k : ℂ)).intervalIntegrable
  rw [intervalIntegral.integral_add hz hs,intervalIntegral.integral_smul]
  rfl

/-- A cubic expansion with an explicitly constructed remainder, exact for every real frequency. -/
theorem rawInteractionSolution_third_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    rawInteractionSolution q k v x = v+(k : ℂ) • rawLinearCoefficient q v x+
      (k : ℂ)^2 • rawSecondSlope q 0 v x+(k : ℂ)^3 • rawThirdSlope q k v x := by
  rw [rawInteractionSolution_second_factor,rawSecondSlope_third_factor,smul_add,smul_smul]
  have he : (k : ℂ)^2*(k : ℂ) = (k : ℂ)^3 := by ring
  rw [he]
  simp only [add_assoc]

theorem rawThirdSlope_bound (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    ‖rawThirdSlope q k v x‖ ≤ (‖v‖*Real.exp (|k| * rawInteractionMass q))*
      ((rawInteractionMass q^2+|k| * rawCubicMass q)*rawInteractionMass q+rawCubicMass q) := by
  have h1 : ‖rawThirdSlope q k v x‖ ≤ ∫ s : ℝ, ‖rawThirdIntegrand q k v s‖ :=
    intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
      (setIntegral_le_integral (rawThirdIntegrand_integrable q k v).norm
        (Eventually.of_forall fun s => norm_nonneg (rawThirdIntegrand q k v s)))
  have h2 := integral_mono (rawThirdIntegrand_integrable q k v).norm
    ((rawThirdDensity_integrable q k).const_mul (‖v‖*Real.exp (|k| * rawInteractionMass q)))
    (rawThirdIntegrand_bound q k v)
  have he : (∫ s : ℝ, rawThirdDensity q k s) =
      (rawInteractionMass q^2+|k| * rawCubicMass q)*rawInteractionMass q+rawCubicMass q := by
    rw [show (fun s => rawThirdDensity q k s) = fun s =>
      (rawInteractionMass q^2+|k| * rawCubicMass q)*rawInteractionDensity q s+rawCubicDensity q s from rfl]
    rw [integral_add ((rawInteractionDensity_integrable q).const_mul _)
      (rawCubicDensity_integrable q),integral_const_mul]
    rfl
  rw [integral_const_mul,he] at h2
  exact h1.trans h2

theorem rawThirdIntegrand_tendsto_zero (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    Tendsto (fun k => rawThirdIntegrand q k v x) (𝓝 0) (𝓝 (rawThirdIntegrand q 0 v x)) := by
  have hL := ((rawDividedOperator q 0 x).continuous.tendsto _).comp (rawSecondSlope_tendsto_zero q v x)
  have hc : Continuous (fun k : ℝ => rawCubicOperator q k x) := by
    have hp : Continuous (fun k : ℝ => (k,x)) := continuous_id.prodMk continuous_const
    have hh := (continuous_rawCubicOperator_parameters q).comp hp
    exact hh
  have hC := (hc.continuousAt.clm_apply (continuousAt_rawInteractionSolution_zero_frequency q v x)).tendsto
  have hh := hL.add hC
  exact hh

/-- The genuine cubic remainder converges, with no formal power-series hypothesis. -/
theorem rawThirdSlope_tendsto_zero (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    Tendsto (fun k => rawThirdSlope q k v x) (𝓝 0) (𝓝 (rawThirdSlope q 0 v x)) := by
  have hb := (rawThirdDensity_integrable q 1).const_mul (‖v‖*Real.exp (rawInteractionMass q))
  have hk : ∀ᶠ k : ℝ in 𝓝 0, |k| < 1 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simp)
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun s => (‖v‖*Real.exp (rawInteractionMass q))*rawThirdDensity q 1 s)
    (Eventually.of_forall fun k => (rawThirdIntegrand_integrable q k v).aestronglyMeasurable.restrict)
    ?_ hb.intervalIntegrable ?_
  · filter_upwards [hk] with k hk
    apply Eventually.of_forall
    intro s _
    have hm : |k| * rawInteractionMass q ≤ rawInteractionMass q := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hk.le (rawInteractionMass_nonneg q)
    have hd : rawThirdDensity q k s ≤ rawThirdDensity q 1 s := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hk.le.trans_eq (abs_one.symm)) (rawCubicMass_nonneg q)))
          (rawInteractionDensity_nonneg q s)) le_rfl
    exact (rawThirdIntegrand_bound q k v s).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hm) (norm_nonneg v)) hd
        (rawThirdDensity_nonneg q k s) (mul_nonneg (norm_nonneg v) (Real.exp_pos _).le))
  · exact Eventually.of_forall fun s _ => rawThirdIntegrand_tendsto_zero q v s

end
end GaloisForLFunctions.HTGeometry.FokasLenells
