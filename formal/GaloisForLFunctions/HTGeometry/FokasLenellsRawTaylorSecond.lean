import GaloisForLFunctions.HTGeometry.FokasLenellsRawTaylorFirst
import GaloisForLFunctions.HTGeometry.FokasLenellsRawCubicKernel

/-!
# An exact second remainder for the original scattering flow

Iterating the divided integral equation exposes the next coefficient of the
actual solution. The remainder is uniformly bounded on the whole spatial
line and converges through zero by dominated convergence. No differentiability
of a hypothetical scattering family is assumed.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawSecondIntegrand (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) : SpectralVector :=
  rawDividedOperator q 0 x (rawSolutionSlope q k v x)+
    (k : ℂ) • rawCubicOperator q k x (rawInteractionSolution q k v x)

def rawSecondDensity (q : SchwartzMap ℝ ℂ) (k x : ℝ) : ℝ :=
  rawInteractionMass q*rawInteractionDensity q x+|k| * rawCubicDensity q x

theorem rawSecondDensity_nonneg (q : SchwartzMap ℝ ℂ) (k x : ℝ) : 0 ≤ rawSecondDensity q k x :=
  add_nonneg (mul_nonneg (rawInteractionMass_nonneg q) (rawInteractionDensity_nonneg q x))
    (mul_nonneg (abs_nonneg k) (rawCubicDensity_nonneg q x))

theorem rawSecondDensity_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) : Integrable (rawSecondDensity q k) :=
  ((rawInteractionDensity_integrable q).const_mul (rawInteractionMass q)).add
    ((rawCubicDensity_integrable q).const_mul |k|)

theorem continuous_rawSecondIntegrand (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Continuous (rawSecondIntegrand q k v) :=
  ((continuous_rawDividedOperator q 0).clm_apply (continuous_rawSolutionSlope q k v)).add
    (((continuous_rawCubicOperator q k).clm_apply (continuous_rawInteractionSolution q k v)).const_smul (k : ℂ))

/-- The second remainder has a whole-line integrable majorant at every real frequency. -/
theorem rawSecondIntegrand_bound (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    ‖rawSecondIntegrand q k v x‖ ≤
      (‖v‖*Real.exp (|k| * rawInteractionMass q))*rawSecondDensity q k x := by
  have hL := ((rawDividedOperator q 0 x).le_opNorm (rawSolutionSlope q k v x)).trans
    (mul_le_mul (rawDividedOperator_bound q 0 x) (rawSolutionSlope_bound q k v x)
      (norm_nonneg _) (rawInteractionDensity_nonneg q x))
  have hC := ((rawCubicOperator q k x).le_opNorm (rawInteractionSolution q k v x)).trans
    (mul_le_mul (rawCubicOperator_bound q k x) (rawInteractionSolution_global_bound q k v x)
      (norm_nonneg _) (rawCubicDensity_nonneg q x))
  have hh := add_le_add hL (mul_le_mul_of_nonneg_left hC (abs_nonneg k))
  have hn := norm_add_le (rawDividedOperator q 0 x (rawSolutionSlope q k v x))
    ((k : ℂ) • rawCubicOperator q k x (rawInteractionSolution q k v x))
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs] at hn
  exact hn.trans (hh.trans_eq (by unfold rawSecondDensity; ring))

theorem rawSecondIntegrand_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Integrable (rawSecondIntegrand q k v) :=
  ((rawSecondDensity_integrable q k).const_mul (‖v‖*Real.exp (|k| * rawInteractionMass q))).mono'
    (continuous_rawSecondIntegrand q k v).aestronglyMeasurable
    (Eventually.of_forall (rawSecondIntegrand_bound q k v))

/-- Exact factorization of the actual divided derivative after subtracting its constant coefficient. -/
theorem rawDividedDerivative_second_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    rawDividedDerivative q k v x = rawDividedDerivative q 0 v x+(k : ℂ) • rawSecondIntegrand q k v x := by
  unfold rawDividedDerivative
  rw [rawInteractionSolution_zero_frequency]
  calc
    _ = rawDividedOperator q 0 x (rawInteractionSolution q k v x)+
        (k : ℂ)^(2 : ℕ) • rawCubicOperator q k x (rawInteractionSolution q k v x) := by
      rw [rawDividedOperator_cubic_factor]
      rfl
    _ = rawDividedOperator q 0 x (v+(k : ℂ) • rawSolutionSlope q k v x)+
        (k : ℂ)^(2 : ℕ) • rawCubicOperator q k x (rawInteractionSolution q k v x) := by
      congr 1
      rw [rawInteractionSolution_first_factor]
    _ = _ := by
      simp only [map_add,map_smul,rawSecondIntegrand,smul_add,smul_smul,pow_two,add_assoc]

def rawSecondSlope (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) : SpectralVector :=
  ∫ s in (0 : ℝ)..x, rawSecondIntegrand q k v s

theorem continuous_rawSecondSlope (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Continuous (rawSecondSlope q k v) := (rawSecondIntegrand_integrable q k v).continuous_primitive 0

/-- Iterating the true integral equation yields an exact second divided difference. -/
theorem rawSolutionSlope_second_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    rawSolutionSlope q k v x = rawLinearCoefficient q v x+(k : ℂ) • rawSecondSlope q k v x := by
  have he : (fun s => rawDividedDerivative q k v s) =
      fun s => rawDividedDerivative q 0 v s+(k : ℂ) • rawSecondIntegrand q k v s := by
    funext s
    exact rawDividedDerivative_second_factor q k v s
  rw [rawSolutionSlope,he]
  have hz : IntervalIntegrable (fun s => rawDividedDerivative q 0 v s) volume 0 x :=
    (rawDividedDerivative_integrable q 0 v).intervalIntegrable
  have hs : IntervalIntegrable (fun s => (k : ℂ) • rawSecondIntegrand q k v s) volume 0 x :=
    ((rawSecondIntegrand_integrable q k v).smul (k : ℂ)).intervalIntegrable
  rw [intervalIntegral.integral_add hz hs,intervalIntegral.integral_smul]
  exact congrArg (fun w => w+(k : ℂ) • rawSecondSlope q k v x) (rawSolutionSlope_zero q v x)

theorem rawInteractionSolution_second_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    rawInteractionSolution q k v x =
      v+(k : ℂ) • rawLinearCoefficient q v x+(k : ℂ)^(2 : ℕ) • rawSecondSlope q k v x := by
  rw [rawInteractionSolution_first_factor,rawSolutionSlope_second_factor]
  simp only [smul_add,smul_smul,pow_two,add_assoc]

theorem rawSecondSlope_bound (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    ‖rawSecondSlope q k v x‖ ≤
      (‖v‖*Real.exp (|k| * rawInteractionMass q))*(rawInteractionMass q^(2 : ℕ)+|k| * rawCubicMass q) := by
  have h1 : ‖rawSecondSlope q k v x‖ ≤ ∫ s : ℝ, ‖rawSecondIntegrand q k v s‖ :=
    intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
      (setIntegral_le_integral (rawSecondIntegrand_integrable q k v).norm
        (Eventually.of_forall fun s => norm_nonneg (rawSecondIntegrand q k v s)))
  have h2 := integral_mono (rawSecondIntegrand_integrable q k v).norm
    ((rawSecondDensity_integrable q k).const_mul (‖v‖*Real.exp (|k| * rawInteractionMass q)))
    (rawSecondIntegrand_bound q k v)
  have he : (∫ s : ℝ, rawSecondDensity q k s) = rawInteractionMass q^(2 : ℕ)+|k| * rawCubicMass q := by
    rw [show (fun s => rawSecondDensity q k s) = fun s =>
      rawInteractionMass q*rawInteractionDensity q s+|k| * rawCubicDensity q s from rfl]
    rw [integral_add ((rawInteractionDensity_integrable q).const_mul _)
      ((rawCubicDensity_integrable q).const_mul _),integral_const_mul,integral_const_mul]
    simp only [rawInteractionMass,rawCubicMass,pow_two]
  rw [integral_const_mul,he] at h2
  exact h1.trans h2

theorem rawSecondIntegrand_tendsto_zero (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    Tendsto (fun k => rawSecondIntegrand q k v x) (𝓝 0) (𝓝 (rawSecondIntegrand q 0 v x)) := by
  have hL := ((rawDividedOperator q 0 x).continuous.tendsto _).comp (rawSolutionSlope_tendsto_zero q v x)
  have hc : Continuous (fun k : ℝ => rawCubicOperator q k x) := by
    have hp : Continuous (fun k : ℝ => (k,x)) := continuous_id.prodMk continuous_const
    have hh := (continuous_rawCubicOperator_parameters q).comp hp
    exact hh
  have hC := (hc.continuousAt.clm_apply (continuousAt_rawInteractionSolution_zero_frequency q v x)).tendsto
  have hh := hL.add ((Complex.continuous_ofReal.tendsto 0).smul hC)
  simpa only [Function.comp_def,rawSecondIntegrand,Complex.ofReal_zero,zero_smul,add_zero,
    rawInteractionSolution_zero_frequency] using hh

/-- The exact second remainder has a well-defined zero-frequency limit, for every spatial point. -/
theorem rawSecondSlope_tendsto_zero (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    Tendsto (fun k => rawSecondSlope q k v x) (𝓝 0) (𝓝 (rawSecondSlope q 0 v x)) := by
  have hb := (rawSecondDensity_integrable q 1).const_mul (‖v‖*Real.exp (rawInteractionMass q))
  have hk : ∀ᶠ k : ℝ in 𝓝 0, |k| < 1 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simp)
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun s => (‖v‖*Real.exp (rawInteractionMass q))*rawSecondDensity q 1 s)
    (Eventually.of_forall fun k => (rawSecondIntegrand_integrable q k v).aestronglyMeasurable.restrict)
    ?_ hb.intervalIntegrable ?_
  · filter_upwards [hk] with k hk
    apply Eventually.of_forall
    intro s _
    have hm : |k| * rawInteractionMass q ≤ rawInteractionMass q := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hk.le (rawInteractionMass_nonneg q)
    have hd : rawSecondDensity q k s ≤ rawSecondDensity q 1 s := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (hk.le.trans_eq (abs_one.symm))
        (rawCubicDensity_nonneg q s))
    exact (rawSecondIntegrand_bound q k v s).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hm) (norm_nonneg v)) hd
        (rawSecondDensity_nonneg q k s) (mul_nonneg (norm_nonneg v) (Real.exp_pos _).le))
  · exact Eventually.of_forall fun s _ => rawSecondIntegrand_tendsto_zero q v s

end
end GaloisForLFunctions.HTGeometry.FokasLenells
