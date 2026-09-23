import GaloisForLFunctions.HTGeometry.FokasLenellsRawZero

/-!
# Removing the first spectral factor from the true scattering equation

The divided coefficient is defined explicitly at zero, without dividing by a
possibly vanishing frequency. Its operator norm is bounded by the same
integrable density for every k. This supplies the majorant for Taylor limits
of the genuine endpoint states.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawDividedOperator (q : SchwartzMap ℝ ℂ) (k x : ℝ) : RawOperator :=
  ((I*FDNLS.staggerPhase (2*k^(2 : ℕ)) x*reflectedDerivative q x) • ContinuousLinearMap.snd ℂ ℂ ℂ).prod
    ((I*FDNLS.staggerPhase (-(2*k^(2 : ℕ))) x*SchwartzMap.derivCLM ℂ ℂ q x) • ContinuousLinearMap.fst ℂ ℂ ℂ)

theorem rawDividedOperator_apply (q : SchwartzMap ℝ ℂ) (k x : ℝ) (v : SpectralVector) :
    rawDividedOperator q k x v =
      (I*FDNLS.staggerPhase (2*k^(2 : ℕ)) x*reflectedDerivative q x*v.2,
       I*FDNLS.staggerPhase (-(2*k^(2 : ℕ))) x*SchwartzMap.derivCLM ℂ ℂ q x*v.1) := rfl

theorem continuous_rawDividedOperator_parameters (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : ℝ × ℝ => rawDividedOperator q p.1 p.2) := by
  let U : ℝ × ℝ → SpectralVector →L[ℂ] ℂ := fun p =>
    (I*FDNLS.staggerPhase (2*p.1^(2 : ℕ)) p.2*reflectedDerivative q p.2) • ContinuousLinearMap.snd ℂ ℂ ℂ
  let V : ℝ × ℝ → SpectralVector →L[ℂ] ℂ := fun p =>
    (I*FDNLS.staggerPhase (-(2*p.1^(2 : ℕ))) p.2*SchwartzMap.derivCLM ℂ ℂ q p.2) • ContinuousLinearMap.fst ℂ ℂ ℂ
  have hU : Continuous U := by unfold U FDNLS.staggerPhase; fun_prop
  have hV : Continuous V := by unfold V FDNLS.staggerPhase; fun_prop
  exact (ContinuousLinearMap.prodₗᵢ (𝕜 := ℂ) (E := SpectralVector) (F := ℂ) (G := ℂ) ℂ).continuous.comp (hU.prodMk hV)

theorem continuous_rawDividedOperator (q : SchwartzMap ℝ ℂ) (k : ℝ) :
    Continuous (rawDividedOperator q k) := by
  have hp : Continuous (fun x : ℝ => (k,x)) := continuous_const.prodMk continuous_id
  have hh := (continuous_rawDividedOperator_parameters q).comp hp
  exact hh

/-- Removing k leaves an operator with a frequency-independent, integrable norm bound. -/
theorem rawDividedOperator_bound (q : SchwartzMap ℝ ℂ) (k x : ℝ) :
    ‖rawDividedOperator q k x‖ ≤ rawInteractionDensity q x := by
  unfold rawDividedOperator
  rw [ContinuousLinearMap.opNorm_prod,Prod.norm_def]
  simp only [norm_smul,ContinuousLinearMap.norm_snd,ContinuousLinearMap.norm_fst,mul_one,
    norm_mul,Complex.norm_I,FDNLS.norm_staggerPhase,one_mul]
  exact max_le (le_add_of_nonneg_left (norm_nonneg _)) (le_add_of_nonneg_right (norm_nonneg _))

theorem rawDividedOperator_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) :
    Integrable (rawDividedOperator q k) :=
  (rawInteractionDensity_integrable q).mono' (continuous_rawDividedOperator q k).aestronglyMeasurable
    (Eventually.of_forall (rawDividedOperator_bound q k))

/-- Exact factorization, valid also at k = 0. -/
theorem rawInteractionOperator_factor (q : SchwartzMap ℝ ℂ) (k x : ℝ) :
    rawInteractionOperator q k x = (k : ℂ) • rawDividedOperator q k x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [rawInteractionOperator_apply]
  change _ = (k : ℂ) • rawDividedOperator q k x v
  rw [rawDividedOperator_apply]
  apply Prod.ext <;> simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring

def rawDividedDerivative (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) : SpectralVector :=
  rawDividedOperator q k x (rawInteractionSolution q k v x)

theorem continuous_rawDividedDerivative (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Continuous (rawDividedDerivative q k v) :=
  (continuous_rawDividedOperator q k).clm_apply (continuous_rawInteractionSolution q k v)

theorem rawDividedDerivative_bound (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    ‖rawDividedDerivative q k v x‖ ≤
      (‖v‖*Real.exp (|k| * rawInteractionMass q))*rawInteractionDensity q x := by
  have hh := ((rawDividedOperator q k x).le_opNorm (rawInteractionSolution q k v x)).trans
    (mul_le_mul_of_nonneg_right (rawDividedOperator_bound q k x) (norm_nonneg _))
  have hb := mul_le_mul_of_nonneg_left (rawInteractionSolution_global_bound q k v x)
    (rawInteractionDensity_nonneg q x)
  exact hh.trans (hb.trans_eq (by ring))

theorem rawDividedDerivative_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    Integrable (rawDividedDerivative q k v) :=
  ((rawInteractionDensity_integrable q).const_mul (‖v‖*Real.exp (|k| * rawInteractionMass q))).mono'
    (continuous_rawDividedDerivative q k v).aestronglyMeasurable
    (Eventually.of_forall (rawDividedDerivative_bound q k v))

theorem rawInteractionDerivative_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (x : ℝ) :
    rawInteractionDerivative q k v x = (k : ℂ) • rawDividedDerivative q k v x := by
  unfold rawInteractionDerivative rawDividedDerivative
  rw [rawInteractionOperator_factor]
  rfl

/-- The integrand for the first Taylor coefficient converges pointwise for the actual flow. -/
theorem rawDividedDerivative_tendsto_zero (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    Tendsto (fun k => rawDividedDerivative q k v x) (𝓝 0) (𝓝 (rawDividedOperator q 0 x v)) := by
  have hc : Continuous (fun k : ℝ => rawDividedOperator q k x) := by
    have hp : Continuous (fun k : ℝ => (k,x)) := continuous_id.prodMk continuous_const
    have hh := (continuous_rawDividedOperator_parameters q).comp hp
    exact hh
  have hh := hc.continuousAt.clm_apply (continuousAt_rawInteractionSolution_zero_frequency q v x)
  simpa only [rawDividedDerivative,rawInteractionSolution_zero_frequency] using hh.tendsto

end
end GaloisForLFunctions.HTGeometry.FokasLenells
