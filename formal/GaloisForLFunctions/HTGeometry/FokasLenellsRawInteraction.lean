import GaloisForLFunctions.HTGeometry.FokasLenellsInteractionFrame
import GaloisForLFunctions.HTGeometry.FokasLenellsOrbitEntries

/-!
# The original interaction operator through zero spectral frequency

The original scattering construction uses k = exp κ. The same interaction
coefficient extends to every real k, with a globally integrable majorant
proportional to |k|. This provides the nonsingular coefficient family for
auditing the low-frequency expansion in Proposition 3.8.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

abbrev RawOperator := SpectralVector →L[ℂ] SpectralVector

def rawInteractionOperator (q : SchwartzMap ℝ ℂ) (k x : ℝ) : RawOperator :=
  ((I*(k : ℂ)*FDNLS.staggerPhase (2*k^2) x*reflectedDerivative q x) •
    ContinuousLinearMap.snd ℂ ℂ ℂ).prod
  ((I*(k : ℂ)*FDNLS.staggerPhase (-(2*k^2)) x*SchwartzMap.derivCLM ℂ ℂ q x) •
    ContinuousLinearMap.fst ℂ ℂ ℂ)

theorem rawInteractionOperator_apply (q : SchwartzMap ℝ ℂ) (k x : ℝ) (v : SpectralVector) :
    rawInteractionOperator q k x v =
      (I*(k : ℂ)*FDNLS.staggerPhase (2*k^2) x*reflectedDerivative q x*v.2,
       I*(k : ℂ)*FDNLS.staggerPhase (-(2*k^2)) x*SchwartzMap.derivCLM ℂ ℂ q x*v.1) := rfl

theorem continuous_rawInteractionOperator_parameters (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : ℝ × ℝ => rawInteractionOperator q p.1 p.2) := by
  let U : ℝ × ℝ → SpectralVector →L[ℂ] ℂ := fun p =>
    (I*(p.1 : ℂ)*FDNLS.staggerPhase (2*p.1^2) p.2*reflectedDerivative q p.2) • ContinuousLinearMap.snd ℂ ℂ ℂ
  let V : ℝ × ℝ → SpectralVector →L[ℂ] ℂ := fun p =>
    (I*(p.1 : ℂ)*FDNLS.staggerPhase (-(2*p.1^2)) p.2*SchwartzMap.derivCLM ℂ ℂ q p.2) • ContinuousLinearMap.fst ℂ ℂ ℂ
  have hU : Continuous U := by unfold U FDNLS.staggerPhase; fun_prop
  have hV : Continuous V := by unfold V FDNLS.staggerPhase; fun_prop
  exact (ContinuousLinearMap.prodₗᵢ (𝕜 := ℂ) (E := SpectralVector) (F := ℂ) (G := ℂ) ℂ).continuous.comp (hU.prodMk hV)

theorem continuous_rawInteractionOperator (q : SchwartzMap ℝ ℂ) (k : ℝ) :
    Continuous (rawInteractionOperator q k) := by
  have hp : Continuous (fun x : ℝ => (k,x)) := continuous_const.prodMk continuous_id
  have hh := (continuous_rawInteractionOperator_parameters q).comp hp
  exact hh

/-- Both channel derivatives enter the same absolutely integrable density. -/
def rawInteractionDensity (q : SchwartzMap ℝ ℂ) (x : ℝ) : ℝ :=
  ‖SchwartzMap.derivCLM ℂ ℂ q x‖+‖reflectedDerivative q x‖

theorem rawInteractionDensity_nonneg (q : SchwartzMap ℝ ℂ) (x : ℝ) : 0 ≤ rawInteractionDensity q x :=
  add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem rawInteractionDensity_integrable (q : SchwartzMap ℝ ℂ) : Integrable (rawInteractionDensity q) :=
  (SchwartzMap.derivCLM ℂ ℂ q).integrable.norm.add (reflectedDerivative q).integrable.norm

theorem rawInteractionOperator_bound (q : SchwartzMap ℝ ℂ) (k x : ℝ) :
    ‖rawInteractionOperator q k x‖ ≤ |k| *rawInteractionDensity q x := by
  unfold rawInteractionOperator
  rw [ContinuousLinearMap.opNorm_prod,Prod.norm_def]
  simp only [norm_smul,ContinuousLinearMap.norm_snd,ContinuousLinearMap.norm_fst,mul_one,
    norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,FDNLS.norm_staggerPhase,one_mul,mul_one]
  apply max_le
  · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) (abs_nonneg k)
  · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) (abs_nonneg k)

theorem rawInteractionOperator_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) : Integrable (rawInteractionOperator q k) :=
  ((rawInteractionDensity_integrable q).const_mul |k|).mono'
    (continuous_rawInteractionOperator q k).aestronglyMeasurable
    (Eventually.of_forall (rawInteractionOperator_bound q k))

def rawInteractionMass (q : SchwartzMap ℝ ℂ) : ℝ := ∫ x : ℝ, rawInteractionDensity q x

theorem rawInteractionMass_nonneg (q : SchwartzMap ℝ ℂ) : 0 ≤ rawInteractionMass q :=
  integral_nonneg (rawInteractionDensity_nonneg q)

theorem integral_norm_rawInteractionOperator (q : SchwartzMap ℝ ℂ) (k : ℝ) :
    (∫ x : ℝ, ‖rawInteractionOperator q k x‖) ≤ |k| *rawInteractionMass q := by
  have h := integral_mono (rawInteractionOperator_integrable q k).norm
    ((rawInteractionDensity_integrable q).const_mul |k|) (rawInteractionOperator_bound q k)
  simpa only [integral_const_mul,rawInteractionMass] using h

def rawInteractionSup (q : SchwartzMap ℝ ℂ) : ℝ :=
  ‖(SchwartzMap.derivCLM ℂ ℂ q).toBoundedContinuousFunction‖+
    ‖(reflectedDerivative q).toBoundedContinuousFunction‖

theorem rawInteractionSup_nonneg (q : SchwartzMap ℝ ℂ) : 0 ≤ rawInteractionSup q :=
  add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem rawInteractionOperator_uniform_bound (q : SchwartzMap ℝ ℂ) (k x : ℝ) :
    ‖rawInteractionOperator q k x‖ ≤ |k| *rawInteractionSup q :=
  (rawInteractionOperator_bound q k x).trans (mul_le_mul_of_nonneg_left
    (add_le_add ((SchwartzMap.derivCLM ℂ ℂ q).toBoundedContinuousFunction.norm_coe_le_norm x)
      ((reflectedDerivative q).toBoundedContinuousFunction.norm_coe_le_norm x)) (abs_nonneg k))

theorem rawInteractionOperator_zero (q : SchwartzMap ℝ ℂ) (x : ℝ) : rawInteractionOperator q 0 x = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  rw [rawInteractionOperator_apply]
  simp

/-- At positive frequency this is exactly the operator driving the existing original scattering solution. -/
theorem rawInteractionOperator_exp_apply (q : SchwartzMap ℝ ℂ) (κ x : ℝ) (v : SpectralVector) :
    rawInteractionOperator q (Real.exp κ) x v = interactionRate q κ x v := by
  rw [rawInteractionOperator_apply]
  apply Prod.ext <;> simp only [interactionRate,rotatingFrame,pairOperator,ContinuousLinearMap.prod_apply,
    _root_.add_apply,_root_.smul_apply,smul_eq_mul,
    zero_mul,zero_add,add_zero,neg_neg]
  · change I*(Real.exp κ : ℂ)*FDNLS.staggerPhase (2*(Real.exp κ)^2) x*reflectedDerivative q x*v.2 =
      FDNLS.staggerPhase ((Real.exp κ)^2) x*
        ((I*(Real.exp κ : ℂ)*reflectedDerivative q x)*(FDNLS.staggerPhase ((Real.exp κ)^2) x*v.2))
    rw [← staggerPhase_square]
    ring
  · change I*(Real.exp κ : ℂ)*FDNLS.staggerPhase (-(2*(Real.exp κ)^2)) x*SchwartzMap.derivCLM ℂ ℂ q x*v.1 =
      FDNLS.staggerPhase (-((Real.exp κ)^2)) x*
        ((I*(Real.exp κ : ℂ)*deriv (q : ℝ → ℂ) x)*(FDNLS.staggerPhase (-((Real.exp κ)^2)) x*v.1))
    rw [SchwartzMap.derivCLM_apply]
    have he : -(2*(Real.exp κ)^2) = 2*(-((Real.exp κ)^2)) := by ring
    rw [he,← staggerPhase_square]
    ring

end
end GaloisForLFunctions.HTGeometry.FokasLenells
