import GaloisForLFunctions.HTGeometry.FokasLenellsRawPhase

/-!
# The genuine cubic kernel of the original scattering equation

The divided original coefficient splits exactly into its zero-frequency
value and k² times an explicitly integrated phase remainder. That remainder
is continuous and has a frequency-independent Schwartz first-moment bound.
It is the missing kernel infrastructure for the cubic scattering expansion.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawCubicOperator (q : SchwartzMap ℝ ℂ) (k x : ℝ) : RawOperator :=
  ((2*(x : ℂ)*reflectedDerivative q x*rawPhaseAverage (2*k^2) x) • ContinuousLinearMap.snd ℂ ℂ ℂ).prod
    ((-2*(x : ℂ)*SchwartzMap.derivCLM ℂ ℂ q x*rawPhaseAverage (-(2*k^2)) x) • ContinuousLinearMap.fst ℂ ℂ ℂ)

theorem rawCubicOperator_apply (q : SchwartzMap ℝ ℂ) (k x : ℝ) (v : SpectralVector) :
    rawCubicOperator q k x v =
      (2*(x : ℂ)*reflectedDerivative q x*rawPhaseAverage (2*k^2) x*v.2,
       -2*(x : ℂ)*SchwartzMap.derivCLM ℂ ℂ q x*rawPhaseAverage (-(2*k^2)) x*v.1) := rfl

theorem continuous_rawCubicOperator_parameters (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : ℝ × ℝ => rawCubicOperator q p.1 p.2) := by
  let U : ℝ × ℝ → SpectralVector →L[ℂ] ℂ := fun p =>
    (2*(p.2 : ℂ)*reflectedDerivative q p.2*rawPhaseAverage (2*p.1^2) p.2) • ContinuousLinearMap.snd ℂ ℂ ℂ
  let V : ℝ × ℝ → SpectralVector →L[ℂ] ℂ := fun p =>
    (-2*(p.2 : ℂ)*SchwartzMap.derivCLM ℂ ℂ q p.2*rawPhaseAverage (-(2*p.1^2)) p.2) • ContinuousLinearMap.fst ℂ ℂ ℂ
  have hpu : Continuous (fun p : ℝ × ℝ => (2*p.1^2,p.2)) := by fun_prop
  have hpv : Continuous (fun p : ℝ × ℝ => (-(2*p.1^2),p.2)) := by fun_prop
  have hu := continuous_rawPhaseAverage_parameters.comp hpu
  have hv := continuous_rawPhaseAverage_parameters.comp hpv
  have hU : Continuous U := by unfold U; fun_prop
  have hV : Continuous V := by unfold V; fun_prop
  exact (ContinuousLinearMap.prodₗᵢ (𝕜 := ℂ) (E := SpectralVector) (F := ℂ) (G := ℂ) ℂ).continuous.comp (hU.prodMk hV)

theorem continuous_rawCubicOperator (q : SchwartzMap ℝ ℂ) (k : ℝ) :
    Continuous (rawCubicOperator q k) := by
  have hp : Continuous (fun x : ℝ => (k,x)) := continuous_const.prodMk continuous_id
  have hh := (continuous_rawCubicOperator_parameters q).comp hp
  exact hh

def rawCubicDensity (q : SchwartzMap ℝ ℂ) (x : ℝ) : ℝ :=
  2*|x| * rawInteractionDensity q x

theorem rawCubicDensity_nonneg (q : SchwartzMap ℝ ℂ) (x : ℝ) : 0 ≤ rawCubicDensity q x :=
  mul_nonneg (mul_nonneg (by positivity) (abs_nonneg x)) (rawInteractionDensity_nonneg q x)

theorem rawCubicDensity_integrable (q : SchwartzMap ℝ ℂ) : Integrable (rawCubicDensity q) := by
  have hq := (SchwartzMap.derivCLM ℂ ℂ q).integrable_pow_mul volume 1
  have hg := (reflectedDerivative q).integrable_pow_mul volume 1
  have hh := (hq.add hg).const_mul 2
  change Integrable (fun x : ℝ => 2*|x| * (‖SchwartzMap.derivCLM ℂ ℂ q x‖+‖reflectedDerivative q x‖))
  convert! hh using 1
  funext x
  simp only [Real.norm_eq_abs,pow_one]
  change 2*|x| * (‖SchwartzMap.derivCLM ℂ ℂ q x‖+‖reflectedDerivative q x‖) =
    2*(|x| * ‖SchwartzMap.derivCLM ℂ ℂ q x‖+|x| * ‖reflectedDerivative q x‖)
  ring

private theorem cubicScalar_bound (f : ℂ) (r x : ℝ) :
    ‖2*(x : ℂ)*f*rawPhaseAverage r x‖ ≤ 2*|x| * ‖f‖ := by
  have hh := mul_le_mul_of_nonneg_left (rawPhaseAverage_bound r x)
    (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2) (abs_nonneg x)) (norm_nonneg f))
  simpa only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,mul_one] using hh

theorem rawCubicOperator_bound (q : SchwartzMap ℝ ℂ) (k x : ℝ) :
    ‖rawCubicOperator q k x‖ ≤ rawCubicDensity q x := by
  unfold rawCubicOperator
  rw [ContinuousLinearMap.opNorm_prod,Prod.norm_def]
  simp only [norm_smul,ContinuousLinearMap.norm_snd,ContinuousLinearMap.norm_fst,mul_one]
  apply max_le
  · exact (cubicScalar_bound (reflectedDerivative q x) (2*k^2) x).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _))
        (mul_nonneg (by positivity) (abs_nonneg x)))
  · rw [neg_mul,neg_mul,neg_mul,norm_neg]
    exact (cubicScalar_bound (SchwartzMap.derivCLM ℂ ℂ q x) (-(2*k^2)) x).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _))
        (mul_nonneg (by positivity) (abs_nonneg x)))

theorem rawCubicOperator_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) : Integrable (rawCubicOperator q k) :=
  (rawCubicDensity_integrable q).mono' (continuous_rawCubicOperator q k).aestronglyMeasurable
    (Eventually.of_forall (rawCubicOperator_bound q k))

def rawCubicMass (q : SchwartzMap ℝ ℂ) : ℝ := ∫ x : ℝ, rawCubicDensity q x

theorem rawCubicMass_nonneg (q : SchwartzMap ℝ ℂ) : 0 ≤ rawCubicMass q :=
  integral_nonneg (rawCubicDensity_nonneg q)

theorem rawCubicOperator_zero_apply (q : SchwartzMap ℝ ℂ) (x : ℝ) (v : SpectralVector) :
    rawCubicOperator q 0 x v =
      (2*(x : ℂ)*reflectedDerivative q x*v.2,-2*(x : ℂ)*SchwartzMap.derivCLM ℂ ℂ q x*v.1) := by
  simp only [rawCubicOperator_apply,zero_pow (by omega : 2 ≠ 0),mul_zero,neg_zero,
    rawPhaseAverage_zero_frequency,mul_one]

/-- The exact expansion of the actual divided original Lax coefficient, at every real k. -/
theorem rawDividedOperator_cubic_factor (q : SchwartzMap ℝ ℂ) (k x : ℝ) :
    rawDividedOperator q k x = rawDividedOperator q 0 x+(k : ℂ)^2 • rawCubicOperator q k x := by
  apply ContinuousLinearMap.ext
  intro v
  have hu := staggerPhase_square_sub_one_factor k x
  have hv := staggerPhase_neg_square_sub_one_factor k x
  rw [rawDividedOperator_apply]
  change _ = rawDividedOperator q 0 x v+(k : ℂ)^2 • rawCubicOperator q k x v
  rw [rawDividedOperator_apply,rawCubicOperator_apply]
  simp only [zero_pow (by omega : 2 ≠ 0),mul_zero,neg_zero,FDNLS.staggerPhase,
    Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one] at hu hv ⊢
  apply Prod.ext
  · simp only [Prod.fst_add,Prod.smul_fst,smul_eq_mul]
    calc
      _ = I*(Complex.exp (-(I*((2*k^2 : ℝ) : ℂ))*(x : ℂ))-1)*reflectedDerivative q x*v.2+
          I*reflectedDerivative q x*v.2 := by ring
      _ = _ := by rw [hu]; ring_nf; simp only [I_sq]; ring
  · simp only [Prod.snd_add,Prod.smul_snd,smul_eq_mul]
    calc
      _ = I*(Complex.exp (-(I*((-(2*k^2) : ℝ) : ℂ))*(x : ℂ))-1)*SchwartzMap.derivCLM ℂ ℂ q x*v.1+
          I*SchwartzMap.derivCLM ℂ ℂ q x*v.1 := by ring
      _ = _ := by rw [hv]; ring_nf; simp only [I_sq]; ring

/-- The original, un-divided coefficient has exactly a linear term and a cubic remainder. -/
theorem rawInteractionOperator_cubic_factor (q : SchwartzMap ℝ ℂ) (k x : ℝ) :
    rawInteractionOperator q k x =
      (k : ℂ) • rawDividedOperator q 0 x+(k : ℂ)^3 • rawCubicOperator q k x := by
  rw [rawInteractionOperator_factor,rawDividedOperator_cubic_factor,smul_add,smul_smul]
  congr 1
  congr 1
  ring

end
end GaloisForLFunctions.HTGeometry.FokasLenells
