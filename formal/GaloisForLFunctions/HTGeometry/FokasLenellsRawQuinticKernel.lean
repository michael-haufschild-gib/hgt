import GaloisForLFunctions.HTGeometry.FokasLenellsRawSecondPhase

/-!
# The genuine quintic kernel of the original scattering equation

The cubic kernel splits into its zero-frequency value and k² times this
continuous quintic remainder. A Schwartz second spatial moment bounds it
uniformly in frequency. This extends the actual flow expansion to fifth order.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawQuinticOperator (q : SchwartzMap ℝ ℂ) (k x : ℝ) : RawOperator :=
  (((-4*I*(x : ℂ)^(2 : ℕ))*reflectedDerivative q x*rawSecondPhaseAverage (2*k^(2 : ℕ)) x) • ContinuousLinearMap.snd ℂ ℂ ℂ).prod
    (((-4*I*(x : ℂ)^(2 : ℕ))*SchwartzMap.derivCLM ℂ ℂ q x*rawSecondPhaseAverage (-(2*k^(2 : ℕ))) x) • ContinuousLinearMap.fst ℂ ℂ ℂ)

theorem rawQuinticOperator_apply (q : SchwartzMap ℝ ℂ) (k x : ℝ) (v : SpectralVector) :
    rawQuinticOperator q k x v =
      ((-4*I*(x : ℂ)^(2 : ℕ))*reflectedDerivative q x*rawSecondPhaseAverage (2*k^(2 : ℕ)) x*v.2,
       (-4*I*(x : ℂ)^(2 : ℕ))*SchwartzMap.derivCLM ℂ ℂ q x*rawSecondPhaseAverage (-(2*k^(2 : ℕ))) x*v.1) := rfl

theorem continuous_rawQuinticOperator_parameters (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : ℝ × ℝ => rawQuinticOperator q p.1 p.2) := by
  let U : ℝ × ℝ → SpectralVector →L[ℂ] ℂ := fun p =>
    ((-4*I*(p.2 : ℂ)^(2 : ℕ))*reflectedDerivative q p.2*rawSecondPhaseAverage (2*p.1^(2 : ℕ)) p.2) • ContinuousLinearMap.snd ℂ ℂ ℂ
  let V : ℝ × ℝ → SpectralVector →L[ℂ] ℂ := fun p =>
    ((-4*I*(p.2 : ℂ)^(2 : ℕ))*SchwartzMap.derivCLM ℂ ℂ q p.2*rawSecondPhaseAverage (-(2*p.1^(2 : ℕ))) p.2) • ContinuousLinearMap.fst ℂ ℂ ℂ
  have hpu : Continuous (fun p : ℝ × ℝ => (2*p.1^(2 : ℕ),p.2)) := by fun_prop
  have hpv : Continuous (fun p : ℝ × ℝ => (-(2*p.1^(2 : ℕ)),p.2)) := by fun_prop
  have hu := continuous_rawSecondPhaseAverage_parameters.comp hpu
  have hv := continuous_rawSecondPhaseAverage_parameters.comp hpv
  have hU : Continuous U := by unfold U; fun_prop
  have hV : Continuous V := by unfold V; fun_prop
  exact (ContinuousLinearMap.prodₗᵢ (𝕜 := ℂ) (E := SpectralVector) (F := ℂ) (G := ℂ) ℂ).continuous.comp (hU.prodMk hV)

theorem continuous_rawQuinticOperator (q : SchwartzMap ℝ ℂ) (k : ℝ) :
    Continuous (rawQuinticOperator q k) := by
  have hp : Continuous (fun x : ℝ => (k,x)) := continuous_const.prodMk continuous_id
  have hh := (continuous_rawQuinticOperator_parameters q).comp hp
  exact hh

def rawQuinticDensity (q : SchwartzMap ℝ ℂ) (x : ℝ) : ℝ :=
  4*|x|^(2 : ℕ) * rawInteractionDensity q x

theorem rawQuinticDensity_nonneg (q : SchwartzMap ℝ ℂ) (x : ℝ) : 0 ≤ rawQuinticDensity q x :=
  mul_nonneg (mul_nonneg (by positivity) (sq_nonneg |x|)) (rawInteractionDensity_nonneg q x)

theorem rawQuinticDensity_integrable (q : SchwartzMap ℝ ℂ) : Integrable (rawQuinticDensity q) := by
  have hq := (SchwartzMap.derivCLM ℂ ℂ q).integrable_pow_mul volume 2
  have hg := (reflectedDerivative q).integrable_pow_mul volume 2
  have hh := (hq.add hg).const_mul 4
  change Integrable (fun x : ℝ => 4*|x|^(2 : ℕ) * (‖SchwartzMap.derivCLM ℂ ℂ q x‖+‖reflectedDerivative q x‖))
  convert! hh using 1
  funext x
  simp only [Real.norm_eq_abs]
  change 4*|x|^(2 : ℕ) * (‖SchwartzMap.derivCLM ℂ ℂ q x‖+‖reflectedDerivative q x‖) =
    4*(|x|^(2 : ℕ) * ‖SchwartzMap.derivCLM ℂ ℂ q x‖+|x|^(2 : ℕ) * ‖reflectedDerivative q x‖)
  ring

private theorem quinticScalar_bound (f : ℂ) (r x : ℝ) :
    ‖(-4*I*(x : ℂ)^(2 : ℕ))*f*rawSecondPhaseAverage r x‖ ≤ 4*|x|^(2 : ℕ) * ‖f‖ := by
  have hh := mul_le_mul_of_nonneg_left (rawSecondPhaseAverage_bound r x)
    (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 4) (sq_nonneg |x|)) (norm_nonneg f))
  simpa only [norm_mul,norm_neg,Complex.norm_ofNat,norm_I,norm_pow,Complex.norm_real,Real.norm_eq_abs,mul_one] using hh

theorem rawQuinticOperator_bound (q : SchwartzMap ℝ ℂ) (k x : ℝ) :
    ‖rawQuinticOperator q k x‖ ≤ rawQuinticDensity q x := by
  unfold rawQuinticOperator
  rw [ContinuousLinearMap.opNorm_prod,Prod.norm_def]
  simp only [norm_smul,ContinuousLinearMap.norm_snd,ContinuousLinearMap.norm_fst,mul_one]
  apply max_le
  · exact (quinticScalar_bound (reflectedDerivative q x) (2*k^(2 : ℕ)) x).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _))
        (mul_nonneg (by positivity) (sq_nonneg |x|)))
  · exact (quinticScalar_bound (SchwartzMap.derivCLM ℂ ℂ q x) (-(2*k^(2 : ℕ))) x).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _))
        (mul_nonneg (by positivity) (sq_nonneg |x|)))

theorem rawQuinticOperator_integrable (q : SchwartzMap ℝ ℂ) (k : ℝ) : Integrable (rawQuinticOperator q k) :=
  (rawQuinticDensity_integrable q).mono' (continuous_rawQuinticOperator q k).aestronglyMeasurable
    (Eventually.of_forall (rawQuinticOperator_bound q k))

def rawQuinticMass (q : SchwartzMap ℝ ℂ) : ℝ := ∫ x : ℝ, rawQuinticDensity q x

theorem rawQuinticMass_nonneg (q : SchwartzMap ℝ ℂ) : 0 ≤ rawQuinticMass q :=
  integral_nonneg (rawQuinticDensity_nonneg q)

/-- The exact refinement of the actual cubic Lax kernel. -/
theorem rawCubicOperator_fifth_factor (q : SchwartzMap ℝ ℂ) (k x : ℝ) :
    rawCubicOperator q k x = rawCubicOperator q 0 x+(k : ℂ)^(2 : ℕ) • rawQuinticOperator q k x := by
  apply ContinuousLinearMap.ext
  intro v
  have hu := rawPhaseAverage_square_sub_one_factor k x
  have hv := rawPhaseAverage_neg_square_sub_one_factor k x
  change rawCubicOperator q k x v = rawCubicOperator q 0 x v+(k : ℂ)^(2 : ℕ) • rawQuinticOperator q k x v
  rw [rawCubicOperator_apply,rawCubicOperator_zero_apply,rawQuinticOperator_apply]
  apply Prod.ext
  · simp only [Prod.fst_add,Prod.smul_fst,smul_eq_mul]
    calc
      _ = 2*(x : ℂ)*reflectedDerivative q x*(rawPhaseAverage (2*k^(2 : ℕ)) x-1)*v.2+
          2*(x : ℂ)*reflectedDerivative q x*v.2 := by ring
      _ = _ := by rw [hu]; ring
  · simp only [Prod.snd_add,Prod.smul_snd,smul_eq_mul]
    calc
      _ = -2*(x : ℂ)*SchwartzMap.derivCLM ℂ ℂ q x*(rawPhaseAverage (-(2*k^(2 : ℕ))) x-1)*v.1+
          -2*(x : ℂ)*SchwartzMap.derivCLM ℂ ℂ q x*v.1 := by ring
      _ = _ := by rw [hv]; ring

/-- The original coefficient has an exact linear, cubic and quintic decomposition. -/
theorem rawInteractionOperator_fifth_factor (q : SchwartzMap ℝ ℂ) (k x : ℝ) :
    rawInteractionOperator q k x = (k : ℂ) • rawDividedOperator q 0 x+
      (k : ℂ)^(3 : ℕ) • rawCubicOperator q 0 x+(k : ℂ)^(5 : ℕ) • rawQuinticOperator q k x := by
  rw [rawInteractionOperator_cubic_factor,rawCubicOperator_fifth_factor,smul_add,smul_smul]
  have he : (k : ℂ)^(3 : ℕ)*(k : ℂ)^(2 : ℕ) = (k : ℂ)^(5 : ℕ) := by ring
  rw [he,add_assoc]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
