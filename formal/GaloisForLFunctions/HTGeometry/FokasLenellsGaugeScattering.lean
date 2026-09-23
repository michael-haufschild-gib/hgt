import GaloisForLFunctions.HTGeometry.FokasLenellsUniformizedScattering

/-!
# Exact gauge comparison and removal of spectral endpoint losses

The uniformized and original scattering matrices of arXiv:2607.19649 are
constructed independently in the corpus. This file proves their exact gauge
relation, including the nontrivial initial gauge and its limiting diagonal
form. Schwartz decay survives the oscillating gauge by an exact norm identity.

The amplitude comparison yields both reciprocal inequalities (3.15)–(3.16).
The previously proved reverse-space symmetry combines them to give a bound
on both transmissions and the reflection numerator independent of every
positive real original spectral parameter. No bounded spectral band or
smallness hypothesis is used in these estimates.
-/

open Complex Matrix MeasureTheory Filter
open scoped Topology Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The direct gauge cancels the inverse gauge at every nonzero exponential parameter. -/
theorem gaugeVector_inverseGauge_exp (u a : ℂ) (v : SpectralVector) :
    gaugeVector u (Complex.exp a) (inverseGaugeVector u (Complex.exp a) v) = v := by
  apply Prod.ext
  · rfl
  · simp only [gaugeVector, inverseGaugeVector]
    field_simp
    ring

theorem spatialEigenfunction_direct_gauge (q : SchwartzMap ℝ ℂ) (a : ℂ)
    (v : SpectralVector) (x : ℝ) :
    gaugeVector (deriv q x) (Complex.exp a) (spatialEigenfunction q a v x) =
      initialSpectralSolution q ((Complex.exp a)^(2 : ℕ)) (gaugeVector (deriv q 0) (Complex.exp a) v) x := by
  rw [spatialEigenfunction, gaugeVector_inverseGauge_exp]

/-- The initial gauge is retained explicitly; it is not assumed to be the identity. -/
theorem uniformizedFundamentalMatrix_gauge (q : SchwartzMap ℝ ℂ) (a : ℂ) (x : ℝ) :
    uniformizedFundamentalMatrix (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
        (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) ((Complex.exp a)^(2 : ℕ)) x *
      uniformizationGauge (deriv q 0) (Complex.exp a) =
    uniformizationGauge (deriv q x) (Complex.exp a)*spatialFundamentalMatrix q a x := by
  have h0 := spatialEigenfunction_direct_gauge q a (1,0) x
  have h1 := spatialEigenfunction_direct_gauge q a (0,1) x
  unfold initialSpectralSolution at h0 h1
  rw [← uniformizedFundamentalMatrix_apply] at h0 h1
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [matrixVector, spatialFundamentalMatrix, uniformizationGauge, gaugeVector,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg] using (congrArg Prod.fst h0).symm
  · simpa [matrixVector, spatialFundamentalMatrix, uniformizationGauge, gaugeVector,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg] using (congrArg Prod.fst h1).symm
  · simpa [matrixVector, spatialFundamentalMatrix, uniformizationGauge, gaugeVector,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg] using (congrArg Prod.snd h0).symm
  · simpa [matrixVector, spatialFundamentalMatrix, uniformizationGauge, gaugeVector,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg] using (congrArg Prod.snd h1).symm

def uniformizedOrbitMatrix (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (b : Bool) (x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(uniformizedOrbit f g h z (1,0) b x).1,(uniformizedOrbit f g h z (0,1) b x).1;
    (uniformizedOrbit f g h z (1,0) b x).2,(uniformizedOrbit f g h z (0,1) b x).2]

theorem uniformizedOrbitMatrix_tendsto (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (b : Bool) :
    Tendsto (uniformizedOrbitMatrix f g h z b) atTop (𝓝 (uniformizedAsymptoticMatrix f g h z b)) := by
  have hc : Continuous (fun p : SpectralVector × SpectralVector =>
      (!![p.1.1,p.2.1;p.1.2,p.2.2] : Matrix (Fin 2) (Fin 2) ℂ)) := by fun_prop
  exact (hc.tendsto _).comp ((uniformizedOrbit_tendsto f g h z (1,0) b).prodMk_nhds
    (uniformizedOrbit_tendsto f g h z (0,1) b))

theorem uniformizedOrbitMatrix_eq_diagonal_mul (f g h : SchwartzMap ℝ ℂ)
    (z : ℝ) (b : Bool) (x : ℝ) :
    uniformizedOrbitMatrix f g h z b x =
      diagonalFrame z (if b then -x else x)*
        uniformizedFundamentalMatrix f g h (z:ℂ) (if b then -x else x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uniformizedOrbitMatrix, uniformizedOrbit, uniformizedInteractionSolution,
      rotatingFrame, uniformizedFundamentalMatrix, diagonalFrame, Matrix.mul_apply, Fin.sum_univ_two]

theorem interactionFundamentalMatrix_eq_diagonal_mul (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    interactionFundamentalMatrix q κ x =
      diagonalFrame ((Real.exp κ)^(2 : ℕ)) x*spatialFundamentalMatrix q (κ:ℂ) x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [interactionFundamentalMatrix, interactionSolution, rotatingFrame,
      spatialFundamentalMatrix, diagonalFrame, Matrix.mul_apply, Fin.sum_univ_two]

def oscillatingGauge (q : SchwartzMap ℝ ℂ) (κ x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonalFrame ((Real.exp κ)^(2 : ℕ)) x*uniformizationGauge (deriv q x) (Complex.exp (κ:ℂ))*
    diagonalFrame (-((Real.exp κ)^(2 : ℕ))) x

theorem uniformizedOrbitMatrix_gauge (q : SchwartzMap ℝ ℂ) (κ : ℝ) (b : Bool) (x : ℝ) :
    uniformizedOrbitMatrix (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
        (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) ((Real.exp κ)^(2 : ℕ)) b x *
      uniformizationGauge (deriv q 0) (Complex.exp (κ:ℂ)) =
    oscillatingGauge q κ (if b then -x else x)*interactionFundamentalMatrix q κ (if b then -x else x) := by
  rw [uniformizedOrbitMatrix_eq_diagonal_mul, Matrix.mul_assoc]
  have he : (↑((Real.exp κ)^(2 : ℕ)) : ℂ) = (Complex.exp (κ:ℂ))^(2 : ℕ) := by simp [Complex.ofReal_exp]
  rw [he, uniformizedFundamentalMatrix_gauge, ← Matrix.mul_assoc,
    interactionFundamentalMatrix_eq_diagonal_mul]
  unfold oscillatingGauge
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (diagonalFrame (-((Real.exp κ)^(2 : ℕ))) _),
    diagonalFrame_neg_inverse, one_mul]

/-- The constant limiting diagonal gauge commutes with every oscillating frame. -/
theorem diagonalFrame_gauge_zero_conjugation (k : ℂ) (z x : ℝ) :
    diagonalFrame z x*uniformizationGauge 0 k*diagonalFrame (-z) x = uniformizationGauge 0 k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalFrame, uniformizationGauge, Matrix.mul_apply, Fin.sum_univ_two,
      FDNLS.staggerPhase, ← Complex.exp_add, ← mul_assoc]
  calc
    _ = (2*k)*(Complex.exp (I*(z:ℂ)*(x:ℂ))*Complex.exp (-(I*(z:ℂ)*(x:ℂ)))) := by ring
    _ = _ := by rw [← Complex.exp_add]; simp

theorem uniformizationGauge_difference_norm (u k : ℂ) :
    ‖uniformizationGauge u k-uniformizationGauge 0 k‖ = ‖u‖ := by
  simp [Matrix.norm_def, uniformizationGauge, Pi.norm_def, Finset.univ_fin2]

/-- Oscillatory conjugation cannot destroy the decay of the off-diagonal gauge entry. -/
theorem oscillatingGauge_difference_norm (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    ‖oscillatingGauge q κ x-uniformizationGauge 0 (Complex.exp (κ:ℂ))‖ = ‖deriv q x‖ := by
  have he : oscillatingGauge q κ x-uniformizationGauge 0 (Complex.exp (κ:ℂ)) =
      diagonalFrame ((Real.exp κ)^(2 : ℕ)) x*
        (uniformizationGauge (deriv q x) (Complex.exp (κ:ℂ))-uniformizationGauge 0 (Complex.exp (κ:ℂ)))*
        diagonalFrame (-((Real.exp κ)^(2 : ℕ))) x := by
    rw [mul_sub, sub_mul, diagonalFrame_gauge_zero_conjugation]
    rfl
  rw [he]
  have hn := diagonalFrame_conjugation_norm (-((Real.exp κ)^(2 : ℕ))) x
    (uniformizationGauge (deriv q x) (Complex.exp (κ:ℂ))-uniformizationGauge 0 (Complex.exp (κ:ℂ)))
  simp only [neg_neg] at hn
  rw [hn, uniformizationGauge_difference_norm]

theorem oscillatingGauge_tendsto (q : SchwartzMap ℝ ℂ) (κ : ℝ) (b : Bool) :
    Tendsto (fun x => oscillatingGauge q κ (if b then -x else x)) atTop
      (𝓝 (uniformizationGauge 0 (Complex.exp (κ:ℂ)))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [oscillatingGauge_difference_norm]
  have hd : Tendsto (fun x => deriv q x) atTop (𝓝 0) := by
    have hh := (SchwartzMap.derivCLM ℂ ℂ q).tendsto_cocompact.mono_left atTop_le_cocompact
    change Tendsto (fun x => SchwartzMap.derivCLM ℂ ℂ q x) atTop _ at hh
    simpa only [SchwartzMap.derivCLM_apply] using hh
  have hdneg : Tendsto (fun x => deriv q (-x)) atTop (𝓝 0) := by
    have hl := (SchwartzMap.derivCLM ℂ ℂ q).tendsto_cocompact.mono_left atBot_le_cocompact
    simpa only [Function.comp_def, SchwartzMap.derivCLM_apply] using hl.comp tendsto_neg_atTop_atBot
  cases b
  · simpa using hd.norm
  · simpa using hdneg.norm

def originalAsymptoticMatrix (q : SchwartzMap ℝ ℂ) (κ : ℝ) (b : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  if b then leftAsymptoticMatrix q κ else rightAsymptoticMatrix q κ

theorem interactionFundamentalMatrix_oriented_tendsto (q : SchwartzMap ℝ ℂ) (κ : ℝ) (b : Bool) :
    Tendsto (fun x => interactionFundamentalMatrix q κ (if b then -x else x)) atTop
      (𝓝 (originalAsymptoticMatrix q κ b)) := by
  cases b
  · exact interactionFundamentalMatrix_tendsto q κ
  · exact (interactionFundamentalMatrix_tendsto_left q κ).comp tendsto_neg_atTop_atBot

/-- The endpoint gauge relation keeps both the initial gauge and the limiting gauge. -/
theorem uniformizedAsymptoticMatrix_gauge_endpoint (q : SchwartzMap ℝ ℂ) (κ : ℝ) (b : Bool) :
    uniformizedAsymptoticMatrix (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
        (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) ((Real.exp κ)^(2 : ℕ)) b *
      uniformizationGauge (deriv q 0) (Complex.exp (κ:ℂ)) =
    uniformizationGauge 0 (Complex.exp (κ:ℂ))*originalAsymptoticMatrix q κ b := by
  have hu := (uniformizedOrbitMatrix_tendsto (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) ((Real.exp κ)^(2 : ℕ)) b).mul_const
      (uniformizationGauge (deriv q 0) (Complex.exp (κ:ℂ)))
  have ho := (oscillatingGauge_tendsto q κ b).mul (interactionFundamentalMatrix_oriented_tendsto q κ b)
  simp only [uniformizedOrbitMatrix_gauge] at hu
  exact tendsto_nhds_unique hu ho

theorem uniformizationGauge_exp_isUnit_det (u a : ℂ) :
    IsUnit (uniformizationGauge u (Complex.exp a)).det := by
  apply isUnit_iff_ne_zero.mpr
  simp [det_uniformizationGauge]

theorem uniformizedAsymptoticMatrix_gauge (q : SchwartzMap ℝ ℂ) (κ : ℝ) (b : Bool) :
    uniformizedAsymptoticMatrix (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
        (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) ((Real.exp κ)^(2 : ℕ)) b =
    uniformizationGauge 0 (Complex.exp (κ:ℂ))*originalAsymptoticMatrix q κ b*
      (uniformizationGauge (deriv q 0) (Complex.exp (κ:ℂ)))⁻¹ := by
  have he := congrArg (fun M => M*(uniformizationGauge (deriv q 0) (Complex.exp (κ:ℂ)))⁻¹)
    (uniformizedAsymptoticMatrix_gauge_endpoint q κ b)
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (uniformizationGauge_exp_isUnit_det _ _), mul_one] at he
  exact he

/-- Equation (3.13)'s gauge comparison holds for the two independently constructed scattering matrices. -/
theorem uniformizedScatteringMatrix_gauge (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    uniformizedScatteringMatrix (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
        (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) ((Real.exp κ)^(2 : ℕ)) =
    uniformizationGauge 0 (Complex.exp (κ:ℂ))*scatteringMatrix q κ*
      (uniformizationGauge 0 (Complex.exp (κ:ℂ)))⁻¹ := by
  have hi := Matrix.nonsing_inv_mul _ (uniformizationGauge_exp_isUnit_det (deriv q 0) (κ:ℂ))
  have hdouble := Matrix.nonsing_inv_nonsing_inv _ (uniformizationGauge_exp_isUnit_det (deriv q 0) (κ:ℂ))
  simp only [uniformizedScatteringMatrix, uniformizedAsymptoticMatrix_gauge,
    originalAsymptoticMatrix, Bool.false_eq_true, ↓reduceIte, Matrix.mul_inv_rev,
    hdouble, scatteringMatrix, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((uniformizationGauge (deriv q 0) (Complex.exp (κ:ℂ)))⁻¹), hi, one_mul]

/-- Both reciprocal spectral factors are exact, including their signs. -/
theorem uniformizedScatteringMatrix_amplitudes (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    uniformizedScatteringMatrix (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
        (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) ((Real.exp κ)^(2 : ℕ)) =
      !![transmission q κ,-reverseReflectionAmplitude q κ/(2*Complex.exp (κ:ℂ));
        -2*Complex.exp (κ:ℂ)*reflectionAmplitude q κ,reverseTransmission q κ] := by
  rw [uniformizedScatteringMatrix_gauge]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uniformizationGauge, transmission, reverseTransmission, reflectionAmplitude,
      reverseReflectionAmplitude, Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> field_simp

/-- A potential-dependent error bound with no remaining spectral parameter. -/
def potentialScatteringError (q : SchwartzMap ℝ ℂ) : ℝ :=
  let δ := effectiveDisplacement (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q))
  4*δ*(1+δ)

theorem potentialScatteringError_nonneg (q : SchwartzMap ℝ ℂ) : 0 ≤ potentialScatteringError q := by
  have hn := effectiveDisplacement_nonneg (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q))
  unfold potentialScatteringError
  positivity

/-- The reciprocal bounds (3.15) and (3.16) both hold for the actual reflection numerator. -/
theorem reflectionAmplitude_reciprocal_bounds (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    (2*Real.exp κ)*‖reflectionAmplitude q κ‖ ≤ potentialScatteringError q ∧
    ‖reflectionAmplitude q κ‖/(2*Real.exp κ) ≤ potentialScatteringError q := by
  have h10 := uniformizedScatteringMatrix_entry_displacement
    (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) ((Real.exp κ)^(2 : ℕ)) 1 0
  have h01 := uniformizedScatteringMatrix_entry_displacement
    (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) ((Real.exp κ)^(2 : ℕ)) 0 1
  constructor
  · simpa [uniformizedScatteringMatrix_amplitudes, potentialScatteringError,
      norm_mul, Complex.norm_exp] using h10
  · simpa [uniformizedScatteringMatrix_amplitudes, potentialScatteringError,
      reverseReflectionAmplitude_eq_neg, norm_div, norm_mul, Complex.norm_exp] using h01

/-- The paper's reciprocal-minimum mechanism removes both spectral endpoint losses. -/
theorem scattering_amplitudes_spectral_bound (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    ‖transmission q κ-1‖ ≤ potentialScatteringError q ∧
    ‖reverseTransmission q κ-1‖ ≤ potentialScatteringError q ∧
    ‖reflectionAmplitude q κ‖ ≤ potentialScatteringError q := by
  have h00 := uniformizedScatteringMatrix_entry_displacement
    (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) ((Real.exp κ)^(2 : ℕ)) 0 0
  have h11 := uniformizedScatteringMatrix_entry_displacement
    (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) ((Real.exp κ)^(2 : ℕ)) 1 1
  refine ⟨?_, ?_, ?_⟩
  · simpa [uniformizedScatteringMatrix_amplitudes, potentialScatteringError] using h00
  · simpa [uniformizedScatteringMatrix_amplitudes, potentialScatteringError] using h11
  · have hb := reflectionAmplitude_reciprocal_bounds q κ
    have hp : 0 < 2*Real.exp κ := by positivity
    by_cases hk : 2*Real.exp κ ≤ 1
    · have he := (div_le_iff₀ hp).mp hb.2
      exact he.trans (by simpa using mul_le_mul_of_nonneg_left hk (potentialScatteringError_nonneg q))
    · have hk' : 1 ≤ 2*Real.exp κ := le_of_not_ge hk
      have hs : ‖reflectionAmplitude q κ‖ ≤ (2*Real.exp κ)*‖reflectionAmplitude q κ‖ := by
        simpa using mul_le_mul_of_nonneg_right hk' (norm_nonneg (reflectionAmplitude q κ))
      exact hs.trans hb.1

end
end GaloisForLFunctions.HTGeometry.FokasLenells
