import GaloisForLFunctions.HilbertMetric.Correlation.GaussianFinitePrediction

/-!
# Complex Gram prediction under the actual real Gaussian law

Realification preserves the adjoint and the optimal synthesized predictor.
Consequently the complex Gram coefficients give the conditional mean of
every real quadrature, given the entire complex observation vector.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ComplexConjugate
namespace HilbertMetric.Correlation
variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [MeasurableSpace H] [BorelSpace H]

local instance : InnerProductSpace ℝ V := InnerProductSpace.complexToReal
local instance : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
local instance : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V
local instance : FiniteDimensional ℝ H := FiniteDimensional.trans ℝ ℂ H
local instance : CompleteSpace V := FiniteDimensional.complete ℂ V
local instance : CompleteSpace H := FiniteDimensional.complete ℂ H

omit [MeasurableSpace V] [BorelSpace V] [MeasurableSpace H] [BorelSpace H] in
/-- Restricting a complex observation map to real scalars preserves its adjoint. -/
theorem complexObservation_real_adjoint (Φ : V →L[ℂ] H) :
    Φ.adjoint.restrictScalars ℝ = (Φ.restrictScalars ℝ).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change (⟪Φ.adjoint x, y⟫_ℂ).re = (⟪x, Φ y⟫_ℂ).re
  rw [ContinuousLinearMap.adjoint_inner_left]

omit [MeasurableSpace V] [BorelSpace V] [MeasurableSpace H] [BorelSpace H] in
/-- Real and complex Gram inverses synthesize the same optimal observation. -/
theorem complexPrediction_real_synthesis (Φ : V →L[ℂ] H) (u : H) :
    Φ (finitePredictionCoefficients Φ u) =
      Φ (finitePredictionCoefficients (Φ.restrictScalars ℝ) u) := by
  have hm := (finitePrediction_minimizer_iff Φ u (finitePredictionCoefficients Φ u)).mpr
    (by rw [sub_self, map_zero])
  have hz := (finitePrediction_minimizer_iff (Φ.restrictScalars ℝ) u
    (finitePredictionCoefficients Φ u)).mp hm
  change Φ (finitePredictionCoefficients Φ u -
    finitePredictionCoefficients (Φ.restrictScalars ℝ) u) = 0 at hz
  rwa [map_sub, sub_eq_zero] at hz

/-- Complex coefficients recover the actual conditional mean of the real target quadrature. -/
theorem complexGaussian_conditional_mean_real (Φ : V →L[ℂ] H) (u : H) :
    (stdGaussian H)[(fun ω : H => (⟪u, ω⟫_ℂ).re) |
      MeasurableSpace.comap Φ.adjoint inferInstance] =ᵐ[stdGaussian H]
      fun ω => (⟪finitePredictionCoefficients Φ u, Φ.adjoint ω⟫_ℂ).re := by
  have h := gaussianPrediction_conditional_mean (Φ.restrictScalars ℝ) u
  have hp : (fun ω : H => ⟪finitePredictionCoefficients (Φ.restrictScalars ℝ) u,
      (Φ.restrictScalars ℝ).adjoint ω⟫_ℝ) =
      fun ω => (⟪finitePredictionCoefficients Φ u, Φ.adjoint ω⟫_ℂ).re := by
    ext ω
    rw [ContinuousLinearMap.adjoint_inner_right]
    change (⟪Φ (finitePredictionCoefficients (Φ.restrictScalars ℝ) u), ω⟫_ℂ).re = _
    rw [← complexPrediction_real_synthesis, ContinuousLinearMap.adjoint_inner_right]
  rw [hp, ← complexObservation_real_adjoint] at h
  exact h

/-- Every complex phase of the target has the predicted conditional mean, including both
the real and imaginary channels. Singular observations require no extra assumption. -/
theorem complexGaussian_conditional_mean_quadrature (Φ : V →L[ℂ] H) (u : H) (a : ℂ) :
    (stdGaussian H)[(fun ω : H => (⟪a • u, ω⟫_ℂ).re) |
      MeasurableSpace.comap Φ.adjoint inferInstance] =ᵐ[stdGaussian H]
      fun ω => (⟪a • finitePredictionCoefficients Φ u, Φ.adjoint ω⟫_ℂ).re := by
  have h := complexGaussian_conditional_mean_real Φ (a • u)
  simpa only [finitePredictionCoefficients, map_smul] using h

/-- The complex Gram predictor is the full complex conditional expectation. -/
theorem complexGaussian_conditional_mean (Φ : V →L[ℂ] H) (u : H) :
    (stdGaussian H)[(fun ω : H => ⟪u, ω⟫_ℂ) |
      MeasurableSpace.comap Φ.adjoint inferInstance] =ᵐ[stdGaussian H]
      fun ω => ⟪finitePredictionCoefficients Φ u, Φ.adjoint ω⟫_ℂ := by
  have hr := complexGaussian_conditional_mean_real Φ u
  have hi := complexGaussian_conditional_mean_quadrature Φ u Complex.I
  simp only [inner_smul_left, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, zero_mul, neg_mul, one_mul, zero_sub, neg_neg] at hi
  have hf : Integrable (fun ω : H => ⟪u, ω⟫_ℂ) (stdGaussian H) :=
    (IsGaussian.hasGaussianLaw_id.map ((innerSL ℂ u).restrictScalars ℝ)).integrable
  have hcr := Complex.reCLM.comp_condExp_comm
    (m := MeasurableSpace.comap Φ.adjoint inferInstance) hf
  have hci := Complex.imCLM.comp_condExp_comm
    (m := MeasurableSpace.comap Φ.adjoint inferInstance) hf
  filter_upwards [hr, hi, hcr, hci] with ω hr hi hcr hci
  exact Complex.ext (hcr.trans hr) (hci.trans hi)

/-- Scaling and conjugating gives the conditional mean in the proper complex signal convention. -/
theorem complexGaussian_conditional_mean_proper (Φ : V →L[ℂ] H) (u : H) :
    (stdGaussian H)[(fun ω : H => (Real.sqrt 2)⁻¹ • conj (⟪u, ω⟫_ℂ)) |
      MeasurableSpace.comap Φ.adjoint inferInstance] =ᵐ[stdGaussian H]
      fun ω => (Real.sqrt 2)⁻¹ • conj (⟪finitePredictionCoefficients Φ u, Φ.adjoint ω⟫_ℂ) := by
  have hf : Integrable (fun ω : H => ⟪u, ω⟫_ℂ) (stdGaussian H) :=
    (IsGaussian.hasGaussianLaw_id.map ((innerSL ℂ u).restrictScalars ℝ)).integrable
  let T : ℂ →L[ℝ] ℂ := (Real.sqrt 2)⁻¹ • (Complex.conjCLE : ℂ →L[ℝ] ℂ)
  have ht := T.comp_condExp_comm
    (m := MeasurableSpace.comap Φ.adjoint inferInstance) hf
  filter_upwards [ht, complexGaussian_conditional_mean Φ u] with ω ht hp
  exact ht.symm.trans (congrArg T hp)

/-- Complex pilot coordinates in the proper Gaussian normalization. -/
def properPilotReadout {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) : Fin n → ℂ :=
  fun i => (Real.sqrt 2)⁻¹ • Complex.conjCLE (v i)

private def properPilotDecode {n : ℕ} (z : Fin n → ℂ) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i => Real.sqrt 2 • Complex.conjCLE (z i))

private theorem properPilotDecode_readout {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    properPilotDecode (properPilotReadout v) = v := by
  ext i
  change Real.sqrt 2 • Complex.conjCLE ((Real.sqrt 2)⁻¹ • Complex.conjCLE (v i)) = v i
  rw [map_smul, Complex.conjCLE_apply, Complex.conjCLE_apply, Complex.conj_conj,
    smul_smul, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num)), one_smul]

/-- Proper normalization and conjugation preserve exactly the information in the pilot vector. -/
theorem properPilotReadout_comap {Ω : Type*} {n : ℕ}
    (Y : Ω → EuclideanSpace ℂ (Fin n)) :
    MeasurableSpace.comap (fun ω => properPilotReadout (Y ω)) inferInstance =
      MeasurableSpace.comap Y inferInstance := by
  have hF : Measurable (properPilotReadout (n := n)) := by unfold properPilotReadout; fun_prop
  have hG : Measurable (properPilotDecode (n := n)) := by unfold properPilotDecode; fun_prop
  apply le_antisymm
  · exact MeasurableSpace.comap_le_comap_of_eq_comp properPilotReadout hF rfl
  · exact MeasurableSpace.comap_le_comap_of_eq_comp properPilotDecode hG
      (funext fun ω => (properPilotDecode_readout (Y ω)).symm)

/-- The normalized complex Gram pairing is the ordinary linear predictor on physical pilots. -/
theorem properPilotReadout_prediction {n : ℕ} (c v : EuclideanSpace ℂ (Fin n)) :
    (Real.sqrt 2)⁻¹ • conj (⟪c, v⟫_ℂ) = ∑ i, c i * properPilotReadout v i := by
  rw [PiLp.inner_apply, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [RCLike.inner_apply, map_mul, Complex.conj_conj, properPilotReadout,
    Complex.conjCLE_apply]
  rw [mul_comm (conj (v i)), mul_smul_comm]

end HilbertMetric.Correlation
