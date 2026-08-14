import GaloisForLFunctions.RHTower.FieldOneFiniteStageConnesMarcolliParseval
import GaloisForLFunctions.RHTower.FieldOneFiniteStageFiniteFourierInversion

/-!
# Connes--Marcolli finite-stage Fourier covariance

Packages the literal additive-adele Fourier endomorphism and proves equation
(2.255), arbitrary-Haar Parseval, correlation inversion, and exact preservation
of the Connes--Marcolli source inner product.
-/

namespace GaloisForLFunctions.RHTower
noncomputable section
open Function IsDedekindDomain MeasureTheory Set TopologicalSpace
open scoped BigOperators ComplexConjugate TensorProduct FourierTransform

def fieldOneFiniteStageBruhatFourierEndomorphism
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageBruhatSchwartz S →ₗ[ℂ]
      FieldOneFiniteStageBruhatSchwartz S :=
  TensorProduct.map
    (FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ)).toLinearMap
    (fieldOneFiniteStageFiniteBruhatFourierLinear S)

@[simp] theorem fieldOneFiniteStageBruhatFourierEndomorphism_tmul
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ)
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    fieldOneFiniteStageBruhatFourierEndomorphism S (f ⊗ₜ[ℂ] phi) =
      (𝓕⁻ f) ⊗ₜ[ℂ]
        fieldOneFiniteStageFiniteBruhatFourierBruhat S phi := by
  rfl

theorem fieldOneFiniteStageBruhatFourierEndomorphism_eval
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (w : FieldOneFiniteStageAdele S) :
    fieldOneFiniteStageBruhatEval S (fieldOneFiniteStageBruhatFourierEndomorphism S x) w =
      fieldOneFiniteStageBruhatFourierEval S x w := by
  induction x using TensorProduct.induction_on with
  | zero => simp [fieldOneFiniteStageBruhatFourierEndomorphism]
  | tmul f phi =>
      rw [fieldOneFiniteStageBruhatFourierEndomorphism_tmul,
        fieldOneFiniteStageBruhatEval_tmul, fieldOneFiniteStageBruhatFourierEval_tmul]
      rw [fieldOneFiniteStageFiniteBruhatFourierBruhat_apply,
        SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg,
        ← SchwartzMap.fourier_coe]
  | add x y hx hy =>
      rw [map_add, map_add, Pi.add_apply, fieldOneFiniteStageBruhatFourierEval_add, hx, hy]

theorem fieldOneFiniteStageBruhatFourier_theta_covariance_eval
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S)
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (w : FieldOneFiniteStageAdele S) :
    fieldOneFiniteStageBruhatFourierEval S
        (fieldOneFiniteStageBruhatTheta S gamma x) w =
      fieldOneFiniteStageBruhatFourierEval S x
        ((fieldOneFiniteStageDiagonalUnit S gamma.1) • w) := by
  let h : fieldOneFiniteStageSUnitImage S :=
    ⟨fieldOneFiniteStageDiagonalUnit S gamma.1,
      fieldOneFiniteStageDiagonalUnit_mem_sUnitImage S gamma⟩
  let μ := fieldOneFiniteStageSelfDualAddHaar S
  letI : μ.IsAddHaarMeasure := by
    dsimp only [μ, fieldOneFiniteStageSelfDualAddHaar]
    infer_instance
  letI : SMulInvariantMeasure (fieldOneFiniteStageSUnitImage S)
      (FieldOneFiniteStageAdele S) μ :=
    ⟨by
      intro q s hs
      rw [preimage_smul]
      exact fieldOneFiniteStageSUnitImage_measure_smul S q⁻¹ μ s⟩
  have hmp : MeasurePreserving (h • ·) μ μ := measurePreserving_smul h μ
  rw [fieldOneFiniteStageBruhatFourierEval_apply,
    fieldOneFiniteStageBruhatFourierEval_apply]
  simp_rw [fieldOneFiniteStageBruhatEval_theta]
  change (∫ a,
      fieldOneFiniteStageCircleAddChar S (-(a * w)) •
        fieldOneFiniteStageBruhatEval S x
          ((fieldOneFiniteStageDiagonalUnit S gamma.1)⁻¹ • a) ∂μ) =
    ∫ a, fieldOneFiniteStageCircleAddChar S
        (-(a * ((fieldOneFiniteStageDiagonalUnit S gamma.1) • w))) •
      fieldOneFiniteStageBruhatEval S x a ∂μ
  rw [← hmp.integral_comp (measurableEmbedding_const_smul h)]
  apply integral_congr_ae
  filter_upwards [] with a
  change fieldOneFiniteStageCircleAddChar S
          (-(((h : FieldOneFiniteStageIdele S) • a) * w)) •
        fieldOneFiniteStageBruhatEval S x
          ((fieldOneFiniteStageDiagonalUnit S gamma.1)⁻¹ •
            ((h : FieldOneFiniteStageIdele S) • a)) =
      fieldOneFiniteStageCircleAddChar S
          (-(a * ((fieldOneFiniteStageDiagonalUnit S gamma.1) • w))) •
        fieldOneFiniteStageBruhatEval S x a
  change fieldOneFiniteStageCircleAddChar S
          (-((fieldOneFiniteStageDiagonalUnit S gamma.1 • a) * w)) •
        fieldOneFiniteStageBruhatEval S x
          ((fieldOneFiniteStageDiagonalUnit S gamma.1)⁻¹ •
            (fieldOneFiniteStageDiagonalUnit S gamma.1 • a)) = _
  rw [inv_smul_smul]
  congr 2
  apply Prod.ext
  · change -((((fieldOneFiniteStageDiagonalUnit S gamma.1).1 : ℝ) * a.1) * w.1) =
      -(a.1 * (((fieldOneFiniteStageDiagonalUnit S gamma.1).1 : ℝ) * w.1))
    ring
  · funext v
    change -((((fieldOneFiniteStageDiagonalUnit S gamma.1).2 v :
        v.1.adicCompletion ℚ) * a.2 v) * w.2 v) =
      -(a.2 v * (((fieldOneFiniteStageDiagonalUnit S gamma.1).2 v :
        v.1.adicCompletion ℚ) * w.2 v))
    ring

theorem fieldOneFiniteStage_connesMarcolli_equation_2_255_covariance
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S)
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (w : FieldOneFiniteStageAdele S) :
    fieldOneFiniteStageBruhatEval S
        (fieldOneFiniteStageBruhatFourierEndomorphism S
          (fieldOneFiniteStageBruhatTheta S gamma x)) w =
      fieldOneFiniteStageBruhatEval S
        (fieldOneFiniteStageBruhatTheta S gamma⁻¹
          (fieldOneFiniteStageBruhatFourierEndomorphism S x)) w := by
  rw [fieldOneFiniteStageBruhatFourierEndomorphism_eval,
    fieldOneFiniteStageBruhatFourier_theta_covariance_eval,
    fieldOneFiniteStageBruhatEval_theta,
    fieldOneFiniteStageBruhatThetaEval,
    fieldOneFiniteStageBruhatFourierEndomorphism_eval]
  apply congrArg (fieldOneFiniteStageBruhatFourierEval S x)
  have hd : fieldOneFiniteStageDiagonalUnit S (gamma⁻¹).1 =
      (fieldOneFiniteStageDiagonalUnit S gamma.1)⁻¹ := by
    change fieldOneFiniteStageDiagonalUnit S (gamma.1)⁻¹ = _
    exact map_inv (fieldOneFiniteStageDiagonalUnit S) gamma.1
  rw [hd, inv_inv]

theorem fieldOneFiniteStageBruhatFourier_parseval_productAddHaar
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    (∫ w, star (fieldOneFiniteStageBruhatFourierEval S x w) *
        fieldOneFiniteStageBruhatFourierEval S y w
        ∂fieldOneFiniteStageProductAddHaar S) =
      ∫ a, star (fieldOneFiniteStageBruhatEval S x a) *
        fieldOneFiniteStageBruhatEval S y a
        ∂fieldOneFiniteStageProductAddHaar S := by
  let μ := fieldOneFiniteStageSelfDualAddHaar S
  let ν := fieldOneFiniteStageProductAddHaar S
  letI : μ.IsAddHaarMeasure := by
    dsimp only [μ, fieldOneFiniteStageSelfDualAddHaar]
    infer_instance
  letI : μ.Regular := by
    dsimp only [μ, fieldOneFiniteStageSelfDualAddHaar]
    infer_instance
  have hν : ν =
      ENNReal.ofNNReal (Measure.addHaarScalarFactor ν μ) • μ :=
    Measure.isAddLeftInvariant_eq_smul_of_regular ν μ
  change (∫ w, star (fieldOneFiniteStageBruhatFourierEval S x w) *
      fieldOneFiniteStageBruhatFourierEval S y w ∂ν) =
    ∫ a, star (fieldOneFiniteStageBruhatEval S x a) *
      fieldOneFiniteStageBruhatEval S y a ∂ν
  rw [hν, integral_smul_measure, integral_smul_measure]
  have hp : (∫ w, star (fieldOneFiniteStageBruhatFourierEval S x w) *
        fieldOneFiniteStageBruhatFourierEval S y w ∂μ) =
      ∫ a, star (fieldOneFiniteStageBruhatEval S x a) *
        fieldOneFiniteStageBruhatEval S y a ∂μ := by
    simpa only [μ, fieldOneFiniteStageBruhatFourierSelfDualPair, fieldOneFiniteStageBruhatSelfDualPair] using
      fieldOneFiniteStageBruhatFourier_parseval S x y
  rw [hp]

theorem fieldOneFiniteStageBruhatFourier_additiveCorrelation
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S)
    (gamma : fieldOneSUnitSubgroup S) :
    fieldOneFiniteStageBruhatAdditiveCorrelation S
        (fieldOneFiniteStageBruhatFourierEndomorphism S x) (fieldOneFiniteStageBruhatFourierEndomorphism S y) gamma =
      fieldOneFiniteStageBruhatAdditiveCorrelation S x y gamma⁻¹ := by
  have htheta (a : FieldOneFiniteStageAdele S) :
      fieldOneFiniteStageBruhatThetaEval S gamma
          (fieldOneFiniteStageBruhatFourierEndomorphism S y) a =
        fieldOneFiniteStageBruhatFourierEval S
          (fieldOneFiniteStageBruhatTheta S gamma⁻¹ y) a := by
    calc
      fieldOneFiniteStageBruhatThetaEval S gamma
          (fieldOneFiniteStageBruhatFourierEndomorphism S y) a =
          fieldOneFiniteStageBruhatEval S
            (fieldOneFiniteStageBruhatTheta S gamma
              (fieldOneFiniteStageBruhatFourierEndomorphism S y)) a :=
        (fieldOneFiniteStageBruhatEval_theta S gamma
          (fieldOneFiniteStageBruhatFourierEndomorphism S y) a).symm
      _ = fieldOneFiniteStageBruhatEval S
          (fieldOneFiniteStageBruhatFourierEndomorphism S
            (fieldOneFiniteStageBruhatTheta S gamma⁻¹ y)) a := by
        simpa using
          (fieldOneFiniteStage_connesMarcolli_equation_2_255_covariance
            S gamma⁻¹ y a).symm
      _ = fieldOneFiniteStageBruhatFourierEval S
          (fieldOneFiniteStageBruhatTheta S gamma⁻¹ y) a :=
        fieldOneFiniteStageBruhatFourierEndomorphism_eval S
          (fieldOneFiniteStageBruhatTheta S gamma⁻¹ y) a
  unfold fieldOneFiniteStageBruhatAdditiveCorrelation
  rw [show (fun a =>
      star (fieldOneFiniteStageBruhatEval S
        (fieldOneFiniteStageBruhatFourierEndomorphism S x) a) *
      fieldOneFiniteStageBruhatThetaEval S gamma
        (fieldOneFiniteStageBruhatFourierEndomorphism S y) a) =
      fun a => star (fieldOneFiniteStageBruhatFourierEval S x a) *
        fieldOneFiniteStageBruhatFourierEval S
          (fieldOneFiniteStageBruhatTheta S gamma⁻¹ y) a by
    funext a
    rw [fieldOneFiniteStageBruhatFourierEndomorphism_eval, htheta]]
  rw [fieldOneFiniteStageBruhatFourier_parseval_productAddHaar]
  apply integral_congr_ae
  filter_upwards [] with a
  rw [fieldOneFiniteStageBruhatEval_theta]

theorem fieldOneFiniteStage_connesMarcolli_lemma_2_33_sourceInner
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatSourceInner S
        (fieldOneFiniteStageBruhatFourierEndomorphism S x) (fieldOneFiniteStageBruhatFourierEndomorphism S y) =
      fieldOneFiniteStageBruhatSourceInner S x y := by
  let e : fieldOneSUnitSubgroup S ≃ fieldOneSUnitSubgroup S :=
    { toFun := fun gamma => gamma⁻¹
      invFun := fun gamma => gamma⁻¹
      left_inv := fun gamma => inv_inv gamma
      right_inv := fun gamma => inv_inv gamma }
  have hsum :
      (∑' gamma : fieldOneSUnitSubgroup S,
        fieldOneFiniteStageBruhatAdditiveCorrelation S
          (fieldOneFiniteStageBruhatFourierEndomorphism S x) (fieldOneFiniteStageBruhatFourierEndomorphism S y) gamma) =
      ∑' gamma : fieldOneSUnitSubgroup S,
        fieldOneFiniteStageBruhatAdditiveCorrelation S x y gamma := by
    simp_rw [fieldOneFiniteStageBruhatFourier_additiveCorrelation]
    change (∑' gamma, fieldOneFiniteStageBruhatAdditiveCorrelation S x y (e gamma)) = _
    exact e.tsum_eq (fieldOneFiniteStageBruhatAdditiveCorrelation S x y)
  rw [fieldOneFiniteStage_connesMarcolli_lemma_2_32,
    fieldOneFiniteStage_connesMarcolli_lemma_2_32] at hsum
  let c := Measure.haarScalarFactor
    (fieldOneFiniteStageIdeleMultiplicativeFromAdditive S)
    (fieldOneFiniteStageIdeleFundamentalHaarMeasure S)
  have hc : (c : ℝ) ≠ 0 := by
    exact_mod_cast
      (fieldOneFiniteStageIdeleMultiplicative_fundamentalScalar_pos S).ne'
  change (c : ℝ) •
      fieldOneFiniteStageBruhatSourceInner S
        (fieldOneFiniteStageBruhatFourierEndomorphism S x) (fieldOneFiniteStageBruhatFourierEndomorphism S y) =
    (c : ℝ) • fieldOneFiniteStageBruhatSourceInner S x y at hsum
  have hcomplex : (c : ℂ) *
      fieldOneFiniteStageBruhatSourceInner S
        (fieldOneFiniteStageBruhatFourierEndomorphism S x) (fieldOneFiniteStageBruhatFourierEndomorphism S y) =
      (c : ℂ) * fieldOneFiniteStageBruhatSourceInner S x y := by
    simpa only [Complex.real_smul] using hsum
  exact mul_left_cancel₀ (by exact_mod_cast hc) hcomplex


end
end GaloisForLFunctions.RHTower

