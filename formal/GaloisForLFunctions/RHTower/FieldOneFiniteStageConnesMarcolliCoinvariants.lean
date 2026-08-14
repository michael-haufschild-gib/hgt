import GaloisForLFunctions.RHTower.FieldOneFiniteStageConnesMarcolliCorrelation

/-!
# Connes--Marcolli finite-stage coinvariants

This file constructs the literal source action

`(ϑₐ(γ)f)(a) = f(γ⁻¹a)`

on the algebraic finite-stage Bruhat--Schwartz tensor core.  It then proves
equation (2.252): every difference `f - ϑₐ(γ)f`, and hence their linear span,
lies in the radical of the source inner product.
-/

open scoped NNReal TensorProduct algebraMap

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain MeasureTheory

/-- Inverse rational scaling on the real Schwartz factor. -/
def fieldOneFiniteStageArchimedeanTheta
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft
      ((fieldOneFiniteStageDiagonalUnit S gamma.1).1⁻¹))).toLinearMap

@[simp]
theorem fieldOneFiniteStageArchimedeanTheta_apply
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    fieldOneFiniteStageArchimedeanTheta S gamma f x =
      f (((fieldOneFiniteStageDiagonalUnit S gamma.1).1⁻¹ : ℝ) * x) :=
  by
    rw [fieldOneFiniteStageArchimedeanTheta]
    change f (((↑((fieldOneFiniteStageDiagonalUnit S gamma.1).1⁻¹) : ℝ) • x)) = _
    rw [smul_eq_mul, Units.val_inv_eq_inv_val]

/-- Inverse rational scaling on the finite local factor. -/
def fieldOneFiniteStageFiniteThetaHomeomorph
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S) :
    FieldOneFiniteStageFinitePart S ≃ₜ FieldOneFiniteStageFinitePart S :=
  Homeomorph.smul ((fieldOneFiniteStageDiagonalUnit S gamma.1).2⁻¹)

/-- Pullback by inverse rational scaling preserves compactly supported local
constancy on the finite factor. -/
def fieldOneFiniteStageFiniteBruhatTheta
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S)
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    FieldOneFiniteStageFiniteBruhatSchwartz S :=
  let h := fieldOneFiniteStageFiniteThetaHomeomorph S gamma
  ⟨LocallyConstant.comap ⟨h, h.continuous⟩ phi.1,
    phi.2.comp_homeomorph h⟩

@[simp]
theorem fieldOneFiniteStageFiniteBruhatTheta_apply
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S)
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (x : FieldOneFiniteStageFinitePart S) :
    (fieldOneFiniteStageFiniteBruhatTheta S gamma phi).1 x =
      phi.1 (((fieldOneFiniteStageDiagonalUnit S gamma.1).2⁻¹) • x) :=
  rfl

theorem fieldOneFiniteStageFiniteBruhatTheta_zero
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S) :
    fieldOneFiniteStageFiniteBruhatTheta S gamma 0 = 0 := by
  apply Subtype.ext
  ext x
  simp

theorem fieldOneFiniteStageFiniteBruhatTheta_add
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S)
    (phi psi : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    fieldOneFiniteStageFiniteBruhatTheta S gamma (phi + psi) =
      fieldOneFiniteStageFiniteBruhatTheta S gamma phi +
        fieldOneFiniteStageFiniteBruhatTheta S gamma psi := by
  apply Subtype.ext
  ext x
  simp

theorem fieldOneFiniteStageFiniteBruhatTheta_smul
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S) (c : ℂ)
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    fieldOneFiniteStageFiniteBruhatTheta S gamma (c • phi) =
      c • fieldOneFiniteStageFiniteBruhatTheta S gamma phi := by
  apply Subtype.ext
  ext x
  simp

/-- Finite-factor source scaling, bundled linearly. -/
def fieldOneFiniteStageFiniteBruhatThetaLinear
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S) :
    FieldOneFiniteStageFiniteBruhatSchwartz S →ₗ[ℂ]
      FieldOneFiniteStageFiniteBruhatSchwartz S where
  toFun := fieldOneFiniteStageFiniteBruhatTheta S gamma
  map_add' := fieldOneFiniteStageFiniteBruhatTheta_add S gamma
  map_smul' := fieldOneFiniteStageFiniteBruhatTheta_smul S gamma

/-- Literal Connes--Marcolli action on the finite-stage Bruhat tensor core. -/
def fieldOneFiniteStageBruhatTheta
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S) :
    FieldOneFiniteStageBruhatSchwartz S →ₗ[ℂ]
      FieldOneFiniteStageBruhatSchwartz S :=
  TensorProduct.map
    (fieldOneFiniteStageArchimedeanTheta S gamma)
    (fieldOneFiniteStageFiniteBruhatThetaLinear S gamma)

@[simp]
theorem fieldOneFiniteStageBruhatTheta_tmul
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S)
    (f : SchwartzMap ℝ ℂ)
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    fieldOneFiniteStageBruhatTheta S gamma (f ⊗ₜ[ℂ] phi) =
      fieldOneFiniteStageArchimedeanTheta S gamma f ⊗ₜ[ℂ]
        fieldOneFiniteStageFiniteBruhatTheta S gamma phi :=
  rfl

/-- The core action realizes the pointwise source formula exactly. -/
theorem fieldOneFiniteStageBruhatEval_theta
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S)
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (a : FieldOneFiniteStageAdele S) :
    fieldOneFiniteStageBruhatEval S
        (fieldOneFiniteStageBruhatTheta S gamma x) a =
      fieldOneFiniteStageBruhatThetaEval S gamma x a := by
  induction x using TensorProduct.induction_on with
  | zero =>
      simp [fieldOneFiniteStageBruhatThetaEval]
  | tmul f phi =>
      rfl
  | add x y hx hy =>
      simpa only [map_add, Pi.add_apply,
        fieldOneFiniteStageBruhatThetaEval] using congrArg₂ (· + ·) hx hy

/-- Source scaling reindexes the literal `S`-unit orbit. -/
theorem fieldOneFiniteStageBruhatOrbit_theta
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma q : fieldOneSUnitSubgroup S)
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S) :
    fieldOneFiniteStageBruhatOrbit S
        (fieldOneFiniteStageBruhatTheta S gamma x) u q =
      fieldOneFiniteStageBruhatOrbit S x u (q * gamma⁻¹) := by
  let uq := fieldOneFiniteStageDiagonalUnit S q.1 * u
  calc
    fieldOneFiniteStageBruhatOrbit S
        (fieldOneFiniteStageBruhatTheta S gamma x) u q =
        fieldOneFiniteStageBruhatOrbit S
          (fieldOneFiniteStageBruhatTheta S gamma x) uq 1 := by
      symm
      simpa [uq] using
        fieldOneFiniteStageBruhatOrbit_diagonal_mul S
          (fieldOneFiniteStageBruhatTheta S gamma x) u q 1
    _ = fieldOneFiniteStageBruhatEval S
        (fieldOneFiniteStageBruhatTheta S gamma x)
          (fieldOneFiniteStageIdeleVal S uq) := by
      symm
      exact fieldOneFiniteStageBruhatEval_val S
        (fieldOneFiniteStageBruhatTheta S gamma x) uq
    _ = fieldOneFiniteStageBruhatThetaEval S gamma x
        (fieldOneFiniteStageIdeleVal S uq) :=
      fieldOneFiniteStageBruhatEval_theta S gamma x _
    _ = fieldOneFiniteStageBruhatOrbit S x uq gamma⁻¹ :=
      fieldOneFiniteStageBruhatThetaEval_val S gamma x uq
    _ = fieldOneFiniteStageBruhatOrbit S x u (gamma⁻¹ * q) := by
      simpa [uq] using
        fieldOneFiniteStageBruhatOrbit_diagonal_mul S x u q gamma⁻¹
    _ = fieldOneFiniteStageBruhatOrbit S x u (q * gamma⁻¹) := by
      rw [mul_comm]

/-- Periodization kills the source `S`-unit action exactly. -/
theorem fieldOneFiniteStageBruhatPeriodization_theta
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S)
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S) :
    fieldOneFiniteStageBruhatPeriodization S
        (fieldOneFiniteStageBruhatTheta S gamma x) u =
      fieldOneFiniteStageBruhatPeriodization S x u := by
  rw [fieldOneFiniteStageBruhatPeriodization,
    fieldOneFiniteStageBruhatPeriodization]
  calc
    (∑' q : fieldOneSUnitSubgroup S,
        fieldOneFiniteStageBruhatOrbit S
          (fieldOneFiniteStageBruhatTheta S gamma x) u q) =
        ∑' q : fieldOneSUnitSubgroup S,
          fieldOneFiniteStageBruhatOrbit S x u (q * gamma⁻¹) := by
      apply tsum_congr
      intro q
      exact fieldOneFiniteStageBruhatOrbit_theta S gamma q x u
    _ = ∑' q : fieldOneSUnitSubgroup S,
        fieldOneFiniteStageBruhatOrbit S x u q := by
      change (∑' q : fieldOneSUnitSubgroup S,
          fieldOneFiniteStageBruhatOrbit S x u
            ((Equiv.mulRight gamma⁻¹) q)) = _
      exact (Equiv.mulRight gamma⁻¹).tsum_eq
        (fieldOneFiniteStageBruhatOrbit S x u)

/-- The source half-density is invariant under the core action. -/
theorem fieldOneFiniteStageBruhatSplitHalfDensity_theta
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S)
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatSplitHalfDensity S
        (fieldOneFiniteStageBruhatTheta S gamma x) =
      fieldOneFiniteStageBruhatSplitHalfDensity S x := by
  funext z
  simp only [fieldOneFiniteStageBruhatSplitHalfDensity,
    fieldOneFiniteStageBruhatLogHalfDensity,
    fieldOneFiniteStageBruhatLogPeriodization]
  rw [fieldOneFiniteStageBruhatPeriodization_theta]

/-- The `L²` half-density realization is invariant under the source action. -/
theorem fieldOneFiniteStageBruhatHalfDensityL2_theta
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S)
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatHalfDensityL2 S
        (fieldOneFiniteStageBruhatTheta S gamma x) =
      fieldOneFiniteStageBruhatHalfDensityL2 S x := by
  apply Lp.ext
  filter_upwards [
    fieldOneFiniteStageBruhatHalfDensityL2_ae S
      (fieldOneFiniteStageBruhatTheta S gamma x),
    fieldOneFiniteStageBruhatHalfDensityL2_ae S x] with z htheta hx
  rw [htheta, hx]
  exact congrFun (fieldOneFiniteStageBruhatSplitHalfDensity_theta S gamma x) z

/-- Radical of the source inner product: kernel of its literal half-density
realization. -/
def fieldOneFiniteStageBruhatSourceRadical
    (S : Finset (HeightOneSpectrum ℤ)) :
    Submodule ℂ (FieldOneFiniteStageBruhatSchwartz S) :=
  LinearMap.ker (fieldOneFiniteStageBruhatHalfDensityLinearMap S)

/-- Every source coinvariant difference belongs to the radical. -/
theorem fieldOneFiniteStageBruhat_sub_theta_mem_sourceRadical
    (S : Finset (HeightOneSpectrum ℤ))
    (gamma : fieldOneSUnitSubgroup S)
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    x - fieldOneFiniteStageBruhatTheta S gamma x ∈
      fieldOneFiniteStageBruhatSourceRadical S := by
  apply LinearMap.mem_ker.2
  rw [map_sub]
  change fieldOneFiniteStageBruhatHalfDensityL2 S x -
      fieldOneFiniteStageBruhatHalfDensityL2 S
        (fieldOneFiniteStageBruhatTheta S gamma x) = 0
  rw [fieldOneFiniteStageBruhatHalfDensityL2_theta, sub_self]

/-- The kernel above is genuinely radical for the published source inner
product: every vector in it pairs to zero with every source vector. -/
theorem fieldOneFiniteStageBruhatSourceInner_eq_zero_of_mem_sourceRadical
    (S : Finset (HeightOneSpectrum ℤ))
    {x : FieldOneFiniteStageBruhatSchwartz S}
    (hx : x ∈ fieldOneFiniteStageBruhatSourceRadical S)
    (y : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatSourceInner S x y = 0 := by
  have hxL2 : fieldOneFiniteStageBruhatHalfDensityL2 S x = 0 :=
    LinearMap.mem_ker.1 hx
  have hxAe := fieldOneFiniteStageBruhatHalfDensityL2_ae S x
  rw [hxL2] at hxAe
  have hxZero :
      fieldOneFiniteStageBruhatSplitHalfDensity S x =ᵐ[
        fieldOneFiniteStageSplitProductHaarMeasure S] 0 := by
    filter_upwards [hxAe] with z hz
    simpa using hz.symm
  rw [fieldOneFiniteStageBruhatSourceInner]
  apply integral_eq_zero_of_ae
  filter_upwards [hxZero] with z hz
  rw [hz]
  simp

/-- Set of the literal source differences in equation (2.252). -/
def fieldOneFiniteStageBruhatCoinvariantDifferences
    (S : Finset (HeightOneSpectrum ℤ)) :
    Set (FieldOneFiniteStageBruhatSchwartz S) :=
  {z | ∃ (x : FieldOneFiniteStageBruhatSchwartz S)
      (gamma : fieldOneSUnitSubgroup S),
    z = x - fieldOneFiniteStageBruhatTheta S gamma x}

/-- Connes--Marcolli equation (2.252), exact finite-stage form: the linear
span of all `f - ϑₐ(γ)f` lies in the radical of the published inner product. -/
theorem fieldOneFiniteStage_connesMarcolli_equation_2_252
    (S : Finset (HeightOneSpectrum ℤ)) :
    Submodule.span ℂ (fieldOneFiniteStageBruhatCoinvariantDifferences S) ≤
      fieldOneFiniteStageBruhatSourceRadical S := by
  apply Submodule.span_le.2
  intro z hz
  rcases hz with ⟨x, gamma, rfl⟩
  exact fieldOneFiniteStageBruhat_sub_theta_mem_sourceRadical S gamma x

end

end GaloisForLFunctions.RHTower
