import GaloisForLFunctions.HTGeometry.BesselOrderParameterizedSl2Closure
import GaloisForLFunctions.HTGeometry.BesselOrderRelationAdaptedPPV
import GaloisForLFunctions.HTGeometry.BesselOrderParameterizedBaseChangePoints
import GaloisForLFunctions.HTGeometry.GaloisMonoidDifferentialRelation
import GaloisForLFunctions.HTGeometry.DifferentialMatrixOrbitScaling
import GaloisForLFunctions.HTGeometry.DifferentialPolynomialScaling

/-!
# Bessel relation contradiction from faithful comparison-torsor descent

This module assembles the algebraic endgame after relation-adapted PPV existence.  If the
comparison algebra has its genuine torsor independence property, full `SL₂` closure propagates a
nonzero scalar differential relation to every constant multiple.  A separating differential point
of the PPV base change then contradicts differential-polynomial scaling over the differentially
closed constants.
-/

open scoped Differential TensorProduct

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

local instance besselOrderGaloisScalingBaseDifferential :
    Differential (RatFunc Constants) := coordinateTotalDifferential

local instance besselOrderGaloisScalingConstantsRatDifferentialAlgebra :
    DifferentialAlgebra Constants (RatFunc Constants) :=
  coordinateTotalDifferentialAlgebra

local instance besselOrderGaloisScalingPPVDifferential {s : ℝ}
    (data : BesselOrderParameterizedPVData s) : Differential data.PPVRing :=
  quotientDifferential data.M data.isSigmaDeltaIdeal.2

local instance besselOrderGaloisScalingPPVDifferentialAlgebra {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    DifferentialAlgebra (RatFunc Constants) data.PPVRing :=
  ppvQuotientDifferentialAlgebra data.M data.isSigmaDeltaIdeal.2

local instance besselOrderGaloisScalingConstantsPPVDifferentialAlgebra {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    DifferentialAlgebra Constants data.PPVRing :=
  differentialAlgebra_trans (C := Constants) (K := RatFunc Constants) (E := data.PPVRing)

local instance besselOrderGaloisScalingClosureDifferentialAlgebra :
    DifferentialAlgebra (RatFunc Constants) (diffClosure (RatFunc Constants)) :=
  DiffFieldExt.differentialAlgebra (diffClosureExt (F := RatFunc Constants))

local instance besselOrderGaloisScalingConstantsClosureAlgebra :
    Algebra Constants (diffClosure (RatFunc Constants)) :=
  ((algebraMap (RatFunc Constants) (diffClosure (RatFunc Constants))).comp
    (algebraMap Constants (RatFunc Constants))).toAlgebra

local instance besselOrderGaloisScalingConstantsClosureTower :
    IsScalarTower Constants (RatFunc Constants) (diffClosure (RatFunc Constants)) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance besselOrderGaloisScalingConstantsClosureDifferentialAlgebra :
    DifferentialAlgebra Constants (diffClosure (RatFunc Constants)) :=
  differentialAlgebra_trans
    (C := Constants) (K := RatFunc Constants) (E := diffClosure (RatFunc Constants))

theorem besselScalarPPVRelation_quotient
    {s : ℝ} (data : BesselOrderParameterizedPVData s)
    (P : DifferentialPolynomial Unit (RatFunc Constants)) :
    Ideal.Quotient.mk data.M (besselScalarPPVRelation P) =
      differentialPolynomialEvalOver (K := RatFunc Constants)
        (fun _ : Unit => data.fundamentalMatrix 0 0) P := by
  have hmap := map_differentialPolynomialEvalOver
    (F := RatFunc Constants)
    (Ideal.Quotient.mk data.M)
    (fun x => quotientDifferential_deriv_mk data.M data.isSigmaDeltaIdeal.2 x)
    (fun a => rfl)
    (fun _ : Unit => ppvFundamental (RatFunc Constants) 2 0 0) P
  simpa [besselScalarPPVRelation, BesselOrderParameterizedPVData.fundamentalMatrix] using hmap

theorem BesselOrderParameterizedPVData.fundamental_zero_zero_ne_zero
    {s : ℝ} (data : BesselOrderParameterizedPVData s) :
    data.fundamentalMatrix 0 0 ≠ 0 := by
  letI : Nontrivial data.PPVRing := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact data.ne_top
  letI : Module.Free (RatFunc Constants) data.PPVRing :=
    Module.Free.of_divisionRing (RatFunc Constants) data.PPVRing
  letI : Module.Flat (RatFunc Constants) data.PPVRing := Module.Flat.of_free
  intro h00
  have h10 : data.fundamentalMatrix 1 0 = 0 := by
    have hfund : data.sigmaEquiv (data.fundamentalMatrix 0 0) =
        data.fundamentalMatrix 1 0 := by
      simpa [BesselOrderParameterizedPVData.sigmaEquiv,
        BesselOrderParameterizedPVData.fundamentalMatrix,
        FieldShift.besselOrderCompanion, Matrix.mul_apply, Fin.sum_univ_two]
        using data.fundamental 0 0
    rw [h00, map_zero] at hfund
    simpa [BesselOrderParameterizedPVData.sigmaEquiv,
      BesselOrderParameterizedPVData.fundamentalMatrix] using hfund.symm
  have hdet : data.fundamentalMatrix.det = 0 := by
    simp [Matrix.det_fin_two, h00, h10]
  have hunit := data.fundamental_det_isUnit
  change IsUnit data.fundamentalMatrix.det at hunit
  rw [hdet] at hunit
  exact not_isUnit_zero hunit

/-- Faithful comparison-torsor descent turns any nonzero relation imposed in a positive-scale
Bessel PPV quotient into a contradiction. -/
theorem false_of_besselRelation_of_comparisonBasisIndependent
    (s : ℝ) (hs : 0 < s)
    (P : DifferentialPolynomial Unit (RatFunc Constants)) (hPne : P ≠ 0)
    (data : BesselOrderParameterizedPVData s)
    (hPmem : besselScalarPPVRelation P ∈ data.M)
    (hLI : ∀ (comparison : data.ComparisonJetData) {ι : Type}
      (basis : Module.Basis ι Constants
        (comparisonJetAlgebra (C := Constants) comparison.Z comparison.w)),
      LinearIndependent data.PPVRing
        (fun i =>
          ((basis i :
              comparisonJetAlgebra (C := Constants) comparison.Z comparison.w) :
            data.TensorSquare))) : False := by
  letI : Nontrivial data.PPVRing := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact data.ne_top
  letI : Algebra data.PPVRing data.TensorSquare :=
    Algebra.TensorProduct.leftAlgebra
      (R := RatFunc Constants) (S := data.PPVRing)
      (A := data.PPVRing) (B := data.PPVRing)
  obtain ⟨comparison, hclosure⟩ :=
    modifiedBesselOrder_sl2_galoisClosure_for_data s hs data
  let E := comparisonJetAlgebra (C := Constants) comparison.Z comparison.w
  letI : Module.Free Constants E := Module.Free.of_divisionRing Constants E
  let b := Module.Free.chooseBasis Constants E
  let hZE : ∀ i j, comparison.Z i j ∈ E :=
    fun i j => mem_comparisonJetAlgebra_entry comparison.Z comparison.w i j
  let H := galoisMonoid E comparison.Z hZE
    (tensorDifferentialPoints E comparison.deriv_stable)
  have hgen := comparison.tensor_generated
  have hindep : LinearIndependent data.PPVRing
      (fun i => ((b i : E) : data.TensorSquare)) := by
    exact hLI comparison b
  have hrelation : differentialPolynomialEvalOver (K := RatFunc Constants)
      (fun _ : Unit => data.fundamentalMatrix 0 0) P = 0 := by
    rw [← besselScalarPPVRelation_quotient data P]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hPmem
  have horbit : ∀ g ∈ H, g.det = 1 →
      differentialPolynomialEvalOver (K := RatFunc Constants)
        (fun _ : Unit => ∑ l : Fin 2,
          data.fundamentalMatrix 0 l * algebraMap Constants data.PPVRing (g l 0)) P = 0 := by
    intro g hg _
    exact differentialRelation_fundamental_mul_of_mem_galoisMonoid
      E b hgen hindep comparison.deriv_stable data.fundamentalMatrix comparison.Z hZE
      comparison.factorization P hrelation hg
  have hscaled : ∀ c : Constants, c ≠ 0 →
      differentialPolynomialEvalOver (K := RatFunc Constants)
        (fun _ : Unit => data.fundamentalMatrix 0 0 *
          algebraMap Constants data.PPVRing c) P = 0 := by
    intro c hc
    exact differentialRelation_scaled_of_matrixZeroSet
      data.fundamentalMatrix P H horbit hclosure c hc
  let L := diffClosure (RatFunc Constants)
  let T := BesselOrderPPVBaseChange data
  letI : Differential T := tensorProductDifferential
  let yR := data.fundamentalMatrix 0 0
  let e : T := Algebra.TensorProduct.includeRight yR
  have hincludeRight : Function.Injective
      (Algebra.TensorProduct.includeRight : data.PPVRing →ₐ[RatFunc Constants] T) := by
    letI : Module.Free (RatFunc Constants) data.PPVRing :=
      Module.Free.of_divisionRing (RatFunc Constants) data.PPVRing
    letI : Module.Flat (RatFunc Constants) data.PPVRing := Module.Flat.of_free
    exact Algebra.TensorProduct.includeRight_injective
      (R := RatFunc Constants) (A := L) (B := data.PPVRing)
      (algebraMap (RatFunc Constants) L).injective
  have he : e ≠ 0 := by
    intro he0
    have htensor :
        (Algebra.TensorProduct.includeRight yR : T) =
          Algebra.TensorProduct.includeRight 0 := by
      rw [map_zero]
      exact he0
    have hyR : yR = 0 := hincludeRight htensor
    exact data.fundamental_zero_zero_ne_zero (by simpa [yR] using hyR)
  obtain ⟨χ, hχδ, hχe⟩ := data.exists_baseChange_differentialPoint_ne_zero he
  let φ : data.PPVRing →ₐ[RatFunc Constants] L :=
    (χ.restrictScalars (RatFunc Constants)).comp
      (Algebra.TensorProduct.includeRight : data.PPVRing →ₐ[RatFunc Constants] T)
  have hφδ : ∀ x : data.PPVRing,
      φ (Differential.deriv x) = Differential.deriv (φ x) := by
    intro x
    change χ (Algebra.TensorProduct.includeRight (Differential.deriv x)) =
      Differential.deriv (χ (Algebra.TensorProduct.includeRight x))
    rw [show Algebra.TensorProduct.includeRight
        (R := RatFunc Constants) (A := L) (B := data.PPVRing)
          (Differential.deriv x) =
        tensorProductDerivation (K := RatFunc Constants)
          (Algebra.TensorProduct.includeRight x) by
      change (1 : L) ⊗ₜ[RatFunc Constants] Differential.deriv x =
        tensorProductDerivation (K := RatFunc Constants)
          ((1 : L) ⊗ₜ[RatFunc Constants] x)
      rw [tensorProductDerivation_tmul, Derivation.map_one_eq_zero,
        TensorProduct.zero_tmul, zero_add], hχδ]
  have hφy : φ yR ≠ 0 := by
    simpa [φ, e] using hχe
  let F : DifferentialPolynomial Unit L :=
    differentialCoeffExtend (ι := Unit) (F := RatFunc Constants) (L := L) P
  have hFscaled : ∀ c : Constants, c ≠ 0 →
      differentialPolynomialEvalOver (K := L)
        (fun _ : Unit => φ yR * algebraMap Constants L c) F = 0 := by
    intro c hc
    have hmapped := congrArg φ (hscaled c hc)
    have heval := evalOver_algHom (C := RatFunc Constants) φ hφδ
      (fun _ : Unit => yR * algebraMap Constants data.PPVRing c) P
    rw [map_zero] at hmapped
    rw [heval] at hmapped
    rw [differentialPolynomialEvalOver_differentialCoeffExtend]
    simpa [map_mul, φ, ← IsScalarTower.algebraMap_apply Constants (RatFunc Constants) L]
      using hmapped
  have hFzero : F = 0 :=
    eq_zero_of_evalOver_scaled_subfield_eq_zero
      (C := Constants) (L := L)
      (fun a => DifferentialAlgebra.deriv_algebraMap a) hφy hFscaled
  apply hPne
  apply MvPolynomial.map_injective (algebraMap (RatFunc Constants) L)
    (algebraMap (RatFunc Constants) L).injective
  simpa [F, differentialCoeffExtend] using hFzero

end

end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
