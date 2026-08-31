import GaloisForLFunctions.HTGeometry.BesselOrderParameterizedDiffFG
import GaloisForLFunctions.HTGeometry.ComparisonJetAlgebraDifferentialGeneration
import GaloisForLFunctions.HTGeometry.ComparisonJetAlgebraDiffFG
import GaloisForLFunctions.HTGeometry.ComparisonJetAlgebraFixed
import GaloisForLFunctions.HTGeometry.TensorReducedGeneral
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraTower

/-!
# Concrete comparison-jet torsor data for the Bessel PPV quotient

The parameterized Bessel PPV construction supplies its fundamental matrix, inverse determinant,
difference action, derivation, and full differential generation.  This file constructs the
comparison matrix and its comparison-jet algebra and discharges stability, fixedness, tensor-square
generation, differential finite generation, and reducedness.

The determinant-square and no-new-difference-constants assertions are deliberately absent: they
are the remaining PPV descent problem, not consequences of the algebraic structure constructed
here.
-/

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

noncomputable section

open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped TensorProduct Differential

local instance besselOrderComparisonJetBaseDifferential :
    Differential (RatFunc Constants) := coordinateTotalDifferential

/-- Quotient ring underlying a concrete parameterized Bessel PV datum. -/
abbrev BesselOrderParameterizedPVData.PPVRing {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :=
  (ppvLocalization (RatFunc Constants) 2) ⧸ data.M

/-- Fundamental matrix in the concrete Bessel PPV quotient. -/
def BesselOrderParameterizedPVData.fundamentalMatrix {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    Matrix (Fin 2) (Fin 2) data.PPVRing :=
  (ppvFundamental (RatFunc Constants) 2).map (Ideal.Quotient.mk data.M)

/-- Difference automorphism of the concrete Bessel PPV quotient. -/
def BesselOrderParameterizedPVData.sigmaEquiv {s : ℝ}
    (data : BesselOrderParameterizedPVData s) : data.PPVRing ≃+* data.PPVRing :=
  sigmaQuotientEquiv (besselOrderPPVSigma s) data.M
    data.isSigmaDeltaIdeal.1 data.isSigmaIdeal_symm

/-- Tensor square of the concrete Bessel PPV quotient. -/
abbrev BesselOrderParameterizedPVData.TensorSquare {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :=
  data.PPVRing ⊗[RatFunc Constants] data.PPVRing

/-- Diagonal difference action on the concrete Bessel PPV tensor square. -/
def BesselOrderParameterizedPVData.tensorSigmaEquiv {s : ℝ}
    (data : BesselOrderParameterizedPVData s) : data.TensorSquare ≃+* data.TensorSquare :=
  differenceTensorEquiv FieldShift.ratShiftEquiv data.sigmaEquiv data.baseCompatible

local instance besselOrderComparisonJetPPVDifferential {s : ℝ}
    (data : BesselOrderParameterizedPVData s) : Differential data.PPVRing :=
  quotientDifferential data.M data.isSigmaDeltaIdeal.2

local instance besselOrderComparisonJetPPVDifferentialAlgebra {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    DifferentialAlgebra (RatFunc Constants) data.PPVRing :=
  ppvQuotientDifferentialAlgebra data.M data.isSigmaDeltaIdeal.2

local instance besselOrderComparisonJetConstantsRatDifferentialAlgebra :
    DifferentialAlgebra Constants (RatFunc Constants) :=
  coordinateTotalDifferentialAlgebra

local instance besselOrderComparisonJetConstantsPPVDifferentialAlgebra {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    DifferentialAlgebra Constants data.PPVRing :=
  differentialAlgebra_trans (C := Constants) (K := RatFunc Constants) (E := data.PPVRing)

local instance besselOrderComparisonJetRatCharZero : CharZero (RatFunc Constants) :=
  charZero_of_injective_ringHom (algebraMap ℚ (RatFunc Constants)).injective

local instance besselOrderComparisonJetPPVReduced {s : ℝ}
    (data : BesselOrderParameterizedPVData s) : IsReduced data.PPVRing :=
  data.isReduced

/-- All derivatives of the four fundamental entries, together with the inverse determinant,
generate the concrete Bessel PPV quotient as an ordinary algebra. -/
theorem BesselOrderParameterizedPVData.adjoin_fundamentalJets_eq_top {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    Algebra.adjoin (RatFunc Constants)
      (Set.range (fun q : (Fin 2 × Fin 2) × ℕ =>
        differentialJet q.2 (data.fundamentalMatrix q.1.1 q.1.2)) ∪
        {data.detInverse}) = ⊤ := by
  rw [← data.generatedJets]
  congr 1
  ext x
  constructor
  · rintro (⟨q, rfl⟩ | hx)
    · left
      refine ⟨q, ?_⟩
      exact (data.jets_are_iteratedDeriv q.1.1 q.1.2 q.2).symm
    · exact Or.inr hx
  · rintro (⟨q, rfl⟩ | hx)
    · left
      refine ⟨q, ?_⟩
      exact data.jets_are_iteratedDeriv q.1.1 q.1.2 q.2
    · exact Or.inr hx

/-- Fully constructed comparison-jet structure, excluding only the genuine no-new-constants and
determinant descent assertions. -/
structure BesselOrderParameterizedPVData.ComparisonJetData {s : ℝ}
    (data : BesselOrderParameterizedPVData s) where
  Z : Matrix (Fin 2) (Fin 2) data.TensorSquare
  w : data.TensorSquare
  factorization :
    leftFundamental (RatFunc Constants) data.fundamentalMatrix * Z =
      rightFundamental (RatFunc Constants) data.fundamentalMatrix
  fixed_entry : ∀ i j,
    data.tensorSigmaEquiv (Z i j) = Z i j
  fixed_entry_deriv : ∀ i j,
    data.tensorSigmaEquiv (tensorSquareDerivation (K := RatFunc Constants) (Z i j)) =
        tensorSquareDerivation (K := RatFunc Constants) (Z i j)
  det_mul_inverse : Z.det * w = 1
  deriv_stable : ∀ e ∈ comparisonJetAlgebra (C := Constants) Z w,
    tensorSquareDerivation (K := RatFunc Constants) e ∈
      comparisonJetAlgebra (C := Constants) Z w
  fixed : ∀ e ∈ comparisonJetAlgebra (C := Constants) Z w,
    data.tensorSigmaEquiv e = e
  tensor_generated : Algebra.adjoin Constants
    (Set.range (fun r : data.PPVRing =>
        r ⊗ₜ[RatFunc Constants] (1 : data.PPVRing)) ∪
      (comparisonJetAlgebra (C := Constants) Z w :
        Set data.TensorSquare)) = ⊤
  differential_generated : Algebra.adjoin Constants
    (Set.range (fun p : Fin 5 × ℕ => tensorJet (K := RatFunc Constants) p.2
      (comparisonJetGeneratorsTwo Z w p.1))) =
        comparisonJetAlgebra (C := Constants) Z w
  reduced : IsReduced (comparisonJetAlgebra (C := Constants) Z w)

/-- Every concrete Bessel PPV datum canonically yields comparison-jet torsor data with all
algebraic and differential structure witnesses constructed. -/
theorem BesselOrderParameterizedPVData.comparisonJetData_nonempty {s : ℝ}
    (data : BesselOrderParameterizedPVData s) : Nonempty data.ComparisonJetData := by
  letI : Invertible data.fundamentalMatrix :=
    Matrix.invertibleOfIsUnitDet data.fundamentalMatrix data.fundamental_det_isUnit
  have hfund : data.fundamentalMatrix.map data.sigmaEquiv =
      ((FieldShift.besselOrderCompanion (slope s)).map
        (algebraMap (RatFunc Constants) data.PPVRing)) * data.fundamentalMatrix := by
    ext i j
    exact data.fundamental i j
  obtain ⟨Z, hZ, hZfixed, hZderivFixed, hZunit⟩ :=
    exists_parameterized_tensor_comparison_matrix
      FieldShift.ratShiftEquiv data.sigmaEquiv data.baseCompatible data.commutesDeriv
      (FieldShift.besselOrderCompanion (slope s)) data.fundamentalMatrix hfund
  rcases hZunit with ⟨detUnit, hdetUnit⟩
  let w : data.TensorSquare := ↑(detUnit⁻¹)
  have hw : Z.det * w = 1 := by
    simp [w, ← hdetUnit]
  have hstable : ∀ e ∈ comparisonJetAlgebra (C := Constants) Z w,
      tensorSquareDerivation (K := RatFunc Constants) e ∈
        comparisonJetAlgebra (C := Constants) Z w := by
    intro e he
    exact comparisonJetAlgebra_deriv_stable Z hw he
  have hconst : ∀ c : Constants,
      data.sigmaEquiv (algebraMap Constants data.PPVRing c) =
        algebraMap Constants data.PPVRing c := by
    intro c
    rw [IsScalarTower.algebraMap_apply Constants (RatFunc Constants) data.PPVRing,
      show data.sigmaEquiv
          (algebraMap (RatFunc Constants) data.PPVRing
            (algebraMap Constants (RatFunc Constants) c)) =
          algebraMap (RatFunc Constants) data.PPVRing
            (FieldShift.ratShiftEquiv (algebraMap Constants (RatFunc Constants) c)) from
        data.baseCompatible (algebraMap Constants (RatFunc Constants) c),
      FieldShift.ratShiftEquiv_apply, FieldShift.ratShift_const]
  have hfixed : ∀ e ∈ comparisonJetAlgebra (C := Constants) Z w,
      data.tensorSigmaEquiv e = e := by
    intro e he
    exact comparisonJetAlgebra_fixed data.baseCompatible hconst data.commutesDeriv
      Z hZfixed w hw he
  have hgenerated : Algebra.adjoin Constants
      (Set.range (fun r : data.PPVRing =>
          r ⊗ₜ[RatFunc Constants] (1 : data.PPVRing)) ∪
        (comparisonJetAlgebra (C := Constants) Z w : Set data.TensorSquare)) = ⊤ := by
    exact adjoin_comparisonJetAlgebra_eq_top_of_differentialGeneration
      data.fundamentalMatrix data.detInverse data.fundamental_det_mul_inverse
      data.adjoin_fundamentalJets_eq_top Z w hZ hw
  have hdiffGenerated : Algebra.adjoin Constants
      (Set.range (fun p : Fin 5 × ℕ => tensorJet (K := RatFunc Constants) p.2
        (comparisonJetGeneratorsTwo Z w p.1))) =
      comparisonJetAlgebra (C := Constants) Z w :=
    adjoin_comparisonJetGeneratorsTwo Z hw
  letI : IsReduced data.TensorSquare :=
    isReduced_tensorSquare_of_charZero
  have hreduced : IsReduced (comparisonJetAlgebra (C := Constants) Z w) :=
    isReduced_of_injective
      (comparisonJetAlgebra (C := Constants) Z w).val Subtype.val_injective
  exact ⟨{
    Z := Z
    w := w
    factorization := hZ
    fixed_entry := hZfixed
    fixed_entry_deriv := hZderivFixed
    det_mul_inverse := hw
    deriv_stable := hstable
    fixed := hfixed
    tensor_generated := hgenerated
    differential_generated := hdiffGenerated
    reduced := hreduced
  }⟩

/-- Unconditional existence of the reduced, differentially finitely generated comparison-jet
torsor algebra for every real Bessel slope.  No PPV datum or structural witness is retained. -/
theorem besselOrder_parameterizedPicardVessiot_comparisonJet_exists :
    ∀ s : ℝ, ∃ data : BesselOrderParameterizedPVData s,
      Nonempty data.ComparisonJetData := by
  intro s
  obtain ⟨data⟩ := besselOrder_parameterizedPicardVessiot_exists s
  exact ⟨data, data.comparisonJetData_nonempty⟩

end

end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
