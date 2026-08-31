import GaloisForLFunctions.HTGeometry.BesselOrderParameterizedDiffFG
import GaloisForLFunctions.HTGeometry.DifferentialFGBaseChangePoint
import GaloisForLFunctions.HTGeometry.DifferentialClosureClosed

/-!
# Differential points of the base-changed Bessel PPV quotient

The concrete reduced, differentially finitely generated quotient is extended from `Constants(z)`
to its constructed differential closure.  Scalar-extension reducedness, finite generation, and
Kolchin's Nullstellensatz then construct enough differential points to separate every nonzero
element.  No differential point, differential closure, reducedness, or finite-generation premise
is retained.
-/

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

noncomputable section

open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped TensorProduct Differential

local instance besselOrderParameterizedBaseChangePointsBaseDifferential :
    Differential (RatFunc Constants) := coordinateTotalDifferential

local instance besselOrderParameterizedBaseChangePointsClosureDifferentialAlgebra :
    DifferentialAlgebra (RatFunc Constants) (diffClosure (RatFunc Constants)) :=
  DiffFieldExt.differentialAlgebra (diffClosureExt (F := RatFunc Constants))

/-- Scalar extension of a concrete Bessel PPV quotient to the differential closure of its base. -/
abbrev BesselOrderPPVBaseChange {s : ℝ} (data : BesselOrderParameterizedPVData s) :=
  diffClosure (RatFunc Constants) ⊗[RatFunc Constants]
    ((ppvLocalization (RatFunc Constants) 2) ⧸ data.M)

/-- Every nonzero element of the base-changed quotient is detected by a differential point. -/
def BesselOrderParameterizedPVData.BaseChangePointsSeparate {s : ℝ}
    (data : BesselOrderParameterizedPVData s) : Prop :=
  letI : Differential ((ppvLocalization (RatFunc Constants) 2) ⧸ data.M) :=
    quotientDifferential data.M data.isSigmaDeltaIdeal.2
  letI : DifferentialAlgebra (RatFunc Constants)
      ((ppvLocalization (RatFunc Constants) 2) ⧸ data.M) :=
    ppvQuotientDifferentialAlgebra data.M data.isSigmaDeltaIdeal.2
  ∀ e : BesselOrderPPVBaseChange data, e ≠ 0 →
    ∃ χ : BesselOrderPPVBaseChange data →ₐ[diffClosure (RatFunc Constants)]
        diffClosure (RatFunc Constants),
      (∀ x : BesselOrderPPVBaseChange data,
        χ (tensorProductDerivation (K := RatFunc Constants) x) =
          Differential.deriv (R := diffClosure (RatFunc Constants)) (χ x)) ∧ χ e ≠ 0

/-- Kolchin specialization separates one specified nonzero element of a concrete base-changed
Bessel PPV quotient. -/
theorem BesselOrderParameterizedPVData.exists_baseChange_differentialPoint_ne_zero
    {s : ℝ} (data : BesselOrderParameterizedPVData s)
    {e : BesselOrderPPVBaseChange data} (he : e ≠ 0) :
    letI : Differential ((ppvLocalization (RatFunc Constants) 2) ⧸ data.M) :=
      quotientDifferential data.M data.isSigmaDeltaIdeal.2
    letI : DifferentialAlgebra (RatFunc Constants)
        ((ppvLocalization (RatFunc Constants) 2) ⧸ data.M) :=
      ppvQuotientDifferentialAlgebra data.M data.isSigmaDeltaIdeal.2
    letI : Differential (BesselOrderPPVBaseChange data) :=
      tensorProductDifferential (K := RatFunc Constants)
        (A := diffClosure (RatFunc Constants))
        (B := (ppvLocalization (RatFunc Constants) 2) ⧸ data.M)
    ∃ χ : BesselOrderPPVBaseChange data →ₐ[diffClosure (RatFunc Constants)]
        diffClosure (RatFunc Constants),
      (∀ x : BesselOrderPPVBaseChange data,
        χ (tensorProductDerivation (K := RatFunc Constants) x) =
          Differential.deriv (R := diffClosure (RatFunc Constants)) (χ x)) ∧ χ e ≠ 0 := by
  letI : Differential ((ppvLocalization (RatFunc Constants) 2) ⧸ data.M) :=
    quotientDifferential data.M data.isSigmaDeltaIdeal.2
  letI : Nontrivial ((ppvLocalization (RatFunc Constants) 2) ⧸ data.M) := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact data.ne_top
  letI : DifferentialAlgebra (RatFunc Constants)
      ((ppvLocalization (RatFunc Constants) 2) ⧸ data.M) :=
    ppvQuotientDifferentialAlgebra data.M data.isSigmaDeltaIdeal.2
  letI : IsReduced ((ppvLocalization (RatFunc Constants) 2) ⧸ data.M) := data.isReduced
  letI : Differential (BesselOrderPPVBaseChange data) :=
    tensorProductDifferential (K := RatFunc Constants)
      (A := diffClosure (RatFunc Constants))
      (B := (ppvLocalization (RatFunc Constants) 2) ⧸ data.M)
  exact exists_differentialAlgHom_ne_zero_of_diffFG_tensorBaseChange
    (K := RatFunc Constants) (L := diffClosure (RatFunc Constants))
    data.diffGenerators data.diffGenerators_surjective he

/-- Separating base-change differential points are constructed for every concrete PPV datum. -/
theorem BesselOrderParameterizedPVData.baseChangePointsSeparate
    {s : ℝ} (data : BesselOrderParameterizedPVData s) :
    data.BaseChangePointsSeparate := by
  intro e he
  exact data.exists_baseChange_differentialPoint_ne_zero he

/-- Unconditional existence of a Bessel PPV quotient whose differential-closure base change has
separating differential points. -/
theorem besselOrder_parameterizedPicardVessiot_baseChangePointsSeparate :
    ∀ s : ℝ, ∃ data : BesselOrderParameterizedPVData s,
      data.BaseChangePointsSeparate := by
  intro s
  obtain ⟨data⟩ := besselOrder_parameterizedPicardVessiot_exists s
  exact ⟨data, data.baseChangePointsSeparate⟩

end

end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
