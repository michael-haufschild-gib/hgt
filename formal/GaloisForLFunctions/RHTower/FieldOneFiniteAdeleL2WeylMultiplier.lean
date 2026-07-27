import GaloisForLFunctions.RHTower.FieldOneSemilocalArchimedeanFaithfulness
import GaloisForLFunctions.RHTower.UnitModulusL2Multiplier
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Finite-adele `L²` Weyl multiplier

The compact open subgroup of integral finite adeles gives local compactness of
the additive finite-adele group.  With its Borel structure, this supplies
additive Haar measure.

The standard finite-adele character has pointwise norm one, so every
multiplicative shift acts unitarily on complex `L²` for Haar measure.  The
unitary agrees with the previously constructed Weyl action on compactly
supported locally constant Bruhat tests.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory

noncomputable instance fieldOneFiniteAdeleLocallyCompactSpace :
    LocallyCompactSpace FieldOneFiniteAdele :=
  IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup
    fieldOneFiniteAdeleIntegralAddSubgroup_isCompact
    (fieldOneFiniteAdeleIntegralAddSubgroup_isOpen.mem_nhds
      (zero_mem fieldOneFiniteAdeleIntegralAddSubgroup))

noncomputable instance fieldOneFiniteAdeleMeasurableSpace :
    MeasurableSpace FieldOneFiniteAdele :=
  borel FieldOneFiniteAdele

instance fieldOneFiniteAdeleBorelSpace :
    BorelSpace FieldOneFiniteAdele :=
  ⟨rfl⟩

/-- Additive Haar measure on the rational finite adeles. -/
noncomputable abbrev fieldOneFiniteAdeleAddHaar :
    Measure FieldOneFiniteAdele :=
  Measure.addHaar

/-- Standard finite-adele Weyl phase. -/
def fieldOneFiniteAdeleL2WeylPhase
    (r x : FieldOneFiniteAdele) : ℂ :=
  fieldOneFiniteAdeleStandardAddChar (r * x)

theorem fieldOneFiniteAdeleL2WeylPhase_continuous
    (r : FieldOneFiniteAdele) :
    Continuous (fieldOneFiniteAdeleL2WeylPhase r) := by
  exact
    (locallyConstantAddCharShift
      fieldOneFiniteAdeleStandardLocallyConstantAddChar r).continuous

@[simp]
theorem norm_fieldOneFiniteAdeleL2WeylPhase
    (r x : FieldOneFiniteAdele) :
    ‖fieldOneFiniteAdeleL2WeylPhase r x‖ = 1 := by
  change
    ‖(AddCircle.toCircle
      (fieldOneFiniteAdeleStandardUnitAddCircleCharacter (r * x)) : ℂ)‖ =
      1
  exact Circle.norm_coe _

/-- Finite-adele standard phase packaged for the general `L²` multiplier
construction. -/
def fieldOneFiniteAdeleUnitModulusL2Phase
    (r : FieldOneFiniteAdele) :
    UnitModulusL2Phase FieldOneFiniteAdele fieldOneFiniteAdeleAddHaar where
  toFun := fieldOneFiniteAdeleL2WeylPhase r
  aestronglyMeasurable :=
    (fieldOneFiniteAdeleL2WeylPhase_continuous r).aestronglyMeasurable
  norm_eq_one :=
    Filter.Eventually.of_forall
      (norm_fieldOneFiniteAdeleL2WeylPhase r)

/-- Unitary finite-adele Weyl multiplier on Haar `L²`. -/
def fieldOneFiniteAdeleL2WeylUnitary
    (r : FieldOneFiniteAdele) :
    Lp ℂ 2 fieldOneFiniteAdeleAddHaar ≃ₗᵢ[ℂ]
      Lp ℂ 2 fieldOneFiniteAdeleAddHaar :=
  (fieldOneFiniteAdeleUnitModulusL2Phase r).mulUnitary

theorem fieldOneFiniteAdeleL2WeylUnitary_ae
    (r : FieldOneFiniteAdele)
    (f : Lp ℂ 2 fieldOneFiniteAdeleAddHaar) :
    fieldOneFiniteAdeleL2WeylUnitary r f
      =ᵐ[fieldOneFiniteAdeleAddHaar]
        fun x => fieldOneFiniteAdeleL2WeylPhase r x * f x :=
  (fieldOneFiniteAdeleUnitModulusL2Phase r).mulUnitary_ae f

theorem fieldOneFiniteAdeleL2WeylUnitary_add_apply
    (r s : FieldOneFiniteAdele)
    (f : Lp ℂ 2 fieldOneFiniteAdeleAddHaar) :
    fieldOneFiniteAdeleL2WeylUnitary r
        (fieldOneFiniteAdeleL2WeylUnitary s f) =
      fieldOneFiniteAdeleL2WeylUnitary (r + s) f := by
  apply Lp.ext
  filter_upwards [
    fieldOneFiniteAdeleL2WeylUnitary_ae s f,
    fieldOneFiniteAdeleL2WeylUnitary_ae r
      (fieldOneFiniteAdeleL2WeylUnitary s f),
    fieldOneFiniteAdeleL2WeylUnitary_ae (r + s) f]
    with x hs hr hrs
  rw [hr, hs, hrs]
  simp only [fieldOneFiniteAdeleL2WeylPhase, add_mul]
  rw [AddChar.map_add_eq_mul]
  ring

/-- A finite Bruhat test defines an `L²` class for additive Haar measure. -/
def fieldOneFiniteBruhatToL2
    (f : FieldOneFiniteBruhatSchwartz) :
    Lp ℂ 2 fieldOneFiniteAdeleAddHaar :=
  (f.1.continuous.memLp_of_hasCompactSupport f.2).toLp f.1

theorem fieldOneFiniteBruhatToL2_ae
    (f : FieldOneFiniteBruhatSchwartz) :
    fieldOneFiniteBruhatToL2 f
      =ᵐ[fieldOneFiniteAdeleAddHaar] f.1 :=
  (f.1.continuous.memLp_of_hasCompactSupport f.2).coeFn_toLp

/-- The Haar-`L²` unitary extends the algebraic finite Bruhat Weyl
multiplier. -/
theorem fieldOneFiniteAdeleL2WeylUnitary_bruhat
    (r : FieldOneFiniteAdele)
    (f : FieldOneFiniteBruhatSchwartz) :
    fieldOneFiniteAdeleL2WeylUnitary r
        (fieldOneFiniteBruhatToL2 f) =
      fieldOneFiniteBruhatToL2
        (fieldOneFiniteAdeleStandardWeylMultiplier r f) := by
  apply Lp.ext
  filter_upwards [
    fieldOneFiniteAdeleL2WeylUnitary_ae r
      (fieldOneFiniteBruhatToL2 f),
    fieldOneFiniteBruhatToL2_ae f,
    fieldOneFiniteBruhatToL2_ae
      (fieldOneFiniteAdeleStandardWeylMultiplier r f)]
    with x hout hin htarget
  rw [hout, hin, htarget]
  rfl

end

end GaloisForLFunctions.RHTower
