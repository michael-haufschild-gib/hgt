import GaloisForLFunctions.RHTower.Deninger.DeningerRegulatorKernel
import GaloisForLFunctions.HTGeometry.Homology.AugmentedHochschildOne

/-!
# Independent prime sectors in Hochschild homology

The ordinary and signed prime moments are augmentation derivations on the actual
Steinberg quotient. Their vector detectors split the map from both prime tangent
spaces to Hochschild degree one. Every associated square-zero unit cycle vanishes
after ordinary cyclic descent. The scalar regulator sees only the logarithmic
moment of the ordinary sector, leaving the log kernel and signed sector invisible.
-/

noncomputable section
namespace RHTower
open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.SquareZeroCyclic
open PositiveSteinbergCyclic

abbrev DeningerPrimeSpace := Nat.Primes →₀ ℂ
abbrev DeningerPrimeJet := TrivSqZeroExt ℂ DeningerPrimeSpace

/-- Augmentation of the ordinary prime sector. -/
def deningerPrimeAugmentation : Quotient →ₐ[ℂ] ℂ where
  toFun q := (deningerSteinbergPrimeEquiv q).1.fst
  map_one' := by simp
  map_mul' a b := by simp
  map_zero' := by simp
  map_add' a b := by simp
  commutes' z := by simp [Algebra.algebraMap_eq_smul_one]

/-- Augmentation of the signed prime sector. -/
def deningerSignedPrimeAugmentation : Quotient →ₐ[ℂ] ℂ where
  toFun q := (deningerSteinbergPrimeEquiv q).2.fst
  map_one' := by simp
  map_mul' a b := by simp
  map_zero' := by simp
  map_add' a b := by simp
  commutes' z := by simp [Algebra.algebraMap_eq_smul_one]

/-- The full ordinary prime moment on the actual Steinberg quotient. -/
def deningerQuotientPrimeMoment : Quotient →ₗ[ℂ] DeningerPrimeSpace where
  toFun q := (deningerSteinbergPrimeEquiv q).1.snd
  map_add' a b := by simp
  map_smul' z a := by simp

/-- The full signed prime moment on the actual Steinberg quotient. -/
def deningerQuotientSignedPrimeMoment : Quotient →ₗ[ℂ] DeningerPrimeSpace where
  toFun q := (deningerSteinbergPrimeEquiv q).2.snd
  map_add' a b := by simp
  map_smul' z a := by simp

@[simp] theorem deningerPrimeAugmentation_quotientMap (a : Source) :
    deningerPrimeAugmentation (quotientMap a) = deningerKummerAugmentation a := by
  change (deningerSteinbergPrimeEquiv (quotientMap a)).1.fst = _
  rw [deningerSteinbergPrimeEquiv_quotientMap]
  exact (TrivSqZeroExt.fst_map deningerPrimeMomentEquiv.toLinearMap _).trans
    (deningerFirstJet_fst a)

@[simp] theorem deningerSignedPrimeAugmentation_quotientMap (a : Source) :
    deningerSignedPrimeAugmentation (quotientMap a) = deningerKummerSignAugmentation a := by
  change (deningerSteinbergPrimeEquiv (quotientMap a)).2.fst = _
  rw [deningerSteinbergPrimeEquiv_quotientMap]
  exact (TrivSqZeroExt.fst_map deningerPrimeMomentEquiv.toLinearMap _).trans
    (deningerSignedFirstJet_fst a)

@[simp] theorem deningerQuotientPrimeMoment_quotientMap (a : Source) :
    deningerQuotientPrimeMoment (quotientMap a) = deningerPrimeMoment a := by
  change (deningerSteinbergPrimeEquiv (quotientMap a)).1.snd = _
  rw [deningerSteinbergPrimeEquiv_quotientMap]
  exact TrivSqZeroExt.snd_map deningerPrimeMomentEquiv.toLinearMap _

@[simp] theorem deningerQuotientSignedPrimeMoment_quotientMap (a : Source) :
    deningerQuotientSignedPrimeMoment (quotientMap a) = deningerSignedPrimeMoment a := by
  change (deningerSteinbergPrimeEquiv (quotientMap a)).2.snd = _
  rw [deningerSteinbergPrimeEquiv_quotientMap]
  exact TrivSqZeroExt.snd_map deningerPrimeMomentEquiv.toLinearMap _

theorem deningerQuotientPrimeMoment_mul (a b : Quotient) :
    deningerQuotientPrimeMoment (a*b) =
      deningerPrimeAugmentation a • deningerQuotientPrimeMoment b +
      deningerPrimeAugmentation b • deningerQuotientPrimeMoment a := by
  change (deningerSteinbergPrimeEquiv (a*b)).1.snd = _
  rw [map_mul]
  simp only [Prod.fst_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul]
  rfl

theorem deningerQuotientSignedPrimeMoment_mul (a b : Quotient) :
    deningerQuotientSignedPrimeMoment (a*b) =
      deningerSignedPrimeAugmentation a • deningerQuotientSignedPrimeMoment b +
      deningerSignedPrimeAugmentation b • deningerQuotientSignedPrimeMoment a := by
  change (deningerSteinbergPrimeEquiv (a*b)).2.snd = _
  rw [map_mul]
  simp only [Prod.snd_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul]
  rfl

/-- Both independent prime tangent sectors, represented in the actual quotient algebra. -/
def deningerPairedPrimeTangent : (DeningerPrimeSpace × DeningerPrimeSpace) →ₗ[ℂ] Quotient where
  toFun x := deningerSteinbergPrimeEquiv.symm
    (TrivSqZeroExt.inr x.1, TrivSqZeroExt.inr x.2)
  map_add' x y := by
    apply deningerSteinbergPrimeEquiv.injective
    simp
  map_smul' z x := by
    apply deningerSteinbergPrimeEquiv.injective
    simp

@[simp] theorem deningerPairedPrimeTangent_coordinates (x : DeningerPrimeSpace × DeningerPrimeSpace) :
    deningerSteinbergPrimeEquiv (deningerPairedPrimeTangent x) =
      (TrivSqZeroExt.inr x.1, TrivSqZeroExt.inr x.2) :=
  deningerSteinbergPrimeEquiv.apply_symm_apply _

@[simp] theorem deningerQuotientPrimeMoment_paired (x : DeningerPrimeSpace × DeningerPrimeSpace) :
    deningerQuotientPrimeMoment (deningerPairedPrimeTangent x) = x.1 := by
  change (deningerSteinbergPrimeEquiv (deningerPairedPrimeTangent x)).1.snd = x.1
  rw [deningerPairedPrimeTangent_coordinates]
  rfl

@[simp] theorem deningerQuotientSignedPrimeMoment_paired (x : DeningerPrimeSpace × DeningerPrimeSpace) :
    deningerQuotientSignedPrimeMoment (deningerPairedPrimeTangent x) = x.2 := by
  change (deningerSteinbergPrimeEquiv (deningerPairedPrimeTangent x)).2.snd = x.2
  rw [deningerPairedPrimeTangent_coordinates]
  rfl

theorem deningerPairedPrimeTangent_mul (x y : DeningerPrimeSpace × DeningerPrimeSpace) :
    deningerPairedPrimeTangent x * deningerPairedPrimeTangent y = 0 := by
  apply deningerSteinbergPrimeEquiv.injective
  rw [map_mul, map_zero, deningerPairedPrimeTangent_coordinates,
    deningerPairedPrimeTangent_coordinates]
  ext <;> simp

/-- Both vector-valued derivations descend to Hochschild homology. -/
def deningerPrimeHochschildDetector : HochschildOne Quotient →ₗ[ℂ]
    (DeningerPrimeSpace × DeningerPrimeSpace) :=
  (hochschildDetector deningerPrimeAugmentation deningerQuotientPrimeMoment
    deningerQuotientPrimeMoment_mul).prod
  (hochschildDetector deningerSignedPrimeAugmentation deningerQuotientSignedPrimeMoment
    deningerQuotientSignedPrimeMoment_mul)

/-- The ordinary and signed prime tangent spaces map to genuine Hochschild classes. -/
def deningerPrimeHochschildClass : (DeningerPrimeSpace × DeningerPrimeSpace) →ₗ[ℂ]
    HochschildOne Quotient :=
  (tangentClass (A := Quotient)).comp deningerPairedPrimeTangent

/-- All prime tangent coordinates are recovered from their homology classes. -/
theorem deningerPrimeHochschildDetector_class (x : DeningerPrimeSpace × DeningerPrimeSpace) :
    deningerPrimeHochschildDetector (deningerPrimeHochschildClass x) = x := by
  apply Prod.ext
  · exact (hochschildDetector_tangentClass _ _ _ _).trans
      (deningerQuotientPrimeMoment_paired x)
  · exact (hochschildDetector_tangentClass _ _ _ _).trans
      (deningerQuotientSignedPrimeMoment_paired x)

theorem deningerPrimeHochschildClass_injective : Function.Injective deningerPrimeHochschildClass := by
  intro x y h
  have := congrArg deningerPrimeHochschildDetector h
  simpa only [deningerPrimeHochschildDetector_class] using this

/-- The square-zero unit cycle represents the same faithful prime tangent class. -/
theorem deningerPrimeUnit_hochschild (x : DeningerPrimeSpace × DeningerPrimeSpace) :
    (LinearMap.range (boundaryTwo (A := Quotient))).mkQ
      (pair (1-deningerPairedPrimeTangent x) (1+deningerPairedPrimeTangent x)) =
      deningerPrimeHochschildClass x :=
  squareZeroUnit_class _ (deningerPairedPrimeTangent_mul x x)

/-- Every such prime unit class dies after the ordinary cyclic relations. -/
theorem deningerPrimeUnit_cyclic (x : DeningerPrimeSpace × DeningerPrimeSpace) :
    pair (1-deningerPairedPrimeTangent x) (1+deningerPairedPrimeTangent x) ∈ cyclicRelations :=
  unit_mem_cyclicRelations _ (deningerPairedPrimeTangent_mul x x)

/-- The scalar regulator reads only the logarithmic moment of the first sector. -/
theorem deningerPairedPrimeTangent_regulator (x : DeningerPrimeSpace × DeningerPrimeSpace) :
    regulator (deningerPairedPrimeTangent x) = deningerPrimeLog x.1 := by
  rw [deningerQuotientRegulator_eq, deningerPairedPrimeTangent_coordinates]
  rfl

/-- All log-kernel directions and the entire signed prime sector survive homology. -/
def deningerInvisiblePrimeHochschildClass :
    (deningerPrimeLog.ker × DeningerPrimeSpace) →ₗ[ℂ] HochschildOne Quotient :=
  deningerPrimeHochschildClass.comp
    (deningerPrimeLog.ker.subtype.prodMap (LinearMap.id : DeningerPrimeSpace →ₗ[ℂ] DeningerPrimeSpace))

theorem deningerInvisiblePrimeHochschildClass_injective :
    Function.Injective deningerInvisiblePrimeHochschildClass := by
  intro x y h
  change deningerPrimeHochschildClass (x.1.val, x.2) =
    deningerPrimeHochschildClass (y.1.val, y.2) at h
  have he := deningerPrimeHochschildClass_injective h
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst he)
  · exact congrArg (fun z : DeningerPrimeSpace × DeningerPrimeSpace => z.2) he

theorem deningerInvisiblePrimeTangent_regulator
    (x : deningerPrimeLog.ker × DeningerPrimeSpace) :
    regulator (deningerPairedPrimeTangent (x.1.val, x.2)) = 0 := by
  rw [deningerPairedPrimeTangent_regulator]
  exact x.1.property

#print axioms deningerPrimeHochschildClass_injective
#print axioms deningerPrimeUnit_hochschild
#print axioms deningerPrimeUnit_cyclic
#print axioms deningerPairedPrimeTangent_regulator
#print axioms deningerInvisiblePrimeHochschildClass_injective
end RHTower
