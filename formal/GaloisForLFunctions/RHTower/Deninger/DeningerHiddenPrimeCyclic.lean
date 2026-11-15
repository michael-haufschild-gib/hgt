import GaloisForLFunctions.RHTower.Deninger.DeningerHiddenPrimeHochschild
import GaloisForLFunctions.HTGeometry.Homology.AlternatingCyclicMoments

/-!
# Surviving cyclic classes from hidden prime tangents

Pair the prime-two tangent with each scalar-invisible source tangent. Alternating
the pivot valuation and full prime moment detects these ordinary cyclic classes
by deleting the pivot coordinate. This deletion is injective on logarithmic
relations because `log 2` is nonzero. The complete normalized prime-relation basis
is recovered as the non-pivot coordinate basis and remains linearly independent.
-/

noncomputable section
namespace RHTower
open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.SquareZeroCyclic
open PositiveSteinbergCyclic

/-- The pivot prime valuation, descended to the actual Steinberg quotient. -/
def deningerPivotMoment : Quotient →ₗ[ℂ] ℂ where
  toFun q := deningerQuotientPrimeMoment q deningerPrimeLogPivot
  map_add' a b := by simp
  map_smul' z a := by simp

theorem deningerPivotMoment_mul (a b : Quotient) :
    deningerPivotMoment (a*b) = deningerPrimeAugmentation a * deningerPivotMoment b +
      deningerPrimeAugmentation b * deningerPivotMoment a := by
  change deningerQuotientPrimeMoment (a*b) deningerPrimeLogPivot = _
  rw [deningerQuotientPrimeMoment_mul]
  rfl

/-- The original positive prime section, viewed in the quotient. -/
def deningerSourcePrimeTangent : DeningerPrimeSpace →ₗ[ℂ] Quotient :=
  quotientMap.toLinearMap.comp deningerPrimeTangentSection

@[simp] theorem deningerSourcePrimeTangent_moment (x : DeningerPrimeSpace) :
    deningerQuotientPrimeMoment (deningerSourcePrimeTangent x) = x := by
  change deningerQuotientPrimeMoment (quotientMap (deningerPrimeTangentSection x)) = x
  rw [deningerQuotientPrimeMoment_quotientMap, deningerPrimeTangentSection_right_inverse]

@[simp] theorem deningerSourcePrimeTangent_pivot (x : DeningerPrimeSpace) :
    deningerPivotMoment (deningerSourcePrimeTangent x) = x deningerPrimeLogPivot :=
  congrArg (fun y : DeningerPrimeSpace => y deningerPrimeLogPivot)
    (deningerSourcePrimeTangent_moment x)

/-- A prime-two tangent anchors the surviving alternating classes. -/
def deningerPivotTangent : Quotient :=
  deningerSourcePrimeTangent (Finsupp.single deningerPrimeLogPivot 1)

@[simp] theorem deningerPivotTangent_moment :
    deningerQuotientPrimeMoment deningerPivotTangent = Finsupp.single deningerPrimeLogPivot 1 :=
  deningerSourcePrimeTangent_moment _

@[simp] theorem deningerPivotTangent_pivot : deningerPivotMoment deningerPivotTangent = 1 := by
  rw [deningerPivotTangent, deningerSourcePrimeTangent_pivot, Finsupp.single_eq_same]

/-- Alternating the pivot valuation with the full moment descends to ordinary cyclic homology. -/
def deningerCyclicPrimeDetector : CyclicOne Quotient →ₗ[ℂ] DeningerPrimeSpace :=
  cyclicAlternatingDetector deningerPrimeAugmentation deningerPivotMoment
    deningerQuotientPrimeMoment deningerPivotMoment_mul deningerQuotientPrimeMoment_mul

/-- Pairing a fixed prime tangent with scalar-invisible source tangents gives cyclic classes. -/
def deningerHiddenPrimeCyclic : deningerPrimeLog.ker →ₗ[ℂ] CyclicOne Quotient :=
  (cyclicRelations (A := Quotient)).mkQ.comp
    ((pairLinearRight deningerPivotTangent).comp
      (deningerSourcePrimeTangent.comp deningerPrimeLog.ker.subtype))

/-- The alternating detector removes exactly the pivot coordinate. -/
theorem deningerCyclicPrimeDetector_hidden (x : deningerPrimeLog.ker) :
    deningerCyclicPrimeDetector (deningerHiddenPrimeCyclic x) =
      x.val - x.val deningerPrimeLogPivot • Finsupp.single deningerPrimeLogPivot 1 := by
  change cyclicAlternatingDetector deningerPrimeAugmentation deningerPivotMoment
    deningerQuotientPrimeMoment deningerPivotMoment_mul deningerQuotientPrimeMoment_mul
    ((cyclicRelations (A := Quotient)).mkQ
      (pair deningerPivotTangent (deningerSourcePrimeTangent x.val))) = _
  rw [cyclicAlternatingDetector_pair, deningerPivotTangent_pivot,
    deningerSourcePrimeTangent_moment, deningerSourcePrimeTangent_pivot,
    deningerPivotTangent_moment, one_smul]

/-- Each normalized hidden prime relation is recovered as its non-pivot prime coordinate. -/
theorem deningerCyclicPrimeDetector_basis (p : DeningerPrimeLogAway) :
    deningerCyclicPrimeDetector (deningerHiddenPrimeCyclic (deningerPrimeLogKernelBasis p)) =
      Finsupp.single p.val 1 := by
  classical
  rw [deningerCyclicPrimeDetector_hidden, deningerPrimeLogKernelBasis_apply]
  simp [Ne.symm p.property]

/-- The logarithmic functional applied to the alternating cyclic prime moment. -/
def deningerCyclicLogMoment : CyclicOne Quotient →ₗ[ℂ] ℂ :=
  deningerPrimeLog.comp deningerCyclicPrimeDetector

/-- The cyclic logarithmic moment is the determinant of the pivot valuation and native regulator. -/
theorem deningerCyclicLogMoment_pair (a b : Quotient) :
    deningerCyclicLogMoment ((cyclicRelations (A := Quotient)).mkQ (pair a b)) =
      deningerPivotMoment a * regulator b - deningerPivotMoment b * regulator a := by
  change deningerPrimeLog (cyclicAlternatingDetector deningerPrimeAugmentation
    deningerPivotMoment deningerQuotientPrimeMoment deningerPivotMoment_mul
    deningerQuotientPrimeMoment_mul ((cyclicRelations (A := Quotient)).mkQ (pair a b))) = _
  rw [cyclicAlternatingDetector_pair, map_sub, map_smul, map_smul,
    deningerQuotientRegulator_eq b, deningerQuotientRegulator_eq a]
  rfl

/-- Pairing the hidden relation at `p` with the pivot recovers `log p` in cyclic homology. -/
theorem deningerCyclicLogMoment_basis (p : DeningerPrimeLogAway) :
    deningerCyclicLogMoment (deningerHiddenPrimeCyclic (deningerPrimeLogKernelBasis p)) =
      (Real.log (p.val : ℝ) : ℂ) := by
  change deningerPrimeLog (deningerCyclicPrimeDetector
    (deningerHiddenPrimeCyclic (deningerPrimeLogKernelBasis p))) = _
  rw [deningerCyclicPrimeDetector_basis, deningerPrimeLog_single, mul_one]

/-- Removing the pivot coordinate is injective on the complete log-relation space. -/
theorem deningerHiddenPrimeCyclic_injective : Function.Injective deningerHiddenPrimeCyclic := by
  intro x y h
  have hd := congrArg deningerCyclicPrimeDetector h
  rw [deningerCyclicPrimeDetector_hidden, deningerCyclicPrimeDetector_hidden] at hd
  have hl := congrArg deningerPrimeLog hd
  have hx : deningerPrimeLog x.val = 0 := x.property
  have hy : deningerPrimeLog y.val = 0 := y.property
  simp only [map_sub, map_smul, hx, hy, deningerPrimeLog_single,
    mul_one, zero_sub, smul_eq_mul] at hl
  have hn : (Real.log (deningerPrimeLogPivot : ℝ) : ℂ) ≠ 0 :=
    Units.ne_zero (deningerPrimeLogUnit deningerPrimeLogPivot)
  have hp : x.val deningerPrimeLogPivot = y.val deningerPrimeLogPivot :=
    mul_right_cancel₀ hn (neg_inj.mp hl)
  rw [hp] at hd
  apply Subtype.ext
  have he := congrArg (fun z : DeningerPrimeSpace =>
    z + y.val deningerPrimeLogPivot • Finsupp.single deningerPrimeLogPivot 1) hd
  simpa only [sub_add_cancel] using he

/-- The complete family of hidden prime relations survives after pairing with the pivot tangent. -/
theorem deningerHiddenPrimeCyclic_linearIndependent :
    LinearIndependent ℂ (fun p : DeningerPrimeLogAway =>
      deningerHiddenPrimeCyclic (deningerPrimeLogKernelBasis p)) := by
  have hf := deningerHiddenPrimeCyclic_injective
  generalize hmap : deningerHiddenPrimeCyclic = f at hf ⊢
  generalize hbasis : deningerPrimeLogKernelBasis = b
  exact GaloisForLFunctions.HTGeometry.basisImage_linearIndependent
    (R := ℂ) (M := deningerPrimeLog.ker) (N := CyclicOne Quotient)
    (ι := DeningerPrimeLogAway) b f hf

theorem deningerHiddenPrimeCyclic_ne_zero (p : DeningerPrimeLogAway) :
    deningerHiddenPrimeCyclic (deningerPrimeLogKernelBasis p) ≠ 0 := by
  intro h
  apply deningerPrimeLogKernelBasis.ne_zero p
  apply deningerHiddenPrimeCyclic_injective
  rw [map_zero]
  exact h

/-- These actual source tensors cannot be killed by boundaries and signed rotations. -/
theorem deningerHiddenPrimePair_not_cyclicRelation (p : DeningerPrimeLogAway) :
    pair deningerPivotTangent (quotientMap (deningerHiddenPrimeTangent p)) ∉
      cyclicRelations := by
  intro h
  apply deningerHiddenPrimeCyclic_ne_zero p
  change (cyclicRelations (A := Quotient)).mkQ
    (pair deningerPivotTangent (quotientMap (deningerHiddenPrimeTangent p))) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr h

#print axioms deningerCyclicLogMoment_pair
#print axioms deningerCyclicLogMoment_basis
#print axioms deningerCyclicPrimeDetector_basis
#print axioms deningerHiddenPrimeCyclic_injective
#print axioms deningerHiddenPrimeCyclic_linearIndependent
#print axioms deningerHiddenPrimePair_not_cyclicRelation
end RHTower
