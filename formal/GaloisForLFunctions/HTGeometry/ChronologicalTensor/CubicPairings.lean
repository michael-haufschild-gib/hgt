import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Activation
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicObservation

/-!
# Five genuine cubic pairing coordinates

Explicit endpoint bijections realize the five noncrossing cubic generators.
Their monotone capacity is exactly the supremum of the cubic readout over the
physical sparse section. This identifies the subsequent norm calculation with
actual pairing capacity, rather than a separately postulated polynomial norm.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Finset Set

def cubicBEndpointPermutation : Equiv.Perm (Fin 6) where
  toFun := ![0,2,3,1,5,4]
  invFun := ![0,3,1,2,5,4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def cubicCEndpointPermutation : Equiv.Perm (Fin 6) where
  toFun := ![0,1,4,3,2,5]
  invFun := ![0,1,4,3,2,5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def cubicDEndpointPermutation : Equiv.Perm (Fin 6) where
  toFun := ![0,1,3,5,2,4]
  invFun := ![0,1,4,2,5,3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def cubicStandardEnumerations : Fin 5 → ((Fin 3 ⊕ Fin 3) ≃ Fin 6) :=
  ![separatedEndpointEnumeration,finSumFinEquiv.trans cubicBEndpointPermutation,
    finSumFinEquiv.trans cubicCEndpointPermutation,
    finSumFinEquiv.trans cubicDEndpointPermutation,rainbowEndpointEnumeration]

theorem cubicStandard_windows : enumeratedFamilyWindows cubicStandardEnumerations =
    ![![{0},{2},{4}],![{0},{2,3,4},{3}],![{0,1,2},{1},{4}],
      ![{0,1,2,3,4},{1},{3}],![{0,1,2,3,4},{1,2,3},{2}]] := by
  funext j i
  fin_cases j <;> fin_cases i <;> ext q <;> fin_cases q <;>
    simp [enumeratedFamilyWindows,enumeratedPairingWindows,cubicStandardEnumerations,
      separatedEndpointEnumeration,separatedEndpointPermutation,rainbowEndpointEnumeration,
      cubicBEndpointPermutation,cubicCEndpointPermutation,cubicDEndpointPermutation,
      finSumFinEquiv,Finset.mem_Ico]

theorem cubicStandard_coefficients (c : Fin 5 → ℝ) :
    enumeratedFamilyCoefficients cubicStandardEnumerations c=c := by
  ext j
  fin_cases j <;>
    simp [enumeratedFamilyCoefficients,enumeratedPairingSign,endpointOrderSign,cubicStandardEnumerations,
      separatedEndpointEnumeration,separatedEndpointPermutation,rainbowEndpointEnumeration,
      cubicBEndpointPermutation,cubicCEndpointPermutation,cubicDEndpointPermutation,
      finSumFinEquiv,Fin.prod_univ_three]

theorem cubicStandard_value (A B C D E : ℝ) (g : Fin 6 → ℝ) :
    familyValue (enumeratedFamilyWindows cubicStandardEnumerations)
      (enumeratedFamilyCoefficients cubicStandardEnumerations ![A,B,C,D,E]) g =
      cubicReadout A B C D E (fun q : Fin 5 => g q.castSucc) := by
  rw [cubicStandard_windows,cubicStandard_coefficients]
  simp [familyValue,diagramValue,windowValue,Fin.sum_univ_five,Fin.prod_univ_three,cubicReadout]
  ring

theorem cubicStandard_extend_value (A B C D E : ℝ) (g : Fin 5 → ℝ) :
    familyValue (enumeratedFamilyWindows cubicStandardEnumerations)
      (enumeratedFamilyCoefficients cubicStandardEnumerations ![A,B,C,D,E]) (cubicProbeExtend g) =
      cubicReadout A B C D E g := by
  rw [cubicStandard_value]
  rfl

def cubicMonotoneCapacity (A B C D E : ℝ) : ℝ :=
  monotoneCapacity (enumeratedFamilyWindows cubicStandardEnumerations)
    (enumeratedFamilyCoefficients cubicStandardEnumerations ![A,B,C,D,E])

theorem cubicMonotoneCapacity_physical (A B C D E : ℝ) :
    cubicMonotoneCapacity A B C D E=
      sSup ((fun g => |cubicReadout A B C D E g|) '' cubicProbeSection) := by
  unfold cubicMonotoneCapacity
  rw [monotoneCapacity_physical_unit,physicalUnitValues_image,physicalProbeSection_six,
    ← Set.image_comp]
  congr 1
  apply Set.image_congr
  intro g _
  exact congrArg abs (cubicStandard_extend_value A B C D E g)


theorem cubicReadoutValues_physical (A B C D E : ℝ) :
    (fun g => |cubicReadout A B C D E g|) '' cubicProbeSection =
      physicalUnitValues cubicStandardEnumerations ![A,B,C,D,E] := by
  rw [physicalUnitValues_image,physicalProbeSection_six, ← Set.image_comp]
  apply Set.image_congr
  intro g _
  exact (congrArg abs (cubicStandard_extend_value A B C D E g)).symm

theorem cubicReadoutValues_bddAbove (A B C D E : ℝ) :
    BddAbove ((fun g => |cubicReadout A B C D E g|) '' cubicProbeSection) := by
  rw [cubicReadoutValues_physical]
  exact physicalUnitValues_bddAbove _ _

theorem cubicReadoutValues_nonempty (A B C D E : ℝ) :
    ((fun g => |cubicReadout A B C D E g|) '' cubicProbeSection).Nonempty := by
  rw [cubicReadoutValues_physical]
  exact physicalUnitValues_nonempty _ _

theorem cubicMonotoneCapacity_bounds (A B C D E : ℝ) :
    Set.MapsTo (fun g => |cubicReadout A B C D E g|) cubicProbeSection
      (Set.Iic (cubicMonotoneCapacity A B C D E)) := by
  intro g hg
  change |cubicReadout A B C D E g| ≤ cubicMonotoneCapacity A B C D E
  rw [cubicMonotoneCapacity_physical]
  exact le_csSup (cubicReadoutValues_bddAbove A B C D E) ⟨g,hg,rfl⟩

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
