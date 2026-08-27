import GaloisForLFunctions.HTGeometry.MilnorKTwoSpinWeylPermutation

noncomputable section


namespace GaloisForLFunctions.HTGeometry
namespace MilnorSpinWeyl

/-- Permutation quotient of the rotor-generated Spin Weyl group. -/
noncomputable def spinWeylPermutationHom :
    spinWeylSubgroup →* Equiv.Perm (Fin 4) :=
  signedMonomialPermutationHom.comp spinWeylMatrixRepresentation

/-- Spin common subgroup candidate: kernel of the permutation quotient. -/
def spinDiagonalWeylSubgroup : Subgroup spinWeylSubgroup :=
  spinWeylPermutationHom.ker

def weylLiftSpinWeyl (i j : Fin 4) (hij : i ≠ j) : spinWeylSubgroup :=
  ⟨weylLift i j hij, weylLift_mem_spinWeylSubgroup i j hij⟩

theorem spinWeylPermutationHom_weylLift (i j : Fin 4) (hij : i ≠ j) :
    spinWeylPermutationHom (weylLiftSpinWeyl i j hij) = Equiv.swap i j := by
  change signedMonomialPermutationHom
    (spinWeylMatrixRepresentation (weylLiftSpinWeyl i j hij)) = _
  rw [signedMonomialPermutationHom_apply]
  exact (signedMonomialData_eq
    (A := spinWeylMatrixRepresentation (weylLiftSpinWeyl i j hij))
    (σ := Equiv.swap i j)
    (c := steinbergWeylRootScale (i := i) (j := j) (1 : ℝˣ))
    (spinWeylMatrixGenerator_signedMonomial i j hij)).1

theorem spinWeylMatrixRepresentation_centralNegOne :
    spinWeylMatrixRepresentation centralNegOneSpinWeyl = 1 :=
  (spinWeylMatrixRepresentation_eq_one_iff centralNegOneSpinWeyl).2
    (Or.inr rfl)

theorem spinWeylPermutationHom_centralNegOne :
    spinWeylPermutationHom centralNegOneSpinWeyl = 1 := by
  rw [spinWeylPermutationHom, MonoidHom.comp_apply,
    spinWeylMatrixRepresentation_centralNegOne, map_one]

def h0GeneratorSpinWeyl (i : Fin 3) : spinWeylSubgroup :=
  ⟨h0Generator i, h0Generator_mem_spinWeylSubgroup i⟩

theorem h0GeneratorSpinWeyl_eq (i : Fin 3) :
    h0GeneratorSpinWeyl i =
      (weylLiftSpinWeyl i.castSucc 3 (Fin.castSucc_ne_last i))⁻¹ ^ 2 := by
  apply Subtype.ext
  rfl

theorem spinWeylPermutationHom_h0Generator (i : Fin 3) :
    spinWeylPermutationHom (h0GeneratorSpinWeyl i) = 1 := by
  rw [h0GeneratorSpinWeyl_eq, map_pow, map_inv,
    spinWeylPermutationHom_weylLift]
  simp [pow_two]

theorem spinWeylMatrixRepresentation_h0Generator (i : Fin 3) :
    spinWeylMatrixRepresentation (h0GeneratorSpinWeyl i) =
      generatedPairFlip i := by
  let r := weylLiftSpinWeyl i.castSucc 3 (Fin.castSucc_ne_last i)
  let M := spinWeylMatrixRepresentation r
  have hr4 : r ^ 4 = centralNegOneSpinWeyl := by
    apply Subtype.ext
    exact weylLift_fourth i.castSucc 3 (Fin.castSucc_ne_last i)
  have hM4 : M ^ 4 = 1 := by
    rw [← map_pow, hr4, spinWeylMatrixRepresentation_centralNegOne]
  have hM2 : M⁻¹ ^ 2 = M ^ 2 := by
    have hsquare : M ^ 2 * M ^ 2 = 1 := by
      rw [← pow_add]
      norm_num
      exact hM4
    calc
      M⁻¹ ^ 2 = (M ^ 2)⁻¹ := by group
      _ = M ^ 2 := inv_eq_of_mul_eq_one_right hsquare
  rw [h0GeneratorSpinWeyl_eq, map_pow, map_inv]
  change M⁻¹ ^ 2 = generatedPairFlip i
  rw [hM2]
  apply Subtype.ext
  rfl

private theorem zmodTwo_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem map_bitElement_eq_one {G K : Type*} [Group G] [Group K]
    (f : G →* K) (x : G) (hx : f x = 1) (a : ZMod 2) :
    f (bitElement a x) = 1 := by
  rcases zmodTwo_eq_zero_or_one a with rfl | rfl <;>
    simp [bitElement, hx]

private theorem coe_bitElement {G : Type*} [Group G]
    (H : Subgroup G) (a : ZMod 2) (x : H) :
    ((bitElement a x : H) : G) = bitElement a (x : G) := by
  rcases zmodTwo_eq_zero_or_one a with rfl | rfl <;>
    simp [bitElement]

theorem coordinatesSpinWeylHom_eq
    (c : MilnorH0Coordinates.Coordinates) :
    coordinatesSpinWeylHom c =
      bitElement c.central centralNegOneSpinWeyl *
        bitElement (c.diag 0) (h0GeneratorSpinWeyl 0) *
        bitElement (c.diag 1) (h0GeneratorSpinWeyl 1) *
        bitElement (c.diag 2) (h0GeneratorSpinWeyl 2) := by
  apply Subtype.ext
  change coordinatesSpin c = _
  simp only [coordinatesSpin, Subgroup.coe_mul, coe_bitElement,
    centralNegOneSpinWeyl, h0GeneratorSpinWeyl]

theorem spinWeylPermutationHom_coordinates
    (c : MilnorH0Coordinates.Coordinates) :
    spinWeylPermutationHom (coordinatesSpinWeylHom c) = 1 := by
  rw [coordinatesSpinWeylHom_eq, map_mul, map_mul, map_mul,
    map_bitElement_eq_one spinWeylPermutationHom centralNegOneSpinWeyl
      spinWeylPermutationHom_centralNegOne,
    map_bitElement_eq_one spinWeylPermutationHom (h0GeneratorSpinWeyl 0)
      (spinWeylPermutationHom_h0Generator 0),
    map_bitElement_eq_one spinWeylPermutationHom (h0GeneratorSpinWeyl 1)
      (spinWeylPermutationHom_h0Generator 1),
    map_bitElement_eq_one spinWeylPermutationHom (h0GeneratorSpinWeyl 2)
      (spinWeylPermutationHom_h0Generator 2)]
  simp

theorem spinWeylMatrixRepresentation_coordinatesDiagonal
    (a : Fin 3 → ZMod 2) :
    spinWeylMatrixRepresentation
        (coordinatesSpinWeylHom ⟨a, 0⟩) =
      generatedDiagonalSignLift
        (MilnorDiagonalExtension.coordinatesDiagonal (F := ℝ) a).1 := by
  rw [coordinatesSpinWeylHom_eq, map_mul, map_mul, map_mul]
  simp only [bitElement_zero, map_one, one_mul]
  rw [show spinWeylMatrixRepresentation
      (bitElement (a 0) (h0GeneratorSpinWeyl 0)) =
        bitElement (a 0) (generatedPairFlip 0) by
      rcases zmodTwo_eq_zero_or_one (a 0) with h | h <;>
        simp [h, spinWeylMatrixRepresentation_h0Generator],
    show spinWeylMatrixRepresentation
      (bitElement (a 1) (h0GeneratorSpinWeyl 1)) =
        bitElement (a 1) (generatedPairFlip 1) by
      rcases zmodTwo_eq_zero_or_one (a 1) with h | h <;>
        simp [h, spinWeylMatrixRepresentation_h0Generator],
    show spinWeylMatrixRepresentation
      (bitElement (a 2) (h0GeneratorSpinWeyl 2)) =
        bitElement (a 2) (generatedPairFlip 2) by
      rcases zmodTwo_eq_zero_or_one (a 2) with h | h <;>
        simp [h, spinWeylMatrixRepresentation_h0Generator]]
  rcases zmodTwo_eq_zero_or_one (a 0) with h0 | h0 <;>
    rcases zmodTwo_eq_zero_or_one (a 1) with h1 | h1 <;>
    rcases zmodTwo_eq_zero_or_one (a 2) with h2 | h2 <;>
    simp [h0, h1, h2, bitElement, generatedDiagonalSignLift,
      MilnorDiagonalExtension.coordinatesDiagonal,
      MilnorDiagonalExtension.signUnit]

theorem coordinatesSpinWeylHom_range_eq_spinDiagonal :
    MonoidHom.range coordinatesSpinWeylHom = spinDiagonalWeylSubgroup := by
  apply le_antisymm
  · rintro s ⟨c, rfl⟩
    exact spinWeylPermutationHom_coordinates c
  · intro s hs
    have hperm : signedMonomialPermutationHom
        (spinWeylMatrixRepresentation s) = 1 := by
      exact hs
    have hdiagonal : spinWeylMatrixRepresentation s ∈
        diagonalSignedMonomialSubgroup := hperm
    obtain ⟨c, hc, hsc⟩ :=
      (mem_diagonalSignedMonomialSubgroup_iff
        (spinWeylMatrixRepresentation s)).1 hdiagonal
    have hdet : Matrix.det (signedMonomialMatrix 1 c) = 1 := by
      rw [← hsc]
      exact generatedSignedMonomialSubgroup_det_one
        (spinWeylMatrixRepresentation s)
    have hcprod : ∏ p, c p = 1 := by
      apply Units.ext
      simpa [det_signedMonomialMatrix_one] using hdet
    let u : detOneDiagonalUnits ℝ 4 := ⟨c, hcprod⟩
    let a : Fin 3 → ZMod 2 := fun i =>
      MilnorDiagonalExtension.signBit (c i.castSucc)
    have hcoordinates :
        MilnorDiagonalExtension.coordinatesDiagonal (F := ℝ) a = u := by
      apply MilnorDiagonalExtension.detOneDiagonalUnits_fin4_ext
      · exact MilnorDiagonalExtension.signUnit_signBit (hc 0)
      · exact MilnorDiagonalExtension.signUnit_signBit (hc 1)
      · exact MilnorDiagonalExtension.signUnit_signBit (hc 2)
    let t : spinWeylSubgroup := coordinatesSpinWeylHom ⟨a, 0⟩
    have htMatrix : spinWeylMatrixRepresentation t =
        spinWeylMatrixRepresentation s := by
      rw [show spinWeylMatrixRepresentation t = generatedDiagonalSignLift c by
        rw [spinWeylMatrixRepresentation_coordinatesDiagonal, hcoordinates]]
      apply Subtype.ext
      apply Units.ext
      rw [generatedDiagonalSignLift_val c hc hdet]
      exact hsc.symm
    have hkernel : spinWeylMatrixRepresentation (s * t⁻¹) = 1 := by
      rw [map_mul, map_inv, htMatrix]
      simp
    have htRange : t ∈ MonoidHom.range coordinatesSpinWeylHom :=
      ⟨⟨a, 0⟩, rfl⟩
    have hzRange : centralNegOneSpinWeyl ∈
        MonoidHom.range coordinatesSpinWeylHom := by
      refine ⟨⟨0, 1⟩, ?_⟩
      rw [coordinatesSpinWeylHom_eq]
      simp
    rcases (spinWeylMatrixRepresentation_eq_one_iff (s * t⁻¹)).1 hkernel with
      hone | hcentral
    · have hst : s = t := by
        calc
          s = (s * t⁻¹) * t := by group
          _ = t := by rw [hone, one_mul]
      rw [hst]
      exact htRange
    · have hst : s = centralNegOneSpinWeyl * t := by
        calc
          s = (s * t⁻¹) * t := by group
          _ = centralNegOneSpinWeyl * t := by rw [hcentral]
      rw [hst]
      exact (MonoidHom.range coordinatesSpinWeylHom).mul_mem hzRange htRange

end MilnorSpinWeyl
end GaloisForLFunctions.HTGeometry

end

noncomputable section

namespace GaloisForLFunctions.HTGeometry
namespace MilnorDiagonalExtension

open MilnorSpinWeyl

variable {F : Type*} [Field F]

theorem fin4MilnorH0ToSpinWeyl_range_eq_spinDiagonal
    (he : fin4MinusOneSymbol F ≠ 0) :
    MonoidHom.range (fin4MilnorH0ToSpinWeyl he) =
      spinDiagonalWeylSubgroup := by
  apply le_antisymm
  · rintro s ⟨x, rfl⟩
    change spinWeylPermutationHom
      (coordinatesSpinWeylHom (fin4MilnorH0ToCoordinates he x)) = 1
    exact spinWeylPermutationHom_coordinates
      (fin4MilnorH0ToCoordinates he x)
  · intro s hs
    have hsRange : s ∈ MonoidHom.range coordinatesSpinWeylHom := by
      rw [coordinatesSpinWeylHom_range_eq_spinDiagonal]
      exact hs
    obtain ⟨c, hc⟩ := hsRange
    obtain ⟨x, hx⟩ := fin4MilnorH0ToCoordinates_surjective he c
    refine ⟨x, ?_⟩
    rw [fin4MilnorH0ToSpinWeyl, MonoidHom.comp_apply, hx, hc]

end MilnorDiagonalExtension
end GaloisForLFunctions.HTGeometry

end

