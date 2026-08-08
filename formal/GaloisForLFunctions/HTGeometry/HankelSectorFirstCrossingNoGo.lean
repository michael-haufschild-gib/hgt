import GaloisForLFunctions.HTGeometry.HankelBoundaryExtension

/-!
# Sector and first-crossing data do not force a Hankel PSD extension

This file gives an exact finite counterexample to a tempting local closure argument for the
mass-shifted spectral-face route.  One conjugate pair lies in the sharp safe sector used by the
route, one additional atom is positive real, all weights are positive, and the moment sequence
sits on a singular positive-semidefinite `2 × 2` Hankel face.  Its exact mass-transport tangent
points into the positive side of that first minor.  Nevertheless the first omitted coupling is
negative and the `3 × 3` Hankel extension is not positive semidefinite.

Thus sector control, positive real parts, positive atomic weights, the moment transport law, and
rightward first-crossing geometry cannot by themselves determine the boundary coupling.  Any
successful argument needs genuinely collective arithmetic information about the Xi source.
-/

open Complex Matrix
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Nonreal atom in the safe sector. -/
def sectorCrossingAtom : ℂ := 1 + (1 / 10 : ℝ) * I

/-- Auxiliary positive real atom. -/
def sectorCrossingRealAtom : ℝ := 1 / 2

/-- Exact positive weight making the first Hankel minor singular. -/
def sectorCrossingRealWeight : ℝ := 101 / 575

/-- Moments of one unit-weight conjugate pair and one positive real atom. -/
def sectorCrossingMoment (k : ℕ) : ℝ :=
  2 * (sectorCrossingAtom ^ (k + 1)).re +
    sectorCrossingRealWeight * sectorCrossingRealAtom ^ (k + 1)

/-- Exact first jet of the mass Möbius transport on moments:
`mₖ' = -(k+1)mₖ₊₁`. -/
def sectorCrossingMomentTangentFlow (t : ℝ) (k : ℕ) : ℝ :=
  sectorCrossingMoment k -
    t * ((k + 1 : ℕ) : ℝ) * sectorCrossingMoment (k + 1)

theorem hasDerivAt_sectorCrossingMomentTangentFlow (k : ℕ) :
    HasDerivAt (fun t => sectorCrossingMomentTangentFlow t k)
      (-((k + 1 : ℕ) : ℝ) * sectorCrossingMoment (k + 1)) 0 := by
  have hconst : HasDerivAt (fun _ : ℝ => sectorCrossingMoment k) 0 0 :=
    hasDerivAt_const 0 _
  have hlinear := (hasDerivAt_id (x := (0 : ℝ))).mul_const
    (((k + 1 : ℕ) : ℝ) * sectorCrossingMoment (k + 1))
  convert! hconst.sub hlinear using 1
  · funext t
    simp only [sectorCrossingMomentTangentFlow, Pi.sub_apply, id_eq]
    push_cast
    ring
  · ring

theorem sectorCrossingMomentTangentFlow_zero (k : ℕ) :
    sectorCrossingMomentTangentFlow 0 k = sectorCrossingMoment k := by
  simp [sectorCrossingMomentTangentFlow]

/-- First Hankel minor along the exact mass-transport tangent. -/
def sectorCrossingMinorFlow (t : ℝ) : ℝ :=
  sectorCrossingMomentTangentFlow t 0 * sectorCrossingMomentTangentFlow t 2 -
    sectorCrossingMomentTangentFlow t 1 ^ 2

theorem hasDerivAt_sectorCrossingMinorFlow :
    HasDerivAt sectorCrossingMinorFlow
      (3 * (sectorCrossingMoment 1 * sectorCrossingMoment 2 -
        sectorCrossingMoment 0 * sectorCrossingMoment 3)) 0 := by
  have h0 := hasDerivAt_sectorCrossingMomentTangentFlow 0
  have h1 := hasDerivAt_sectorCrossingMomentTangentFlow 1
  have h2 := hasDerivAt_sectorCrossingMomentTangentFlow 2
  convert! (h0.mul h2).sub (h1.pow 2) using 1
  simp only [sectorCrossingMomentTangentFlow_zero]
  norm_num
  ring

theorem sectorCrossingMinorFlow_deriv_pos :
    0 < deriv sectorCrossingMinorFlow 0 := by
  rw [hasDerivAt_sectorCrossingMinorFlow.deriv]
  norm_num [sectorCrossingMoment, sectorCrossingAtom,
    sectorCrossingRealWeight, sectorCrossingRealAtom, pow_two, pow_succ]

theorem sectorCrossingMinorFlow_zero : sectorCrossingMinorFlow 0 = 0 := by
  norm_num [sectorCrossingMinorFlow, sectorCrossingMomentTangentFlow,
    sectorCrossingMoment, sectorCrossingAtom, sectorCrossingRealWeight,
    sectorCrossingRealAtom, pow_two, pow_succ]

/-- The singular first minor becomes strictly positive immediately to the right. -/
theorem eventually_sectorCrossingMinorFlow_pos_right :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < sectorCrossingMinorFlow t := by
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos
    sectorCrossingMinorFlow_deriv_pos sectorCrossingMinorFlow_zero
  filter_upwards [hsign.filter_mono inf_le_left, self_mem_nhdsWithin] with t ht hpos
  rw [← sign_eq_one_iff, ht, sign_eq_one_iff]
  simpa using hpos

theorem sectorCrossingAtom_re : sectorCrossingAtom.re = 1 := by
  norm_num [sectorCrossingAtom]

theorem sectorCrossingAtom_in_safeSector :
    sectorCrossingAtom.im ^ 2 ≤ (1 / 84 : ℝ) * sectorCrossingAtom.re ^ 2 := by
  norm_num [sectorCrossingAtom]

theorem sectorCrossingRealAtom_pos : 0 < sectorCrossingRealAtom := by
  norm_num [sectorCrossingRealAtom]

theorem sectorCrossingRealWeight_pos : 0 < sectorCrossingRealWeight := by
  norm_num [sectorCrossingRealWeight]

theorem sectorCrossingMoment_zero_value : sectorCrossingMoment 0 = 2401 / 1150 := by
  norm_num [sectorCrossingMoment, sectorCrossingAtom,
    sectorCrossingRealWeight, sectorCrossingRealAtom, pow_two, pow_succ]

theorem sectorCrossingMoment_one_value : sectorCrossingMoment 1 = 931 / 460 := by
  norm_num [sectorCrossingMoment, sectorCrossingAtom,
    sectorCrossingRealWeight, sectorCrossingRealAtom, pow_two, pow_succ]

theorem sectorCrossingMoment_two_value : sectorCrossingMoment 2 = 361 / 184 := by
  norm_num [sectorCrossingMoment, sectorCrossingAtom,
    sectorCrossingRealWeight, sectorCrossingRealAtom, pow_two, pow_succ]

theorem sectorCrossingFirstMinor_eq_zero :
    sectorCrossingMoment 0 * sectorCrossingMoment 2 -
      sectorCrossingMoment 1 ^ 2 = 0 := by
  norm_num [sectorCrossingMoment, sectorCrossingAtom,
    sectorCrossingRealWeight, sectorCrossingRealAtom, pow_two, pow_succ]

theorem sectorCrossingBorderMinor_neg :
    sectorCrossingMoment 0 * sectorCrossingMoment 3 -
      sectorCrossingMoment 1 * sectorCrossingMoment 2 < 0 := by
  norm_num [sectorCrossingMoment, sectorCrossingAtom,
    sectorCrossingRealWeight, sectorCrossingRealAtom, pow_two, pow_succ]

/-- Exact null vector of the singular `2 × 2` Hankel face. -/
def sectorCrossingNullVector : Fin 2 → ℝ :=
  ![-sectorCrossingMoment 1, sectorCrossingMoment 0]

theorem finiteHankelMatrix_sectorCrossing_mulVec_null :
    finiteHankelMatrix sectorCrossingMoment 2 *ᵥ sectorCrossingNullVector = 0 := by
  funext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, finiteHankelMatrix,
      sectorCrossingNullVector, sectorCrossingMoment, sectorCrossingAtom,
      sectorCrossingRealWeight, sectorCrossingRealAtom, pow_two, pow_succ]

theorem finiteHankelMatrix_sectorCrossing_two_posSemidef :
    (finiteHankelMatrix sectorCrossingMoment 2).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (finiteHankelMatrix_isHermitian sectorCrossingMoment 2)
  intro c
  simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  norm_num [finiteHankelMatrix, sectorCrossingMoment, sectorCrossingAtom,
    sectorCrossingRealWeight, sectorCrossingRealAtom, pow_two, pow_succ]
  have hsq : 0 ≤ (c 0 + (95 / 98 : ℝ) * c 1) ^ 2 := sq_nonneg _
  nlinarith

theorem sectorCrossingFirstOmittedCoupling_neg :
    hankelFirstOmittedCoupling sectorCrossingMoment 2 sectorCrossingNullVector < 0 := by
  norm_num [hankelFirstOmittedCoupling, sectorCrossingNullVector,
    sectorCrossingMoment, sectorCrossingAtom, sectorCrossingRealWeight,
    sectorCrossingRealAtom, pow_two, pow_succ]

/-- Despite all preceding local data, the next Hankel block is already indefinite. -/
theorem finiteHankelMatrix_sectorCrossing_three_not_posSemidef :
    ¬ (finiteHankelMatrix sectorCrossingMoment 3).PosSemidef := by
  apply finiteHankelMatrix_succ_not_posSemidef_of_kernel_of_coupling_ne_zero
    sectorCrossingMoment 2 sectorCrossingNullVector
  · exact finiteHankelMatrix_sectorCrossing_mulVec_null
  · exact ne_of_lt sectorCrossingFirstOmittedCoupling_neg

end

end GaloisForLFunctions.HTGeometry
