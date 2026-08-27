import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.Tactic

/-!
# Explicit spin lifts of rank-four signed Weyl generators

The negative Euclidean Clifford algebra supplies a faithful central sign and canonical Spin(4)
lifts of signed coordinate transpositions. Their inverse squares satisfy Milnor's sign-diagonal
relations; their exact braid, distant-commutation, reversal, and fourth-power laws provide the
finite double-cover infrastructure needed for Milnor's amalgam.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

namespace MilnorSpinWeyl

open CliffordAlgebra

/-- Negative Euclidean quadratic form on four real coordinates. -/
def spinQ : QuadraticForm ℝ (Fin 4 → ℝ) :=
  Matrix.toQuadraticForm' (-1 : Matrix (Fin 4) (Fin 4) ℝ)

/-- Standard coordinate vector in the rank-four spin model. -/
def basisVector (i : Fin 4) : Fin 4 → ℝ := Pi.single i 1

theorem spinQ_basisVector (i : Fin 4) : spinQ (basisVector i) = -1 := by
  fin_cases i <;>
    simp [spinQ, basisVector, Matrix.toQuadraticForm',
      LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply,
      Fin.sum_univ_four]

theorem spinQ_normalizedBasisSum (i j : Fin 4) (hij : i ≠ j) :
    spinQ ((1 / Real.sqrt 2) • (basisVector i + basisVector j)) = -1 := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hi : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← mul_inv_rev, hs2]
    norm_num
  fin_cases i <;> fin_cases j <;> simp_all [spinQ, basisVector, Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply,
    Fin.sum_univ_four] <;> norm_num

theorem spinQ_basisVector_ortho (i j : Fin 4) (hij : i ≠ j) : spinQ.IsOrtho (basisVector i) (basisVector j) := by
  rw [QuadraticMap.isOrtho_def]
  fin_cases i <;> fin_cases j <;> simp_all [spinQ, basisVector, Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply,
    Fin.sum_univ_four]

/-- Negative Euclidean rank-four Clifford algebra. -/
abbrev Clifford := CliffordAlgebra spinQ

/-- Clifford image of a standard coordinate vector. -/
def basisClifford (i : Fin 4) : Clifford := CliffordAlgebra.ι spinQ (basisVector i)

/-- Oriented coordinate bivector `eᵢeⱼ`. -/
def bivector (i j : Fin 4) : Clifford := basisClifford i * basisClifford j

@[simp] theorem basisClifford_sq (i : Fin 4) : basisClifford i * basisClifford i = -1 := by
  rw [basisClifford, CliffordAlgebra.ι_sq_scalar, spinQ_basisVector]
  simp

theorem basisClifford_anti (i j : Fin 4) (hij : i ≠ j) : basisClifford i * basisClifford j = -(basisClifford j * basisClifford i) := by
  exact CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (spinQ_basisVector_ortho i j hij)

theorem bivector_reverse (i j : Fin 4) (hij : i ≠ j) : bivector j i = -bivector i j := by
  simpa [bivector] using basisClifford_anti j i (Ne.symm hij)

@[simp] theorem bivector_sq (i j : Fin 4) (hij : i ≠ j) : bivector i j * bivector i j = -1 := by
  calc
    bivector i j * bivector i j = basisClifford i * (basisClifford j * basisClifford i) * basisClifford j := by simp [bivector, mul_assoc]
    _ = basisClifford i * (-(basisClifford i * basisClifford j)) * basisClifford j := by rw [basisClifford_anti j i (Ne.symm hij)]
    _ = -1 := by simp [← mul_assoc]

/-- Normalized sum of two coordinate vectors; it has negative unit norm off the diagonal. -/
def averageVector (i j : Fin 4) : Fin 4 → ℝ :=
  (1 / Real.sqrt 2) • (basisVector i + basisVector j)

theorem spinQ_averageVector (i j : Fin 4) (hij : i ≠ j) : spinQ (averageVector i j) = -1 :=
  spinQ_normalizedBasisSum i j hij

theorem cliffordIota_mem_pin_of_spinQ_eq_neg_one (v : Fin 4 → ℝ) (hv : spinQ v = -1) :
    CliffordAlgebra.ι spinQ v ∈ pinGroup spinQ := by
  have hq_unit : IsUnit (spinQ v) := by
    rw [hv]
    exact isUnit_neg_one
  have hi_unit : IsUnit (CliffordAlgebra.ι spinQ v) :=
    CliffordAlgebra.isUnit_ι_of_isUnit spinQ hq_unit
  let u : Cliffordˣ := hi_unit.unit
  have hu : (u : Clifford) = CliffordAlgebra.ι spinQ v := hi_unit.unit_spec
  have hu_lipschitz : u ∈ lipschitzGroup spinQ := by
    change u ∈ Subgroup.closure
      ((fun x : Cliffordˣ => (x : Clifford)) ⁻¹' Set.range (CliffordAlgebra.ι spinQ))
    apply Subgroup.subset_closure
    exact ⟨v, hu⟩
  apply pinGroup.mem_iff.mpr
  constructor
  · exact ⟨u, hu_lipschitz, hu⟩
  · constructor
    · rw [CliffordAlgebra.star_ι, neg_mul, CliffordAlgebra.ι_sq_scalar, hv]
      norm_num
    · rw [CliffordAlgebra.star_ι, mul_neg, CliffordAlgebra.ι_sq_scalar, hv]
      norm_num

/-- Clifford value of the canonical spin lift of the signed Weyl matrix `wᵢⱼ(1)`. -/
def weylLiftVal (i j : Fin 4) : Clifford :=
  CliffordAlgebra.ι spinQ (basisVector i) * CliffordAlgebra.ι spinQ (averageVector i j)

theorem weylLiftVal_mem_spin (i j : Fin 4) (hij : i ≠ j) :
    weylLiftVal i j ∈ spinGroup spinQ := by
  apply spinGroup.mem_iff.mpr
  constructor
  · exact (pinGroup spinQ).mul_mem
      (cliffordIota_mem_pin_of_spinQ_eq_neg_one (basisVector i) (spinQ_basisVector i))
      (cliffordIota_mem_pin_of_spinQ_eq_neg_one (averageVector i j) (spinQ_averageVector i j hij))
  · exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero spinQ (basisVector i) (averageVector i j)

/-- Canonical Spin(4) lift of a rank-four signed coordinate transposition. -/
def weylLift (i j : Fin 4) (hij : i ≠ j) : spinGroup spinQ :=
  ⟨weylLiftVal i j, weylLiftVal_mem_spin i j hij⟩

theorem weylLiftVal_formula (i j : Fin 4) :
    weylLiftVal i j = (1 / Real.sqrt 2) • (bivector i j - 1) := by
  simp only [weylLiftVal, averageVector, map_smul, map_add, basisClifford, bivector, mul_add,
    Algebra.mul_smul_comm, CliffordAlgebra.ι_sq_scalar, spinQ_basisVector]
  rw [map_neg, map_one]
  module

theorem invSqrtTwo_mul_self :
    (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = 1 / 2 := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [div_eq_mul_inv, one_mul, div_eq_mul_inv, one_mul, ← mul_inv_rev, hs2]

theorem weylLiftVal_sq (i j : Fin 4) (hij : i ≠ j) :
    weylLiftVal i j * weylLiftVal i j = -bivector i j := by
  rw [weylLiftVal_formula, smul_mul_smul, invSqrtTwo_mul_self]
  rw [show (1 / 2 : ℝ) • ((bivector i j - 1) * (bivector i j - 1)) = -bivector i j by
    calc
      (1 / 2 : ℝ) • ((bivector i j - 1) * (bivector i j - 1)) =
          (1 / 2 : ℝ) • (bivector i j * bivector i j - bivector i j - bivector i j + 1) := by
            congr 1
            noncomm_ring
      _ = -bivector i j := by rw [bivector_sq i j hij]; module]

theorem weylLiftVal_fourth (i j : Fin 4) (hij : i ≠ j) :
    weylLiftVal i j ^ 4 = -1 := by
  calc
    weylLiftVal i j ^ 4 = (weylLiftVal i j * weylLiftVal i j) *
        (weylLiftVal i j * weylLiftVal i j) := by noncomm_ring
    _ = (-bivector i j) * (-bivector i j) := by rw [weylLiftVal_sq i j hij]
    _ = -1 := by simpa using bivector_sq i j hij

theorem weylLiftVal_reverse_mul (i j : Fin 4) (hij : i ≠ j) :
    weylLiftVal j i * weylLiftVal i j = 1 := by
  rw [weylLiftVal_formula, weylLiftVal_formula, smul_mul_smul,
    invSqrtTwo_mul_self, bivector_reverse i j hij]
  rw [show (1 / 2 : ℝ) • ((-bivector i j - 1) * (bivector i j - 1)) = 1 by
    calc
      (1 / 2 : ℝ) • ((-bivector i j - 1) * (bivector i j - 1)) =
          (1 / 2 : ℝ) • (-(bivector i j * bivector i j) + 1) := by
            congr 1
            noncomm_ring
      _ = 1 := by rw [bivector_sq i j hij]; module]

theorem weylLift_reverse (i j : Fin 4) (hij : i ≠ j) :
    weylLift j i (Ne.symm hij) = (weylLift i j hij)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply Subtype.ext
  exact weylLiftVal_reverse_mul i j hij

theorem bivector_adjacent_anti (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    bivector i j * bivector j k = -(bivector j k * bivector i j) := by
  have hki := basisClifford_anti k i (Ne.symm hik)
  have hji := basisClifford_anti j i (Ne.symm hij)
  have hkj := basisClifford_anti k j (Ne.symm hjk)
  have hleft : bivector i j * bivector j k = -(basisClifford i * basisClifford k) := by
    calc
      bivector i j * bivector j k = basisClifford i * (basisClifford j * basisClifford j) * basisClifford k := by
        simp only [bivector]
        noncomm_ring
      _ = -(basisClifford i * basisClifford k) := by rw [basisClifford_sq]; simp
  have hright : bivector j k * bivector i j = basisClifford i * basisClifford k := by
    calc
      bivector j k * bivector i j = basisClifford j * (basisClifford k * basisClifford i) * basisClifford j := by simp [bivector, mul_assoc]
      _ = basisClifford j * (-(basisClifford i * basisClifford k)) * basisClifford j := by rw [hki]
      _ = -(basisClifford j * basisClifford i) * (basisClifford k * basisClifford j) := by noncomm_ring
      _ = -(-(basisClifford i * basisClifford j)) * (-(basisClifford j * basisClifford k)) := by rw [hji, hkj]
      _ = -(basisClifford i * basisClifford j * basisClifford j * basisClifford k) := by noncomm_ring
      _ = basisClifford i * basisClifford k := by
        rw [show basisClifford i * basisClifford j * basisClifford j * basisClifford k = basisClifford i * (basisClifford j * basisClifford j) * basisClifford k by
          noncomm_ring, basisClifford_sq]
        simp
  rw [hleft, hright]

theorem bivector_triangle (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    bivector k i * bivector j k = bivector j i := by
  have hki := basisClifford_anti k i (Ne.symm hik)
  have hkj := basisClifford_anti k j (Ne.symm hjk)
  calc
    bivector k i * bivector j k = basisClifford k * basisClifford i * basisClifford j * basisClifford k := by simp [bivector, mul_assoc]
    _ = -(basisClifford i * basisClifford k) * basisClifford j * basisClifford k := by rw [hki]
    _ = -(basisClifford i * (basisClifford k * basisClifford j)) * basisClifford k := by noncomm_ring
    _ = -(basisClifford i * (-(basisClifford j * basisClifford k))) * basisClifford k := by rw [hkj]
    _ = basisClifford i * basisClifford j * (basisClifford k * basisClifford k) := by noncomm_ring
    _ = bivector j i := by rw [basisClifford_sq, bivector_reverse i j hij]; simp [bivector]

theorem bivector_comm_of_disjoint (i j k l : Fin 4)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    bivector i j * bivector k l = bivector k l * bivector i j := by
  have hjk' := basisClifford_anti j k hjk
  have hik' := basisClifford_anti i k hik
  have hjl' := basisClifford_anti j l hjl
  have hil' := basisClifford_anti i l hil
  calc
    bivector i j * bivector k l = basisClifford i * (basisClifford j * basisClifford k) * basisClifford l := by simp [bivector, mul_assoc]
    _ = basisClifford i * (-(basisClifford k * basisClifford j)) * basisClifford l := by rw [hjk']
    _ = -(basisClifford i * basisClifford k) * basisClifford j * basisClifford l := by noncomm_ring
    _ = basisClifford k * basisClifford i * basisClifford j * basisClifford l := by rw [hik']; noncomm_ring
    _ = basisClifford k * basisClifford i * (basisClifford j * basisClifford l) := by simp [mul_assoc]
    _ = basisClifford k * basisClifford i * (-(basisClifford l * basisClifford j)) := by rw [hjl']
    _ = -(basisClifford k * (basisClifford i * basisClifford l)) * basisClifford j := by noncomm_ring
    _ = basisClifford k * basisClifford l * basisClifford i * basisClifford j := by rw [hil']; noncomm_ring
    _ = bivector k l * bivector i j := by simp [bivector, mul_assoc]

theorem weylLiftVal_comm_of_disjoint (i j k l : Fin 4)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    weylLiftVal i j * weylLiftVal k l = weylLiftVal k l * weylLiftVal i j := by
  rw [weylLiftVal_formula, weylLiftVal_formula, smul_mul_smul, smul_mul_smul]
  congr 1
  calc
    (bivector i j - 1) * (bivector k l - 1) =
        bivector i j * bivector k l - bivector i j - bivector k l + 1 := by noncomm_ring
    _ = bivector k l * bivector i j - bivector i j - bivector k l + 1 := by
      rw [bivector_comm_of_disjoint i j k l hik hil hjk hjl]
    _ = (bivector k l - 1) * (bivector i j - 1) := by noncomm_ring

theorem weylLift_comm_of_disjoint (i j k l : Fin 4)
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    weylLift i j hij * weylLift k l hkl = weylLift k l hkl * weylLift i j hij := by
  apply Subtype.ext
  exact weylLiftVal_comm_of_disjoint i j k l hik hil hjk hjl

theorem smul_triple (c : ℝ) (x y z : Clifford) :
    (c • x) * (c • y) * (c • z) = (c * c * c) • (x * y * z) := by
  rw [smul_mul_smul, smul_mul_smul]

theorem weylLiftVal_braid (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    weylLiftVal i j * weylLiftVal j k * weylLiftVal i j =
      weylLiftVal j k * weylLiftVal i j * weylLiftVal j k := by
  let A := bivector i j
  let B := bivector j k
  have hA2 : A * A = -1 := bivector_sq i j hij
  have hB2 : B * B = -1 := bivector_sq j k hjk
  have hAB : A * B = -(B * A) := bivector_adjacent_anti i j k hij hik hjk
  have hBA : B * A = -(A * B) := by
    simpa using congrArg Neg.neg hAB.symm
  have hABA : A * B * A = B := by
    calc
      A * B * A = A * (B * A) := by rw [mul_assoc]
      _ = A * (-(A * B)) := by rw [hBA]
      _ = -(A * A) * B := by noncomm_ring
      _ = B := by rw [hA2]; simp
  have hBAB : B * A * B = A := by
    calc
      B * A * B = B * (A * B) := by rw [mul_assoc]
      _ = B * (-(B * A)) := by rw [hAB]
      _ = -(B * B) * A := by noncomm_ring
      _ = A := by rw [hB2]; simp
  have hleft : (A - 1) * (B - 1) * (A - 1) = 2 • (A + B) := by
    calc
      (A - 1) * (B - 1) * (A - 1) =
          A * B * A - A * B - A * A + A - B * A + B + A - 1 := by
            noncomm_ring
      _ = 2 • (A + B) := by rw [hABA, hA2, hBA]; module
  have hright : (B - 1) * (A - 1) * (B - 1) = 2 • (A + B) := by
    calc
      (B - 1) * (A - 1) * (B - 1) =
          B * A * B - B * A - B * B + B - A * B + A + B - 1 := by
            noncomm_ring
      _ = 2 • (A + B) := by rw [hBAB, hB2, hAB]; module
  rw [weylLiftVal_formula, weylLiftVal_formula, smul_triple, smul_triple]
  change _ • ((A - 1) * (B - 1) * (A - 1)) =
    _ • ((B - 1) * (A - 1) * (B - 1))
  rw [hleft, hright]

/-- Exact type-A braid relation for the spin Weyl lifts. -/
theorem weylLift_braid (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    weylLift i j hij * weylLift j k hjk * weylLift i j hij =
      weylLift j k hjk * weylLift i j hij * weylLift j k hjk := by
  apply Subtype.ext
  exact weylLiftVal_braid i j k hij hik hjk

/-- Nontrivial scalar `-1` in Spin(4), exhibited as a Weyl lift's fourth power. -/
def centralNegOne : spinGroup spinQ := weylLift 0 1 (by decide) ^ 4

@[simp] theorem centralNegOne_val : (centralNegOne : Clifford) = -1 := by
  simpa [centralNegOne, weylLift] using weylLiftVal_fourth 0 1 (by decide)

theorem clifford_neg_one_ne_one : (-1 : Clifford) ≠ 1 := by
  intro h
  have hr : (-1 : ℝ) = 1 := FaithfulSMul.algebraMap_injective ℝ Clifford (by simpa using h)
  norm_num at hr

theorem centralNegOne_ne_one : centralNegOne ≠ 1 := by
  intro h
  apply clifford_neg_one_ne_one
  simpa using congrArg (fun x : spinGroup spinQ => (x : Clifford)) h

/-- Every oriented spin Weyl lift has fourth power equal to the same central sign. -/
theorem weylLift_fourth (i j : Fin 4) (hij : i ≠ j) : weylLift i j hij ^ 4 = centralNegOne := by
  apply Subtype.ext
  rw [centralNegOne_val]
  simpa [weylLift] using weylLiftVal_fourth i j hij

/-- The inverse square lifting `hᵢⱼ(-1)` has Clifford value `eᵢeⱼ`. -/
theorem weylLift_inv_sq_val (i j : Fin 4) (hij : i ≠ j) :
    (((weylLift i j hij)⁻¹ ^ 2 : spinGroup spinQ) : Clifford) = bivector i j := by
  rw [← weylLift_reverse i j hij]
  simp only [pow_two]
  change weylLiftVal j i * weylLiftVal j i = bivector i j
  rw [weylLiftVal_sq j i (Ne.symm hij), bivector_reverse i j hij]
  simp

end MilnorSpinWeyl

end GaloisForLFunctions.HTGeometry

end
