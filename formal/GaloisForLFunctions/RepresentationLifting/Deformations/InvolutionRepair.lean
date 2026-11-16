import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.NoncommRing

/-!
# Repairing involutions across the characteristic-five thickening

The correction `u ↦ (3u-u³)/2` squares the involution error. Over `ℤ/25ℤ`,
`13` is a half, so the correction lifts every matrix involution over `𝔽₅`
to an involution over `ℤ/25ℤ`, in every finite size.
Two lifts with the same reduction are conjugate by a change of basis that
reduces to the identity.

This implements the infinitesimal involution repair in the proof of
Proposition 6.3 of Burek–Chmiel–Cynk–Oczko, https://arxiv.org/abs/2611.15943.
It isolates the symmetry lifting step from the geometric branch obstruction.
-/

namespace GaloisForLFunctions.RepresentationLifting.InvolutionRepair

/-- The numerator of the Newton correction has a universal error factorization. -/
theorem numerator_error {R : Type*} [Ring R] (u : R) :
    (3 * u - u ^ 3) ^ 2 - 4 = (u ^ 2 - 1) ^ 2 * (u ^ 2 - 4) := by
  noncomm_ring
  norm_num

/-- Integer formula for division by two in characteristic twenty-five. -/
def repair {R : Type*} [Ring R] (u : R) : R := 13 * (3 * u - u ^ 3)

/-- No commutativity or nilpotence is needed for the exact error identity. -/
theorem repair_error {R : Type*} [Ring R] (u : R) :
    (repair u) ^ 2 - 1 = 169 * ((u ^ 2 - 1) ^ 2 * (u ^ 2 - 4)) + 675 := by
  unfold repair
  noncomm_ring
  norm_num

/-- Reduction along the square-zero characteristic-five thickening. -/
def reduction : ZMod 25 →+* ZMod 5 := ZMod.castHom (by norm_num) (ZMod 5)

private theorem reduction_eq_val (a : ZMod 25) : reduction a = (a.val : ZMod 5) :=
  ZMod.cast_eq_val a

/-- The kernel of `ℤ/25ℤ → 𝔽₅` has zero multiplication. -/
theorem reduction_kernel_mul (a b : ZMod 25)
    (ha : reduction a = 0) (hb : reduction b = 0) : a * b = 0 := by
  rw [reduction_eq_val] at ha hb
  obtain ⟨r, hr⟩ := (CharP.cast_eq_zero_iff (ZMod 5) 5 a.val).mp ha
  obtain ⟨s, hs⟩ := (CharP.cast_eq_zero_iff (ZMod 5) 5 b.val).mp hb
  have har : a = 5 * (r : ZMod 25) := by
    rw [← ZMod.natCast_zmod_val a, hr, Nat.cast_mul, Nat.cast_ofNat]
  have hbs : b = 5 * (s : ZMod 25) := by
    rw [← ZMod.natCast_zmod_val b, hs, Nat.cast_mul, Nat.cast_ofNat]
  rw [har, hbs]
  calc
    (5 * (r : ZMod 25)) * (5 * (s : ZMod 25)) = 25 * ((r : ZMod 25) * s) := by ring
    _ = 0 := by rw [show (25 : ZMod 25) = 0 from ZMod.natCast_self 25, zero_mul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise reduction is a ring homomorphism on square matrices. -/
def matrixReduction : Matrix ι ι (ZMod 25) →+* Matrix ι ι (ZMod 5) :=
  reduction.mapMatrix

/-- The matrix kernel is square-zero even though the matrix ring is noncommutative. -/
theorem matrixReduction_kernel_mul (A B : Matrix ι ι (ZMod 25))
    (hA : matrixReduction A = 0) (hB : matrixReduction B = 0) : A * B = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  change ∑ k, A i k * B k j = 0
  apply Finset.sum_eq_zero
  intro k _
  exact reduction_kernel_mul _ _
    (congrFun (congrFun hA i) k) (congrFun (congrFun hB k) j)

/-- Any lifted matrix whose reduction is involutive can be repaired. -/
theorem repair_sq (A : Matrix ι ι (ZMod 25))
    (hA : (matrixReduction A) ^ 2 = 1) : repair A ^ 2 = 1 := by
  have hE : matrixReduction (A ^ 2 - 1) = 0 := by
    rw [map_sub, map_pow, map_one, hA, sub_self]
  have hsq : (A ^ 2 - 1) ^ 2 = 0 := by
    rw [pow_two]
    exact matrixReduction_kernel_mul _ _ hE hE
  have hc : (675 : Matrix ι ι (ZMod 25)) = 0 := by
    have h := congrArg (algebraMap (ZMod 25) (Matrix ι ι (ZMod 25)))
      (show (675 : ZMod 25) = 0 from (ZMod.natCast_eq_zero_iff 675 25).mpr (by norm_num))
    simpa only [map_ofNat, map_zero] using h
  apply sub_eq_zero.mp
  rw [repair_error, hsq, zero_mul, mul_zero, zero_add, hc]

/-- Repair does not change an involutive reduction. -/
theorem matrixReduction_repair (A : Matrix ι ι (ZMod 25))
    (hA : (matrixReduction A) ^ 2 = 1) : matrixReduction (repair A) = matrixReduction A := by
  have hcube : (matrixReduction A) ^ 3 = matrixReduction A := by
    rw [pow_succ, hA, one_mul]
  have hc : (26 : Matrix ι ι (ZMod 5)) = 1 := by
    have h := congrArg (algebraMap (ZMod 5) (Matrix ι ι (ZMod 5)))
      (show (26 : ZMod 5) = 1 from
        (ZMod.natCast_eq_natCast_iff 26 1 5).mpr (by norm_num [Nat.ModEq]))
    simpa only [map_ofNat, map_one] using h
  simp only [repair, map_mul, map_sub, map_pow, map_ofNat, hcube]
  calc
    13 * (3 * matrixReduction A - matrixReduction A) = 26 * matrixReduction A := by
      noncomm_ring
    _ = matrixReduction A := by rw [hc, one_mul]

/-- A canonical entrywise lift; its defect is removed by `repair`. -/
def entryLift (A : Matrix ι ι (ZMod 5)) : Matrix ι ι (ZMod 25) :=
  fun i j => (A i j).val

@[simp] theorem matrixReduction_entryLift (A : Matrix ι ι (ZMod 5)) :
    matrixReduction (entryLift A) = A := by
  ext i j
  change reduction ((A i j).val : ZMod 25) = A i j
  rw [map_natCast, ZMod.natCast_zmod_val]

/-- Every finite matrix involution over `𝔽₅` lifts across `ℤ/25ℤ → 𝔽₅`. -/
theorem involutions_lift_mod25 :
    Set.SurjOn (matrixReduction (ι := ι)) {A | A ^ 2 = 1} {A | A ^ 2 = 1} := by
  intro A hA
  have hred : (matrixReduction (entryLift A)) ^ 2 = 1 := by
    rw [matrixReduction_entryLift]
    exact hA
  exact ⟨repair (entryLift A), repair_sq _ hred,
    (matrixReduction_repair _ hred).trans (matrixReduction_entryLift A)⟩

/-- Involutive lifts of the same matrix are conjugate by a basis change reducing to identity. -/
theorem involution_lift_classification (U V : Matrix ι ι (ZMod 25)) :
    (U ^ 2 = 1 ∧ V ^ 2 = 1 ∧ matrixReduction U = matrixReduction V) ↔
      (U ^ 2 = 1 ∧ ∃ C : (Matrix ι ι (ZMod 25))ˣ,
        matrixReduction (C : Matrix ι ι (ZMod 25)) = 1 ∧
          (C : Matrix ι ι (ZMod 25)) * U = V * C) := by
  constructor
  · rintro ⟨hU, hV, hUV⟩
    let W : Matrix ι ι (ZMod 25) := 13 * (1 + V * U)
    have h26 : (26 : Matrix ι ι (ZMod 5)) = 1 := by
      have h := congrArg (algebraMap (ZMod 5) (Matrix ι ι (ZMod 5)))
        (show (26 : ZMod 5) = 1 from
          (ZMod.natCast_eq_natCast_iff 26 1 5).mpr (by norm_num [Nat.ModEq]))
      simpa only [map_ofNat, map_one] using h
    have hW : matrixReduction W = 1 := by
      have hVV : matrixReduction V * matrixReduction V = 1 := by
        rw [← map_mul, ← pow_two, hV, map_one]
      simp only [W, map_mul, map_add, map_one, map_ofNat, hUV, hVV]
      convert h26 using 1
      norm_num
    have hE : matrixReduction (W - 1) = 0 := by rw [map_sub, hW, map_one, sub_self]
    have hsq : (W - 1) ^ 2 = 0 := by
      rw [pow_two]
      exact matrixReduction_kernel_mul _ _ hE hE
    have hleft : W * (2 - W) = 1 := by
      calc
        W * (2 - W) = 1 - (W - 1) ^ 2 := by noncomm_ring
        _ = 1 := by rw [hsq, sub_zero]
    have hright : (2 - W) * W = 1 := by
      calc
        (2 - W) * W = 1 - (W - 1) ^ 2 := by noncomm_ring
        _ = 1 := by rw [hsq, sub_zero]
    have hWU : W * U = V * W := by
      have hUU : U * U = 1 := by simpa only [pow_two] using hU
      have hVVU : V * (V * U) = U := by rw [← mul_assoc, ← pow_two, hV, one_mul]
      dsimp [W]
      noncomm_ring [hUU, hVVU]
    exact ⟨hU, ⟨W, 2 - W, hleft, hright⟩, hW, hWU⟩
  · rintro ⟨hU, C, hC, hCU⟩
    have hCi : ((C⁻¹ : (Matrix ι ι (ZMod 25))ˣ) : Matrix ι ι (ZMod 25)) * C = 1 :=
      C.inv_val
    have hCv : (C : Matrix ι ι (ZMod 25)) *
        ((C⁻¹ : (Matrix ι ι (ZMod 25))ˣ) : Matrix ι ι (ZMod 25)) = 1 := C.val_inv
    have hconj : V = (C : Matrix ι ι (ZMod 25)) * U *
        ((C⁻¹ : (Matrix ι ι (ZMod 25))ˣ) : Matrix ι ι (ZMod 25)) := by
      rw [hCU, mul_assoc, hCv, mul_one]
    refine ⟨hU, ?_, ?_⟩
    · rw [hconj, pow_two]
      calc
        _ = (C : Matrix ι ι (ZMod 25)) * U * (↑(C⁻¹) * C) * U * ↑(C⁻¹) := by
          simp only [mul_assoc]
        _ = (C : Matrix ι ι (ZMod 25)) * (U * U) * ↑(C⁻¹) := by
          rw [hCi, mul_one]
          simp only [mul_assoc]
        _ = 1 := by rw [← pow_two, hU, mul_one, hCv]
    · have h := congrArg matrixReduction hCU
      simpa only [map_mul, hC, one_mul, mul_one] using h

#print axioms repair_error
#print axioms involutions_lift_mod25
#print axioms involution_lift_classification
end GaloisForLFunctions.RepresentationLifting.InvolutionRepair
