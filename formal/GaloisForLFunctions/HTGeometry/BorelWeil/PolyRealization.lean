/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.BorelWeil.PolyHomogeneous
import GaloisForLFunctions.HTGeometry.BorelWeil.PrincipalMinors
import GaloisForLFunctions.HTGeometry.BorelWeil.Realization

/-!
# The highest weight vector in the polynomial model

The product of powers of leading principal minors is a polynomial section of the Borel–Weil line
bundle attached to the dominant weight `weightOfMult m`, and it takes the value `1` at the identity
matrix.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.leadingMinorMat` — the leading principal minor of a
  matrix.
* `GaloisForLFunctions.HTGeometry.BorelWeil.minorPoly` — the same as a polynomial.
* `GaloisForLFunctions.HTGeometry.BorelWeil.bwPoly` — the highest weight vector.

## Main results

* `bwPoly_mem_polySections`, `matEval_one_bwPoly`
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k]

/-- The `j`-th leading principal minor of a matrix. -/
def leadingMinorMat (j : ℕ) (g : Matrix (Fin N) (Fin N) k) : k := (truncate j g).det

@[simp] theorem leadingMinorMat_one (j : ℕ) :
    leadingMinorMat j (1 : Matrix (Fin N) (Fin N) k) = 1 := by
  simp [leadingMinorMat, truncate_one]

theorem leadingMinorMat_mul_borel (j : ℕ) (g : Matrix (Fin N) (Fin N) k)
    {B : Matrix (Fin N) (Fin N) k} (hB : B.BlockTriangular id) :
    leadingMinorMat j (g * B)
      = leadingMinorMat j g * ∏ i : Fin N, (if (i : ℕ) < j then B i i else 1) := by
  rw [leadingMinorMat, truncate_mul j _ _ hB, Matrix.det_mul, leadingMinorMat,
    det_truncate_of_blockTriangular hB]

/-- The minor product attached to a multiplicity vector, as a function of matrices. -/
def bwVectorMat (m : Fin N → ℕ) (g : Matrix (Fin N) (Fin N) k) : k :=
  ∏ j : Fin N, (leadingMinorMat ((j : ℕ) + 1) g) ^ (m j)

@[simp] theorem bwVectorMat_one (m : Fin N → ℕ) :
    bwVectorMat m (1 : Matrix (Fin N) (Fin N) k) = 1 := by simp [bwVectorMat]

theorem bwVectorMat_mul_borel (m : Fin N → ℕ) (g : Matrix (Fin N) (Fin N) k)
    {B : Matrix (Fin N) (Fin N) k} (hB : B.BlockTriangular id) :
    bwVectorMat m (g * B) = borelCharMat (weightOfMult m) B * bwVectorMat m g := by
  classical
  have hstep : ∀ j : Fin N,
      (leadingMinorMat ((j : ℕ) + 1) (g * B)) ^ (m j)
        = (leadingMinorMat ((j : ℕ) + 1) g) ^ (m j)
          * (∏ i : Fin N, (if i ≤ j then B i i else 1)) ^ (m j) := by
    intro j
    rw [leadingMinorMat_mul_borel _ g hB, mul_pow]
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : i ≤ j
    · rw [if_pos (by exact Nat.lt_succ_of_le (Fin.le_def.mp h)), if_pos h]
    · rw [if_neg (by
        intro hcon
        exact h (Fin.le_def.mpr (Nat.lt_succ_iff.mp hcon))), if_neg h]
  rw [bwVectorMat, Finset.prod_congr rfl fun j _ => hstep j, Finset.prod_mul_distrib, mul_comm]
  congr 1
  · rw [borelCharMat]
    rw [Finset.prod_congr rfl fun j (_ : j ∈ Finset.univ) =>
      (Finset.prod_pow (Finset.univ) (m j) (fun i : Fin N => (if i ≤ j then B i i else 1))).symm]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hpt : ∀ j : Fin N, (if i ≤ j then B i i else 1) ^ (m j)
        = if i ≤ j then (B i i) ^ (m j) else 1 := by
      intro j
      by_cases h : i ≤ j
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, one_pow]
    rw [Finset.prod_congr rfl fun j (_ : j ∈ Finset.univ) => hpt j, ← Finset.prod_filter,
      Finset.prod_pow_eq_pow_sum, weightOfMult]

/-- The generic matrix of indeterminates. -/
noncomputable def genericMatrix (N : ℕ) (k : Type*) [CommRing k] :
    Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) k) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

/-- The `j`-th leading principal minor as a polynomial. -/
noncomputable def minorPoly (j : ℕ) (N : ℕ) (k : Type*) [CommRing k] :
    MvPolynomial (Fin N × Fin N) k :=
  (truncate j (genericMatrix N k)).det

theorem matEval_minorPoly (j : ℕ) (g : Matrix (Fin N) (Fin N) k) :
    matEval g (minorPoly j N k) = leadingMinorMat j g := by
  have hmap : (truncate j (genericMatrix N k)).map
      (MvPolynomial.eval (fun ij : Fin N × Fin N => g ij.1 ij.2)) = truncate j g := by
    ext i i'
    by_cases h1 : (i : ℕ) < j
    · by_cases h2 : (i' : ℕ) < j
      · simp [Matrix.map_apply, truncate_apply_of_both h1 h2, genericMatrix]
      · rw [Matrix.map_apply, truncate_apply_of_not_right h2, truncate_apply_of_not_right h2]
        by_cases h3 : i = i' <;> simp [h3]
    · rw [Matrix.map_apply, truncate_apply_of_not_left h1, truncate_apply_of_not_left h1]
      by_cases h3 : i = i' <;> simp [h3]
  rw [minorPoly, leadingMinorMat, matEval, ← hmap, RingHom.map_det]
  rfl

/-- The Borel–Weil highest weight vector in the polynomial model. -/
noncomputable def bwPoly (m : Fin N → ℕ) (k : Type*) [CommRing k] :
    MvPolynomial (Fin N × Fin N) k :=
  ∏ j : Fin N, (minorPoly ((j : ℕ) + 1) N k) ^ (m j)

theorem matEval_bwPoly (m : Fin N → ℕ) (g : Matrix (Fin N) (Fin N) k) :
    matEval g (bwPoly m k) = bwVectorMat m g := by
  rw [bwPoly, bwVectorMat, matEval, map_prod]
  exact Finset.prod_congr rfl fun j _ => by
    rw [map_pow]
    exact congrArg (· ^ m j) (matEval_minorPoly ((j : ℕ) + 1) g)

@[simp] theorem matEval_one_bwPoly (m : Fin N → ℕ) :
    matEval (1 : Matrix (Fin N) (Fin N) k) (bwPoly m k) = 1 := by
  rw [matEval_bwPoly, bwVectorMat_one]

/-- **The minor product is a polynomial section.** -/
theorem bwPoly_mem_polySections (m : Fin N → ℕ) :
    bwPoly m k ∈ polySections (weightOfMult m) := by
  intro g B hB
  rw [matEval_bwPoly, matEval_bwPoly, bwVectorMat_mul_borel m g hB.1]

/-- **Non-vanishing of the polynomial model.** -/
theorem polySections_ne_bot_of_antitone {lam : Fin N → ℕ} (hlam : Antitone lam) :
    polySections (k := k) lam ≠ ⊥ := by
  intro hbot
  have hmem : bwPoly (multOfWeight lam) k ∈ polySections (k := k) lam := by
    have h := bwPoly_mem_polySections (k := k) (multOfWeight lam)
    rwa [weightOfMult_multOfWeight hlam] at h
  rw [hbot, Submodule.mem_bot] at hmem
  have := congrArg (matEval (1 : Matrix (Fin N) (Fin N) k)) hmem
  rw [matEval_one_bwPoly, matEval_zero] at this
  exact one_ne_zero this

end GaloisForLFunctions.HTGeometry.BorelWeil
