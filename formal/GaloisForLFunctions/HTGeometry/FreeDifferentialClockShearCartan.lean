import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpProjectiveEuclideanAction
import GaloisForLFunctions.HTGeometry.FreeDifferentialClockShearOrbit

/-!
# Exact dominant Cartan vector of the free differential clock shear

Sharp one-sided lattice inclusions recover the bottom and top coordinates of a canonical Cartan
vector from entry degrees of a matrix and its inverse.  Applied to the free rank-two clock shear,
whose two degree maxima are both exactly `n`, this proves the literal vector `(n, -n)` for every
iterate.  No determinant or balance hypothesis is used.
-/

open scoped Differential
open nonZeroDivisors OreLocalization

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K] {r : ℕ}

theorem leftScale_uniformizer_mapMatrix_standard_carrier_le_iff_relativePosition
    (A : (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ) (z : ℤ) :
    (leftScaleCompletedPseudoDiffOpLattice
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ z)
      (mapCompletedPseudoDiffOpLatticeLinear
        (completedPseudoDiffOpMatrixLinearEquiv A)
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)))).carrier ≤
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)).carrier ↔
      ∀ i, 0 ≤ completedPseudoDiffOpDominantRelativePosition
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv A)
          (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))) i + z := by
  let L := standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)
  let M := mapCompletedPseudoDiffOpLatticeLinear
    (completedPseudoDiffOpMatrixLinearEquiv A) L
  let d := completedPseudoDiffOpDominantCartanData L M
  rw [← mapCompletedPseudoDiffOpLatticeLinear_carrier_le_iff d.frame]
  rw [mapCompletedPseudoDiffOpLatticeLinear_leftScale, d.map_right, d.map_left,
    leftScale_standardCompletedPseudoDiffOpLatticeAtCoweight_add_const,
    ← standardCompletedPseudoDiffOpLatticeAtCoweight_zero,
    standardCompletedPseudoDiffOpLatticeAtCoweight_carrier_le_iff]
  rw [standardCompletedPseudoDiffOpLatticeAtCoweight_zero]
  simp only [Pi.add_apply]
  change (∀ i, 0 ≤ d.coweight i + z) ↔ ∀ i, 0 ≤
    completedPseudoDiffOpDominantRelativePosition L M i + z
  rw [show d.coweight = completedPseudoDiffOpDominantRelativePosition L M from
    completedPseudoDiffOpDominantRelativePosition_eq L M d.frame d.coweight
      d.map_left d.map_right d.dominant]

theorem standard_carrier_le_leftScale_uniformizer_mapMatrix_iff_relativePosition
    (A : (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ) (z : ℤ) :
    (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)).carrier ≤
      (leftScaleCompletedPseudoDiffOpLattice
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ z)
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv A)
          (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)))).carrier ↔
      ∀ i, completedPseudoDiffOpDominantRelativePosition
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv A)
          (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))) i + z ≤ 0 := by
  let L := standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)
  let M := mapCompletedPseudoDiffOpLatticeLinear
    (completedPseudoDiffOpMatrixLinearEquiv A) L
  let d := completedPseudoDiffOpDominantCartanData L M
  rw [← mapCompletedPseudoDiffOpLatticeLinear_carrier_le_iff d.frame]
  rw [mapCompletedPseudoDiffOpLatticeLinear_leftScale, d.map_right, d.map_left,
    leftScale_standardCompletedPseudoDiffOpLatticeAtCoweight_add_const,
    ← standardCompletedPseudoDiffOpLatticeAtCoweight_zero,
    standardCompletedPseudoDiffOpLatticeAtCoweight_carrier_le_iff]
  rw [standardCompletedPseudoDiffOpLatticeAtCoweight_zero]
  simp only [Pi.add_apply]
  change (∀ i, d.coweight i + z ≤ 0) ↔ ∀ i,
    completedPseudoDiffOpDominantRelativePosition L M i + z ≤ 0
  rw [show d.coweight = completedPseudoDiffOpDominantRelativePosition L M from
    completedPseudoDiffOpDominantRelativePosition_eq L M d.frame d.coweight
      d.map_left d.map_right d.dominant]

end

end GaloisForLFunctions.HTGeometry.DiffOp

namespace GaloisForLFunctions.HTGeometry.DifferentialFieldAut

noncomputable section

variable {C : Type u} [Field C] [CharZero C]

theorem completedPseudoDiffOpDominantRelativePosition_freeClockShear
    (n : ℕ) :
    DiffOp.completedPseudoDiffOpDominantRelativePosition
        (DiffOp.standardCompletedPseudoDiffOpLattice
          (K := JetField C (Fin 2)) (ι := Fin 2))
        (freeClockShearCompletedOrbitLattice (C := C) n) =
      ![(n : ℤ), -(n : ℤ)] := by
  by_cases hn : n = 0
  · subst n
    have hM : freeClockShearCompletedOrbitLattice (C := C) 0 =
        DiffOp.standardCompletedPseudoDiffOpLattice
          (K := JetField C (Fin 2)) (ι := Fin 2) := by
      have hU : DiffOp.completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit
          (1 : (Matrix (Fin 2) (Fin 2) (DiffOp (JetField C (Fin 2))))ˣ) =
          (1 : (Matrix (Fin 2) (Fin 2)
            (DiffOp.CompletedPseudoDiffOp (JetField C (Fin 2))))ˣ) := by
        let f : Matrix (Fin 2) (Fin 2) (DiffOp (JetField C (Fin 2))) →+*
            Matrix (Fin 2) (Fin 2)
              (DiffOp.CompletedPseudoDiffOp (JetField C (Fin 2))) :=
          (DiffOp.diffOpToCompletedPseudoRingHom
            (K := JetField C (Fin 2))).mapMatrix
        change Units.map f.toMonoidHom 1 = 1
        exact map_one _
      unfold freeClockShearCompletedOrbitLattice
      rw [pow_zero, hU, DiffOp.completedPseudoDiffOpMatrixLinearEquiv_one,
        DiffOp.mapCompletedPseudoDiffOpLatticeLinear_refl]
    have hrel : DiffOp.completedPseudoDiffOpDominantRelativePosition
        (DiffOp.standardCompletedPseudoDiffOpLattice
          (K := JetField C (Fin 2)) (ι := Fin 2))
        (DiffOp.standardCompletedPseudoDiffOpLattice
          (K := JetField C (Fin 2)) (ι := Fin 2)) =
        (fun _ : Fin 2 => 0) := by
      have h := DiffOp.completedPseudoDiffOpDominantRelativePosition_standard_coweight
        (K := JetField C (Fin 2)) (m := fun _ : Fin 2 => 0) (by
          intro i j hij
          simp)
      rwa [DiffOp.standardCompletedPseudoDiffOpLatticeAtCoweight_zero] at h
    rw [hM, hrel]
    ext i
    fin_cases i <;> simp
  · let U := DiffOp.completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit
      (freeClockShearFrechetMatrixUnit (C := C) ^ n)
    let L := DiffOp.standardCompletedPseudoDiffOpLattice
      (K := JetField C (Fin 2)) (ι := Fin 2)
    let M := DiffOp.mapCompletedPseudoDiffOpLatticeLinear
      (DiffOp.completedPseudoDiffOpMatrixLinearEquiv U) L
    let m := DiffOp.completedPseudoDiffOpDominantRelativePosition L M
    change DiffOp.completedPseudoDiffOpDominantRelativePosition L M = _
    have hmanti : Antitone m :=
      DiffOp.completedPseudoDiffOpDominantRelativePosition_antitone L M
    have hforwardUpper :
        (DiffOp.leftScaleCompletedPseudoDiffOpLattice
          (DiffOp.completedPseudoDiffOpUniformizerUnit
            (K := JetField C (Fin 2)) ^ (n : ℤ)) M).carrier ≤ L.carrier := by
      dsimp [M, L]
      apply (DiffOp.leftScale_mapMatrix_standard_carrier_le_iff
        (DiffOp.completedPseudoDiffOpUniformizerUnit
          (K := JetField C (Fin 2)) ^ (n : ℤ)) U).2
      intro i j
      rw [DiffOp.completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_val]
      change ((DiffOp.completedPseudoDiffOpUniformizerUnit
          (K := JetField C (Fin 2)) ^ (n : ℤ) :
            (DiffOp.CompletedPseudoDiffOp (JetField C (Fin 2)))ˣ) :
          DiffOp.CompletedPseudoDiffOp (JetField C (Fin 2))) *
        DiffOp.diffOpToCompletedPseudoRingHom
          ((freeClockShearFrechetMatrix (C := C) ^ n) i j) ∈
        DiffOp.CompletedPseudoDiffOpInteger (K := JetField C (Fin 2))
      rw [DiffOp.uniformizer_zpow_mul_diffOpToCompletedPseudoRingHom_mem_integer_iff]
      have hdeg := DiffOp.degree_le_matDeg
        (freeClockShearFrechetMatrix (C := C) ^ n) i j
      simpa [matDeg_freeClockShearFrechetMatrix_pow] using hdeg
    have hm1Lower : -(n : ℤ) ≤ m 1 := by
      have h := (DiffOp.leftScale_uniformizer_mapMatrix_standard_carrier_le_iff_relativePosition
        U (n : ℤ)).1 (by simpa only [L, M] using hforwardUpper) 1
      change 0 ≤ m 1 + (n : ℤ) at h
      omega
    have hforwardSharp :
        (DiffOp.leftScaleCompletedPseudoDiffOpLattice
          (DiffOp.completedPseudoDiffOpUniformizerUnit
            (K := JetField C (Fin 2)) ^ (-m 1)) M).carrier ≤ L.carrier := by
      dsimp [M, L]
      apply (DiffOp.leftScale_uniformizer_mapMatrix_standard_carrier_le_iff_relativePosition
        U (-m 1)).2
      change ∀ i, 0 ≤ m i + -m 1
      intro i
      have hi : i ≤ (1 : Fin 2) := by omega
      have hdom : m 1 ≤ m i := hmanti hi
      omega
    obtain ⟨iP, jP, hPdeg⟩ :=
      exists_degree_freeClockShearFrechetMatrix_pow (C := C) n
    have hP0 : (freeClockShearFrechetMatrix (C := C) ^ n) iP jP ≠ 0 := by
      intro hzero
      rw [hzero, DiffOp.degree_zero] at hPdeg
      omega
    have hm1Upper : m 1 ≤ -(n : ℤ) := by
      have hentry := (DiffOp.leftScale_mapMatrix_standard_carrier_le_iff
        (DiffOp.completedPseudoDiffOpUniformizerUnit
          (K := JetField C (Fin 2)) ^ (-m 1)) U).1
          (by simpa only [L, M] using hforwardSharp) iP jP
      rw [DiffOp.completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_val] at hentry
      change ((DiffOp.completedPseudoDiffOpUniformizerUnit
          (K := JetField C (Fin 2)) ^ (-m 1) :
            (DiffOp.CompletedPseudoDiffOp (JetField C (Fin 2)))ˣ) :
          DiffOp.CompletedPseudoDiffOp (JetField C (Fin 2))) *
        DiffOp.diffOpToCompletedPseudoRingHom
          ((freeClockShearFrechetMatrix (C := C) ^ n) iP jP) ∈
        DiffOp.CompletedPseudoDiffOpInteger (K := JetField C (Fin 2)) at hentry
      rw [DiffOp.uniformizer_zpow_mul_diffOpToCompletedPseudoRingHom_mem_integer_iff_int]
        at hentry
      rcases hentry with hzero | hdegree
      · exact absurd hzero hP0
      · rw [hPdeg] at hdegree
        omega
    have hbackwardUpper : L.carrier ≤
        (DiffOp.leftScaleCompletedPseudoDiffOpLattice
          (DiffOp.completedPseudoDiffOpUniformizerUnit
            (K := JetField C (Fin 2)) ^ (-(n : ℤ))) M).carrier := by
      dsimp [M, L]
      apply (DiffOp.standard_carrier_le_leftScale_mapMatrix_iff
        (DiffOp.completedPseudoDiffOpUniformizerUnit
          (K := JetField C (Fin 2)) ^ (-(n : ℤ))) U).2
      intro i j
      rw [show ((DiffOp.completedPseudoDiffOpUniformizerUnit
          (K := JetField C (Fin 2)) ^ (-(n : ℤ)))⁻¹ :
            (DiffOp.CompletedPseudoDiffOp (JetField C (Fin 2)))ˣ) =
          DiffOp.completedPseudoDiffOpUniformizerUnit
            (K := JetField C (Fin 2)) ^ (n : ℤ) by simp]
      rw [DiffOp.completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_inv_val]
      change ((DiffOp.completedPseudoDiffOpUniformizerUnit
          (K := JetField C (Fin 2)) ^ (n : ℤ) :
            (DiffOp.CompletedPseudoDiffOp (JetField C (Fin 2)))ˣ) :
          DiffOp.CompletedPseudoDiffOp (JetField C (Fin 2))) *
        DiffOp.diffOpToCompletedPseudoRingHom
          ((freeClockShearFrechetInverseMatrix (C := C) ^ n) i j) ∈
        DiffOp.CompletedPseudoDiffOpInteger (K := JetField C (Fin 2))
      rw [DiffOp.uniformizer_zpow_mul_diffOpToCompletedPseudoRingHom_mem_integer_iff]
      have hdeg := DiffOp.degree_le_matDeg
        (freeClockShearFrechetInverseMatrix (C := C) ^ n) i j
      simpa [matDeg_freeClockShearFrechetInverseMatrix_pow] using hdeg
    have hm0Upper : m 0 ≤ (n : ℤ) := by
      have h :=
        (DiffOp.standard_carrier_le_leftScale_uniformizer_mapMatrix_iff_relativePosition
          U (-(n : ℤ))).1 (by simpa only [L, M] using hbackwardUpper) 0
      change m 0 - (n : ℤ) ≤ 0 at h
      omega
    have hbackwardSharp : L.carrier ≤
        (DiffOp.leftScaleCompletedPseudoDiffOpLattice
          (DiffOp.completedPseudoDiffOpUniformizerUnit
            (K := JetField C (Fin 2)) ^ (-m 0)) M).carrier := by
      dsimp [M, L]
      apply (DiffOp.standard_carrier_le_leftScale_uniformizer_mapMatrix_iff_relativePosition
        U (-m 0)).2
      change ∀ i, m i + -m 0 ≤ 0
      intro i
      have hdom : m i ≤ m 0 := hmanti (Fin.zero_le i)
      omega
    obtain ⟨iQ, jQ, hQdeg⟩ :=
      exists_degree_freeClockShearFrechetInverseMatrix_pow (C := C) n
    have hQ0 : (freeClockShearFrechetInverseMatrix (C := C) ^ n) iQ jQ ≠ 0 := by
      intro hzero
      rw [hzero, DiffOp.degree_zero] at hQdeg
      omega
    have hm0Lower : (n : ℤ) ≤ m 0 := by
      have hentry := (DiffOp.standard_carrier_le_leftScale_mapMatrix_iff
        (DiffOp.completedPseudoDiffOpUniformizerUnit
          (K := JetField C (Fin 2)) ^ (-m 0)) U).1
          (by simpa only [L, M] using hbackwardSharp) iQ jQ
      rw [show ((DiffOp.completedPseudoDiffOpUniformizerUnit
          (K := JetField C (Fin 2)) ^ (-m 0))⁻¹ :
            (DiffOp.CompletedPseudoDiffOp (JetField C (Fin 2)))ˣ) =
          DiffOp.completedPseudoDiffOpUniformizerUnit
            (K := JetField C (Fin 2)) ^ m 0 by simp] at hentry
      rw [DiffOp.completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_inv_val] at hentry
      change ((DiffOp.completedPseudoDiffOpUniformizerUnit
          (K := JetField C (Fin 2)) ^ m 0 :
            (DiffOp.CompletedPseudoDiffOp (JetField C (Fin 2)))ˣ) :
          DiffOp.CompletedPseudoDiffOp (JetField C (Fin 2))) *
        DiffOp.diffOpToCompletedPseudoRingHom
          ((freeClockShearFrechetInverseMatrix (C := C) ^ n) iQ jQ) ∈
        DiffOp.CompletedPseudoDiffOpInteger (K := JetField C (Fin 2)) at hentry
      rw [DiffOp.uniformizer_zpow_mul_diffOpToCompletedPseudoRingHom_mem_integer_iff_int]
        at hentry
      rcases hentry with hzero | hdegree
      · exact absurd hzero hQ0
      · rw [hQdeg] at hdegree
        omega
    funext i
    fin_cases i
    · change m 0 = (n : ℤ)
      omega
    · change m 1 = -(n : ℤ)
      omega

end

end GaloisForLFunctions.HTGeometry.DifferentialFieldAut
