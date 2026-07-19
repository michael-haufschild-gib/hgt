import GaloisForLFunctions.HTGeometry.ProjectiveHorizonLogPotential
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonCausticQSystem
import GaloisForLFunctions.HTGeometry.HypertranscendentalHorizonFunctionField
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The all-rank hypertranscendental horizon Q-system

This module reindexes the general two-border Desnanot--Jacobi identity as the complete
rectangular horizon Q-system, proves finite reciprocal and reciprocal-square genericity, and
constructs the global normalized power-series section of a hypertranscendental source.  It also
identifies the normalized amplitude with the critical reciprocal Jacobian determinant up to its
exact universal sign and nonzero scale.
-/

open Matrix
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open scoped IntermediateField.algebraAdjoinAdjoin

namespace GaloisForLFunctions.HTGeometry

def fullBorderIndex (c : ℕ) : Fin c ⊕ Fin 2 → Fin (c + 2)
  | Sum.inl i => ⟨i + 1, by omega⟩
  | Sum.inr j => if (j : ℕ) = 0 then 0 else Fin.last (c + 1)

theorem fullBorderIndex_bijective (c : ℕ) : Function.Bijective (fullBorderIndex c) := by
  constructor
  · intro a b hab
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            apply congrArg Sum.inl
            apply Fin.ext
            simpa [fullBorderIndex] using congrArg Fin.val hab
        | inr j =>
            exfalso
            have hv := congrArg Fin.val hab
            fin_cases j
            · simp [fullBorderIndex] at hv
            · simp [fullBorderIndex] at hv
              omega
    | inr i =>
        cases b with
        | inl j =>
            exfalso
            have hv := congrArg Fin.val hab
            fin_cases i
            · simp [fullBorderIndex] at hv
            · simp [fullBorderIndex] at hv
              omega
        | inr j =>
            fin_cases i <;> fin_cases j <;>
              simp [fullBorderIndex] at hab ⊢
  · intro x
    by_cases hx0 : (x : ℕ) = 0
    · refine ⟨Sum.inr 0, ?_⟩
      apply Fin.ext
      simp [fullBorderIndex, hx0]
    by_cases hxlast : (x : ℕ) = c + 1
    · refine ⟨Sum.inr 1, ?_⟩
      apply Fin.ext
      simp [fullBorderIndex, hxlast]
    · refine ⟨Sum.inl ⟨(x : ℕ) - 1, by omega⟩, ?_⟩
      apply Fin.ext
      simp [fullBorderIndex]
      omega

noncomputable def fullBorderEquiv (c : ℕ) : Fin c ⊕ Fin 2 ≃ Fin (c + 2) :=
  Equiv.ofBijective (fullBorderIndex c) (fullBorderIndex_bijective c)

@[simp] theorem fullBorderEquiv_inl (c : ℕ) (i : Fin c) :
    (fullBorderEquiv c (Sum.inl i) : ℕ) = i + 1 := rfl

@[simp] theorem fullBorderEquiv_inr_zero (c : ℕ) :
    fullBorderEquiv c (Sum.inr (0 : Fin 2)) = 0 := rfl

@[simp] theorem fullBorderEquiv_inr_one (c : ℕ) :
    fullBorderEquiv c (Sum.inr (1 : Fin 2)) = Fin.last (c + 1) := rfl

def topBorderEquiv (c : ℕ) : Fin c ⊕ Fin 1 ≃ Fin (c + 1) :=
  (Equiv.sumComm (Fin c) (Fin 1)).trans
    ((finSumFinEquiv : Fin 1 ⊕ Fin c ≃ Fin (1 + c)).trans
      (finCongr (Nat.add_comm 1 c)))

def bottomBorderEquiv (c : ℕ) : Fin c ⊕ Fin 1 ≃ Fin (c + 1) :=
  finSumFinEquiv

@[simp] theorem topBorderEquiv_inl (c : ℕ) (i : Fin c) :
    (topBorderEquiv c (Sum.inl i) : ℕ) = i + 1 := by
  simp [topBorderEquiv, finSumFinEquiv]

@[simp] theorem topBorderEquiv_inr (c : ℕ) (i : Fin 1) :
    topBorderEquiv c (Sum.inr i) = 0 := by
  fin_cases i
  rfl

@[simp] theorem bottomBorderEquiv_inl (c : ℕ) (i : Fin c) :
    (bottomBorderEquiv c (Sum.inl i) : ℕ) = i := by
  simp [bottomBorderEquiv, finSumFinEquiv]

@[simp] theorem bottomBorderEquiv_inr (c : ℕ) (i : Fin 1) :
    bottomBorderEquiv c (Sum.inr i) = Fin.last c := by
  fin_cases i
  apply Fin.ext
  simp [bottomBorderEquiv, finSumFinEquiv]

noncomputable def horizonAmplitude {K : Type*} [CommRing K]
    (h : ℕ → K) (m n : ℕ) : K :=
  (rectangularSchurToeplitz h n m).det

noncomputable def borderedHorizonMatrix {K : Type*} [CommRing K]
    (h : ℕ → K) (c n : ℕ) : Matrix (Fin c ⊕ Fin 2) (Fin c ⊕ Fin 2) K :=
  (rectangularSchurToeplitz h n (c + 2)).submatrix
    (fullBorderEquiv c) (fullBorderEquiv c)

noncomputable def horizonCenter {K : Type*} [CommRing K]
    (h : ℕ → K) (c n : ℕ) : Matrix (Fin c) (Fin c) K :=
  fun r s => borderedHorizonMatrix h c n (Sum.inl r) (Sum.inl s)

noncomputable def horizonRightBorder {K : Type*} [CommRing K]
    (h : ℕ → K) (c n : ℕ) : Matrix (Fin c) (Fin 2) K :=
  fun r j => borderedHorizonMatrix h c n (Sum.inl r) (Sum.inr j)

noncomputable def horizonBottomBorder {K : Type*} [CommRing K]
    (h : ℕ → K) (c n : ℕ) : Matrix (Fin 2) (Fin c) K :=
  fun i s => borderedHorizonMatrix h c n (Sum.inr i) (Sum.inl s)

noncomputable def horizonCorners {K : Type*} [CommRing K]
    (h : ℕ → K) (c n : ℕ) : Matrix (Fin 2) (Fin 2) K :=
  fun i j => borderedHorizonMatrix h c n (Sum.inr i) (Sum.inr j)

theorem borderedHorizonMatrix_eq_fromBlocks
    {K : Type*} [CommRing K] (h : ℕ → K) (c n : ℕ) :
    borderedHorizonMatrix h c n = Matrix.fromBlocks
      (horizonCenter h c n) (horizonRightBorder h c n)
      (horizonBottomBorder h c n) (horizonCorners h c n) := by
  ext (i | i) (j | j) <;> rfl

theorem horizonCenter_eq
    {K : Type*} [CommRing K] (h : ℕ → K) (c n : ℕ) :
    horizonCenter h c n = rectangularSchurToeplitz h n c := by
  ext i j
  simp only [horizonCenter, borderedHorizonMatrix, Matrix.submatrix_apply,
    rectangularSchurToeplitz, fullBorderEquiv_inl]
  split_ifs <;> congr 1 <;> omega

theorem borderedHorizonMatrix_det
    {K : Type*} [CommRing K] (h : ℕ → K) (c n : ℕ) :
    (borderedHorizonMatrix h c n).det = horizonAmplitude h (c + 2) n := by
  rw [borderedHorizonMatrix, horizonAmplitude,
    Matrix.det_submatrix_equiv_self]

theorem horizonCenter_det
    {K : Type*} [CommRing K] (h : ℕ → K) (c n : ℕ) :
    (horizonCenter h c n).det = horizonAmplitude h c n := by
  rw [horizonCenter_eq, horizonAmplitude]

theorem topPrincipalBorderMinor_eq
    {K : Type*} [CommRing K] (h : ℕ → K) (c n : ℕ) :
    twoBorderMinor (horizonCenter h c n) (horizonRightBorder h c n)
        (horizonBottomBorder h c n) (horizonCorners h c n) 0 0 =
      (rectangularSchurToeplitz h n (c + 1)).submatrix
        (topBorderEquiv c) (topBorderEquiv c) := by
  ext (i | i) (j | j)
  · simp [twoBorderMinor, horizonCenter_eq, rectangularSchurToeplitz,
      topBorderEquiv_inl]
    by_cases hij : (j : ℕ) ≤ n + (i : ℕ)
    · rw [if_pos hij, if_pos (by omega)]
      congr 1
      omega
    · rw [if_neg hij, if_neg (by omega)]
  · fin_cases j
    simp [twoBorderMinor, horizonRightBorder, horizonBottomBorder,
      horizonCorners, borderedHorizonMatrix, rectangularSchurToeplitz]
  · fin_cases i
    simp [twoBorderMinor, horizonRightBorder, horizonBottomBorder,
      horizonCorners, borderedHorizonMatrix, rectangularSchurToeplitz]
  · fin_cases i
    fin_cases j
    simp [twoBorderMinor, horizonCorners, borderedHorizonMatrix,
      rectangularSchurToeplitz]

theorem bottomPrincipalBorderMinor_eq
    {K : Type*} [CommRing K] (h : ℕ → K) (c n : ℕ) :
    twoBorderMinor (horizonCenter h c n) (horizonRightBorder h c n)
        (horizonBottomBorder h c n) (horizonCorners h c n) 1 1 =
      (rectangularSchurToeplitz h n (c + 1)).submatrix
        (bottomBorderEquiv c) (bottomBorderEquiv c) := by
  ext (i | i) (j | j)
  · simp [twoBorderMinor, horizonCenter_eq, rectangularSchurToeplitz,
      bottomBorderEquiv_inl]
  · fin_cases j
    simp [twoBorderMinor, horizonRightBorder, horizonBottomBorder,
      horizonCorners, borderedHorizonMatrix, rectangularSchurToeplitz]
    split_ifs with h₁ h₂
    · congr 1; omega
    · omega
    · omega
    · rfl
  · fin_cases i
    simp [twoBorderMinor, horizonRightBorder, horizonBottomBorder,
      horizonCorners, borderedHorizonMatrix, rectangularSchurToeplitz]
    split_ifs with h₁ h₂
    · congr 1; omega
    · omega
    · omega
    · rfl
  · fin_cases i
    fin_cases j
    simp [twoBorderMinor, horizonCorners, borderedHorizonMatrix,
      rectangularSchurToeplitz]

theorem upperCrossBorderMinor_eq
    {K : Type*} [CommRing K] (h : ℕ → K) (c n : ℕ) (hn : 0 < n) :
    twoBorderMinor (horizonCenter h c n) (horizonRightBorder h c n)
        (horizonBottomBorder h c n) (horizonCorners h c n) 0 1 =
      (rectangularSchurToeplitz h (n - 1) (c + 1)).submatrix
        (topBorderEquiv c) (bottomBorderEquiv c) := by
  ext (i | i) (j | j)
  · simp [twoBorderMinor, horizonCenter, borderedHorizonMatrix,
      rectangularSchurToeplitz]
    split_ifs with h₁ h₂
    · congr 1; omega
    · omega
    · omega
    · rfl
  · fin_cases j
    simp [twoBorderMinor, horizonRightBorder, borderedHorizonMatrix,
      rectangularSchurToeplitz]
    split_ifs with h₁ h₂
    · congr 1; omega
    · omega
    · omega
    · rfl
  · fin_cases i
    simp [twoBorderMinor, horizonBottomBorder, borderedHorizonMatrix,
      rectangularSchurToeplitz]
    split_ifs with h₁ h₂
    · congr 1; omega
    · omega
    · omega
    · rfl
  · fin_cases i
    fin_cases j
    simp [twoBorderMinor, horizonCorners, borderedHorizonMatrix,
      rectangularSchurToeplitz]
    split_ifs with h₁ h₂
    · congr 1; omega
    · omega
    · omega
    · rfl

theorem lowerCrossBorderMinor_eq
    {K : Type*} [CommRing K] (h : ℕ → K) (c n : ℕ) :
    twoBorderMinor (horizonCenter h c n) (horizonRightBorder h c n)
        (horizonBottomBorder h c n) (horizonCorners h c n) 1 0 =
      (rectangularSchurToeplitz h (n + 1) (c + 1)).submatrix
        (bottomBorderEquiv c) (topBorderEquiv c) := by
  ext (i | i) (j | j)
  · simp [twoBorderMinor, horizonCenter, borderedHorizonMatrix,
      rectangularSchurToeplitz]
    split_ifs with h₁ h₂
    · congr 1; omega
    · omega
    · omega
    · rfl
  · fin_cases j
    simp [twoBorderMinor, horizonRightBorder, borderedHorizonMatrix,
      rectangularSchurToeplitz]
    (congr 1; omega)
  · fin_cases i
    simp [twoBorderMinor, horizonBottomBorder, borderedHorizonMatrix,
      rectangularSchurToeplitz]
    split_ifs with h₁ h₂
    · congr 1; omega
    · omega
    · omega
    · rfl
  · fin_cases i
    fin_cases j
    simp [twoBorderMinor, horizonCorners, borderedHorizonMatrix,
      rectangularSchurToeplitz]
    (congr 1; omega)

theorem det_submatrix_two_equiv
    {K I J : Type*} [CommRing K] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (A : Matrix J J K) (e f : I ≃ J) :
    (A.submatrix e f).det =
      (Equiv.Perm.sign (f.trans e.symm) : K) * A.det := by
  let σ : Equiv.Perm I := f.trans e.symm
  have hmatrix : A.submatrix e f =
      (A.submatrix e e).submatrix id σ := by
    ext i j
    simp [σ]
  rw [hmatrix, Matrix.det_permute', Matrix.det_submatrix_equiv_self]

theorem crossedBorderMinors_det_mul
    {K : Type*} [CommRing K] (h : ℕ → K) (c n : ℕ) (hn : 0 < n) :
    (twoBorderMinor (horizonCenter h c n) (horizonRightBorder h c n)
          (horizonBottomBorder h c n) (horizonCorners h c n) 0 1).det *
      (twoBorderMinor (horizonCenter h c n) (horizonRightBorder h c n)
          (horizonBottomBorder h c n) (horizonCorners h c n) 1 0).det =
      horizonAmplitude h (c + 1) (n - 1) *
        horizonAmplitude h (c + 1) (n + 1) := by
  rw [upperCrossBorderMinor_eq h c n hn, lowerCrossBorderMinor_eq h c n]
  rw [det_submatrix_two_equiv, det_submatrix_two_equiv]
  simp only [horizonAmplitude]
  let σ : Equiv.Perm (Fin c ⊕ Fin 1) :=
    (bottomBorderEquiv c).trans (topBorderEquiv c).symm
  have hs : ((Equiv.Perm.sign σ : K) * (Equiv.Perm.sign σ : K)) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
    · rw [hσ]
      simp
    · rw [hσ]
      simp
  have hsign :
      (Equiv.Perm.sign ((bottomBorderEquiv c).trans (topBorderEquiv c).symm) : K) =
        (Equiv.Perm.sign ((topBorderEquiv c).trans (bottomBorderEquiv c).symm) : K) := by
    rw [show (topBorderEquiv c).trans (bottomBorderEquiv c).symm = σ⁻¹ by
      ext i
      simp [σ]]
    simp [σ]
  rw [← hsign]
  change ((Equiv.Perm.sign σ : K) * _) * ((Equiv.Perm.sign σ : K) * _) = _
  rw [show ((Equiv.Perm.sign σ : K) * _) * ((Equiv.Perm.sign σ : K) * _) =
      ((Equiv.Perm.sign σ : K) * (Equiv.Perm.sign σ : K)) *
        ((rectangularSchurToeplitz h (n - 1) (c + 1)).det *
          (rectangularSchurToeplitz h (n + 1) (c + 1)).det) by ring]
  rw [hs, one_mul]

/-- The all-rank rectangular Jacobi--Trudi Q-system at every nonzero central amplitude.  The
nonvanishing hypothesis is exactly what is available on the hypertranscendental generic section. -/
theorem horizonAmplitude_qSystem_of_center_ne_zero
    {K : Type*} [Field K] (h : ℕ → K) (c n : ℕ) (hn : 0 < n)
    (hcenter : horizonAmplitude h c n ≠ 0) :
    horizonAmplitude h (c + 1) n ^ 2 =
      horizonAmplitude h (c + 1) (n - 1) *
          horizonAmplitude h (c + 1) (n + 1) +
        horizonAmplitude h c n * horizonAmplitude h (c + 2) n := by
  let D := horizonCenter h c n
  let B := horizonRightBorder h c n
  let C := horizonBottomBorder h c n
  let E := horizonCorners h c n
  have hDdet : D.det ≠ 0 := by
    simpa [D, horizonCenter_det] using hcenter
  letI : Invertible D := Matrix.invertibleOfIsUnitDet D
    (isUnit_iff_ne_zero.mpr hDdet)
  have hdj := det_fromBlocks_twoBorder_mul_center D B C E
  dsimp [D, B, C, E] at hdj
  rw [← borderedHorizonMatrix_eq_fromBlocks,
    borderedHorizonMatrix_det, horizonCenter_det,
    topPrincipalBorderMinor_eq,
    Matrix.det_submatrix_equiv_self,
    bottomPrincipalBorderMinor_eq,
    Matrix.det_submatrix_equiv_self] at hdj
  have hcross :
      (twoBorderMinor D B C E 0 1).det *
        (twoBorderMinor D B C E 1 0).det =
      horizonAmplitude h (c + 1) (n - 1) *
        horizonAmplitude h (c + 1) (n + 1) := by
    simpa [D, B, C, E] using crossedBorderMinors_det_mul h c n hn
  rw [hcross] at hdj
  simp only [horizonAmplitude] at hdj ⊢
  linear_combination -hdj

@[simp]
theorem horizonAmplitude_zero_rank
    {K : Type*} [CommRing K] (h : ℕ → K) (n : ℕ) :
    horizonAmplitude h 0 n = 1 := by
  simp [horizonAmplitude]

theorem horizonAmplitude_zero_depth
    {K : Type*} [CommRing K] (h : ℕ → K) (m : ℕ) (h0 : h 0 = 1) :
    horizonAmplitude h m 0 = 1 := by
  let M := rectangularSchurToeplitz h 0 m
  have htri : M.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hji : (i : ℕ) < (j : ℕ) := by exact hij
    simp [M, rectangularSchurToeplitz, show ¬(j : ℕ) ≤ (i : ℕ) by omega]
  rw [horizonAmplitude, show rectangularSchurToeplitz h 0 m = M by rfl,
    Matrix.det_of_lowerTriangular M htri]
  simp [M, rectangularSchurToeplitz, h0]

noncomputable def horizonAmplitudePolynomial
    (F : Type*) [Field F] (m n : ℕ) : MvPolynomial ℕ F :=
  horizonAmplitude (MvPolynomial.X : ℕ → MvPolynomial ℕ F) m n

theorem horizonAmplitudePolynomial_ne_zero
    (F : Type*) [Field F] (m n : ℕ) :
    horizonAmplitudePolynomial F m n ≠ 0 := by
  let δ : ℕ → F := fun k => if k = n then 1 else 0
  let ev : MvPolynomial ℕ F →+* F := MvPolynomial.eval δ
  let M := rectangularSchurToeplitz
    (MvPolynomial.X : ℕ → MvPolynomial ℕ F) n m
  have hmap : M.map ev = (1 : Matrix (Fin m) (Fin m) F) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [M, ev, δ, rectangularSchurToeplitz]
    · simp only [M, Matrix.map_apply, rectangularSchurToeplitz]
      split_ifs with hle
      · rw [MvPolynomial.eval_X]
        have hindex : n + (i : ℕ) - (j : ℕ) ≠ n := by
          intro heq
          apply hij
          apply Fin.ext
          omega
        simp [δ, hindex, hij]
      · simp [hij]
  intro hp
  have hdet := ev.map_det M
  change ev M.det = (M.map ev).det at hdet
  rw [hmap, Matrix.det_one] at hdet
  have hevzero : ev (horizonAmplitudePolynomial F m n) = 0 := by rw [hp, map_zero]
  rw [horizonAmplitudePolynomial, horizonAmplitude] at hevzero
  change ev M.det = 0 at hevzero
  rw [hdet] at hevzero
  exact one_ne_zero hevzero

theorem aeval_horizonAmplitudePolynomial
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (h : ℕ → E) (m n : ℕ) :
    MvPolynomial.aeval h (horizonAmplitudePolynomial F m n) =
      horizonAmplitude h m n := by
  rw [horizonAmplitudePolynomial, horizonAmplitude, horizonAmplitude]
  rw [AlgHom.map_det]
  congr 1
  ext i j
  by_cases hle : (j : ℕ) ≤ n + (i : ℕ)
  · simp [rectangularSchurToeplitz, hle]
  · simp [rectangularSchurToeplitz, hle]

theorem horizonAmplitude_ne_zero_of_algebraicIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (h : ℕ → E) (hai : AlgebraicIndependent F h) (m n : ℕ) :
    horizonAmplitude h m n ≠ 0 := by
  intro hz
  have hinj : Function.Injective
      (MvPolynomial.aeval h : MvPolynomial ℕ F → E) :=
    algebraicIndependent_iff_injective_aeval.mp hai
  have heval :
      MvPolynomial.aeval h (horizonAmplitudePolynomial F m n) =
        MvPolynomial.aeval h (0 : MvPolynomial ℕ F) := by
    rw [aeval_horizonAmplitudePolynomial, hz, map_zero]
  exact horizonAmplitudePolynomial_ne_zero F m n (hinj heval)

theorem adjoin_range_lift_eq_top
    {F E I : Type*} [Field F] [Field E] [Algebra F E]
    (x y : I → E)
    (hspan : IntermediateField.adjoin F (Set.range x) =
      IntermediateField.adjoin F (Set.range y)) :
    let A := IntermediateField.adjoin F (Set.range x)
    let yA : I → A := fun i =>
      ⟨y i, by
        change y i ∈ IntermediateField.adjoin F (Set.range x)
        rw [hspan]
        exact IntermediateField.subset_adjoin F _ (Set.mem_range_self i)⟩
    IntermediateField.adjoin F (Set.range yA) = ⊤ := by
  dsimp only
  let A := IntermediateField.adjoin F (Set.range x)
  let yA : I → A := fun i =>
    ⟨y i, by
      change y i ∈ IntermediateField.adjoin F (Set.range x)
      rw [hspan]
      exact IntermediateField.subset_adjoin F _ (Set.mem_range_self i)⟩
  let J := IntermediateField.adjoin F (Set.range yA)
  apply top_unique
  intro a ha
  change a ∈ J
  have hay : (a : E) ∈ IntermediateField.adjoin F (Set.range y) := by
    rw [← hspan]
    exact a.property
  let p : ∀ z, z ∈ IntermediateField.adjoin F (Set.range y) → Prop :=
    fun z hz => (⟨z, by
      change z ∈ IntermediateField.adjoin F (Set.range x)
      rw [hspan]
      exact hz⟩ : A) ∈ J
  change p (a : E) hay
  refine IntermediateField.adjoin_induction F (p := p) ?_ ?_ ?_ ?_ ?_ hay
  · intro z hz
    obtain ⟨i, rfl⟩ := hz
    simpa [p, J, yA] using
      (IntermediateField.subset_adjoin F (Set.range yA) (Set.mem_range_self i))
  · intro z
    simp [p, J, A]
  · intro z w hz hw hzJ hwJ
    simpa only [p, Subtype.coe_eta] using J.add_mem hzJ hwJ
  · intro z hz hzJ
    simpa only [p, Subtype.coe_eta] using J.inv_mem hzJ
  · intro z w hz hw hzJ hwJ
    simpa only [p, Subtype.coe_eta] using J.mul_mem hzJ hwJ

theorem isAlgebraic_adjoin_of_intermediate_adjoin_eq_top
    {F A I : Type*} [Field F] [Field A] [Algebra F A]
    (y : I → A)
    (htop : IntermediateField.adjoin F (Set.range y) = ⊤) :
    Algebra.IsAlgebraic (Algebra.adjoin F (Set.range y)) A := by
  apply (IntermediateField.isAlgebraic_adjoin_iff_top
    (F := F) (s := Set.range y) (S := A)).mp
  constructor
  intro a
  let B := IntermediateField.adjoin F (Set.range y)
  let b : B := ⟨a, by
    change a ∈ IntermediateField.adjoin F (Set.range y)
    rw [htop]
    trivial⟩
  have hab : algebraMap B A b = a := rfl
  rw [← hab]
  exact isAlgebraic_algebraMap (R := B) (A := A) b

theorem algebraicIndependent_of_adjoin_eq_of_finite
    {F E I : Type*} [Field F] [Field E] [Algebra F E]
    [Finite I] (x y : I → E) (hx : AlgebraicIndependent F x)
    (hspan : IntermediateField.adjoin F (Set.range x) =
      IntermediateField.adjoin F (Set.range y)) :
    AlgebraicIndependent F y := by
  let A := IntermediateField.adjoin F (Set.range x)
  let xA : I → A := fun i =>
    ⟨x i, IntermediateField.subset_adjoin F _ (Set.mem_range_self i)⟩
  let yA : I → A := fun i =>
    ⟨y i, by
      change y i ∈ IntermediateField.adjoin F (Set.range x)
      rw [hspan]
      exact IntermediateField.subset_adjoin F _ (Set.mem_range_self i)⟩
  have hxA : AlgebraicIndependent F xA := by
    apply AlgebraicIndependent.of_comp (A.val : A →ₐ[F] E)
    simpa only [Function.comp_apply, A, xA] using hx
  have hxTop : IntermediateField.adjoin F (Set.range xA) = ⊤ := by
    simpa [A, xA] using adjoin_range_lift_eq_top x x rfl
  have hyTop : IntermediateField.adjoin F (Set.range yA) = ⊤ := by
    simpa [A, yA] using adjoin_range_lift_eq_top x y hspan
  have hxBasis : IsTranscendenceBasis F xA := by
    apply hxA.isTranscendenceBasis_iff_isAlgebraic.mpr
    exact isAlgebraic_adjoin_of_intermediate_adjoin_eq_top xA hxTop
  letI : Algebra.IsAlgebraic (Algebra.adjoin F (Set.range yA)) A :=
    isAlgebraic_adjoin_of_intermediate_adjoin_eq_top yA hyTop
  have hyBasis : IsTranscendenceBasis F yA :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite F yA (by
      rw [← hxBasis.lift_cardinalMk_eq_trdeg])
  have hyA : AlgebraicIndependent F yA := hyBasis.1
  have hval : ((A.val : A →ₐ[F] E) ∘ yA) = y := by
    funext i
    rfl
  rw [← hval]
  exact hyA.map (A.val.injective.injOn)

noncomputable def normalizedFiniteJet
    {E : Type*} [Field E] {L : ℕ} (x : Fin (L + 1) → E) :
    Fin (L + 1) → E := fun i =>
  if (i : ℕ) = 0 then x 0 else x i / x 0

theorem adjoin_normalizedFiniteJet_eq
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {L : ℕ} (x : Fin (L + 1) → E) (hx0 : x 0 ≠ 0) :
    IntermediateField.adjoin F (Set.range x) =
      IntermediateField.adjoin F (Set.range (normalizedFiniteJet x)) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    obtain ⟨i, rfl⟩ := hz
    let J := IntermediateField.adjoin F (Set.range (normalizedFiniteJet x))
    have hi : normalizedFiniteJet x i ∈ J :=
      IntermediateField.subset_adjoin F _ (Set.mem_range_self i)
    have hzero : normalizedFiniteJet x 0 ∈ J :=
      IntermediateField.subset_adjoin F _ (Set.mem_range_self 0)
    by_cases hi0 : (i : ℕ) = 0
    · have hii : i = 0 := Fin.ext hi0
      subst i
      simpa [normalizedFiniteJet] using hzero
    · have hmul := J.mul_mem hi hzero
      convert hmul using 1
      simp [normalizedFiniteJet, hi0, hx0]
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    obtain ⟨i, rfl⟩ := hz
    let J := IntermediateField.adjoin F (Set.range x)
    have hi : x i ∈ J := IntermediateField.subset_adjoin F _ (Set.mem_range_self i)
    have hzero : x 0 ∈ J := IntermediateField.subset_adjoin F _ (Set.mem_range_self 0)
    by_cases hi0 : (i : ℕ) = 0
    · simpa [normalizedFiniteJet, hi0] using hzero
    · simpa [normalizedFiniteJet, hi0] using J.div_mem hi hzero

theorem normalizedFiniteJet_algebraicIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {L : ℕ} (x : Fin (L + 1) → E) (hx : AlgebraicIndependent F x)
    (hx0 : x 0 ≠ 0) :
    AlgebraicIndependent F (normalizedFiniteJet x) :=
  algebraicIndependent_of_adjoin_eq_of_finite x (normalizedFiniteJet x) hx
    (adjoin_normalizedFiniteJet_eq x hx0)

noncomputable def normalizedPositiveFiniteJet
    {E : Type*} [Field E] {L : ℕ} (x : Fin (L + 1) → E) : Fin L → E :=
  fun i => normalizedFiniteJet x i.succ

theorem normalizedPositiveFiniteJet_algebraicIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {L : ℕ} (x : Fin (L + 1) → E) (hx : AlgebraicIndependent F x)
    (hx0 : x 0 ≠ 0) :
    AlgebraicIndependent F (normalizedPositiveFiniteJet x) := by
  have hfull := normalizedFiniteJet_algebraicIndependent x hx hx0
  exact hfull.comp Fin.succ (Fin.succ_injective _)

/-- The finite unit polynomial with prescribed positive coefficients. -/
noncomputable def finiteUnitPolynomial
    {E : Type*} [Field E] {L : ℕ} (u : Fin L → E) : Polynomial E :=
  1 + ∑ i : Fin L, Polynomial.monomial ((i : ℕ) + 1) (u i)

@[simp]
theorem finiteUnitPolynomial_coeff_zero
    {E : Type*} [Field E] {L : ℕ} (u : Fin L → E) :
    (finiteUnitPolynomial u).coeff 0 = 1 := by
  simp [finiteUnitPolynomial]

@[simp]
theorem finiteUnitPolynomial_coeff_succ
    {E : Type*} [Field E] {L : ℕ} (u : Fin L → E) (i : Fin L) :
    (finiteUnitPolynomial u).coeff ((i : ℕ) + 1) = u i := by
  rw [finiteUnitPolynomial, Polynomial.coeff_add, Polynomial.coeff_one,
    if_neg (Nat.succ_ne_zero _), zero_add]
  change (Polynomial.lcoeff E ((i : ℕ) + 1))
    (∑ j : Fin L, Polynomial.monomial ((j : ℕ) + 1) (u j)) = u i
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · rw [show (Polynomial.lcoeff E ((i : ℕ) + 1))
        (Polynomial.monomial ((i : ℕ) + 1) (u i)) = u i by
      change (Polynomial.monomial ((i : ℕ) + 1) (u i)).coeff
        ((i : ℕ) + 1) = u i
      simp]
  · intro j hj hji
    change (Polynomial.monomial ((j : ℕ) + 1) (u j)).coeff
      ((i : ℕ) + 1) = 0
    rw [Polynomial.coeff_monomial, if_neg]
    intro heq
    apply hji
    apply Fin.ext
    omega
  · simp

/-- Every coefficient of a polynomial belongs to a fixed intermediate field. -/
def PolynomialCoefficientsIn
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (J : IntermediateField F E) (P : Polynomial E) : Prop :=
  ∀ k, P.coeff k ∈ J

theorem polynomialCoefficientsIn_one
    {F E : Type*} [Field F] [Field E] [Algebra F E]
  (J : IntermediateField F E) : PolynomialCoefficientsIn J 1 := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs
  · exact J.one_mem
  · exact J.zero_mem

theorem PolynomialCoefficientsIn.sub
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {J : IntermediateField F E} {P Q : Polynomial E}
    (hP : PolynomialCoefficientsIn J P) (hQ : PolynomialCoefficientsIn J Q) :
    PolynomialCoefficientsIn J (P - Q) := by
  intro k
  rw [Polynomial.coeff_sub]
  exact J.sub_mem (hP k) (hQ k)

theorem PolynomialCoefficientsIn.neg
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {J : IntermediateField F E} {P : Polynomial E}
    (hP : PolynomialCoefficientsIn J P) : PolynomialCoefficientsIn J (-P) := by
  intro k
  rw [Polynomial.coeff_neg]
  exact J.neg_mem (hP k)

theorem PolynomialCoefficientsIn.mul
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {J : IntermediateField F E} {P Q : Polynomial E}
    (hP : PolynomialCoefficientsIn J P) (hQ : PolynomialCoefficientsIn J Q) :
    PolynomialCoefficientsIn J (P * Q) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact J.sum_mem fun ij hij => J.mul_mem (hP ij.1) (hQ ij.2)

theorem PolynomialCoefficientsIn.pow
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {J : IntermediateField F E} {P : Polynomial E}
    (hP : PolynomialCoefficientsIn J P) (r : ℕ) :
    PolynomialCoefficientsIn J (P ^ r) := by
  induction r with
  | zero => simpa using polynomialCoefficientsIn_one J
  | succ r ihr => simpa [pow_succ] using ihr.mul hP

theorem PolynomialCoefficientsIn.sum
    {F E I : Type*} [Field F] [Field E] [Algebra F E]
    {J : IntermediateField F E} {s : Finset I} {P : I → Polynomial E}
    (hP : ∀ i ∈ s, PolynomialCoefficientsIn J (P i)) :
    PolynomialCoefficientsIn J (∑ i ∈ s, P i) := by
  intro k
  change (Polynomial.lcoeff E k) (∑ i ∈ s, P i) ∈ J
  rw [map_sum]
  exact J.sum_mem fun i hi => hP i hi k

theorem finiteUnitPolynomial_coefficientsIn_adjoin
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {L : ℕ} (u : Fin L → E) :
    PolynomialCoefficientsIn (IntermediateField.adjoin F (Set.range u))
      (finiteUnitPolynomial u) := by
  intro k
  rw [finiteUnitPolynomial, Polynomial.coeff_add, Polynomial.coeff_one]
  apply IntermediateField.add_mem
  · split_ifs
    · exact (IntermediateField.adjoin F (Set.range u)).one_mem
    · exact (IntermediateField.adjoin F (Set.range u)).zero_mem
  · change (Polynomial.lcoeff E k)
      (∑ i : Fin L, Polynomial.monomial ((i : ℕ) + 1) (u i)) ∈ _
    rw [map_sum]
    apply IntermediateField.sum_mem
    intro i hi
    change (Polynomial.monomial ((i : ℕ) + 1) (u i)).coeff k ∈ _
    rw [Polynomial.coeff_monomial]
    split_ifs
    · exact IntermediateField.subset_adjoin F _ (Set.mem_range_self i)
    · exact (IntermediateField.adjoin F (Set.range u)).zero_mem

theorem truncatedReciprocalKernel_coefficientsIn
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E]
    {J : IntermediateField F E} (N : ℕ) (U : Polynomial E)
    (hU : PolynomialCoefficientsIn J U) :
    PolynomialCoefficientsIn J (truncatedReciprocalKernel N U) := by
  rw [truncatedReciprocalKernel]
  apply PolynomialCoefficientsIn.sum
  intro j hj
  exact (hU.sub (polynomialCoefficientsIn_one J)).neg.pow j

/-- Positive coefficients of the reciprocal of a finite unit jet, through the same horizon. -/
noncomputable def finiteReciprocalPositive
    {E : Type*} [Field E] [CharZero E] {L : ℕ} (u : Fin L → E) : Fin L → E :=
  fun i => (truncatedReciprocalKernel (L + 1) (finiteUnitPolynomial u)).coeff
    ((i : ℕ) + 1)

theorem adjoin_finiteReciprocalPositive_le
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E]
    {L : ℕ} (u : Fin L → E) :
    IntermediateField.adjoin F (Set.range (finiteReciprocalPositive u)) ≤
      IntermediateField.adjoin F (Set.range u) := by
  rw [IntermediateField.adjoin_le_iff]
  intro z hz
  obtain ⟨i, rfl⟩ := hz
  exact truncatedReciprocalKernel_coefficientsIn (L + 1) (finiteUnitPolynomial u)
    (finiteUnitPolynomial_coefficientsIn_adjoin u) ((i : ℕ) + 1)

theorem X_pow_dvd_mul_sub_of_coeff_eq
    {E : Type*} [Field E] (N : ℕ) (U V Y : Polynomial E)
    (hInv : Polynomial.X ^ N ∣ U * Y - 1)
    (hcoeff : ∀ k < N, V.coeff k = Y.coeff k) :
    Polynomial.X ^ N ∣ U * V - 1 := by
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  have hy := (Polynomial.X_pow_dvd_iff.mp hInv) k hk
  simp only [Polynomial.coeff_sub] at hy ⊢
  suffices (U * V).coeff k = (U * Y).coeff k by simpa [this] using hy
  simp only [Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  congr 1
  apply hcoeff
  have hs := Finset.mem_antidiagonal.mp hij
  omega

theorem inverse_mod_coeff_unique
    {E : Type*} [Field E] (N : ℕ) (U Y Z : Polynomial E)
    (hU : U.coeff 0 = 1)
    (hY : Polynomial.X ^ N ∣ U * Y - 1)
    (hZ : Polynomial.X ^ N ∣ U * Z - 1)
    {k : ℕ} (hk : k < N) : Y.coeff k = Z.coeff k := by
  have hmul : Polynomial.X ^ N ∣ U * (Y - Z) := by
    rw [show U * (Y - Z) = (U * Y - 1) - (U * Z - 1) by ring]
    exact dvd_sub hY hZ
  have hcop : IsCoprime (Polynomial.X ^ N) U :=
    (isCoprime_of_coeff_zero_eq_one U hU).pow_right.symm
  have hdiff : Polynomial.X ^ N ∣ Y - Z := hcop.dvd_of_dvd_mul_left hmul
  have hz := (Polynomial.X_pow_dvd_iff.mp hdiff) k hk
  rw [Polynomial.coeff_sub] at hz
  exact sub_eq_zero.mp hz

theorem truncatedReciprocalKernel_coeff_zero
    {E : Type*} [Field E] [CharZero E] (N : ℕ) (hN : 0 < N)
    (U : Polynomial E) (hU : U.coeff 0 = 1) :
    (truncatedReciprocalKernel N U).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  change (Polynomial.evalRingHom 0) (truncatedReciprocalKernel N U) = 1
  rw [truncatedReciprocalKernel, map_sum]
  simp [← Polynomial.coeff_zero_eq_eval_zero, hU, hN.ne']

theorem finiteUnitPolynomial_reciprocal_coeff
    {E : Type*} [Field E] [CharZero E] {L : ℕ} (u : Fin L → E) (k : ℕ)
    (hk : k < L + 1) :
    (finiteUnitPolynomial (finiteReciprocalPositive u)).coeff k =
      (truncatedReciprocalKernel (L + 1) (finiteUnitPolynomial u)).coeff k := by
  rcases k with _ | k
  · rw [finiteUnitPolynomial_coeff_zero,
      truncatedReciprocalKernel_coeff_zero (L + 1) (by omega)
        (finiteUnitPolynomial u) (finiteUnitPolynomial_coeff_zero u)]
  · have hkL : k < L := by omega
    let i : Fin L := ⟨k, hkL⟩
    simpa [i, finiteReciprocalPositive] using
      finiteUnitPolynomial_coeff_succ (finiteReciprocalPositive u) i

theorem adjoin_finiteReciprocalPositive_eq
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E]
    {L : ℕ} (u : Fin L → E) :
    IntermediateField.adjoin F (Set.range (finiteReciprocalPositive u)) =
      IntermediateField.adjoin F (Set.range u) := by
  apply le_antisymm (adjoin_finiteReciprocalPositive_le u)
  rw [IntermediateField.adjoin_le_iff]
  intro z hz
  obtain ⟨i, rfl⟩ := hz
  let U := finiteUnitPolynomial u
  let Y := truncatedReciprocalKernel (L + 1) U
  let V := finiteUnitPolynomial (finiteReciprocalPositive u)
  let W := truncatedReciprocalKernel (L + 1) V
  let J := IntermediateField.adjoin F (Set.range (finiteReciprocalPositive u))
  have hU0 : U.coeff 0 = 1 := finiteUnitPolynomial_coeff_zero u
  have hV0 : V.coeff 0 = 1 := finiteUnitPolynomial_coeff_zero _
  have hUY : Polynomial.X ^ (L + 1) ∣ U * Y - 1 :=
    truncatedReciprocalKernel_isInverseMod (L + 1) U hU0
  have hUV : Polynomial.X ^ (L + 1) ∣ U * V - 1 :=
    X_pow_dvd_mul_sub_of_coeff_eq (L + 1) U V Y hUY
      (finiteUnitPolynomial_reciprocal_coeff u)
  have hVW : Polynomial.X ^ (L + 1) ∣ V * W - 1 :=
    truncatedReciprocalKernel_isInverseMod (L + 1) V hV0
  have hVU : Polynomial.X ^ (L + 1) ∣ V * U - 1 := by
    simpa [mul_comm] using hUV
  have hcoeff : W.coeff ((i : ℕ) + 1) = U.coeff ((i : ℕ) + 1) :=
    inverse_mod_coeff_unique (L + 1) V W U hV0 hVW hVU (by omega)
  rw [← finiteUnitPolynomial_coeff_succ u i, ← hcoeff]
  exact truncatedReciprocalKernel_coefficientsIn (L + 1) V
    (finiteUnitPolynomial_coefficientsIn_adjoin (finiteReciprocalPositive u))
    ((i : ℕ) + 1)

theorem finiteReciprocalPositive_algebraicIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E]
    {L : ℕ} (u : Fin L → E) (hu : AlgebraicIndependent F u) :
    AlgebraicIndependent F (finiteReciprocalPositive u) :=
  algebraicIndependent_of_adjoin_eq_of_finite u (finiteReciprocalPositive u) hu
    (adjoin_finiteReciprocalPositive_eq u).symm

/-- The positive coefficients of the square of a finite unit series. -/
noncomputable def finiteUnitSquarePositive
    {E : Type*} [Field E] {L : ℕ} (z : Fin L → E) : Fin L → E :=
  fun i => ((finiteUnitPolynomial z) ^ 2).coeff ((i : ℕ) + 1)

theorem finiteUnitSquarePositive_zero
    {E : Type*} [Field E] {L : ℕ} (z : Fin L → E) (hL : 0 < L) :
    finiteUnitSquarePositive z ⟨0, hL⟩ = 2 * z ⟨0, hL⟩ := by
  rw [finiteUnitSquarePositive, pow_two, Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_succ]
  simp [finiteUnitPolynomial_coeff_zero]
  rw [show (finiteUnitPolynomial z).coeff 1 = z ⟨0, hL⟩ by
    simpa using finiteUnitPolynomial_coeff_succ z ⟨0, hL⟩]
  ring

theorem finiteUnitSquarePositive_succ
    {E : Type*} [Field E] {L k : ℕ} (z : Fin L → E) (hk : k + 1 < L) :
    finiteUnitSquarePositive z ⟨k + 1, hk⟩ =
      2 * z ⟨k + 1, hk⟩ +
        ∑ p ∈ Finset.antidiagonal k,
          (finiteUnitPolynomial z).coeff (p.1 + 1) *
            (finiteUnitPolynomial z).coeff (p.2 + 1) := by
  rw [finiteUnitSquarePositive, pow_two, Polynomial.coeff_mul]
  rw [show (k + 1 : ℕ) + 1 = k + 2 by omega,
    Finset.Nat.antidiagonal_succ_succ']
  simp only [Finset.sum_cons, Finset.sum_map]
  rw [finiteUnitPolynomial_coeff_zero]
  rw [show (finiteUnitPolynomial z).coeff (k + 2) = z ⟨k + 1, hk⟩ by
    simpa using finiteUnitPolynomial_coeff_succ z ⟨k + 1, hk⟩]
  ring_nf
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  change (finiteUnitPolynomial z).coeff (p.1 + 1) *
      (finiteUnitPolynomial z).coeff (p.2 + 1) = _
  simp [Nat.add_comm]

theorem adjoin_finiteUnitSquarePositive_le
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {L : ℕ} (z : Fin L → E) :
    IntermediateField.adjoin F (Set.range (finiteUnitSquarePositive z)) ≤
      IntermediateField.adjoin F (Set.range z) := by
  rw [IntermediateField.adjoin_le_iff]
  intro a ha
  obtain ⟨i, rfl⟩ := ha
  exact (finiteUnitPolynomial_coefficientsIn_adjoin z).pow 2 ((i : ℕ) + 1)

theorem adjoin_finiteUnitSquarePositive_eq
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E]
    {L : ℕ} (z : Fin L → E) :
    IntermediateField.adjoin F (Set.range (finiteUnitSquarePositive z)) =
      IntermediateField.adjoin F (Set.range z) := by
  apply le_antisymm (adjoin_finiteUnitSquarePositive_le z)
  let J := IntermediateField.adjoin F (Set.range (finiteUnitSquarePositive z))
  have htwo : (2 : E) ∈ J := by
    (convert J.add_mem J.one_mem J.one_mem using 1; norm_num)
  have htwo0 : (2 : E) ≠ 0 := by norm_num
  have hzmem : ∀ k (hk : k < L), z ⟨k, hk⟩ ∈ J := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        rcases k with _ | k
        · have hsq : finiteUnitSquarePositive z ⟨0, hk⟩ ∈ J :=
            IntermediateField.subset_adjoin F _
              (Set.mem_range_self (⟨0, hk⟩ : Fin L))
          have hrel := finiteUnitSquarePositive_zero z hk
          have hsolve : z ⟨0, hk⟩ = (2 : E)⁻¹ *
              finiteUnitSquarePositive z ⟨0, hk⟩ := by
            rw [hrel]
            field_simp
          rw [hsolve]
          exact J.mul_mem (J.inv_mem htwo) hsq
        · have hsq : finiteUnitSquarePositive z ⟨k + 1, hk⟩ ∈ J :=
            IntermediateField.subset_adjoin F _
              (Set.mem_range_self (⟨k + 1, hk⟩ : Fin L))
          let S : E := ∑ p ∈ Finset.antidiagonal k,
            (finiteUnitPolynomial z).coeff (p.1 + 1) *
              (finiteUnitPolynomial z).coeff (p.2 + 1)
          have hS : S ∈ J := by
            apply J.sum_mem
            intro p hp
            apply J.mul_mem
            · rw [show (finiteUnitPolynomial z).coeff (p.1 + 1) =
                  z ⟨p.1, by
                    have hp1 := Finset.antidiagonal.fst_le hp
                    omega⟩ by
                simpa using finiteUnitPolynomial_coeff_succ z
                  ⟨p.1, by
                    have hp1 := Finset.antidiagonal.fst_le hp
                    omega⟩]
              exact ih p.1 (by
                have hp1 := Finset.antidiagonal.fst_le hp
                omega) (by
                have hp1 := Finset.antidiagonal.fst_le hp
                omega)
            · rw [show (finiteUnitPolynomial z).coeff (p.2 + 1) =
                  z ⟨p.2, by
                    have hp2 := Finset.antidiagonal.snd_le hp
                    omega⟩ by
                simpa using finiteUnitPolynomial_coeff_succ z
                  ⟨p.2, by
                    have hp2 := Finset.antidiagonal.snd_le hp
                    omega⟩]
              exact ih p.2 (by
                have hp2 := Finset.antidiagonal.snd_le hp
                omega) (by
                have hp2 := Finset.antidiagonal.snd_le hp
                omega)
          have hrel := finiteUnitSquarePositive_succ z hk
          have hsolve : z ⟨k + 1, hk⟩ = (2 : E)⁻¹ *
              (finiteUnitSquarePositive z ⟨k + 1, hk⟩ - S) := by
            rw [hrel]
            dsimp only [S]
            field_simp
            ring
          rw [hsolve]
          exact J.mul_mem (J.inv_mem htwo) (J.sub_mem hsq hS)
  rw [IntermediateField.adjoin_le_iff]
  intro a ha
  obtain ⟨i, rfl⟩ := ha
  exact hzmem i i.isLt

theorem finiteUnitSquarePositive_algebraicIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E]
    {L : ℕ} (z : Fin L → E) (hz : AlgebraicIndependent F z) :
    AlgebraicIndependent F (finiteUnitSquarePositive z) :=
  algebraicIndependent_of_adjoin_eq_of_finite z (finiteUnitSquarePositive z) hz
    (adjoin_finiteUnitSquarePositive_eq z).symm

/-- The normalized reciprocal-square positive jet attached to a finite unit raw jet. -/
noncomputable def finiteReciprocalSquarePositive
    {E : Type*} [Field E] [CharZero E] {L : ℕ} (u : Fin L → E) : Fin L → E :=
  finiteUnitSquarePositive (finiteReciprocalPositive u)

theorem finiteReciprocalSquarePositive_algebraicIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E]
    {L : ℕ} (u : Fin L → E) (hu : AlgebraicIndependent F u) :
    AlgebraicIndependent F (finiteReciprocalSquarePositive u) :=
  finiteUnitSquarePositive_algebraicIndependent (finiteReciprocalPositive u)
    (finiteReciprocalPositive_algebraicIndependent u hu)

/-- Adjoin the unit constant coefficient to a finite positive jet and extend by zero. -/
noncomputable def unitConstantSeries
    {E : Type*} [CommRing E] {L : ℕ} (u : Fin L → E) : ℕ → E
  | 0 => 1
  | k + 1 => if hk : k < L then u ⟨k, hk⟩ else 0

@[simp]
theorem unitConstantSeries_zero
    {E : Type*} [CommRing E] {L : ℕ} (u : Fin L → E) :
    unitConstantSeries u 0 = 1 := rfl

@[simp]
theorem unitConstantSeries_succ
    {E : Type*} [CommRing E] {L k : ℕ} (u : Fin L → E) (hk : k < L) :
    unitConstantSeries u (k + 1) = u ⟨k, hk⟩ := by
  simp [unitConstantSeries, hk]

noncomputable def positiveHorizonAmplitude
    {E : Type*} [CommRing E] {L : ℕ} (u : Fin L → E) (m n : ℕ) : E :=
  horizonAmplitude (unitConstantSeries u) m n

noncomputable def positiveHorizonAmplitudePolynomial
    (F : Type*) [Field F] (m n : ℕ) : MvPolynomial (Fin (m + n)) F :=
  positiveHorizonAmplitude (MvPolynomial.X :
    Fin (m + n) → MvPolynomial (Fin (m + n)) F) m n

theorem eval_unitConstantSeries_X
    (F : Type*) [Field F] {L : ℕ} (δ : Fin L → F) (k : ℕ) :
    MvPolynomial.eval δ
        (unitConstantSeries (MvPolynomial.X :
          Fin L → MvPolynomial (Fin L) F) k) =
      unitConstantSeries δ k := by
  rcases k with _ | k
  · simp
  · by_cases hk : k < L
    · simp [unitConstantSeries, hk]
    · simp [unitConstantSeries, hk]

theorem aeval_unitConstantSeries_X
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {L : ℕ} (u : Fin L → E) (k : ℕ) :
    MvPolynomial.aeval u
        (unitConstantSeries (MvPolynomial.X :
          Fin L → MvPolynomial (Fin L) F) k) =
      unitConstantSeries u k := by
  rcases k with _ | k
  · simp
  · by_cases hk : k < L
    · simp [unitConstantSeries, hk]
    · simp [unitConstantSeries, hk]

private theorem positiveHorizonAmplitudePolynomial_ne_zero_of_pos
    (F : Type*) [Field F] (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    positiveHorizonAmplitudePolynomial F m n ≠ 0 := by
  let δ : Fin (m + n) → F := fun i =>
    if (i : ℕ) + 1 = n then 1 else 0
  let ev : MvPolynomial (Fin (m + n)) F →+* F := MvPolynomial.eval δ
  let H := unitConstantSeries δ
  let M := rectangularSchurToeplitz H n m
  have htri : M.BlockTriangular id := by
    intro i j hji
    have hji' : (j : ℕ) < (i : ℕ) := hji
    simp only [M, rectangularSchurToeplitz]
    rw [if_pos (by omega)]
    have hindex : n + (i : ℕ) - (j : ℕ) =
        (n + (i : ℕ) - (j : ℕ) - 1) + 1 := by omega
    rw [hindex]
    simp only [H, unitConstantSeries]
    rw [dif_pos (by omega)]
    simp [δ]
    omega
  have hdiag : ∀ i : Fin m, M i i = 1 := by
    intro i
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    simp [M, H, δ, rectangularSchurToeplitz, unitConstantSeries]
    omega
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_upperTriangular htri]
    simp [hdiag]
  have hmap :
      (rectangularSchurToeplitz
        (unitConstantSeries (MvPolynomial.X :
          Fin (m + n) → MvPolynomial (Fin (m + n)) F)) n m).map ev = M := by
    ext i j
    simp only [M, H, Matrix.map_apply, rectangularSchurToeplitz]
    by_cases hle : (j : ℕ) ≤ n + (i : ℕ)
    · rw [if_pos hle, if_pos hle]
      exact eval_unitConstantSeries_X F δ (n + (i : ℕ) - (j : ℕ))
    · rw [if_neg hle, if_neg hle, map_zero]
  intro hp
  have hev := ev.map_det
    (rectangularSchurToeplitz
      (unitConstantSeries (MvPolynomial.X :
        Fin (m + n) → MvPolynomial (Fin (m + n)) F)) n m)
  change ev _ =
    ((rectangularSchurToeplitz
      (unitConstantSeries (MvPolynomial.X :
        Fin (m + n) → MvPolynomial (Fin (m + n)) F)) n m).map ev).det at hev
  rw [hmap, hdet] at hev
  have hz : ev (positiveHorizonAmplitudePolynomial F m n) = 0 := by
    rw [hp, map_zero]
  rw [positiveHorizonAmplitudePolynomial, positiveHorizonAmplitude,
    horizonAmplitude] at hz
  rw [hev] at hz
  exact one_ne_zero hz

/-- The positive-coordinate horizon amplitude polynomial is nonzero in every rank and depth,
including the empty-rank and zero-depth boundary faces. -/
theorem positiveHorizonAmplitudePolynomial_ne_zero
    (F : Type*) [Field F] (m n : ℕ) :
    positiveHorizonAmplitudePolynomial F m n ≠ 0 := by
  by_cases hm : m = 0
  · subst m
    simp [positiveHorizonAmplitudePolynomial, positiveHorizonAmplitude,
      horizonAmplitude_zero_rank]
  by_cases hn : n = 0
  · subst n
    simp [positiveHorizonAmplitudePolynomial, positiveHorizonAmplitude,
      horizonAmplitude_zero_depth]
  exact positiveHorizonAmplitudePolynomial_ne_zero_of_pos F m n
    (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)

theorem aeval_positiveHorizonAmplitudePolynomial
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (m n : ℕ) (u : Fin (m + n) → E) :
    MvPolynomial.aeval u (positiveHorizonAmplitudePolynomial F m n) =
      positiveHorizonAmplitude u m n := by
  rw [positiveHorizonAmplitudePolynomial, positiveHorizonAmplitude,
    horizonAmplitude]
  rw [AlgHom.map_det]
  congr 1
  ext i j
  change MvPolynomial.aeval u
      (rectangularSchurToeplitz
        (unitConstantSeries (MvPolynomial.X :
          Fin (m + n) → MvPolynomial (Fin (m + n)) F)) n m i j) =
    rectangularSchurToeplitz (unitConstantSeries u) n m i j
  simp only [rectangularSchurToeplitz]
  by_cases hle : (j : ℕ) ≤ n + (i : ℕ)
  · rw [if_pos hle, if_pos hle]
    exact aeval_unitConstantSeries_X u (n + (i : ℕ) - (j : ℕ))
  · rw [if_neg hle, if_neg hle, map_zero]

theorem positiveHorizonAmplitude_ne_zero_of_algebraicIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (m n : ℕ) (u : Fin (m + n) → E) (hu : AlgebraicIndependent F u) :
    positiveHorizonAmplitude u m n ≠ 0 := by
  intro hz
  have hinj : Function.Injective
      (MvPolynomial.aeval u : MvPolynomial (Fin (m + n)) F → E) :=
    algebraicIndependent_iff_injective_aeval.mp hu
  have heval :
      MvPolynomial.aeval u (positiveHorizonAmplitudePolynomial F m n) =
        MvPolynomial.aeval u (0 : MvPolynomial (Fin (m + n)) F) := by
    rw [aeval_positiveHorizonAmplitudePolynomial m n, hz, map_zero]
  exact positiveHorizonAmplitudePolynomial_ne_zero F m n (hinj heval)

/-- The first `L` positive coefficients of a power series. -/
noncomputable def powerSeriesPositiveJet
    {E : Type*} [Field E] (P : PowerSeries E) (L : ℕ) : Fin L → E :=
  fun i => PowerSeries.coeff ((i : ℕ) + 1) P

theorem adjoin_powerSeriesInvPositive_le
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (P : PowerSeries E) (hP0 : PowerSeries.constantCoeff P = 1) (L : ℕ) :
    IntermediateField.adjoin F (Set.range (powerSeriesPositiveJet P⁻¹ L)) ≤
      IntermediateField.adjoin F (Set.range (powerSeriesPositiveJet P L)) := by
  let J := IntermediateField.adjoin F (Set.range (powerSeriesPositiveJet P L))
  have hInv0 : PowerSeries.constantCoeff P⁻¹ = 1 := by
    rw [PowerSeries.constantCoeff_inv, hP0, inv_one]
  have hmem : ∀ k (hk : k < L),
      PowerSeries.coeff (k + 1) P⁻¹ ∈ J := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        rw [PowerSeries.coeff_inv, if_neg (Nat.succ_ne_zero k), hP0,
          inv_one, neg_one_mul]
        apply J.neg_mem
        apply J.sum_mem
        intro p hp
        rcases p with ⟨a, b⟩
        split_ifs with hp2
        · apply J.mul_mem
          · rcases a with _ | r
            · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hP0]
              exact J.one_mem
            · have hrL : r < L := by
                have hp1 := Finset.antidiagonal.fst_le hp
                omega
              change powerSeriesPositiveJet P L ⟨r, hrL⟩ ∈ J
              exact IntermediateField.subset_adjoin F _
                (Set.mem_range_self (⟨r, hrL⟩ : Fin L))
          · rcases b with _ | r
            · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hInv0]
              exact J.one_mem
            · have hrk : r < k := by omega
              have hrL : r < L := by
                omega
              exact ih r hrk hrL
        · exact J.zero_mem
  rw [IntermediateField.adjoin_le_iff]
  intro a ha
  obtain ⟨i, rfl⟩ := ha
  exact hmem i i.isLt

theorem powerSeries_inv_inv_of_constantCoeff_ne
    {E : Type*} [Field E] (P : PowerSeries E)
    (hP0 : PowerSeries.constantCoeff P ≠ 0) : P⁻¹⁻¹ = P := by
  have hInv0 : PowerSeries.constantCoeff P⁻¹ ≠ 0 := by
    rw [PowerSeries.constantCoeff_inv]
    exact inv_ne_zero hP0
  apply (PowerSeries.inv_eq_iff_mul_eq_one hInv0).mpr
  exact PowerSeries.mul_inv_cancel P hP0

theorem adjoin_powerSeriesInvPositive_eq
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (P : PowerSeries E) (hP0 : PowerSeries.constantCoeff P = 1) (L : ℕ) :
    IntermediateField.adjoin F (Set.range (powerSeriesPositiveJet P⁻¹ L)) =
      IntermediateField.adjoin F (Set.range (powerSeriesPositiveJet P L)) := by
  apply le_antisymm (adjoin_powerSeriesInvPositive_le P hP0 L)
  have hInv0 : PowerSeries.constantCoeff P⁻¹ = 1 := by
    rw [PowerSeries.constantCoeff_inv, hP0, inv_one]
  have hback := adjoin_powerSeriesInvPositive_le (F := F) P⁻¹ hInv0 L
  have hinv : P⁻¹⁻¹ = P :=
    powerSeries_inv_inv_of_constantCoeff_ne P (by rw [hP0]; exact one_ne_zero)
  simpa only [hinv] using hback

theorem powerSeriesInvPositive_algebraicIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (P : PowerSeries E) (hP0 : PowerSeries.constantCoeff P = 1) (L : ℕ)
    (hP : AlgebraicIndependent F (powerSeriesPositiveJet P L)) :
    AlgebraicIndependent F (powerSeriesPositiveJet P⁻¹ L) :=
  algebraicIndependent_of_adjoin_eq_of_finite
    (powerSeriesPositiveJet P L) (powerSeriesPositiveJet P⁻¹ L) hP
    (adjoin_powerSeriesInvPositive_eq P hP0 L).symm

/-- The first `L` positive coefficients of the square of a power series. -/
noncomputable def powerSeriesSquarePositiveJet
    {E : Type*} [Field E] (P : PowerSeries E) (L : ℕ) : Fin L → E :=
  fun i => PowerSeries.coeff ((i : ℕ) + 1) (P ^ 2)

theorem powerSeriesSquarePositiveJet_eq_finite
    {E : Type*} [Field E] (P : PowerSeries E)
    (hP0 : PowerSeries.constantCoeff P = 1) (L : ℕ) :
    powerSeriesSquarePositiveJet P L =
      finiteUnitSquarePositive (powerSeriesPositiveJet P L) := by
  funext i
  rw [powerSeriesSquarePositiveJet, finiteUnitSquarePositive, pow_two, pow_two,
    PowerSeries.coeff_mul, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rcases p with ⟨a, b⟩
  congr 1
  · rcases a with _ | r
    · rw [finiteUnitPolynomial_coeff_zero,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hP0]
    · have hrL : r < L := by
        have hp1 := Finset.antidiagonal.fst_le hp
        omega
      exact (by
        simpa [powerSeriesPositiveJet] using
          (finiteUnitPolynomial_coeff_succ (powerSeriesPositiveJet P L)
            ⟨r, hrL⟩).symm)
  · rcases b with _ | r
    · rw [finiteUnitPolynomial_coeff_zero,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hP0]
    · have hrL : r < L := by
        have hp2 := Finset.antidiagonal.snd_le hp
        omega
      exact (by
        simpa [powerSeriesPositiveJet] using
          (finiteUnitPolynomial_coeff_succ (powerSeriesPositiveJet P L)
            ⟨r, hrL⟩).symm)

theorem powerSeriesSquarePositive_algebraicIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E]
    (P : PowerSeries E) (hP0 : PowerSeries.constantCoeff P = 1) (L : ℕ)
    (hP : AlgebraicIndependent F (powerSeriesPositiveJet P L)) :
    AlgebraicIndependent F (powerSeriesSquarePositiveJet P L) := by
  rw [powerSeriesSquarePositiveJet_eq_finite P hP0 L]
  exact finiteUnitSquarePositive_algebraicIndependent
    (powerSeriesPositiveJet P L) hP

/-- The normalized ordinary differential jet as one source-pure formal power series. -/
noncomputable def normalizedDifferentialJetSeries
    {E : Type*} [Field E] [Differential E] (x : E) : PowerSeries E :=
  PowerSeries.mk fun k => differentialJet k x / x

theorem normalizedDifferentialJetSeries_constantCoeff
    {E : Type*} [Field E] [Differential E] (x : E) (hx0 : x ≠ 0) :
    PowerSeries.constantCoeff (normalizedDifferentialJetSeries x) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [normalizedDifferentialJetSeries, differentialJet_zero, hx0]

theorem normalizedDifferentialJetSeries_positive_algebraicIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (L : ℕ) :
    AlgebraicIndependent F
      (powerSeriesPositiveJet (normalizedDifferentialJetSeries x) L) := by
  let v := finiteDifferentialJet x (L + 1)
  have hv : AlgebraicIndependent F v :=
    finiteDifferentialJet_algebraicIndependent_of_hypertranscendentalOver hx (L + 1)
  have hv0 : v 0 ≠ 0 := by
    intro hz
    exact (hv.transcendental 0) (by
      rw [hz]
      exact isAlgebraic_zero)
  have hn := normalizedPositiveFiniteJet_algebraicIndependent v hv hv0
  have heq : powerSeriesPositiveJet (normalizedDifferentialJetSeries x) L =
      normalizedPositiveFiniteJet v := by
    funext i
    simp [powerSeriesPositiveJet, normalizedDifferentialJetSeries,
      normalizedPositiveFiniteJet, normalizedFiniteJet, v, finiteDifferentialJet,
      differentialJet_zero]
  rwa [heq]

/-- The global normalized reciprocal-square jet `h_k = [t^k](X/X₀)⁻²`. -/
noncomputable def hypertranscendentalHorizonCoefficient
    {E : Type*} [Field E] [Differential E] (x : E) (k : ℕ) : E :=
  PowerSeries.coeff k ((normalizedDifferentialJetSeries x)⁻¹ ^ 2)

theorem hypertranscendentalHorizonCoefficient_zero
    {E : Type*} [Field E] [Differential E] (x : E) (hx0 : x ≠ 0) :
    hypertranscendentalHorizonCoefficient x 0 = 1 := by
  rw [hypertranscendentalHorizonCoefficient,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
    PowerSeries.constantCoeff_inv,
    normalizedDifferentialJetSeries_constantCoeff x hx0]
  simp

theorem hypertranscendentalHorizonPositive_algebraicIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (L : ℕ) :
    AlgebraicIndependent F (fun i : Fin L =>
      hypertranscendentalHorizonCoefficient x ((i : ℕ) + 1)) := by
  let P := normalizedDifferentialJetSeries x
  have hraw : AlgebraicIndependent F (powerSeriesPositiveJet P L) :=
    normalizedDifferentialJetSeries_positive_algebraicIndependent hx L
  have hx0 : x ≠ 0 := by
    intro hz
    exact (hypertranscendentalOver_jet_transcendental hx 0) (by
      simpa [hz, differentialJet_zero] using (isAlgebraic_zero : IsAlgebraic F (0 : E)))
  have hP0 : PowerSeries.constantCoeff P = 1 :=
    normalizedDifferentialJetSeries_constantCoeff x hx0
  have hzinv : AlgebraicIndependent F (powerSeriesPositiveJet P⁻¹ L) :=
    powerSeriesInvPositive_algebraicIndependent P hP0 L hraw
  have hPinv0 : PowerSeries.constantCoeff P⁻¹ = 1 := by
    rw [PowerSeries.constantCoeff_inv, hP0, inv_one]
  have hsquare := powerSeriesSquarePositive_algebraicIndependent
    (F := F) P⁻¹ hPinv0 L hzinv
  simpa [powerSeriesSquarePositiveJet, hypertranscendentalHorizonCoefficient, P] using hsquare

theorem horizonAmplitude_eq_positiveHorizonAmplitude
    {E : Type*} [Field E] (h : ℕ → E) (h0 : h 0 = 1) (m n : ℕ) :
    horizonAmplitude h m n =
      positiveHorizonAmplitude (fun i : Fin (m + n) => h ((i : ℕ) + 1)) m n := by
  rw [horizonAmplitude, positiveHorizonAmplitude, horizonAmplitude]
  congr 1
  ext i j
  simp only [rectangularSchurToeplitz]
  by_cases hle : (j : ℕ) ≤ n + (i : ℕ)
  · rw [if_pos hle, if_pos hle]
    rcases hindex : n + (i : ℕ) - (j : ℕ) with _ | k
    · simp [unitConstantSeries, h0]
    · have hk : k < m + n := by
        have hi := i.isLt
        omega
      simp [unitConstantSeries, hk]
  · rw [if_neg hle, if_neg hle]

/-- The normalized rectangular horizon determinant of one source. -/
noncomputable def hypertranscendentalHorizonAmplitude
    {E : Type*} [Field E] [Differential E] (x : E) (m n : ℕ) : E :=
  horizonAmplitude (hypertranscendentalHorizonCoefficient x) m n

theorem hypertranscendentalHorizonAmplitude_ne_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (m n : ℕ) :
    hypertranscendentalHorizonAmplitude x m n ≠ 0 := by
  have hx0 : x ≠ 0 := by
    intro hz
    exact (hypertranscendentalOver_jet_transcendental hx 0) (by
      simpa [hz, differentialJet_zero] using (isAlgebraic_zero : IsAlgebraic F (0 : E)))
  rw [hypertranscendentalHorizonAmplitude,
    horizonAmplitude_eq_positiveHorizonAmplitude _
      (hypertranscendentalHorizonCoefficient_zero x hx0)]
  exact positiveHorizonAmplitude_ne_zero_of_algebraicIndependent m n _
    (hypertranscendentalHorizonPositive_algebraicIndependent hx (m + n))

@[simp]
theorem hypertranscendentalHorizonAmplitude_zero_rank
    {E : Type*} [Field E] [Differential E] (x : E) (n : ℕ) :
    hypertranscendentalHorizonAmplitude x 0 n = 1 := by
  simp [hypertranscendentalHorizonAmplitude, horizonAmplitude_zero_rank]

theorem hypertranscendentalHorizonAmplitude_zero_depth
    {E : Type*} [Field E] [Differential E] (x : E) (hx0 : x ≠ 0) (m : ℕ) :
    hypertranscendentalHorizonAmplitude x m 0 = 1 := by
  rw [hypertranscendentalHorizonAmplitude]
  exact horizonAmplitude_zero_depth _ m
    (hypertranscendentalHorizonCoefficient_zero x hx0)

/-- The complete static `A∞` Q-system on the hypertranscendental section. -/
theorem hypertranscendentalHorizonAmplitude_qSystem
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (c n : ℕ) (hn : 0 < n) :
    hypertranscendentalHorizonAmplitude x (c + 1) n ^ 2 =
      hypertranscendentalHorizonAmplitude x (c + 1) (n - 1) *
          hypertranscendentalHorizonAmplitude x (c + 1) (n + 1) +
        hypertranscendentalHorizonAmplitude x c n *
          hypertranscendentalHorizonAmplitude x (c + 2) n := by
  have hcenter : hypertranscendentalHorizonAmplitude x c n ≠ 0 := by
    exact hypertranscendentalHorizonAmplitude_ne_zero hx c n
  exact horizonAmplitude_qSystem_of_center_ne_zero
    (hypertranscendentalHorizonCoefficient x) c n hn hcenter

theorem hypertranscendentalHorizonCaustic_zero_propagation
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (c n : ℕ) (hn : 0 < n)
    (hcenter : hypertranscendentalHorizonAmplitude x (c + 1) n = 0)
    (hleft : hypertranscendentalHorizonAmplitude x (c + 1) (n - 1) = 0) :
    hypertranscendentalHorizonAmplitude x c n = 0 ∨
      hypertranscendentalHorizonAmplitude x (c + 2) n = 0 := by
  exact qSystem_zero_propagation
    (hypertranscendentalHorizonAmplitude_qSystem hx c n hn) hcenter hleft

/-- The normalized mass determinant attached to a polynomial reciprocal jet. -/
noncomputable def normalizedReciprocalHorizonAmplitude
    {E : Type*} [Field E] (Y : Polynomial E) (m n : ℕ) : E :=
  horizonAmplitude
    (fun k => (normalizedPolynomial Y * normalizedPolynomial Y).coeff k) m n

theorem criticalReciprocalJacobian_det_eq_normalizedHorizonAmplitude
    {E : Type*} [Field E] (Y : Polynomial E) (m n : ℕ)
    (hY0 : Y.coeff 0 ≠ 0) :
    (criticalReciprocalJacobian Y n m).det =
      (-1 : E) ^ m * Y.coeff 0 ^ (2 * m) *
        normalizedReciprocalHorizonAmplitude Y m n := by
  let Z := normalizedPolynomial Y
  have hYZ : Polynomial.C (Y.coeff 0) * Z = Y := by
    dsimp [Z, normalizedPolynomial]
    rw [← mul_assoc, ← Polynomial.C_mul]
    simp [hY0]
  have hsq : Y * Y = Polynomial.C (Y.coeff 0 ^ 2) * (Z * Z) := by
    nth_rw 1 [← hYZ]
    nth_rw 2 [← hYZ]
    rw [show (Polynomial.C (Y.coeff 0) * Z) *
          (Polynomial.C (Y.coeff 0) * Z) =
        Polynomial.C (Y.coeff 0 ^ 2) * (Z * Z) by
      rw [pow_two, Polynomial.C_mul]
      ring]
  have hmatrix : rectangularSchurToeplitz (fun k => (Y * Y).coeff k) n m =
      Y.coeff 0 ^ 2 • rectangularSchurToeplitz (fun k => (Z * Z).coeff k) n m := by
    ext i j
    simp only [rectangularSchurToeplitz, Matrix.smul_apply, smul_eq_mul]
    split_ifs
    · rw [hsq, Polynomial.coeff_C_mul]
    · simp
  rw [criticalReciprocalJacobian_det_eq_rectangularSchur, hmatrix,
    Matrix.det_smul]
  simp only [Fintype.card_fin]
  rw [normalizedReciprocalHorizonAmplitude, horizonAmplitude]
  dsimp only [Z]
  rw [show (Y.coeff 0 ^ 2) ^ m = Y.coeff 0 ^ (2 * m) by
    rw [← pow_mul]]
  ring

end GaloisForLFunctions.HTGeometry
