import GaloisForLFunctions.HTGeometry.StokesGlobalPuiseuxWittLaw
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.BilinearForm

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.StokesSpectralWitt

noncomputable section

open Matrix

def AboveTwo {ι : Type*} (eig : ι → ℝ) : Set ι := {i | 2 < eig i}

def AtTwo {ι : Type*} (eig : ι → ℝ) : Set ι := {i | eig i = 2}

theorem secondEigenvalue_obstruction
    {n : ℕ} (hn : 2 ≤ n) (eig : Fin n → ℝ) (heig : Antitone eig)
    (hdefect : (AboveTwo eig).ncard + (AtTwo eig).ncard ≤ 1) :
    eig ⟨1, by omega⟩ ≤ 2 := by
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  change eig i₁ ≤ 2
  by_contra hnot
  have h1 : i₁ ∈ AboveTwo eig := by
    exact lt_of_not_ge hnot
  have h0value : 2 < eig i₀ :=
    lt_of_lt_of_le (show (2 : ℝ) < eig i₁ from h1)
      (heig (by simp [i₀, i₁]))
  have h0 : i₀ ∈ AboveTwo eig := h0value
  have hpair : ({i₀, i₁} : Set (Fin n)) ⊆ AboveTwo eig := by
    intro i hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with (rfl | rfl) <;> assumption
  have hcard : 2 ≤ (AboveTwo eig).ncard := by
    rw [← Set.ncard_pair (by
      intro h
      have hval := congrArg Fin.val h
      exact Nat.zero_ne_one hval : i₀ ≠ i₁)]
    exact Set.ncard_le_ncard hpair
  omega

theorem topCritical_isSimple
    {n : ℕ} (hn : 0 < n) (eig : Fin n → ℝ)
    (hdefect : (AboveTwo eig).ncard + (AtTwo eig).ncard ≤ 1)
    (htop : eig ⟨0, hn⟩ = 2) :
    ∀ i, eig i = 2 → i = ⟨0, hn⟩ := by
  intro i hi
  have hzero : ⟨0, hn⟩ ∈ AtTwo eig := htop
  by_contra hne
  have hpair : ({⟨0, hn⟩, i} : Set (Fin n)) ⊆ AtTwo eig := by
    intro j hj
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
    rcases hj with (rfl | rfl) <;> assumption
  have hcard : 2 ≤ (AtTwo eig).ncard := by
    rw [← Set.ncard_pair (Ne.symm hne)]
    exact Set.ncard_le_ncard hpair
  omega

theorem supercritical_top_exact
    {n : ℕ} (hn : 0 < n) (eig : Fin n → ℝ)
    (hdefect : (AboveTwo eig).ncard + (AtTwo eig).ncard ≤ 1)
    (htop : 2 < eig ⟨0, hn⟩) :
    (AboveTwo eig).ncard = 1 ∧ (AtTwo eig).ncard = 0 := by
  have hmem : ⟨0, hn⟩ ∈ AboveTwo eig := htop
  have hpositive : 0 < (AboveTwo eig).ncard := (Set.ncard_pos).2 ⟨_, hmem⟩
  omega

theorem diagonal_defect_eq
    {ι : Type*} [Fintype ι] (eig : ι → ℝ) :
    sigNeg (QuadraticMap.weightedSumSquares ℝ (fun i ↦ 2 - eig i)) +
        Module.finrank ℝ (QuadraticMap.weightedSumSquares ℝ (fun i ↦ 2 - eig i)).radical =
      (AboveTwo eig).ncard + (AtTwo eig).ncard := by
  rw [QuadraticForm.sigNeg_weightedSumSquares,
    QuadraticForm.radical_weightedSumSquares, Pi.dim_spanSubset]
  congr 1
  · apply congrArg Set.ncard
    ext i
    simp [AboveTwo]
  · apply congrArg Set.ncard
    ext i
    simp only [Set.mem_setOf_eq, AtTwo]
    constructor <;> intro h <;> linarith

section MatrixBridge

variable {m : Type*} [Fintype m] [DecidableEq m]

def cartanPolarization (B : Matrix m m ℝ) : Matrix m m ℝ :=
  (2 : ℝ) • (1 : Matrix m m ℝ) - B

noncomputable def rawEigenvectorBasis {B : Matrix m m ℝ} (hB : B.IsHermitian) :
    Module.Basis m ℝ (m → ℝ) :=
  hB.eigenvectorBasis.toBasis.map (WithLp.linearEquiv 2 ℝ (m → ℝ))

@[simp]
theorem rawEigenvectorBasis_apply {B : Matrix m m ℝ} (hB : B.IsHermitian) (j : m) :
    rawEigenvectorBasis hB j = ⇑(hB.eigenvectorBasis j) := by
  simp [rawEigenvectorBasis, Module.Basis.map_apply]

theorem cartanPolarization_mulVec_eigenvector
    {B : Matrix m m ℝ} (hB : B.IsHermitian) (j : m) :
    cartanPolarization B *ᵥ ⇑(hB.eigenvectorBasis j) =
      (2 - hB.eigenvalues j) • ⇑(hB.eigenvectorBasis j) := by
  simp only [cartanPolarization, sub_mulVec, smul_mulVec, one_mulVec,
    hB.mulVec_eigenvectorBasis]
  module

theorem cartanPolarization_eigenvector_value
    {B : Matrix m m ℝ} (hB : B.IsHermitian) (j : m) :
    (cartanPolarization B).toQuadraticForm' ⇑(hB.eigenvectorBasis j) =
      2 - hB.eigenvalues j := by
  rw [Matrix.toQuadraticForm']
  simp only [LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', cartanPolarization_mulVec_eigenvector hB]
  rw [dotProduct_smul]
  have hinner := hB.eigenvectorBasis.inner_eq_ite j j
  have hdot : dotProduct ⇑(hB.eigenvectorBasis j)
      ⇑(hB.eigenvectorBasis j) = 1 := by
    calc
      dotProduct ⇑(hB.eigenvectorBasis j) ⇑(hB.eigenvectorBasis j) =
          inner ℝ (hB.eigenvectorBasis j) (hB.eigenvectorBasis j) := by
        simpa using (EuclideanSpace.inner_eq_star_dotProduct
          (hB.eigenvectorBasis j) (hB.eigenvectorBasis j)).symm
      _ = 1 := hinner.trans (if_pos rfl)
  simp [hdot]

theorem cartanPolarization_associated_orthogonal
    {B : Matrix m m ℝ} (hB : B.IsHermitian) :
    ((cartanPolarization B).toQuadraticForm').associated.IsOrthoᵢ
      (rawEigenvectorBasis hB) := by
  have hC : (cartanPolarization B).IsHermitian :=
    (Matrix.isHermitian_one.smul (by simp)).sub hB
  have hCsymm : (cartanPolarization B).IsSymm :=
    Matrix.isHermitian_iff_isSymm.mp hC
  have hbilin : (Matrix.toBilin' (cartanPolarization B)).IsSymm :=
    Matrix.isSymm_toBilin'_iff_isSymm.mpr hCsymm
  have hassoc : ((cartanPolarization B).toQuadraticForm').associated =
      Matrix.toBilin' (cartanPolarization B) := by
    exact QuadraticMap.associated_left_inverse ℝ hbilin.eq
  rw [hassoc]
  intro i j hij
  change Matrix.toBilin' (cartanPolarization B) (rawEigenvectorBasis hB i)
      (rawEigenvectorBasis hB j) = 0
  rw [Matrix.toBilin'_apply', rawEigenvectorBasis_apply,
    rawEigenvectorBasis_apply, cartanPolarization_mulVec_eigenvector hB,
    dotProduct_smul]
  have hinner := hB.eigenvectorBasis.inner_eq_ite j i
  have hdot : dotProduct ⇑(hB.eigenvectorBasis i)
      ⇑(hB.eigenvectorBasis j) = 0 := by
    calc
      dotProduct ⇑(hB.eigenvectorBasis i) ⇑(hB.eigenvectorBasis j) =
          inner ℝ (hB.eigenvectorBasis j) (hB.eigenvectorBasis i) := by
        simpa using (EuclideanSpace.inner_eq_star_dotProduct
          (hB.eigenvectorBasis j) (hB.eigenvectorBasis i)).symm
      _ = 0 := hinner.trans (if_neg (Ne.symm hij))
  simp [hdot]

theorem cartanPolarization_equivalent_weightedSumSquares
    {B : Matrix m m ℝ} (hB : B.IsHermitian) :
    QuadraticMap.Equivalent (cartanPolarization B).toQuadraticForm'
      (QuadraticMap.weightedSumSquares ℝ (fun i ↦ 2 - hB.eigenvalues i)) := by
  let v := rawEigenvectorBasis hB
  have hv : ((cartanPolarization B).toQuadraticForm').associated.IsOrthoᵢ v :=
    cartanPolarization_associated_orthogonal hB
  have hrepr : ((cartanPolarization B).toQuadraticForm').basisRepr v =
      QuadraticMap.weightedSumSquares ℝ
        (fun i ↦ (cartanPolarization B).toQuadraticForm' (v i)) :=
    QuadraticMap.basisRepr_eq_of_iIsOrtho _ _ hv
  have hiso := QuadraticMap.isometryEquivBasisRepr
    (cartanPolarization B).toQuadraticForm' v
  rw [hrepr] at hiso
  change QuadraticMap.IsometryEquiv (cartanPolarization B).toQuadraticForm'
    (QuadraticMap.weightedSumSquares ℝ
      (fun i ↦ (cartanPolarization B).toQuadraticForm' (v i))) at hiso
  have hvapply (i : m) : v i = ⇑(hB.eigenvectorBasis i) := by
    exact rawEigenvectorBasis_apply hB i
  simp_rw [hvapply, cartanPolarization_eigenvector_value hB] at hiso
  exact ⟨hiso⟩

noncomputable def eigenIndexEquiv : Fin (Fintype.card m) ≃ m :=
  Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card m))

@[simp]
theorem eigenvalues_eigenIndexEquiv
    {B : Matrix m m ℝ} (hB : B.IsHermitian) (i : Fin (Fintype.card m)) :
    hB.eigenvalues (eigenIndexEquiv i) = hB.eigenvalues₀ i := by
  simp [Matrix.IsHermitian.eigenvalues, eigenIndexEquiv]

theorem aboveTwo_eigenvalues_ncard_eq_eigenvalues₀
    {B : Matrix m m ℝ} (hB : B.IsHermitian) :
    (AboveTwo hB.eigenvalues).ncard = (AboveTwo hB.eigenvalues₀).ncard := by
  symm
  apply Set.ncard_congr (fun i _ ↦ eigenIndexEquiv i)
  · intro i hi
    simpa [AboveTwo] using hi
  · intro i j _ _ hij
    exact eigenIndexEquiv.injective hij
  · intro j hj
    refine ⟨eigenIndexEquiv.symm j, ?_, by simp⟩
    have hval := eigenvalues_eigenIndexEquiv hB (eigenIndexEquiv.symm j)
    rw [eigenIndexEquiv.apply_symm_apply] at hval
    simpa [AboveTwo, ← hval] using hj

theorem atTwo_eigenvalues_ncard_eq_eigenvalues₀
    {B : Matrix m m ℝ} (hB : B.IsHermitian) :
    (AtTwo hB.eigenvalues).ncard = (AtTwo hB.eigenvalues₀).ncard := by
  symm
  apply Set.ncard_congr (fun i _ ↦ eigenIndexEquiv i)
  · intro i hi
    simpa [AtTwo] using hi
  · intro i j _ _ hij
    exact eigenIndexEquiv.injective hij
  · intro j hj
    refine ⟨eigenIndexEquiv.symm j, ?_, by simp⟩
    have hval := eigenvalues_eigenIndexEquiv hB (eigenIndexEquiv.symm j)
    rw [eigenIndexEquiv.apply_symm_apply] at hval
    simpa [AtTwo, ← hval] using hj

theorem cartanPolarization_defect_eq_sorted_eigenvalues
    {B : Matrix m m ℝ} (hB : B.IsHermitian) :
    sigNeg (cartanPolarization B).toQuadraticForm' +
        Module.finrank ℝ (cartanPolarization B).toQuadraticForm'.radical =
      (AboveTwo hB.eigenvalues₀).ncard + (AtTwo hB.eigenvalues₀).ncard := by
  have hequiv := cartanPolarization_equivalent_weightedSumSquares hB
  rw [hequiv.sigNeg_eq, hequiv.rank_radical_eq,
    diagonal_defect_eq hB.eigenvalues,
    aboveTwo_eigenvalues_ncard_eq_eigenvalues₀ hB,
    atTwo_eigenvalues_ncard_eq_eigenvalues₀ hB]

/-- Spectral obstruction for every real symmetric adjacency matrix whose Cartan polarization has
at most one joint negative-or-null channel. -/
theorem cartanPolarization_secondEigenvalue_obstruction
    {B : Matrix m m ℝ} (hB : B.IsHermitian) (hn : 2 ≤ Fintype.card m)
    (hdefect : sigNeg (cartanPolarization B).toQuadraticForm' +
      Module.finrank ℝ (cartanPolarization B).toQuadraticForm'.radical ≤ 1) :
    hB.eigenvalues₀ ⟨1, hn⟩ ≤ 2 ∧
      (hB.eigenvalues₀ ⟨0, by omega⟩ = 2 →
        ∀ i, hB.eigenvalues₀ i = 2 → i = ⟨0, by omega⟩) ∧
      (2 < hB.eigenvalues₀ ⟨0, by omega⟩ →
        (AboveTwo hB.eigenvalues₀).ncard = 1 ∧
          (AtTwo hB.eigenvalues₀).ncard = 0) := by
  have hsorted : Antitone hB.eigenvalues₀ := hB.eigenvalues₀_antitone
  have hcounts : (AboveTwo hB.eigenvalues₀).ncard +
      (AtTwo hB.eigenvalues₀).ncard ≤ 1 := by
    rw [← cartanPolarization_defect_eq_sorted_eigenvalues hB]
    exact hdefect
  exact ⟨secondEigenvalue_obstruction hn hB.eigenvalues₀ hsorted hcounts,
    topCritical_isSimple (by omega) hB.eigenvalues₀ hcounts,
    supercritical_top_exact (by omega) hB.eigenvalues₀ hcounts⟩

end MatrixBridge

section SharpTriangle

def sharpTriangleAdjacency : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 6, 4;
     6, 0, 3;
     4, 3, 0]

def sharpTriangleCartan : Matrix (Fin 3) (Fin 3) ℝ :=
  cartanPolarization sharpTriangleAdjacency

def sharpTriangleChange : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, -3, -2;
     0, 1, 15 / 16;
     0, 0, 1]

def sharpTriangleWeights : Fin 3 → ℝ := ![2, -16, 129 / 16]

theorem sharpTriangleAdjacency_isHermitian : sharpTriangleAdjacency.IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sharpTriangleAdjacency]

theorem sharpTriangle_ones_value :
    sharpTriangleCartan.toQuadraticForm' (fun _ ↦ 1) = -20 := by
  norm_num [sharpTriangleCartan, cartanPolarization, sharpTriangleAdjacency,
    Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply', Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, Matrix.one_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem sharpTriangle_det : sharpTriangleCartan.det = -258 := by
  simp [sharpTriangleCartan, cartanPolarization, sharpTriangleAdjacency,
    Matrix.det_fin_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]
  norm_num

theorem sharpTriangle_trace : sharpTriangleCartan.trace = 6 := by
  norm_num [sharpTriangleCartan, cartanPolarization, sharpTriangleAdjacency,
    Matrix.trace_fin_three, Matrix.one_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem sharpTriangleChange_det : sharpTriangleChange.det = 1 := by
  norm_num [sharpTriangleChange, Matrix.det_fin_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

noncomputable def sharpTriangleLinearEquiv :
    (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) := by
  apply Matrix.toLinearEquiv'
  apply Matrix.invertibleOfIsUnitDet sharpTriangleChange
  rw [sharpTriangleChange_det]
  exact isUnit_one

theorem sharpTriangle_equivalent_weightedSumSquares :
    QuadraticMap.Equivalent sharpTriangleCartan.toQuadraticForm'
      (QuadraticMap.weightedSumSquares ℝ sharpTriangleWeights) := by
  let e : QuadraticMap.IsometryEquiv sharpTriangleCartan.toQuadraticForm'
      (QuadraticMap.weightedSumSquares ℝ sharpTriangleWeights) :=
    { sharpTriangleLinearEquiv with
      map_app' := by
        intro x
        simp only [sharpTriangleLinearEquiv, Matrix.toLinearEquiv'_apply]
        simp [QuadraticMap.weightedSumSquares_apply, sharpTriangleWeights,
          sharpTriangleCartan, cartanPolarization, sharpTriangleAdjacency,
          sharpTriangleChange, Matrix.toQuadraticForm',
          Matrix.toLinearMap₂'_apply', Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ, Matrix.one_apply, Matrix.cons_val_zero]
        ring }
  exact ⟨e⟩

theorem sharpTriangle_inertia :
    sigPos sharpTriangleCartan.toQuadraticForm' = 2 ∧
    sigNeg sharpTriangleCartan.toQuadraticForm' = 1 ∧
    Module.finrank ℝ sharpTriangleCartan.toQuadraticForm'.radical = 0 := by
  have he := sharpTriangle_equivalent_weightedSumSquares
  rw [he.sigPos_eq, he.sigNeg_eq, he.rank_radical_eq,
    QuadraticForm.sigPos_weightedSumSquares,
    QuadraticForm.sigNeg_weightedSumSquares,
    QuadraticForm.radical_weightedSumSquares, Pi.dim_spanSubset]
  have hpos : ({i | 0 < sharpTriangleWeights i} : Set (Fin 3)) = {0, 2} := by
    ext i
    fin_cases i
    all_goals norm_num [sharpTriangleWeights, Fin.mk.injEq]
    all_goals decide
  have hneg : ({i | sharpTriangleWeights i < 0} : Set (Fin 3)) = {1} := by
    ext i
    fin_cases i
    all_goals norm_num [sharpTriangleWeights, Fin.mk.injEq]
  have hzero : ({i | sharpTriangleWeights i = 0} : Set (Fin 3)) = ∅ := by
    ext i
    fin_cases i <;> norm_num [sharpTriangleWeights]
  rw [hpos, hneg, hzero]
  simp

end SharpTriangle

end

end GaloisForLFunctions.HTGeometry.StokesSpectralWitt
