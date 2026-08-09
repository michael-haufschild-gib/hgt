/-
# Finite nuclear incidence law

Rectangular incidence matrices require a nuclear norm which retains every nonzero singular value
with multiplicity.  This module defines that norm from the positive Gram matrix, proves the exact
left--right Gram invariance by the rectangular characteristic-polynomial identity, and identifies
the trace of a positive square root with the corresponding singular-value sum.
-/
import GaloisForLFunctions.HTGeometry.ComplexIntegralGram
import GaloisForLFunctions.HTGeometry.ReplicaHilbertCoareaIncidenceLaw
import GaloisForLFunctions.HTGeometry.ReturnExcisedOptimalDesignCoareaLaw
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

open Matrix Polynomial
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Nuclear norm of a finite rectangular complex matrix, defined from its target-side Gram
operator.  All nonzero singular values occur with algebraic multiplicity. -/
noncomputable def finiteMatrixNuclearNorm
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (K : Matrix m n ℂ) : ℝ :=
  ∑ j, Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self K).1.eigenvalues j)

/-- The trace of the positive square root is the sum of the square roots of the eigenvalues. -/
theorem Matrix.PosSemidef.trace_sqrt_re_eq_sum_sqrt_eigenvalues
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (CFC.sqrt A).trace.re = ∑ i, Real.sqrt (hA.1.eigenvalues i) := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ A hA.nonneg,
    hA.isHermitian.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
    Matrix.trace_diagonal]
  simp [Function.comp_def, hA.eigenvalues_nonneg]

/-- Positive square root commutes with multiplication by a nonnegative real
scalar on finite positive semidefinite matrices. -/
theorem finiteMatrix_cfcSqrt_smul_nonneg
    {n : Type*} [Fintype n] [DecidableEq n]
    (r : ℝ) (hr : 0 ≤ r) {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    CFC.sqrt (r • A) = Real.sqrt r • CFC.sqrt A := by
  apply CFC.sqrt_unique
  · rw [smul_mul_smul]
    rw [Real.mul_self_sqrt hr, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  · exact smul_nonneg (Real.sqrt_nonneg r) (CFC.sqrt_nonneg A)

/-- The finite nuclear norm is the real trace of the positive square root of
the target-side Gram operator. -/
theorem finiteMatrixNuclearNorm_eq_trace_sqrt_re
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (K : Matrix m n ℂ) :
    finiteMatrixNuclearNorm K =
      (CFC.sqrt (Kᴴ * K)).trace.re := by
  simpa [finiteMatrixNuclearNorm] using
    (Matrix.PosSemidef.trace_sqrt_re_eq_sum_sqrt_eigenvalues
      (Matrix.posSemidef_conjTranspose_mul_self K)).symm

/-- Finite nuclear mass is positively homogeneous under nonnegative real
scaling, including the singular scalar `0`. -/
theorem finiteMatrixNuclearNorm_smul_nonneg
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (r : ℝ) (hr : 0 ≤ r) (K : Matrix m n ℂ) :
    finiteMatrixNuclearNorm (r • K) = r * finiteMatrixNuclearNorm K := by
  have hGram : (r • K)ᴴ * (r • K) =
      (r ^ 2) • (Kᴴ * K) := by
    ext i j
    simp [Matrix.mul_apply, Finset.mul_sum, pow_two]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [finiteMatrixNuclearNorm_eq_trace_sqrt_re, hGram,
    finiteMatrix_cfcSqrt_smul_nonneg (r ^ 2) (sq_nonneg r)
      (Matrix.posSemidef_conjTranspose_mul_self K),
    finiteMatrixNuclearNorm_eq_trace_sqrt_re]
  simp [Real.sqrt_sq_eq_abs, abs_of_nonneg hr]

/-- Rectangular Gram duality: `AᴴA` and `AAᴴ` have the same positive spectral mass, including
multiplicity.  Dimension mismatch contributes only zero roots and hence no square-root mass. -/
theorem sum_sqrt_eigenvalues_conjTranspose_mul_self_eq_self_mul_conjTranspose
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) :
    (∑ j, Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self A).1.eigenvalues j)) =
      ∑ i, Real.sqrt ((Matrix.posSemidef_self_mul_conjTranspose A).1.eigenvalues i) := by
  let P : Matrix m m ℂ := A * Aᴴ
  let Q : Matrix n n ℂ := Aᴴ * A
  have hP : P.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose A
  have hQ : Q.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  have hpoly :
      X ^ Fintype.card n * P.charpoly = X ^ Fintype.card m * Q.charpoly := by
    simpa [P, Q] using Matrix.charpoly_mul_comm' A Aᴴ
  have hleft : X ^ Fintype.card n * P.charpoly ≠ (0 : ℂ[X]) :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) (Matrix.charpoly_monic P).ne_zero
  have hright : X ^ Fintype.card m * Q.charpoly ≠ (0 : ℂ[X]) :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) (Matrix.charpoly_monic Q).ne_zero
  have hroots := congrArg Polynomial.roots hpoly
  rw [Polynomial.roots_mul hleft, Polynomial.roots_X_pow,
    hP.isHermitian.roots_charpoly_eq_eigenvalues,
    Polynomial.roots_mul hright, Polynomial.roots_X_pow,
    hQ.isHermitian.roots_charpoly_eq_eigenvalues] at hroots
  have hmass := congrArg
    (fun s : Multiset ℂ => (s.map fun z => Real.sqrt z.re).sum) hroots
  simpa [P, Q, Function.comp_def, Multiset.nsmul_singleton,
    Multiset.map_replicate] using hmass.symm

/-- The rectangular nuclear norm can equally be read from the source-side Gram operator. -/
theorem finiteMatrixNuclearNorm_eq_sum_sqrt_self_mul_conjTranspose
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (K : Matrix m n ℂ) :
    finiteMatrixNuclearNorm K =
      ∑ i, Real.sqrt ((Matrix.posSemidef_self_mul_conjTranspose K).1.eigenvalues i) := by
  simpa [finiteMatrixNuclearNorm] using
    sum_sqrt_eigenvalues_conjTranspose_mul_self_eq_self_mul_conjTranspose K

/-- **Finite sheet--target nuclear identity.**  For arbitrary source and target synthesis
matrices `U` and `V`, the nuclear norm of the incidence matrix `UᴴV` is exactly the Bures root
fidelity of their two covariance matrices `UUᴴ` and `VVᴴ`.  No rank, injectivity, or positivity
assumption is required. -/
theorem finiteMatrixNuclearNorm_conjTranspose_mul_eq_buresTrace
    {h x y : Type*} [Fintype h] [Fintype x] [Fintype y]
    [DecidableEq h] [DecidableEq x] [DecidableEq y]
    (U : Matrix h x ℂ) (V : Matrix h y ℂ) :
    finiteMatrixNuclearNorm (Uᴴ * V) =
      (CFC.sqrt (CFC.conjSqrt (U * Uᴴ) (V * Vᴴ))).trace.re := by
  let C : Matrix h h ℂ := U * Uᴴ
  let M : Matrix h h ℂ := V * Vᴴ
  let S : Matrix h h ℂ := CFC.sqrt C
  let A : Matrix h y ℂ := S * V
  have hC : C.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose U
  have hSH : Sᴴ = S := by
    simpa [S, Matrix.star_eq_conjTranspose] using (CFC.sqrt_nonneg C).star_eq
  have hS2 : S * S = C := by
    simpa [S, pow_two] using CFC.sq_sqrt C hC.nonneg
  have hGram : (Uᴴ * V)ᴴ * (Uᴴ * V) = Aᴴ * A := by
    simp only [A, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hSH]
    rw [Matrix.mul_assoc Vᴴ U (Uᴴ * V), ← Matrix.mul_assoc U Uᴴ V,
      Matrix.mul_assoc Vᴴ S (S * V), ← Matrix.mul_assoc S S V, hS2]
  have hRange : A * Aᴴ = CFC.conjSqrt C M := by
    simp only [A, M, Matrix.conjTranspose_mul, hSH, CFC.conjSqrt_apply]
    simp only [Matrix.mul_assoc]
    rfl
  have hEig :
      (Matrix.posSemidef_conjTranspose_mul_self (Uᴴ * V)).1.eigenvalues =
        (Matrix.posSemidef_conjTranspose_mul_self A).1.eigenvalues := by
    exact (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
      (Matrix.posSemidef_conjTranspose_mul_self (Uᴴ * V)).1
      (Matrix.posSemidef_conjTranspose_mul_self A).1).2
        (congrArg Matrix.charpoly hGram)
  calc
    finiteMatrixNuclearNorm (Uᴴ * V) =
        ∑ j, Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self A).1.eigenvalues j) := by
      unfold finiteMatrixNuclearNorm
      rw [hEig]
    _ = ∑ i, Real.sqrt
        ((Matrix.posSemidef_self_mul_conjTranspose A).1.eigenvalues i) :=
      sum_sqrt_eigenvalues_conjTranspose_mul_self_eq_self_mul_conjTranspose A
    _ = (CFC.sqrt (A * Aᴴ)).trace.re :=
      (Matrix.PosSemidef.trace_sqrt_re_eq_sum_sqrt_eigenvalues
        (Matrix.posSemidef_self_mul_conjTranspose A)).symm
    _ = (CFC.sqrt (CFC.conjSqrt (U * Uᴴ) (V * Vᴴ))).trace.re := by
      rw [hRange]

/-! ## Atomic source and occupied-target synthesis -/

/-- Finite weighted synthesis matrix with column `√wᵢ zᵢ`.  Nonnegative weights are encoded by
`ℝ≥0`, so no positivity premise is needed. -/
noncomputable def finiteWeightedSynthesisMatrix
    {h i : Type*} [Fintype h] [Fintype i]
    (weight : i → ℝ≥0) (vector : i → h → ℂ) : Matrix h i ℂ :=
  fun a j => (NNReal.sqrt (weight j) : ℂ) * vector j a

/-- Weighted covariance retaining every labelled source sheet. -/
noncomputable def finiteWeightedCovarianceMatrix
    {h i : Type*} [Fintype h] [Fintype i]
    (weight : i → ℝ≥0) (vector : i → h → ℂ) : Matrix h h ℂ :=
  ∑ j, (weight j : ℂ) • Matrix.vecMulVec (vector j) (star (vector j))

/-- Weighted synthesis has exactly the expected covariance `∑ᵢ wᵢ|zᵢ⟩⟨zᵢ|`. -/
theorem finiteWeightedSynthesisMatrix_mul_conjTranspose
    {h i : Type*} [Fintype h] [Fintype i]
    (weight : i → ℝ≥0) (vector : i → h → ℂ) :
    finiteWeightedSynthesisMatrix weight vector *
        (finiteWeightedSynthesisMatrix weight vector)ᴴ =
      finiteWeightedCovarianceMatrix weight vector := by
  classical
  ext a b
  simp only [finiteWeightedSynthesisMatrix, finiteWeightedCovarianceMatrix,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, star_mul']
  apply Finset.sum_congr rfl
  intro j _
  have hstar : star (NNReal.sqrt (weight j) : ℂ) =
      (NNReal.sqrt (weight j) : ℂ) := by simp
  have hsq : (NNReal.sqrt (weight j) : ℂ) *
      (NNReal.sqrt (weight j) : ℂ) = (weight j : ℂ) := by
    have hsquare := NNReal.sq_sqrt (weight j)
    rw [pow_two] at hsquare
    exact_mod_cast hsquare
  rw [hstar, smul_eq_mul]
  calc
    (NNReal.sqrt (weight j) : ℂ) * vector j a *
          ((NNReal.sqrt (weight j) : ℂ) * star (vector j b)) =
        ((NNReal.sqrt (weight j) : ℂ) * (NNReal.sqrt (weight j) : ℂ)) *
          (vector j a * star (vector j b)) := by ring
    _ = (weight j : ℂ) * (vector j a * star (vector j b)) := by rw [hsq]

/-- Every finite nonnegatively weighted covariance is positive semidefinite. -/
theorem finiteWeightedCovarianceMatrix_posSemidef
    {h i : Type*} [Fintype h] [Fintype i] [DecidableEq h]
    (weight : i → ℝ≥0) (vector : i → h → ℂ) :
    (finiteWeightedCovarianceMatrix weight vector).PosSemidef := by
  rw [← finiteWeightedSynthesisMatrix_mul_conjTranspose]
  exact Matrix.posSemidef_self_mul_conjTranspose
    (finiteWeightedSynthesisMatrix weight vector)

/-- The NNReal-weighted covariance is the existing real-weighted design
Gram after the canonical scalar coercion. -/
theorem finiteWeightedCovarianceMatrix_eq_finiteDesignGram
    {i : Type*} [Fintype i] {n : ℕ}
    (weight : i → ℝ≥0) (vector : i → Fin n → ℂ) :
    finiteWeightedCovarianceMatrix weight vector =
      finiteDesignGram vector (fun j => (weight j : ℝ)) := by
  classical
  ext a b
  simp [finiteWeightedCovarianceMatrix, finiteDesignGram]

/-- Finite weighted sheet--target incidence matrix `UᴴV`. -/
noncomputable def finiteWeightedIncidenceMatrix
    {h x y : Type*} [Fintype h] [Fintype x] [Fintype y]
    (sourceWeight : x → ℝ≥0) (source : x → h → ℂ)
    (targetWeight : y → ℝ≥0) (target : y → h → ℂ) : Matrix x y ℂ :=
  (finiteWeightedSynthesisMatrix sourceWeight source)ᴴ *
    finiteWeightedSynthesisMatrix targetWeight target

/-- **Sheet kernel law (INC1):** each matrix entry is the weighted source--target inner product;
source labels are not quotiented or pushed forward. -/
theorem finiteWeightedIncidenceMatrix_apply
    {h x y : Type*} [Fintype h] [Fintype x] [Fintype y]
    (sourceWeight : x → ℝ≥0) (source : x → h → ℂ)
    (targetWeight : y → ℝ≥0) (target : y → h → ℂ)
    (i : x) (j : y) :
    finiteWeightedIncidenceMatrix sourceWeight source targetWeight target i j =
      (NNReal.sqrt (sourceWeight i) : ℂ) *
        (NNReal.sqrt (targetWeight j) : ℂ) *
          finiteComplexInner (source i) (target j) := by
  classical
  simp only [finiteWeightedIncidenceMatrix, finiteWeightedSynthesisMatrix,
    Matrix.mul_apply, Matrix.conjTranspose_apply, finiteComplexInner, star_mul']
  have hstar : star (NNReal.sqrt (sourceWeight i) : ℂ) =
      (NNReal.sqrt (sourceWeight i) : ℂ) := by simp
  rw [hstar]
  calc
    (∑ a, (NNReal.sqrt (sourceWeight i) : ℂ) * star (source i a) *
          ((NNReal.sqrt (targetWeight j) : ℂ) * target j a)) =
        ∑ a, ((NNReal.sqrt (sourceWeight i) : ℂ) *
          (NNReal.sqrt (targetWeight j) : ℂ)) *
            (star (source i a) * target j a) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ((NNReal.sqrt (sourceWeight i) : ℂ) *
          (NNReal.sqrt (targetWeight j) : ℂ)) *
            ∑ a, star (source i a) * target j a := by
      rw [Finset.mul_sum]
    _ = (NNReal.sqrt (sourceWeight i) : ℂ) *
        (NNReal.sqrt (targetWeight j) : ℂ) *
          ∑ a, star (source i a) * target j a := rfl

/-- **Finite weighted sheet--target incidence law (INC2):** nuclear incidence mass is exactly
Bures root fidelity between weighted source and target covariances. -/
theorem finiteWeightedIncidence_nuclearNorm_eq_buresTrace
    {h x y : Type*} [Fintype h] [Fintype x] [Fintype y]
    [DecidableEq h] [DecidableEq x] [DecidableEq y]
    (sourceWeight : x → ℝ≥0) (source : x → h → ℂ)
    (targetWeight : y → ℝ≥0) (target : y → h → ℂ) :
    finiteMatrixNuclearNorm
        (finiteWeightedIncidenceMatrix sourceWeight source targetWeight target) =
      (CFC.sqrt (CFC.conjSqrt
        (finiteWeightedCovarianceMatrix sourceWeight source)
        (finiteWeightedCovarianceMatrix targetWeight target))).trace.re := by
  rw [finiteWeightedIncidenceMatrix,
    finiteMatrixNuclearNorm_conjTranspose_mul_eq_buresTrace,
    finiteWeightedSynthesisMatrix_mul_conjTranspose,
    finiteWeightedSynthesisMatrix_mul_conjTranspose]

/-- **Replica kernel law (INC4):** replica order acts on the physical incidence kernel before
the nuclear norm is taken. -/
theorem finiteWeightedReplicaIncidenceMatrix_apply
    {α x y : Type*} [Fintype α] [Fintype x] [Fintype y]
    (r : ℕ) (sourceWeight : x → ℝ≥0) (source : x → α → ℂ)
    (targetWeight : y → ℝ≥0) (target : y → α → ℂ)
    (i : x) (j : y) :
    finiteWeightedIncidenceMatrix sourceWeight
        (fun i => finitePureTensorPowerEuclidean r (source i)) targetWeight
        (fun j => finitePureTensorPowerEuclidean r (target j)) i j =
      (NNReal.sqrt (sourceWeight i) : ℂ) *
        (NNReal.sqrt (targetWeight j) : ℂ) *
          finiteComplexInner (source i) (target j) ^ r := by
  rw [finiteWeightedIncidenceMatrix_apply,
    ← inner_toLp_eq_finiteComplexInner,
    inner_finitePureTensorPowerEuclidean]

/-! ## Rank-sensitive Hilbert--Schmidt comparison -/

/-- Squared Hilbert--Schmidt mass of a finite rectangular matrix. -/
noncomputable def finiteMatrixHilbertSchmidtSq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (K : Matrix m n ℂ) : ℝ :=
  ((Kᴴ * K).trace).re

/-- The Gram trace is the explicit entrywise Hilbert--Schmidt mass. -/
theorem finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (K : Matrix m n ℂ) :
    finiteMatrixHilbertSchmidtSq K = ∑ i, ∑ j, ‖K i j‖ ^ 2 := by
  classical
  unfold finiteMatrixHilbertSchmidtSq Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Complex.re_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [RCLike.star_def, RCLike.conj_mul]
  change ((‖K i j‖ : ℂ) ^ 2).re = ‖K i j‖ ^ 2
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- **Rank-sensitive nuclear/Hilbert--Schmidt law (INC5):** the exact loss in replacing nuclear
incidence mass by collision mass is occupied incidence rank, not ambient source or target size. -/
theorem finiteMatrixNuclearNorm_sq_le_rank_mul_hilbertSchmidtSq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (K : Matrix m n ℂ) :
    finiteMatrixNuclearNorm K ^ 2 ≤
      (K.rank : ℝ) * finiteMatrixHilbertSchmidtSq K := by
  classical
  let G : Matrix n n ℂ := Kᴴ * K
  let hG : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self K
  let e : n → ℝ := hG.1.eigenvalues
  let live : Finset n := Finset.univ.filter fun j => e j ≠ 0
  have hsum_live : (∑ j, Real.sqrt (e j)) = ∑ j ∈ live, Real.sqrt (e j) := by
    simp only [live, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : e j = 0
    · simp [hj]
    · simp [hj]
  have hcs : (∑ j ∈ live, Real.sqrt (e j)) ^ 2 ≤
      (live.card : ℝ) * ∑ j ∈ live, Real.sqrt (e j) ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq (s := live) (f := fun j => Real.sqrt (e j)))
  have hcard : live.card = K.rank := by
    rw [← Matrix.rank_conjTranspose_mul_self K,
      hG.1.rank_eq_card_non_zero_eigs]
    simp [live, e, Fintype.card_subtype]
  have hsquares : (∑ j ∈ live, Real.sqrt (e j) ^ 2) = ∑ j, e j := by
    calc
      (∑ j ∈ live, Real.sqrt (e j) ^ 2) = ∑ j ∈ live, e j := by
        apply Finset.sum_congr rfl
        intro j _
        exact Real.sq_sqrt (hG.eigenvalues_nonneg j)
      _ = ∑ j, e j := by
        simp only [live, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : e j = 0
        · simp [hj]
        · simp [hj]
  have htrace : (∑ j, e j) = G.trace.re := by
    have ht := hG.1.trace_eq_sum_eigenvalues
    simpa [e] using (congrArg Complex.re ht).symm
  calc
    finiteMatrixNuclearNorm K ^ 2 = (∑ j, Real.sqrt (e j)) ^ 2 := by
      rfl
    _ = (∑ j ∈ live, Real.sqrt (e j)) ^ 2 := by rw [hsum_live]
    _ ≤ (live.card : ℝ) * ∑ j ∈ live, Real.sqrt (e j) ^ 2 := hcs
    _ = (K.rank : ℝ) * finiteMatrixHilbertSchmidtSq K := by
      rw [hcard, hsquares, htrace]
      rfl

/-- Hilbert--Schmidt mass is always bounded by squared nuclear mass. -/
theorem finiteMatrixHilbertSchmidtSq_le_nuclearNorm_sq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (K : Matrix m n ℂ) :
    finiteMatrixHilbertSchmidtSq K ≤ finiteMatrixNuclearNorm K ^ 2 := by
  classical
  let G : Matrix n n ℂ := Kᴴ * K
  let hG : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self K
  let e : n → ℝ := hG.1.eigenvalues
  have hsquares : (∑ j, Real.sqrt (e j) ^ 2) = ∑ j, e j := by
    apply Finset.sum_congr rfl
    intro j _
    exact Real.sq_sqrt (hG.eigenvalues_nonneg j)
  have htrace : (∑ j, e j) = G.trace.re := by
    have ht := hG.1.trace_eq_sum_eigenvalues
    simpa [e] using (congrArg Complex.re ht).symm
  have hsum : (∑ j, Real.sqrt (e j) ^ 2) ≤
      (∑ j, Real.sqrt (e j)) ^ 2 := by
    simpa using (Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ) (f := fun j => Real.sqrt (e j))
      (fun j _ => Real.sqrt_nonneg (e j)))
  calc
    finiteMatrixHilbertSchmidtSq K = G.trace.re := rfl
    _ = ∑ j, e j := htrace.symm
    _ = ∑ j, Real.sqrt (e j) ^ 2 := hsquares.symm
    _ ≤ (∑ j, Real.sqrt (e j)) ^ 2 := hsum
    _ = finiteMatrixNuclearNorm K ^ 2 := rfl

theorem finiteMatrixNuclearNorm_nonneg
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (K : Matrix m n ℂ) : 0 ≤ finiteMatrixNuclearNorm K := by
  unfold finiteMatrixNuclearNorm
  exact Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _

/-- Finite nuclear mass is faithful: it vanishes exactly on the zero
rectangular matrix. -/
theorem finiteMatrixNuclearNorm_eq_zero_iff
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (K : Matrix m n ℂ) : finiteMatrixNuclearNorm K = 0 ↔ K = 0 := by
  constructor
  · intro hnuclear
    have hle := finiteMatrixHilbertSchmidtSq_le_nuclearNorm_sq K
    have hhs_le : finiteMatrixHilbertSchmidtSq K ≤ 0 := by
      simpa [hnuclear] using hle
    have hhs_nonneg : 0 ≤ finiteMatrixHilbertSchmidtSq K := by
      rw [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq]
      positivity
    have hhs : finiteMatrixHilbertSchmidtSq K = 0 :=
      le_antisymm hhs_le hhs_nonneg
    rw [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq] at hhs
    ext i j
    have hi : (∑ k, ‖K i k‖ ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg ‖K a b‖))).mp
          hhs i (Finset.mem_univ i)
    have hij : ‖K i j‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun b _ => sq_nonneg ‖K i b‖)).mp hi j (Finset.mem_univ j)
    have hnorm : ‖K i j‖ = 0 := by
      nlinarith [norm_nonneg (K i j)]
    exact norm_eq_zero.mp hnorm
  · intro hK
    subst K
    have hsq := finiteMatrixNuclearNorm_sq_le_rank_mul_hilbertSchmidtSq
      (0 : Matrix m n ℂ)
    have hn := finiteMatrixNuclearNorm_nonneg (0 : Matrix m n ℂ)
    have hsq0 : finiteMatrixNuclearNorm (0 : Matrix m n ℂ) ^ 2 ≤ 0 := by
      simpa [finiteMatrixHilbertSchmidtSq] using hsq
    nlinarith

/-- Nuclear mass is invariant under rectangular adjoint. -/
theorem finiteMatrixNuclearNorm_conjTranspose
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (K : Matrix m n ℂ) :
    finiteMatrixNuclearNorm Kᴴ = finiteMatrixNuclearNorm K := by
  calc
    finiteMatrixNuclearNorm Kᴴ =
        ∑ i, Real.sqrt
          ((Matrix.posSemidef_self_mul_conjTranspose K).1.eigenvalues i) := by
      unfold finiteMatrixNuclearNorm
      simp only [Matrix.conjTranspose_conjTranspose]
    _ = finiteMatrixNuclearNorm K :=
      (finiteMatrixNuclearNorm_eq_sum_sqrt_self_mul_conjTranspose K).symm

/-- A finite matrix of rank at most one has nuclear mass squared exactly
equal to its Hilbert--Schmidt mass. -/
theorem finiteMatrixNuclearNorm_sq_eq_hilbertSchmidtSq_of_rank_le_one
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (K : Matrix m n ℂ) (hK : K.rank ≤ 1) :
    finiteMatrixNuclearNorm K ^ 2 = finiteMatrixHilbertSchmidtSq K := by
  apply le_antisymm
  · calc
      finiteMatrixNuclearNorm K ^ 2 ≤
          (K.rank : ℝ) * finiteMatrixHilbertSchmidtSq K :=
        finiteMatrixNuclearNorm_sq_le_rank_mul_hilbertSchmidtSq K
      _ ≤ 1 * finiteMatrixHilbertSchmidtSq K := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hK
        · rw [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq]
          positivity
      _ = finiteMatrixHilbertSchmidtSq K := one_mul _
  · exact finiteMatrixHilbertSchmidtSq_le_nuclearNorm_sq K

/-- Bures root fidelity is symmetric for arbitrary finite positive
semidefinite matrices. -/
theorem finiteBuresTrace_comm
    {n : Type*} [Fintype n] [DecidableEq n]
    {C M : Matrix n n ℂ} (hC : C.PosSemidef) (hM : M.PosSemidef) :
    (CFC.sqrt (CFC.conjSqrt C M)).trace.re =
      (CFC.sqrt (CFC.conjSqrt M C)).trace.re := by
  let U : Matrix n n ℂ := CFC.sqrt C
  let V : Matrix n n ℂ := CFC.sqrt M
  have hUH : Uᴴ = U := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg C).star_eq
  have hVH : Vᴴ = V := by
    simpa [V, Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg M).star_eq
  have hU2 : U * U = C := by
    simpa [U, pow_two] using CFC.sq_sqrt C hC.nonneg
  have hV2 : V * V = M := by
    simpa [V, pow_two] using CFC.sq_sqrt M hM.nonneg
  have hcovU : U * Uᴴ = C := by rw [hUH, hU2]
  have hcovV : V * Vᴴ = M := by rw [hVH, hV2]
  have hCM := finiteMatrixNuclearNorm_conjTranspose_mul_eq_buresTrace U V
  have hMC := finiteMatrixNuclearNorm_conjTranspose_mul_eq_buresTrace V U
  rw [hcovU, hcovV] at hCM hMC
  calc
    (CFC.sqrt (CFC.conjSqrt C M)).trace.re =
        finiteMatrixNuclearNorm (Uᴴ * V) := hCM.symm
    _ = finiteMatrixNuclearNorm ((Uᴴ * V)ᴴ) :=
      (finiteMatrixNuclearNorm_conjTranspose (Uᴴ * V)).symm
    _ = finiteMatrixNuclearNorm (Vᴴ * U) := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    _ = (CFC.sqrt (CFC.conjSqrt M C)).trace.re := hMC

/-- Bures root fidelity is homogeneous of degree one half in its first
positive-semidefinite argument, including zero scaling. -/
theorem finiteBuresTrace_smul_left
    {n : Type*} [Fintype n] [DecidableEq n]
    (r : ℝ) (hr : 0 ≤ r) {C M : Matrix n n ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) :
    (CFC.sqrt (CFC.conjSqrt (r • C) M)).trace.re =
      Real.sqrt r * (CFC.sqrt (CFC.conjSqrt C M)).trace.re := by
  let U : Matrix n n ℂ := CFC.sqrt C
  let V : Matrix n n ℂ := CFC.sqrt M
  let s : ℝ := Real.sqrt r
  let Ur : Matrix n n ℂ := s • U
  have hUH : Uᴴ = U := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg C).star_eq
  have hVH : Vᴴ = V := by
    simpa [V, Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg M).star_eq
  have hU2 : U * U = C := by
    simpa [U, pow_two] using CFC.sq_sqrt C hC.nonneg
  have hV2 : V * V = M := by
    simpa [V, pow_two] using CFC.sq_sqrt M hM.nonneg
  have hcovU : U * Uᴴ = C := by rw [hUH, hU2]
  have hcovV : V * Vᴴ = M := by rw [hVH, hV2]
  have hcovUr : Ur * Urᴴ = r • C := by
    simp [Ur, s, hUH, hU2]
    rw [smul_smul, Real.mul_self_sqrt hr]
  have hinc : Urᴴ * V = s • (Uᴴ * V) := by
    simp [Ur, mul_smul_comm]
  have hfidr := finiteMatrixNuclearNorm_conjTranspose_mul_eq_buresTrace Ur V
  have hfid := finiteMatrixNuclearNorm_conjTranspose_mul_eq_buresTrace U V
  rw [hcovUr, hcovV] at hfidr
  rw [hcovU, hcovV] at hfid
  calc
    (CFC.sqrt (CFC.conjSqrt (r • C) M)).trace.re =
        finiteMatrixNuclearNorm (Urᴴ * V) := hfidr.symm
    _ = finiteMatrixNuclearNorm (s • (Uᴴ * V)) := by rw [hinc]
    _ = s * finiteMatrixNuclearNorm (Uᴴ * V) :=
      finiteMatrixNuclearNorm_smul_nonneg s (Real.sqrt_nonneg r) (Uᴴ * V)
    _ = Real.sqrt r *
        (CFC.sqrt (CFC.conjSqrt C M)).trace.re := by
      rw [hfid]

/-- Bures root fidelity is homogeneous of degree one half in its second
positive-semidefinite argument. -/
theorem finiteBuresTrace_smul_right
    {n : Type*} [Fintype n] [DecidableEq n]
    (r : ℝ) (hr : 0 ≤ r) {C M : Matrix n n ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) :
    (CFC.sqrt (CFC.conjSqrt C (r • M))).trace.re =
      Real.sqrt r * (CFC.sqrt (CFC.conjSqrt C M)).trace.re := by
  have hrM : (r • M).PosSemidef := hM.smul hr
  calc
    (CFC.sqrt (CFC.conjSqrt C (r • M))).trace.re =
        (CFC.sqrt (CFC.conjSqrt (r • M) C)).trace.re :=
      finiteBuresTrace_comm hC hrM
    _ = Real.sqrt r *
        (CFC.sqrt (CFC.conjSqrt M C)).trace.re :=
      finiteBuresTrace_smul_left r hr hM hC
    _ = Real.sqrt r *
        (CFC.sqrt (CFC.conjSqrt C M)).trace.re := by
      rw [finiteBuresTrace_comm hM hC]

/-- Squared Bures fidelity is linear under nonnegative scaling of its first
argument. -/
theorem finiteBuresTrace_sq_smul_left
    {n : Type*} [Fintype n] [DecidableEq n]
    (r : ℝ) (hr : 0 ≤ r) {C M : Matrix n n ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) :
    (CFC.sqrt (CFC.conjSqrt (r • C) M)).trace.re ^ 2 =
      r * (CFC.sqrt (CFC.conjSqrt C M)).trace.re ^ 2 := by
  rw [finiteBuresTrace_smul_left r hr hC hM]
  rw [mul_pow, Real.sq_sqrt hr]

/-- Squared Bures fidelity is linear under nonnegative scaling of its second
argument. -/
theorem finiteBuresTrace_sq_smul_right
    {n : Type*} [Fintype n] [DecidableEq n]
    (r : ℝ) (hr : 0 ≤ r) {C M : Matrix n n ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) :
    (CFC.sqrt (CFC.conjSqrt C (r • M))).trace.re ^ 2 =
      r * (CFC.sqrt (CFC.conjSqrt C M)).trace.re ^ 2 := by
  rw [finiteBuresTrace_smul_right r hr hC hM]
  rw [mul_pow, Real.sq_sqrt hr]

/-- Self-fidelity is exactly positive trace, including singular matrices. -/
theorem finiteBuresTrace_self_eq_trace
    {n : Type*} [Fintype n] [DecidableEq n]
    {C : Matrix n n ℂ} (hC : C.PosSemidef) :
    (CFC.sqrt (CFC.conjSqrt C C)).trace.re = C.trace.re := by
  let S : Matrix n n ℂ := CFC.sqrt C
  have hS2 : S * S = C := by
    simpa [S, pow_two] using CFC.sq_sqrt C hC.nonneg
  have hconj : CFC.conjSqrt C C = C ^ 2 := by
    rw [CFC.conjSqrt_apply]
    change S * C * S = C ^ 2
    rw [← hS2]
    simp [pow_two, Matrix.mul_assoc]
  rw [hconj, CFC.sqrt_sq C hC.nonneg]

/-- Bures root fidelity vanishes exactly when the two covariance square
roots have zero product. -/
theorem finiteBuresTrace_eq_zero_iff_sqrt_mul_sqrt_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    {C M : Matrix n n ℂ} (hC : C.PosSemidef) (hM : M.PosSemidef) :
    (CFC.sqrt (CFC.conjSqrt C M)).trace.re = 0 ↔
      CFC.sqrt C * CFC.sqrt M = 0 := by
  let U : Matrix n n ℂ := CFC.sqrt C
  let V : Matrix n n ℂ := CFC.sqrt M
  let K : Matrix n n ℂ := Uᴴ * V
  have hUH : Uᴴ = U := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg C).star_eq
  have hVH : Vᴴ = V := by
    simpa [V, Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg M).star_eq
  have hU2 : U * U = C := by
    simpa [U, pow_two] using CFC.sq_sqrt C hC.nonneg
  have hV2 : V * V = M := by
    simpa [V, pow_two] using CFC.sq_sqrt M hM.nonneg
  have hcovU : U * Uᴴ = C := by rw [hUH, hU2]
  have hcovV : V * Vᴴ = M := by rw [hVH, hV2]
  have hfid : finiteMatrixNuclearNorm K =
      (CFC.sqrt (CFC.conjSqrt C M)).trace.re := by
    simpa [K, hcovU, hcovV] using
      (finiteMatrixNuclearNorm_conjTranspose_mul_eq_buresTrace U V)
  constructor
  · intro hzero
    have hnuclear : finiteMatrixNuclearNorm K = 0 := hfid.trans hzero
    have hK : K = 0 :=
      (finiteMatrixNuclearNorm_eq_zero_iff K).mp hnuclear
    simpa [K, hUH, U, V] using hK
  · intro hzero
    have hK : K = 0 := by
      simpa [K, hUH, U, V] using hzero
    have hnuclear : finiteMatrixNuclearNorm K = 0 :=
      (finiteMatrixNuclearNorm_eq_zero_iff K).mpr hK
    exact hfid.symm.trans hnuclear

/-- **Pure-source Bures identity.**  Fidelity against a rank-one source ray
is exactly its quadratic expectation in the target, including singular and
unnormalized vectors. -/
theorem finiteBuresTrace_sq_rankOne_left
    {n : Type*} [Fintype n] [DecidableEq n]
    (u : n → ℂ) {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    (CFC.sqrt (CFC.conjSqrt (Matrix.vecMulVec u (star u)) M)).trace.re ^ 2 =
      (finiteComplexInner u (M *ᵥ u)).re := by
  classical
  let U : Matrix n Unit ℂ := fun i _ => u i
  let V : Matrix n n ℂ := CFC.sqrt M
  let K : Matrix Unit n ℂ := Uᴴ * V
  have hVH : Vᴴ = V := by
    simpa [V, Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg M).star_eq
  have hV2 : V * V = M := by
    simpa [V, pow_two] using CFC.sq_sqrt M hM.nonneg
  have hcovU : U * Uᴴ = Matrix.vecMulVec u (star u) := by
    ext i j
    simp [U, Matrix.mul_apply, Matrix.vecMulVec_apply]
  have hcovV : V * Vᴴ = M := by rw [hVH, hV2]
  have hfid : finiteMatrixNuclearNorm K =
      (CFC.sqrt (CFC.conjSqrt (Matrix.vecMulVec u (star u)) M)).trace.re := by
    have h := finiteMatrixNuclearNorm_conjTranspose_mul_eq_buresTrace U V
    rw [hcovU, hcovV] at h
    simpa [K] using h
  have hKrank : K.rank ≤ 1 := by
    simpa using Matrix.rank_le_card_height K
  have hKKH : K * Kᴴ = Uᴴ * M * U := by
    simp only [K, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hVH]
    calc
      (Uᴴ * V) * (V * U) = Uᴴ * (V * V) * U := by
        simp [Matrix.mul_assoc]
      _ = Uᴴ * M * U := by rw [hV2]
  have hhs : finiteMatrixHilbertSchmidtSq K =
      (finiteComplexInner u (M *ᵥ u)).re := by
    unfold finiteMatrixHilbertSchmidtSq
    apply congrArg Complex.re
    rw [Matrix.trace_mul_comm, hKKH]
    rw [Matrix.trace_mul_cycle Uᴴ M U,
      Matrix.trace_mul_cycle U Uᴴ M, Matrix.mul_assoc, hcovU]
    unfold Matrix.trace finiteComplexInner Matrix.mulVec
    simp only [Matrix.diag_apply, Matrix.mul_apply,
      Matrix.vecMulVec_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.star_apply, starRingEnd_apply]
    ring
  calc
    (CFC.sqrt (CFC.conjSqrt (Matrix.vecMulVec u (star u)) M)).trace.re ^ 2 =
        finiteMatrixNuclearNorm K ^ 2 := by rw [hfid]
    _ = finiteMatrixHilbertSchmidtSq K :=
      finiteMatrixNuclearNorm_sq_eq_hilbertSchmidtSq_of_rank_le_one K hKrank
    _ = (finiteComplexInner u (M *ᵥ u)).re := hhs

/-- Pure-target form of the rank-one Bures identity. -/
theorem finiteBuresTrace_sq_rankOne_right
    {n : Type*} [Fintype n] [DecidableEq n]
    {C : Matrix n n ℂ} (hC : C.PosSemidef) (v : n → ℂ) :
    (CFC.sqrt (CFC.conjSqrt C (Matrix.vecMulVec v (star v)))).trace.re ^ 2 =
      (finiteComplexInner v (C *ᵥ v)).re := by
  have hRay : (Matrix.vecMulVec v (star v)).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star v
  calc
    (CFC.sqrt (CFC.conjSqrt C (Matrix.vecMulVec v (star v)))).trace.re ^ 2 =
        (CFC.sqrt (CFC.conjSqrt (Matrix.vecMulVec v (star v)) C)).trace.re ^ 2 :=
      congrArg (fun x : ℝ => x ^ 2) (finiteBuresTrace_comm hC hRay)
    _ = (finiteComplexInner v (C *ᵥ v)).re :=
      finiteBuresTrace_sq_rankOne_left v hC

/-- **Rank-one support law `(14)`.**  Bures incidence with one occupied ray
vanishes exactly when source covariance annihilates that target vector. -/
theorem finiteBuresTrace_sq_rankOne_right_eq_zero_iff
    {n : Type*} [Fintype n] [DecidableEq n]
    {C : Matrix n n ℂ} (hC : C.PosSemidef) (v : n → ℂ) :
    (CFC.sqrt (CFC.conjSqrt C (Matrix.vecMulVec v (star v)))).trace.re ^ 2 = 0 ↔
      C *ᵥ v = 0 := by
  rw [finiteBuresTrace_sq_rankOne_right hC v]
  let q : ℂ := star v ⬝ᵥ C *ᵥ v
  have hq : 0 ≤ q := hC.dotProduct_mulVec_nonneg v
  have hinner : finiteComplexInner v (C *ᵥ v) = q := by
    unfold finiteComplexInner q dotProduct
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.star_apply, RCLike.star_def]
  rw [hinner]
  have hreal : q.re = 0 ↔ q = 0 := by
    constructor
    · intro hre
      apply Complex.ext
      · simpa using hre
      · simpa using (Complex.nonneg_iff.mp hq).2.symm
    · intro hq0
      simp [hq0]
  rw [hreal]
  exact hC.dotProduct_mulVec_zero_iff v

/-- Positive square root and the original covariance have exactly the same
kernel. -/
theorem finiteMatrix_sqrt_mulVec_eq_zero_iff
    {n : Type*} [Fintype n] [DecidableEq n]
    {C : Matrix n n ℂ} (hC : C.PosSemidef) (v : n → ℂ) :
    CFC.sqrt C *ᵥ v = 0 ↔ C *ᵥ v = 0 := by
  let S : Matrix n n ℂ := CFC.sqrt C
  have hSH : Sᴴ = S := by
    simpa [S, Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg C).star_eq
  have hS2 : S * S = C := by
    simpa [S, pow_two] using CFC.sq_sqrt C hC.nonneg
  have hker := Matrix.conjTranspose_mul_self_mulVec_eq_zero S v
  rw [hSH, hS2] at hker
  exact hker.symm

/-- **Complete finite occupied-support law `(14)`.**  Fidelity from a
positive source to every probability mixture of occupied rays vanishes
exactly when source covariance annihilates every occupied target.  The
forward direction tests Dirac mixtures; the reverse direction keeps every
weighted sheet in the synthesis matrix. -/
theorem finiteBuresTrace_allWeightedTargetMixtures_eq_zero_iff
    {i : Type*} [Fintype i] [Nonempty i] {n : ℕ}
    {C : Matrix (Fin n) (Fin n) ℂ} (hC : C.PosSemidef)
    (target : i → Fin n → ℂ) :
    (∀ weight : i → ℝ≥0, (∑ j, weight j) = 1 →
      (CFC.sqrt (CFC.conjSqrt C
        (finiteWeightedCovarianceMatrix weight target))).trace.re = 0) ↔
      ∀ j, C *ᵥ target j = 0 := by
  classical
  constructor
  · intro hall j
    let weight : i → ℝ≥0 := Pi.single j 1
    have hweight : (∑ k, weight k) = 1 := by simp [weight]
    have hzero := hall weight hweight
    have hcov : finiteWeightedCovarianceMatrix weight target =
        Matrix.vecMulVec (target j) (star (target j)) := by
      ext a b
      simp [finiteWeightedCovarianceMatrix, weight]
    rw [hcov] at hzero
    have hsqzero := congrArg (fun x : ℝ => x ^ 2) hzero
    exact (finiteBuresTrace_sq_rankOne_right_eq_zero_iff
      hC (target j)).mp (by simpa using hsqzero)
  · intro hkill weight _
    let U : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt C
    let V : Matrix (Fin n) i ℂ :=
      finiteWeightedSynthesisMatrix weight target
    have hUH : Uᴴ = U := by
      simpa [U, Matrix.star_eq_conjTranspose] using
        (CFC.sqrt_nonneg C).star_eq
    have hU2 : U * U = C := by
      simpa [U, pow_two] using CFC.sq_sqrt C hC.nonneg
    have hcovU : U * Uᴴ = C := by rw [hUH, hU2]
    have hcovV : V * Vᴴ = finiteWeightedCovarianceMatrix weight target := by
      exact finiteWeightedSynthesisMatrix_mul_conjTranspose weight target
    have hUV : U * V = 0 := by
      ext a j
      have hj : U *ᵥ target j = 0 :=
        (finiteMatrix_sqrt_mulVec_eq_zero_iff hC (target j)).2 (hkill j)
      have hja : (∑ k, U a k * target j k) = 0 := by
        simpa [Matrix.mulVec, dotProduct] using congrFun hj a
      change (∑ k, U a k *
        ((NNReal.sqrt (weight j) : ℂ) * target j k)) = 0
      calc
        (∑ k, U a k *
            ((NNReal.sqrt (weight j) : ℂ) * target j k)) =
            (NNReal.sqrt (weight j) : ℂ) *
              ∑ k, U a k * target j k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = 0 := by rw [hja, mul_zero]
    have hK : Uᴴ * V = 0 := by simpa [hUH] using hUV
    have hfid := finiteMatrixNuclearNorm_conjTranspose_mul_eq_buresTrace U V
    rw [hcovU, hcovV] at hfid
    have hnuclear : finiteMatrixNuclearNorm (Uᴴ * V) = 0 :=
      (finiteMatrixNuclearNorm_eq_zero_iff (Uᴴ * V)).2 hK
    exact hfid.symm.trans hnuclear

theorem star_dotProduct_eq_finiteComplexInner
    {n : Type*} [Fintype n] (u v : n → ℂ) :
    star u ⬝ᵥ v = finiteComplexInner u v := by
  unfold dotProduct finiteComplexInner
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.star_apply, RCLike.star_def]

/-- Pure-source fidelity against a nonnegative occupied-ray mixture is the
weighted average of squared endpoint overlaps. -/
theorem finiteBuresTrace_sq_weightedTargetMixture
    {i : Type*} [Fintype i] {n : ℕ}
    (weight : i → ℝ≥0) (target : i → Fin n → ℂ) (u : Fin n → ℂ) :
    (CFC.sqrt (CFC.conjSqrt (Matrix.vecMulVec u (star u))
      (finiteWeightedCovarianceMatrix weight target))).trace.re ^ 2 =
      ∑ j, (weight j : ℝ) * ‖finiteComplexInner u (target j)‖ ^ 2 := by
  classical
  rw [finiteBuresTrace_sq_rankOne_left u
    (finiteWeightedCovarianceMatrix_posSemidef weight target)]
  rw [finiteWeightedCovarianceMatrix_eq_finiteDesignGram]
  have hquad := finiteDesignGram_quadratic_expand
    target (fun j => (weight j : ℝ)) u
  rw [← star_dotProduct_eq_finiteComplexInner]
  calc
    (star u ⬝ᵥ (finiteDesignGram target
        (fun j => (weight j : ℝ))).mulVec u).re =
        (((∑ j, (weight j : ℝ) *
          ‖finiteComplexInner u (target j)‖ ^ 2 : ℝ) : ℂ)).re :=
      congrArg Complex.re hquad
    _ = ∑ j, (weight j : ℝ) *
        ‖finiteComplexInner u (target j)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rfl

/-- Values obtained from every probability mixture of a finite occupied
target family against one pure source ray. -/
def finitePureBuresMixtureValueSet
    {i : Type*} [Fintype i] {n : ℕ}
    (u : Fin n → ℂ) (target : i → Fin n → ℂ) : Set ℝ :=
  {q | ∃ weight : i → ℝ≥0, (∑ j, weight j) = 1 ∧
    q = (CFC.sqrt (CFC.conjSqrt (Matrix.vecMulVec u (star u))
      (finiteWeightedCovarianceMatrix weight target))).trace.re ^ 2}

/-- Largest squared overlap with a finite occupied target family. -/
def finitePureTargetFidelityMaximum
    {i : Type*} [Fintype i] [Nonempty i] {n : ℕ}
    (u : Fin n → ℂ) (target : i → Fin n → ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun j => ‖finiteComplexInner u (target j)‖ ^ 2)

theorem finitePureTargetFidelity_le_maximum
    {i : Type*} [Fintype i] [Nonempty i] {n : ℕ}
    (u : Fin n → ℂ) (target : i → Fin n → ℂ) (j : i) :
    ‖finiteComplexInner u (target j)‖ ^ 2 ≤
      finitePureTargetFidelityMaximum u target := by
  exact Finset.le_sup'
    (fun k => ‖finiteComplexInner u (target k)‖ ^ 2)
    (Finset.mem_univ j)

/-- **Deterministic-source occupied-body law `(11)`.**  Among all probability
mixtures of finitely many occupied rays, pure-source Bures fidelity squared
has a greatest value, and it is exactly the largest squared overlap with one
occupied endpoint.  Mixtures cannot improve on the hardest ray. -/
theorem finitePureBuresMixtureValueSet_isGreatest
    {i : Type*} [Fintype i] [Nonempty i] {n : ℕ}
    (u : Fin n → ℂ) (target : i → Fin n → ℂ) :
    IsGreatest (finitePureBuresMixtureValueSet u target)
      (finitePureTargetFidelityMaximum u target) := by
  classical
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_eq_sup'
    Finset.univ_nonempty
    (fun j => ‖finiteComplexInner u (target j)‖ ^ 2)
  let weight : i → ℝ≥0 := Pi.single c 1
  have hweight : (∑ j, weight j) = 1 := by
    simp [weight]
  have hattain :
      (CFC.sqrt (CFC.conjSqrt (Matrix.vecMulVec u (star u))
        (finiteWeightedCovarianceMatrix weight target))).trace.re ^ 2 =
        finitePureTargetFidelityMaximum u target := by
    rw [finiteBuresTrace_sq_weightedTargetMixture]
    calc
      (∑ x, (weight x : ℝ) * ‖finiteComplexInner u (target x)‖ ^ 2) =
          ‖finiteComplexInner u (target c)‖ ^ 2 := by
        rw [Finset.sum_eq_single c]
        · simp [weight]
        · intro b _ hbc
          simp [weight, hbc]
        · simp
      _ = finitePureTargetFidelityMaximum u target := hc.symm
  constructor
  · exact ⟨weight, hweight, hattain.symm⟩
  · rintro q ⟨w, hw, rfl⟩
    rw [finiteBuresTrace_sq_weightedTargetMixture]
    calc
      (∑ j, (w j : ℝ) * ‖finiteComplexInner u (target j)‖ ^ 2) ≤
          ∑ j, (w j : ℝ) * finitePureTargetFidelityMaximum u target := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left
          (finitePureTargetFidelity_le_maximum u target j)
          (NNReal.coe_nonneg (w j))
      _ = finitePureTargetFidelityMaximum u target := by
        rw [← Finset.sum_mul]
        have hwReal : (∑ j, (w j : ℝ)) = 1 := by
          exact_mod_cast hw
        rw [hwReal, one_mul]

theorem sSup_finitePureBuresMixtureValueSet
    {i : Type*} [Fintype i] [Nonempty i] {n : ℕ}
    (u : Fin n → ℂ) (target : i → Fin n → ℂ) :
    sSup (finitePureBuresMixtureValueSet u target) =
      finitePureTargetFidelityMaximum u target :=
  (finitePureBuresMixtureValueSet_isGreatest u target).csSup_eq

/-- **Rank-sensitive Bures comparison.**  For arbitrary positive semidefinite
finite matrices, Bures root fidelity squared is bounded by target rank times
the source--target Hilbert--Schmidt pairing.  Singular matrices are included;
the rank is the actual target rank rather than ambient dimension. -/
theorem finiteBuresTrace_sq_le_rank_mul_traceProduct
    {n : Type*} [Fintype n] [DecidableEq n]
    {C M : Matrix n n ℂ} (hC : C.PosSemidef) (hM : M.PosSemidef) :
    (CFC.sqrt (CFC.conjSqrt C M)).trace.re ^ 2 ≤
      (M.rank : ℝ) * (C * M).trace.re := by
  let U : Matrix n n ℂ := CFC.sqrt C
  let V : Matrix n n ℂ := CFC.sqrt M
  let K : Matrix n n ℂ := Uᴴ * V
  have hUH : Uᴴ = U := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg C).star_eq
  have hVH : Vᴴ = V := by
    simpa [V, Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg M).star_eq
  have hU2 : U * U = C := by
    simpa [U, pow_two] using CFC.sq_sqrt C hC.nonneg
  have hV2 : V * V = M := by
    simpa [V, pow_two] using CFC.sq_sqrt M hM.nonneg
  have hcovU : U * Uᴴ = C := by rw [hUH, hU2]
  have hcovV : V * Vᴴ = M := by rw [hVH, hV2]
  have hfid : finiteMatrixNuclearNorm K =
      (CFC.sqrt (CFC.conjSqrt C M)).trace.re := by
    simpa [K, hcovU, hcovV] using
      (finiteMatrixNuclearNorm_conjTranspose_mul_eq_buresTrace U V)
  have hVrank : V.rank = M.rank := by
    calc
      V.rank = (Vᴴ * V).rank := (Matrix.rank_conjTranspose_mul_self V).symm
      _ = M.rank := by rw [hVH, hV2]
  have hKrank : K.rank ≤ M.rank := by
    calc
      K.rank ≤ V.rank := by
        exact Matrix.rank_mul_le_right Uᴴ V
      _ = M.rank := hVrank
  have hKgram : Kᴴ * K = V * C * V := by
    simp only [K, Matrix.conjTranspose_mul, hUH, hVH]
    calc
      (V * U) * (U * V) = V * (U * U) * V := by noncomm_ring
      _ = V * C * V := by rw [hU2]
  have hhs : finiteMatrixHilbertSchmidtSq K = (C * M).trace.re := by
    unfold finiteMatrixHilbertSchmidtSq
    rw [hKgram, Matrix.trace_mul_cycle V C V,
      Matrix.trace_mul_cycle V V C, Matrix.mul_assoc, hV2]
  have hhs0 : 0 ≤ finiteMatrixHilbertSchmidtSq K := by
    rw [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq]
    positivity
  have hnuclear := finiteMatrixNuclearNorm_sq_le_rank_mul_hilbertSchmidtSq K
  rw [hfid] at hnuclear
  calc
    (CFC.sqrt (CFC.conjSqrt C M)).trace.re ^ 2 ≤
        (K.rank : ℝ) * finiteMatrixHilbertSchmidtSq K := hnuclear
    _ ≤ (M.rank : ℝ) * finiteMatrixHilbertSchmidtSq K := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hKrank) hhs0
    _ = (M.rank : ℝ) * (C * M).trace.re := by rw [hhs]

end

end GaloisForLFunctions.HTGeometry
