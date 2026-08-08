/-
# Finite nuclear incidence law

Rectangular incidence matrices require a nuclear norm which retains every nonzero singular value
with multiplicity.  This module defines that norm from the positive Gram matrix, proves the exact
left--right Gram invariance by the rectangular characteristic-polynomial identity, and identifies
the trace of a positive square root with the corresponding singular-value sum.
-/
import GaloisForLFunctions.HTGeometry.ComplexIntegralGram
import GaloisForLFunctions.HTGeometry.ReplicaHilbertCoareaIncidenceLaw
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

end

end GaloisForLFunctions.HTGeometry
