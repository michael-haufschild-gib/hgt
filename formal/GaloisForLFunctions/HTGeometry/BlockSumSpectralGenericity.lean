import GaloisForLFunctions.HTGeometry.PolynomialHermitianSpectrumGenericity
import GaloisForLFunctions.HTGeometry.DisconnectedProjectiveGapModuleLaw
import GaloisForLFunctions.HTGeometry.BlockDiagonalDeterminant
import GaloisForLFunctions.HTGeometry.RootPacketRelabelling

/-!
# Genericity of transverse component spectra

Two non-interacting components have transverse rational gap modules as soon as
the *concatenation* of their spectra is maximally projective: a relation that is
balanced inside each component is balanced overall.  Concatenated spectra are
the spectra of the block-diagonal family, so the existing one-witness
polynomial genericity theorem applies to them verbatim.

This file records the reduction — which holds for any finite family of
components — and the two-block direct sum, whose characteristic determinant
factors by `Matrix.det_fromBlocks_zero₁₂`.
-/

open scoped Matrix BigOperators
open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Concatenated spectra control component transversality -/

/-- **Maximal projectivity of a concatenated spectrum forces component
transversality.**  A relation balanced inside every component is balanced
overall, so it is killed by maximal projectivity of the concatenation. -/
theorem componentProjectivelyIndependent_of_maximallyProjective_sigma
    {C : Type*} [Fintype C] {I : C → Type*} [∀ c, Fintype (I c)]
    (energy : ∀ c, I c → ℝ)
    (hmax : MaximallyProjectiveEnergy
      (fun x : Σ c, I c => energy x.1 x.2)) :
    ComponentProjectivelyIndependent energy := by
  classical
  intro k hbalanced hzero c
  let K : (Σ c, I c) → ℤ := fun x => k x.1 x.2
  have hKbalanced : SpectralCharacterBalanced K := by
    show (∑ x : Σ c, I c, K x) = 0
    rw [Fintype.sum_sigma]
    exact Finset.sum_eq_zero fun c _ => hbalanced c
  have hKzero : (∑ x : Σ c, I c, (K x : ℝ) * energy x.1 x.2) = 0 := by
    rw [Fintype.sum_sigma]
    exact hzero
  have hK := hmax K hKbalanced hKzero
  funext i
  exact congrFun hK ⟨c, i⟩

/-! ### The direct sum of two square matrices -/

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Direct sum of two square matrices. -/
def blockSum {R : Type*} [Zero R] (A : Matrix I I R) (D : Matrix J J R) :
    Matrix (I ⊕ J) (I ⊕ J) R :=
  Matrix.fromBlocks A 0 0 D

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem blockSum_map {R R' : Type*} [Zero R] [Zero R'] (f : R → R')
    (hf : f 0 = 0) (A : Matrix I I R) (D : Matrix J J R) :
    (blockSum A D).map f = blockSum (A.map f) (D.map f) := by
  ext x y
  cases x <;> cases y <;> simp [blockSum, Matrix.fromBlocks, hf]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem conjTranspose_blockSum (A : Matrix I I ℂ) (D : Matrix J J ℂ) :
    (blockSum A D)ᴴ = blockSum Aᴴ Dᴴ := by
  ext x y
  cases x <;> cases y <;>
    simp [blockSum, Matrix.fromBlocks, Matrix.conjTranspose_apply]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem isHermitian_blockSum {A : Matrix I I ℂ} {D : Matrix J J ℂ}
    (hA : A.IsHermitian) (hD : D.IsHermitian) :
    (blockSum A D).IsHermitian := by
  show (blockSum A D)ᴴ = _
  rw [conjTranspose_blockSum, hA, hD]

theorem scalar_sub_blockSum (A : Matrix I I ℂ) (D : Matrix J J ℂ) (μ : ℂ) :
    Matrix.scalar (I ⊕ J) μ - blockSum A D =
      blockSum (Matrix.scalar I μ - A) (Matrix.scalar J μ - D) := by
  ext x y
  cases x <;> cases y <;>
    simp [blockSum, Matrix.fromBlocks, Matrix.scalar_apply,
      Matrix.diagonal_apply]

theorem det_blockSum {R : Type*} [CommRing R] (A : Matrix I I R)
    (D : Matrix J J R) : (blockSum A D).det = A.det * D.det :=
  Matrix.det_fromBlocks_zero₁₂ A 0 D

/-- The characteristic relation of a direct sum factors. -/
theorem matrixCharpolyRelation_blockSum (A : Matrix I I ℂ) (D : Matrix J J ℂ)
    (μ : ℂ) :
    matrixCharpolyRelation (blockSum A D, μ) =
      matrixCharpolyRelation (A, μ) * matrixCharpolyRelation (D, μ) := by
  show (Matrix.scalar (I ⊕ J) μ - blockSum A D).det = _
  rw [scalar_sub_blockSum, det_blockSum]
  rfl

/-- A concatenated root packet is a root packet of the direct sum. -/
theorem matrixCharpolyRelation_blockSum_sumElim (A : Matrix I I ℂ)
    (D : Matrix J J ℂ) {e₁ : I → ℝ} {e₂ : J → ℝ}
    (h₁ : ∀ i, matrixCharpolyRelation (A, (e₁ i : ℂ)) = 0)
    (h₂ : ∀ j, matrixCharpolyRelation (D, (e₂ j : ℂ)) = 0)
    (x : I ⊕ J) :
    matrixCharpolyRelation (blockSum A D, ((Sum.elim e₁ e₂ x : ℝ) : ℂ)) = 0 := by
  cases x with
  | inl i =>
      rw [matrixCharpolyRelation_blockSum]
      simp [h₁ i]
  | inr j =>
      rw [matrixCharpolyRelation_blockSum]
      simp [h₂ j]

/-! ### One-witness genericity for two non-interacting components -/

/-- Direct sum of two polynomial matrix families over one parameter space. -/
def blockSumPolynomialMatrix {m : ℕ}
    (M₁ : Matrix I I (MvPolynomial (Fin m) ℂ))
    (M₂ : Matrix J J (MvPolynomial (Fin m) ℂ)) :
    Matrix (I ⊕ J) (I ⊕ J) (MvPolynomial (Fin m) ℂ) :=
  blockSum M₁ M₂

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem blockSumPolynomialMatrix_eval {m : ℕ}
    (M₁ : Matrix I I (MvPolynomial (Fin m) ℂ))
    (M₂ : Matrix J J (MvPolynomial (Fin m) ℂ)) (p : Fin m → ℝ) :
    (blockSumPolynomialMatrix M₁ M₂).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (p t : ℂ))) =
      blockSum
        (M₁.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (p t : ℂ))))
        (M₂.map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (fun t => (p t : ℂ)))) :=
  blockSum_map _ (map_zero _) M₁ M₂

/-- **Two-component transversality is generic.**  One parameter at which the
concatenated spectrum of two non-interacting polynomial Hermitian families is
maximally projective makes the concatenation maximally projective on a dense,
residual, full-measure set of parameters. -/
theorem blockSumProjectiveGenericSet_dense_residual_fullMeasure {m : ℕ}
    (M₁ : Matrix I I (MvPolynomial (Fin m) ℂ))
    (M₂ : Matrix J J (MvPolynomial (Fin m) ℂ))
    (p₀ : Fin m → ℝ) (e₁ : I → ℝ) (e₂ : J → ℝ)
    (hmax : MaximallyProjectiveEnergy (Sum.elim e₁ e₂))
    (hroot₁ : ∀ i, matrixCharpolyRelation
      (M₁.map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => (p₀ t : ℂ))), (e₁ i : ℂ)) = 0)
    (hroot₂ : ∀ j, matrixCharpolyRelation
      (M₂.map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => (p₀ t : ℂ))), (e₂ j : ℂ)) = 0) :
    Dense (polynomialMatrixProjectiveGenericSet
        (blockSumPolynomialMatrix M₁ M₂)) ∧
      polynomialMatrixProjectiveGenericSet
          (blockSumPolynomialMatrix M₁ M₂) ∈ residual (Fin m → ℝ) ∧
      volume (polynomialMatrixProjectiveGenericSet
        (blockSumPolynomialMatrix M₁ M₂))ᶜ = 0 := by
  refine polynomialMatrixProjectiveGenericSet_dense_residual_fullMeasure
    (blockSumPolynomialMatrix M₁ M₂) p₀ (Sum.elim e₁ e₂) hmax
    (MaximallyProjectiveEnergy.injective hmax) ?_
  intro x
  rw [blockSumPolynomialMatrix_eval]
  exact matrixCharpolyRelation_blockSum_sumElim _ _ hroot₁ hroot₂ x

/-! ### Any finite family of non-interacting components -/

section Family

variable {C : Type*} [Fintype C] [DecidableEq C]
    {I : C → Type*} [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)]

theorem scalar_sub_blockDiagonal' (M : ∀ c, Matrix (I c) (I c) ℂ) (μ : ℂ) :
    Matrix.scalar (Σ c, I c) μ - Matrix.blockDiagonal' M =
      Matrix.blockDiagonal' fun c => Matrix.scalar (I c) μ - M c := by
  classical
  refine Matrix.ext fun x y => ?_
  obtain ⟨c, a⟩ := x
  obtain ⟨d, b⟩ := y
  by_cases hcd : c = d
  · subst hcd
    rw [Matrix.blockDiagonal'_apply_eq
        (fun c => Matrix.scalar (I c) μ - M c),
      Matrix.sub_apply, Matrix.sub_apply, Matrix.blockDiagonal'_apply_eq M]
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Sigma.mk.injEq]
  · rw [Matrix.blockDiagonal'_apply_ne
        (fun c => Matrix.scalar (I c) μ - M c) a b hcd,
      Matrix.sub_apply, Matrix.blockDiagonal'_apply_ne M a b hcd]
    simp [Matrix.scalar_apply, Sigma.mk.injEq, hcd]

/-- The characteristic relation of a block-diagonal family factors over its
blocks. -/
theorem matrixCharpolyRelation_blockDiagonal'
    (M : ∀ c, Matrix (I c) (I c) ℂ) (μ : ℂ) :
    matrixCharpolyRelation (Matrix.blockDiagonal' M, μ) =
      ∏ c, matrixCharpolyRelation (M c, μ) := by
  show (Matrix.scalar (Σ c, I c) μ - Matrix.blockDiagonal' M).det = _
  rw [scalar_sub_blockDiagonal', det_blockDiagonal']
  rfl

/-- A concatenated root packet is a root packet of the block-diagonal
family. -/
theorem matrixCharpolyRelation_blockDiagonal'_concat
    (M : ∀ c, Matrix (I c) (I c) ℂ) {e : ∀ c, I c → ℝ}
    (h : ∀ c i, matrixCharpolyRelation (M c, (e c i : ℂ)) = 0)
    (x : Σ c, I c) :
    matrixCharpolyRelation (Matrix.blockDiagonal' M, ((e x.1 x.2 : ℝ) : ℂ))
      = 0 := by
  rw [matrixCharpolyRelation_blockDiagonal']
  exact Finset.prod_eq_zero (Finset.mem_univ x.1) (h x.1 x.2)

omit [Fintype C] [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)] in
theorem blockDiagonal'_map {m : ℕ}
    (M : ∀ c, Matrix (I c) (I c) (MvPolynomial (Fin m) ℂ)) (p : Fin m → ℝ) :
    (Matrix.blockDiagonal' M).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (p t : ℂ))) =
      Matrix.blockDiagonal' fun c =>
        (M c).map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (fun t => (p t : ℂ))) := by
  classical
  refine Matrix.ext fun x y => ?_
  obtain ⟨c, a⟩ := x
  obtain ⟨d, b⟩ := y
  by_cases hcd : c = d
  · subst hcd
    rw [Matrix.map_apply, Matrix.blockDiagonal'_apply_eq M,
      Matrix.blockDiagonal'_apply_eq]
    rfl
  · rw [Matrix.map_apply, Matrix.blockDiagonal'_apply_ne M a b hcd,
      Matrix.blockDiagonal'_apply_ne _ a b hcd, map_zero]

/-- **Component transversality is generic for any finite family.**  One
parameter at which the concatenated spectrum of a finite family of
non-interacting polynomial Hermitian families is maximally projective makes the
concatenation maximally projective on a dense, residual, full-measure set of
parameters. -/
theorem blockDiagonalProjectiveGenericSet_dense_residual_fullMeasure {m : ℕ}
    (M : ∀ c, Matrix (I c) (I c) (MvPolynomial (Fin m) ℂ))
    (p₀ : Fin m → ℝ) (e : ∀ c, I c → ℝ)
    (hmax : MaximallyProjectiveEnergy (fun x : Σ c, I c => e x.1 x.2))
    (hroot : ∀ c i, matrixCharpolyRelation
      ((M c).map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => (p₀ t : ℂ))), (e c i : ℂ)) = 0) :
    Dense (polynomialMatrixProjectiveGenericSet
        (Matrix.blockDiagonal' M)) ∧
      polynomialMatrixProjectiveGenericSet (Matrix.blockDiagonal' M) ∈
        residual (Fin m → ℝ) ∧
      volume (polynomialMatrixProjectiveGenericSet
        (Matrix.blockDiagonal' M))ᶜ = 0 := by
  refine polynomialMatrixProjectiveGenericSet_dense_residual_fullMeasure
    (Matrix.blockDiagonal' M) p₀ (fun x : Σ c, I c => e x.1 x.2) hmax
    (MaximallyProjectiveEnergy.injective hmax) ?_
  intro x
  rw [blockDiagonal'_map]
  exact matrixCharpolyRelation_blockDiagonal'_concat _ hroot x

omit [Fintype C] [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)] in
theorem isHermitian_blockDiagonal' {H : ∀ c, Matrix (I c) (I c) ℂ}
    (hH : ∀ c, (H c).IsHermitian) :
    (Matrix.blockDiagonal' H).IsHermitian := by
  show (Matrix.blockDiagonal' H)ᴴ = _
  rw [Matrix.blockDiagonal'_conjTranspose]
  exact congrArg Matrix.blockDiagonal' (funext hH)

/-- The characteristic roots of a block-diagonal Hermitian matrix are the
concatenated eigenvalues of its blocks. -/
theorem rootMultiset_blockDiagonal' (H : ∀ c, Matrix (I c) (I c) ℂ)
    (hH : ∀ c, (H c).IsHermitian) :
    Finset.univ.val.map
        (fun x : Σ c, I c => (((hH x.1).eigenvalues x.2 : ℝ) : ℂ)) =
      (Matrix.blockDiagonal' H).charpoly.roots := by
  classical
  rw [charpoly_blockDiagonal']
  have hfac : ∀ c, (H c).charpoly =
      ∏ i, (Polynomial.X -
        Polynomial.C (((hH c).eigenvalues i : ℝ) : ℂ)) :=
    fun c => (hH c).charpoly_eq
  simp_rw [hfac]
  rw [Finset.prod_sigma' Finset.univ (fun _ => Finset.univ)
    (fun c i => Polynomial.X -
      Polynomial.C (((hH c).eigenvalues i : ℝ) : ℂ))]
  rw [Finset.univ_sigma_univ]
  rw [← Polynomial.roots_multiset_prod_X_sub_C
    (Finset.univ.val.map
      (fun x : Σ c, I c => (((hH x.1).eigenvalues x.2 : ℝ) : ℂ)))]
  congr 1
  rw [Multiset.map_map]
  rfl

/-- **Component transversality from the block-diagonal generic set.**  At a
parameter where the block-diagonal family has maximally projective spectrum, the
block spectra are mutually projectively independent. -/
theorem componentProjectivelyIndependent_of_mem_blockDiagonalGenericSet
    {m : ℕ} (M : ∀ c, Matrix (I c) (I c) (MvPolynomial (Fin m) ℂ))
    (p : Fin m → ℝ)
    (hherm : ∀ c, ((M c).map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
      (fun t => (p t : ℂ)))).IsHermitian)
    (hp : p ∈ polynomialMatrixProjectiveGenericSet (Matrix.blockDiagonal' M)) :
    ComponentProjectivelyIndependent (fun c => (hherm c).eigenvalues) := by
  classical
  have hmapEq := blockDiagonal'_map M p
  have hHermBD :
      ((Matrix.blockDiagonal' M).map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => (p t : ℂ)))).IsHermitian := by
    rw [hmapEq]
    exact isHermitian_blockDiagonal' hherm
  have hmax := maximallyProjectiveEnergy_eigenvalues_of_mem_polynomialMatrixGenericSet
    (Matrix.blockDiagonal' M) p hp hHermBD
  refine componentProjectivelyIndependent_of_maximallyProjective_sigma _ ?_
  refine maximallyProjectiveEnergy_of_rootMultiset hHermBD hmax _ ?_
  rw [hmapEq] at hHermBD ⊢
  exact rootMultiset_blockDiagonal' _ hherm

end Family

end

end GaloisForLFunctions.HTGeometry
