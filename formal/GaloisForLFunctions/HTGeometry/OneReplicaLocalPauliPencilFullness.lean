import GaloisForLFunctions.HTGeometry.PauliCharacterFirstDefectCovariance
import GaloisForLFunctions.HTGeometry.CentralCasimirComplementHallExpansion
import GaloisForLFunctions.HTGeometry.NonidentityPauliWordCount
import GaloisForLFunctions.HTGeometry.FiniteQubitPauliComplexBasis
import GaloisForLFunctions.HTGeometry.PauliCharacterProjectorExtraction

/-!
# Exact one-replica local-Pauli support Casimir and full pencil

This module proves the finite algebraic core of one-replica planar cavity decay. The literal
one-site Pauli commutator matrices are Hermitian, their quadratic Casimir is exactly `8 |T|` on
each nonempty Pauli-support block, and their simultaneous kernel consists exactly of scalar
operators. Consequently the orthogonal complement is the literal trace-zero operator space.

The explicit block inverse-square-root scale satisfies `η₁(C) = C⁻¹`. Central-Casimir scaling is
exactly bi-tight, and every bounded-weight Pauli pencil retaining a common strictly positive
weight-one variance is full. Adding arbitrary higher-weight Kraus coefficients cannot destroy the
Hall rank inequality.
-/

open scoped BigOperators Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def oneReplicaLocalPauliCommutatorMatrix (i : σ) (a : Fin 3) :
    Matrix (FiniteQubitConfiguration σ × FiniteQubitConfiguration σ)
      (FiniteQubitConfiguration σ × FiniteQubitConfiguration σ) ℂ :=
  matrixCommutatorRepresentation (finitePauliMatrix (singlePauliAxisLabel i a))

theorem oneReplicaLocalPauliCommutatorMatrix_eq_singleSite
    (i : σ) (a : Fin 3) :
    oneReplicaLocalPauliCommutatorMatrix i a =
      matrixCommutatorRepresentation
        (finiteSingleSiteMatrix i (finiteQubitPauli a)) := by
  rw [oneReplicaLocalPauliCommutatorMatrix, finiteSingleSiteMatrix_pauli]
  rfl

theorem oneReplicaLocalPauliCommutatorMatrix_conjTranspose
    (i : σ) (a : Fin 3) :
    (oneReplicaLocalPauliCommutatorMatrix i a).conjTranspose =
      oneReplicaLocalPauliCommutatorMatrix i a := by
  rw [oneReplicaLocalPauliCommutatorMatrix_eq_singleSite]
  exact matrixCommutatorRepresentation_conjTranspose
    (by rw [finiteSingleSiteMatrix_pauli]; exact finitePauliMatrix_isHermitian _)

theorem oneReplicaLocalPauliCommutatorMatrix_bracket
    (i : σ) (a b : Fin 3) :
    oneReplicaLocalPauliCommutatorMatrix i a *
          oneReplicaLocalPauliCommutatorMatrix i b -
        oneReplicaLocalPauliCommutatorMatrix i b *
          oneReplicaLocalPauliCommutatorMatrix i a =
      ∑ k : Fin 3, pauliStructureCoeff a b k •
        oneReplicaLocalPauliCommutatorMatrix i k := by
  simp_rw [oneReplicaLocalPauliCommutatorMatrix_eq_singleSite]
  rw [matrixCommutatorRepresentation_bracket, finiteSingleSitePauli_bracket]
  simp

theorem oneReplicaLocalPauliCommutatorMatrix_comm_of_ne
    {i j : σ} (hij : i ≠ j) (a b : Fin 3) :
    oneReplicaLocalPauliCommutatorMatrix i a *
        oneReplicaLocalPauliCommutatorMatrix j b =
      oneReplicaLocalPauliCommutatorMatrix j b *
        oneReplicaLocalPauliCommutatorMatrix i a := by
  simp_rw [oneReplicaLocalPauliCommutatorMatrix_eq_singleSite]
  exact matrixCommutatorRepresentation_comm_of_comm
    (finiteSingleSiteMatrix_comm_of_ne hij _ _)

theorem oneReplicaLocalPauli_quadraticCasimir_commutes
    (j : σ) (b : Fin 3) :
    (∑ p : σ × Fin 3, oneReplicaLocalPauliCommutatorMatrix p.1 p.2 *
        oneReplicaLocalPauliCommutatorMatrix p.1 p.2) *
        oneReplicaLocalPauliCommutatorMatrix j b =
      oneReplicaLocalPauliCommutatorMatrix j b *
        ∑ p : σ × Fin 3, oneReplicaLocalPauliCommutatorMatrix p.1 p.2 *
          oneReplicaLocalPauliCommutatorMatrix p.1 p.2 := by
  rw [Fintype.sum_prod_type, Finset.sum_mul, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hij : i = j
  · subst i
    exact quadraticCasimir_commutes_of_antisymmetric_structure
      (oneReplicaLocalPauliCommutatorMatrix j)
      pauliStructureCoeff
      (oneReplicaLocalPauliCommutatorMatrix_bracket j)
      pauliStructureCoeff_antisymmetric_contracted
      b
  · rw [Finset.sum_mul, Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    let A := oneReplicaLocalPauliCommutatorMatrix i a
    let B := oneReplicaLocalPauliCommutatorMatrix j b
    have hAB : A * B = B * A :=
      oneReplicaLocalPauliCommutatorMatrix_comm_of_ne hij a b
    change (A * A) * B = B * (A * A)
    calc
      (A * A) * B = A * (A * B) := Matrix.mul_assoc _ _ _
      _ = A * (B * A) := by rw [hAB]
      _ = (A * B) * A := (Matrix.mul_assoc _ _ _).symm
      _ = (B * A) * A := by rw [hAB]
      _ = B * (A * A) := Matrix.mul_assoc _ _ _

theorem ringCommutator_sq_finitePauliMatrix
    (Q P : σ → Option (Fin 3)) :
    ringCommutator (finitePauliMatrix Q)
        (ringCommutator (finitePauliMatrix Q) (finitePauliMatrix P)) =
      (2 * (1 - finitePauliConjugationSign Q P)) • finitePauliMatrix P := by
  have hQsq := finitePauliMatrix_mul_self Q
  have hconj := finitePauliMatrix_conj Q P
  simp only [ringCommutator]
  rw [Matrix.mul_sub, Matrix.sub_mul]
  calc
    finitePauliMatrix Q * (finitePauliMatrix Q * finitePauliMatrix P) -
          finitePauliMatrix Q * (finitePauliMatrix P * finitePauliMatrix Q) -
        (finitePauliMatrix Q * finitePauliMatrix P * finitePauliMatrix Q -
          finitePauliMatrix P * finitePauliMatrix Q * finitePauliMatrix Q) =
        (finitePauliMatrix Q * finitePauliMatrix Q) * finitePauliMatrix P -
          2 • (finitePauliMatrix Q * finitePauliMatrix P * finitePauliMatrix Q) +
          finitePauliMatrix P * (finitePauliMatrix Q * finitePauliMatrix Q) := by
            noncomm_ring
    _ = finitePauliMatrix P -
          2 • (finitePauliConjugationSign Q P • finitePauliMatrix P) +
          finitePauliMatrix P := by rw [hQsq, Matrix.one_mul, Matrix.mul_one, hconj]
    _ = (2 * (1 - finitePauliConjugationSign Q P)) • finitePauliMatrix P := by
      module

theorem oneReplicaLocalPauliCommutatorMatrix_sq_mulVec_pauli
    (i : σ) (a : Fin 3) (P : σ → Option (Fin 3)) :
    (oneReplicaLocalPauliCommutatorMatrix i a *
        oneReplicaLocalPauliCommutatorMatrix i a) *ᵥ Matrix.vec (finitePauliMatrix P) =
      (2 * (1 - boolPauliConjugationSign (some a) (P i))) •
        Matrix.vec (finitePauliMatrix P) := by
  rw [← Matrix.mulVec_mulVec]
  rw [oneReplicaLocalPauliCommutatorMatrix,
    matrixCommutatorRepresentation_mulVec_vec,
    matrixCommutatorRepresentation_mulVec_vec,
    ringCommutator_sq_finitePauliMatrix,
    finitePauliConjugationSign_singlePauliAxisLabel]
  rw [Matrix.vec_smul]

theorem sum_axis_oneReplicaLocalPauliCommutatorMatrix_sq_mulVec_pauli
    (i : σ) (P : σ → Option (Fin 3)) :
    (∑ a : Fin 3, oneReplicaLocalPauliCommutatorMatrix i a *
        oneReplicaLocalPauliCommutatorMatrix i a) *ᵥ Matrix.vec (finitePauliMatrix P) =
      (if P i = none then (0 : ℂ) else 8) • Matrix.vec (finitePauliMatrix P) := by
  rw [Matrix.sum_mulVec]
  simp_rw [oneReplicaLocalPauliCommutatorMatrix_sq_mulVec_pauli]
  rw [← Finset.sum_smul]
  have hcoeff : (∑ a : Fin 3,
      (2 * (1 - boolPauliConjugationSign (some a) (P i)) : ℂ)) =
      if P i = none then 0 else 8 := by
    cases hPi : P i with
    | none => simp [boolPauliConjugationSign]
    | some b =>
      fin_cases b <;>
          rw [Fin.sum_univ_three] <;>
          simp [boolPauliConjugationSign] <;> norm_num
  rw [hcoeff]

def finitePauliSupport (P : σ → Option (Fin 3)) : Finset σ :=
  Finset.univ.filter fun i => P i ≠ none

omit [DecidableEq σ] in
@[simp] theorem mem_finitePauliSupport (P : σ → Option (Fin 3)) (i : σ) :
    i ∈ finitePauliSupport P ↔ P i ≠ none := by
  simp [finitePauliSupport]

omit [DecidableEq σ] in
theorem sum_site_localPauli_eight_indicator (P : σ → Option (Fin 3)) :
    (∑ i : σ, if P i = none then (0 : ℂ) else 8) =
      8 * (finitePauliSupport P).card := by
  classical
  calc
    (∑ i : σ, if P i = none then (0 : ℂ) else 8) =
        ∑ i : σ, if P i ≠ none then (8 : ℂ) else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : P i = none <;> simp [hi]
    _ = ∑ i ∈ finitePauliSupport P, (8 : ℂ) := by
          rw [finitePauliSupport, Finset.sum_filter]
    _ = 8 * (finitePauliSupport P).card := by simp [mul_comm]

theorem oneReplicaLocalPauli_quadraticCasimir_mulVec_pauli
    (P : σ → Option (Fin 3)) :
    (∑ p : σ × Fin 3, oneReplicaLocalPauliCommutatorMatrix p.1 p.2 *
        oneReplicaLocalPauliCommutatorMatrix p.1 p.2) *ᵥ
        Matrix.vec (finitePauliMatrix P) =
      (8 * (finitePauliSupport P).card : ℂ) •
        Matrix.vec (finitePauliMatrix P) := by
  rw [Fintype.sum_prod_type, Matrix.sum_mulVec]
  simp_rw [sum_axis_oneReplicaLocalPauliCommutatorMatrix_sq_mulVec_pauli]
  rw [← Finset.sum_smul, sum_site_localPauli_eight_indicator]

def oneReplicaPauliSupportSubspace (T : Finset σ) :
    Submodule ℂ ((FiniteQubitConfiguration σ × FiniteQubitConfiguration σ) → ℂ) :=
  Submodule.span ℂ {x | ∃ P : σ → Option (Fin 3),
    finitePauliSupport P = T ∧ x = Matrix.vec (finitePauliMatrix P)}

theorem oneReplicaLocalPauli_quadraticCasimir_mulVec_of_mem_supportSubspace
    (T : Finset σ)
    (x : (FiniteQubitConfiguration σ × FiniteQubitConfiguration σ) → ℂ)
    (hx : x ∈ oneReplicaPauliSupportSubspace T) :
    (∑ p : σ × Fin 3, oneReplicaLocalPauliCommutatorMatrix p.1 p.2 *
        oneReplicaLocalPauliCommutatorMatrix p.1 p.2) *ᵥ x =
      (8 * T.card : ℂ) • x := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨P, hPT, rfl⟩ := hx
      rw [oneReplicaLocalPauli_quadraticCasimir_mulVec_pauli, hPT]
  | zero => simp
  | add x y _ _ hx hy => simp only [Matrix.mulVec_add, hx, hy, smul_add]
  | smul c x _ hx =>
      simp only [Matrix.mulVec_smul, hx, smul_smul]
      rw [mul_comm c]

def oneReplicaSupportBlockScale (v₁ : ℝ) (T : Finset σ) : ℝ :=
  (Real.sqrt (8 * v₁ * T.card))⁻¹

omit [Fintype σ] [DecidableEq σ] in
theorem oneReplicaSupportBlockScale_pos
    {v₁ : ℝ} (hv₁ : 0 < v₁) {T : Finset σ} (hT : T.Nonempty) :
    0 < oneReplicaSupportBlockScale v₁ T := by
  rw [oneReplicaSupportBlockScale]
  positivity

omit [Fintype σ] [DecidableEq σ] in
theorem oneReplicaSupportBlockCasimir_mul_scale_eq_inv
    {v₁ : ℝ} (hv₁ : 0 < v₁) {T : Finset σ} (hT : T.Nonempty) :
    (8 * v₁ * T.card) * oneReplicaSupportBlockScale v₁ T =
      (oneReplicaSupportBlockScale v₁ T)⁻¹ := by
  let d : ℝ := 8 * v₁ * T.card
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hs : Real.sqrt d ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd)
  change d * (Real.sqrt d)⁻¹ = ((Real.sqrt d)⁻¹)⁻¹
  rw [inv_inv]
  field_simp
  nlinarith [Real.sq_sqrt hd.le]

/-- Blockwise form of `η₁(C)=C⁻¹`: on a nonempty support block, insertion of the explicit
inverse-square-root scalar between the two one-site commutators gives its reciprocal. -/
theorem oneReplicaWeightOneCovariance_blockScale
    {v₁ : ℝ} (hv₁ : 0 < v₁) {T : Finset σ} (hT : T.Nonempty)
    (x : (FiniteQubitConfiguration σ × FiniteQubitConfiguration σ) → ℂ)
    (hx : x ∈ oneReplicaPauliSupportSubspace T) :
    (∑ p : σ × Fin 3,
        oneReplicaLocalPauliCommutatorMatrix p.1 p.2 *
          ((((v₁ * oneReplicaSupportBlockScale v₁ T : ℝ) : ℂ)) •
            oneReplicaLocalPauliCommutatorMatrix p.1 p.2)) *ᵥ x =
      (((oneReplicaSupportBlockScale v₁ T)⁻¹ : ℝ) : ℂ) • x := by
  simp_rw [Matrix.mul_smul]
  rw [← Finset.smul_sum, Matrix.smul_mulVec,
    oneReplicaLocalPauli_quadraticCasimir_mulVec_of_mem_supportSubspace T x hx,
    smul_smul]
  have hscale := oneReplicaSupportBlockCasimir_mul_scale_eq_inv hv₁ hT
  have hreal :
      (v₁ * oneReplicaSupportBlockScale v₁ T) * (8 * T.card : ℝ) =
        (oneReplicaSupportBlockScale v₁ T)⁻¹ := by
    calc
      (v₁ * oneReplicaSupportBlockScale v₁ T) * (8 * T.card : ℝ) =
          (8 * v₁ * T.card) * oneReplicaSupportBlockScale v₁ T := by ring
      _ = (oneReplicaSupportBlockScale v₁ T)⁻¹ := hscale
  have hcomplex :
      (((v₁ * oneReplicaSupportBlockScale v₁ T : ℝ) : ℂ)) *
          ((8 * T.card : ℝ) : ℂ) =
        (((oneReplicaSupportBlockScale v₁ T)⁻¹ : ℝ) : ℂ) := by
    exact_mod_cast hreal
  congr 1
  norm_num at hcomplex ⊢
  exact hcomplex

def finitePauliConjugationLinearMap (Q : σ → Option (Fin 3)) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ →ₗ[ℂ]
      Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ where
  toFun X := finitePauliMatrix Q * X * finitePauliMatrix Q
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

theorem finitePauliConjugationLinearMap_apply_basis
    (Q P : σ → Option (Fin 3)) :
    finitePauliConjugationLinearMap Q (finitePauliMatrixBasis σ P) =
      finitePauliConjugationSign Q P • finitePauliMatrixBasis σ P := by
  simp only [finitePauliConjugationLinearMap, finitePauliMatrixBasis_apply]
  exact finitePauliMatrix_conj Q P

@[simp] theorem finitePauliMatrixBasis_repr_finitePauliMatrix
    (P Q : σ → Option (Fin 3)) :
    (finitePauliMatrixBasis σ).repr (finitePauliMatrix P) Q =
      if P = Q then 1 else 0 := by
  rw [show finitePauliMatrix P = finitePauliMatrixBasis σ P by
    exact (finitePauliMatrixBasis_apply P).symm]
  rw [Module.Basis.repr_self, Finsupp.single_apply]

theorem finitePauliMatrixBasis_repr_conjugation
    (Q P : σ → Option (Fin 3))
    (X : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    (finitePauliMatrixBasis σ).repr
        (finitePauliConjugationLinearMap Q X) P =
      finitePauliConjugationSign Q P *
        (finitePauliMatrixBasis σ).repr X P := by
  rw [← (finitePauliMatrixBasis σ).sum_repr X]
  rw [map_sum]
  simp_rw [map_smul, finitePauliConjugationLinearMap_apply_basis]
  simp [mul_comm]

theorem eq_smul_identity_of_oneReplicaLocalPauli_commutators_zero
    (X : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)
    (hX : ∀ i a,
      oneReplicaLocalPauliCommutatorMatrix i a *ᵥ Matrix.vec X = 0) :
    ∃ c : ℂ, X = c • 1 := by
  classical
  let zeroLabel : σ → Option (Fin 3) := fun _ => none
  have hcoeff : ∀ P : σ → Option (Fin 3), P ≠ zeroLabel →
      (finitePauliMatrixBasis σ).repr X P = 0 := by
    intro P hP
    obtain ⟨i, hi⟩ : ∃ i, P i ≠ none := by
      simpa only [zeroLabel, Function.ne_iff] using hP
    cases hPi : P i with
    | none => exact (hi hPi).elim
    | some b =>
      let a := pauliAxisNext b
      let Q := singlePauliAxisLabel i a
      have hsign : finitePauliConjugationSign Q P = -1 := by
        rw [finitePauliConjugationSign_singlePauliAxisLabel, hPi]
        simp [a, boolPauliConjugationSign, pauliAxisNext_ne]
      have hcomm : ringCommutator (finitePauliMatrix Q) X = 0 := by
        have h := hX i a
        rw [oneReplicaLocalPauliCommutatorMatrix,
          matrixCommutatorRepresentation_mulVec_vec] at h
        exact Matrix.vec_eq_zero_iff.mp h
      have hQX : finitePauliMatrix Q * X = X * finitePauliMatrix Q := by
        exact sub_eq_zero.mp (by simpa [ringCommutator] using hcomm)
      have hconj : finitePauliConjugationLinearMap Q X = X := by
        change finitePauliMatrix Q * X * finitePauliMatrix Q = X
        calc
          finitePauliMatrix Q * X * finitePauliMatrix Q =
              (X * finitePauliMatrix Q) * finitePauliMatrix Q := by rw [hQX]
          _ = X * (finitePauliMatrix Q * finitePauliMatrix Q) :=
            Matrix.mul_assoc _ _ _
          _ = X := by rw [finitePauliMatrix_mul_self, Matrix.mul_one]
      have hre := finitePauliMatrixBasis_repr_conjugation Q P X
      rw [hconj, hsign] at hre
      have htwo : (2 : ℂ) * (finitePauliMatrixBasis σ).repr X P = 0 := by
        linear_combination hre
      exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  let c : ℂ := (finitePauliMatrixBasis σ).repr X zeroLabel
  refine ⟨c, ?_⟩
  apply (finitePauliMatrixBasis σ).repr.injective
  ext P
  rw [map_smul]
  rw [show (1 : Matrix (FiniteQubitConfiguration σ)
      (FiniteQubitConfiguration σ) ℂ) = finitePauliMatrix zeroLabel by
        exact finitePauliMatrix_const_none.symm]
  change (finitePauliMatrixBasis σ).repr X P =
    c * (finitePauliMatrixBasis σ).repr (finitePauliMatrix zeroLabel) P
  rw [finitePauliMatrixBasis_repr_finitePauliMatrix]
  by_cases hP : P = zeroLabel
  · subst P
    simp [c]
  · rw [if_neg (Ne.symm hP), mul_zero, hcoeff P hP]

def oneReplicaLocalPauliSingletSubspace :
    Submodule ℂ (EuclideanSpace ℂ
      (FiniteQubitConfiguration σ × FiniteQubitConfiguration σ)) :=
  hermitianMatrixFamilyCommonKernel
    (fun p : σ × Fin 3 => oneReplicaLocalPauliCommutatorMatrix p.1 p.2)

def oneReplicaScalarOperatorSubspace :
    Submodule ℂ (EuclideanSpace ℂ
      (FiniteQubitConfiguration σ × FiniteQubitConfiguration σ)) :=
  Submodule.span ℂ {WithLp.toLp 2 (Matrix.vec
    (1 : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ))}

theorem oneReplicaLocalPauliSingletSubspace_eq_scalar :
    oneReplicaLocalPauliSingletSubspace (σ := σ) =
      oneReplicaScalarOperatorSubspace (σ := σ) := by
  classical
  apply le_antisymm
  · intro x hx
    rw [oneReplicaLocalPauliSingletSubspace,
      hermitianMatrixFamilyCommonKernel] at hx
    have hxker : ∀ p : σ × Fin 3,
        (oneReplicaLocalPauliCommutatorMatrix p.1 p.2).toEuclideanLin x = 0 :=
      (Submodule.mem_iInf _).mp hx
    obtain ⟨X, hX⟩ := Matrix.vec_bijective.surjective x.ofLp
    have hzero : ∀ i a,
        oneReplicaLocalPauliCommutatorMatrix i a *ᵥ Matrix.vec X = 0 := by
      intro i a
      have h := hxker (i, a)
      have h' := congrArg (fun y => y.ofLp) h
      simpa [Matrix.toLpLin_apply, hX] using h'
    obtain ⟨c, hc⟩ :=
      eq_smul_identity_of_oneReplicaLocalPauli_commutators_zero X hzero
    have hxeq : x = c • WithLp.toLp 2 (Matrix.vec
        (1 : Matrix (FiniteQubitConfiguration σ)
          (FiniteQubitConfiguration σ) ℂ)) := by
      apply WithLp.ofLp_injective
      rw [← hX, hc, Matrix.vec_smul]
      change c • Matrix.vec 1 = c • Matrix.vec 1
      rfl
    rw [hxeq]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  · rw [oneReplicaScalarOperatorSubspace, Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    change WithLp.toLp 2 (Matrix.vec 1) ∈
      hermitianMatrixFamilyCommonKernel
        (fun p : σ × Fin 3 => oneReplicaLocalPauliCommutatorMatrix p.1 p.2)
    rw [hermitianMatrixFamilyCommonKernel]
    refine (Submodule.mem_iInf _).2 fun p => ?_
    rw [LinearMap.mem_ker]
    apply WithLp.ofLp_injective
    change oneReplicaLocalPauliCommutatorMatrix p.1 p.2 *ᵥ Matrix.vec 1 = 0
    rw [oneReplicaLocalPauliCommutatorMatrix,
      matrixCommutatorRepresentation_mulVec_vec]
    simp [ringCommutator]

def oneReplicaOperatorTraceLinear :
    EuclideanSpace ℂ
      (FiniteQubitConfiguration σ × FiniteQubitConfiguration σ) →ₗ[ℂ] ℂ where
  toFun x := ∑ i : FiniteQubitConfiguration σ, x.ofLp (i, i)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

def oneReplicaTraceZeroOperatorSubspace :
    Submodule ℂ (EuclideanSpace ℂ
      (FiniteQubitConfiguration σ × FiniteQubitConfiguration σ)) :=
  LinearMap.ker (oneReplicaOperatorTraceLinear (σ := σ))

theorem inner_vec_one_eq_oneReplicaOperatorTraceLinear
    (x : EuclideanSpace ℂ
      (FiniteQubitConfiguration σ × FiniteQubitConfiguration σ)) :
    inner ℂ (WithLp.toLp 2 (Matrix.vec
      (1 : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ))) x =
      oneReplicaOperatorTraceLinear x := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp [oneReplicaOperatorTraceLinear, Matrix.one_apply, RCLike.inner_apply]

def oneReplicaTracelessOperatorSubspace :
    Submodule ℂ (EuclideanSpace ℂ
      (FiniteQubitConfiguration σ × FiniteQubitConfiguration σ)) :=
  (oneReplicaLocalPauliSingletSubspace (σ := σ))ᗮ

theorem oneReplicaTracelessOperatorSubspace_eq_traceZero :
    oneReplicaTracelessOperatorSubspace (σ := σ) =
      oneReplicaTraceZeroOperatorSubspace (σ := σ) := by
  rw [oneReplicaTracelessOperatorSubspace,
    oneReplicaLocalPauliSingletSubspace_eq_scalar]
  ext x
  change x ∈ (ℂ ∙ WithLp.toLp 2 (Matrix.vec
      (1 : Matrix (FiniteQubitConfiguration σ)
        (FiniteQubitConfiguration σ) ℂ)))ᗮ ↔
    oneReplicaOperatorTraceLinear x = 0
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  rw [inner_vec_one_eq_oneReplicaOperatorTraceLinear]

theorem oneReplicaLocalPauli_subspace_finrank
    (U V : Submodule ℂ (EuclideanSpace ℂ
      (FiniteQubitConfiguration σ × FiniteQubitConfiguration σ)))
    (hU : U ≤ oneReplicaTracelessOperatorSubspace (σ := σ))
    (hUV : ∀ p : σ × Fin 3, ∀ x, x ∈ U →
      (oneReplicaLocalPauliCommutatorMatrix p.1 p.2).toEuclideanLin x ∈ V) :
    Module.finrank ℂ U ≤ Module.finrank ℂ V := by
  exact centralHermitianMatrixFamily_subspace_finrank_of_orthogonal_commonKernel
    (fun p : σ × Fin 3 => oneReplicaLocalPauliCommutatorMatrix p.1 p.2)
    (fun p => oneReplicaLocalPauliCommutatorMatrix_conjTranspose p.1 p.2)
    (fun p => oneReplicaLocalPauli_quadraticCasimir_commutes p.1 p.2)
    U V hU hUV

def oneReplicaWeightedLocalPauliCommutatorMatrix (v₁ : ℝ)
    (p : σ × Fin 3) :
    Matrix (FiniteQubitConfiguration σ × FiniteQubitConfiguration σ)
      (FiniteQubitConfiguration σ × FiniteQubitConfiguration σ) ℂ :=
  ((Real.sqrt v₁ : ℝ) : ℂ) •
    oneReplicaLocalPauliCommutatorMatrix p.1 p.2

theorem oneReplicaWeightedLocalPauliCommutatorMatrix_conjTranspose
    (v₁ : ℝ) (p : σ × Fin 3) :
    (oneReplicaWeightedLocalPauliCommutatorMatrix v₁ p).conjTranspose =
      oneReplicaWeightedLocalPauliCommutatorMatrix v₁ p := by
  rw [oneReplicaWeightedLocalPauliCommutatorMatrix,
    Matrix.conjTranspose_smul,
    oneReplicaLocalPauliCommutatorMatrix_conjTranspose]
  simp

theorem oneReplicaWeightedLocalPauli_quadraticCasimir_commutes
    (v₁ : ℝ) (p : σ × Fin 3) :
    (∑ k : σ × Fin 3,
        oneReplicaWeightedLocalPauliCommutatorMatrix v₁ k *
          oneReplicaWeightedLocalPauliCommutatorMatrix v₁ k) *
        oneReplicaWeightedLocalPauliCommutatorMatrix v₁ p =
      oneReplicaWeightedLocalPauliCommutatorMatrix v₁ p *
        ∑ k : σ × Fin 3,
          oneReplicaWeightedLocalPauliCommutatorMatrix v₁ k *
            oneReplicaWeightedLocalPauliCommutatorMatrix v₁ k := by
  have hcentral := oneReplicaLocalPauli_quadraticCasimir_commutes p.1 p.2
  simp only [oneReplicaWeightedLocalPauliCommutatorMatrix,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← Finset.smul_sum, Matrix.smul_mul, Matrix.mul_smul, hcentral]

/-- Canonical inverse-square-root Casimir scaling of the positive weight-one family is exactly
symmetric doubly stochastic after adjoining its scalar-kernel projector. On the trace-zero sector
that projector vanishes, so this is the paper's scaling certificate. -/
theorem oneReplicaWeightedLocalPauli_completed_scaled_biTight (v₁ : ℝ) :
    (∑ j : Option (σ × Fin 3),
        (centralCasimirInvSqrtScaleRCLike
            (completedHermitianFamily
              (oneReplicaWeightedLocalPauliCommutatorMatrix v₁)) *
          completedHermitianFamily
            (oneReplicaWeightedLocalPauliCommutatorMatrix v₁) j).conjTranspose *
        (centralCasimirInvSqrtScaleRCLike
            (completedHermitianFamily
              (oneReplicaWeightedLocalPauliCommutatorMatrix v₁)) *
          completedHermitianFamily
            (oneReplicaWeightedLocalPauliCommutatorMatrix v₁) j) = 1) ∧
    (∑ j : Option (σ × Fin 3),
        (centralCasimirInvSqrtScaleRCLike
            (completedHermitianFamily
              (oneReplicaWeightedLocalPauliCommutatorMatrix v₁)) *
          completedHermitianFamily
            (oneReplicaWeightedLocalPauliCommutatorMatrix v₁) j) *
        (centralCasimirInvSqrtScaleRCLike
            (completedHermitianFamily
              (oneReplicaWeightedLocalPauliCommutatorMatrix v₁)) *
          completedHermitianFamily
            (oneReplicaWeightedLocalPauliCommutatorMatrix v₁) j).conjTranspose = 1) := by
  exact completedHermitianFamily_scaled_biTight
    (oneReplicaWeightedLocalPauliCommutatorMatrix v₁)
    (oneReplicaWeightedLocalPauliCommutatorMatrix_conjTranspose v₁)
    (oneReplicaWeightedLocalPauli_quadraticCasimir_commutes v₁)

/-- Adding arbitrary further pencil coefficients cannot destroy fullness once nonzero scalar
multiples of every weight-one Pauli commutator remain in the family. -/
theorem oneReplicaPauliPencil_subspace_finrank_of_contains_local
    {J : Type*} [Fintype J]
    (B : J → Matrix
      (FiniteQubitConfiguration σ × FiniteQubitConfiguration σ)
      (FiniteQubitConfiguration σ × FiniteQubitConfiguration σ) ℂ)
    (embed : σ × Fin 3 → J) (c : σ × Fin 3 → ℂ)
    (hc : ∀ p, c p ≠ 0)
    (hB : ∀ p, B (embed p) = c p •
      oneReplicaLocalPauliCommutatorMatrix p.1 p.2)
    (U V : Submodule ℂ (EuclideanSpace ℂ
      (FiniteQubitConfiguration σ × FiniteQubitConfiguration σ)))
    (hU : U ≤ oneReplicaTracelessOperatorSubspace (σ := σ))
    (hUV : ∀ j x, x ∈ U → (B j).toEuclideanLin x ∈ V) :
    Module.finrank ℂ U ≤ Module.finrank ℂ V := by
  apply oneReplicaLocalPauli_subspace_finrank U V hU
  intro p x hx
  have hscaled := V.smul_mem (c p)⁻¹ (hUV (embed p) x hx)
  rw [hB p] at hscaled
  simpa [hc p] using hscaled

abbrev OneReplicaBoundedPauliWord (n q : ℕ) :=
  {P : Fin n → Option (Fin 3) // P ∈ nonidentityPauliWords n q}

theorem pauliWeight_singlePauliAxisLabel {n : ℕ} (i : Fin n) (a : Fin 3) :
    pauliWeight (singlePauliAxisLabel i a) = 1 := by
  rw [pauliWeight]
  have hfilter :
      Finset.univ.filter (fun s => singlePauliAxisLabel i a s ≠ none) = {i} := by
    ext s
    by_cases hs : s = i <;> simp [singlePauliAxisLabel, hs]
  rw [hfilter, Finset.card_singleton]

def oneReplicaLocalBoundedPauliWord {n q : ℕ} (hq : 1 ≤ q)
    (i : Fin n) (a : Fin 3) : OneReplicaBoundedPauliWord n q :=
  ⟨singlePauliAxisLabel i a, mem_nonidentityPauliWords.mpr
    ⟨by rw [pauliWeight_singlePauliAxisLabel],
      by rw [pauliWeight_singlePauliAxisLabel]; exact hq⟩⟩

def oneReplicaWeightedPauliPencil {n q : ℕ}
    (v : OneReplicaBoundedPauliWord n q → ℝ)
    (P : OneReplicaBoundedPauliWord n q) :
    Matrix
      (FiniteQubitConfiguration (Fin n) × FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n) × FiniteQubitConfiguration (Fin n)) ℂ :=
  ((Real.sqrt (v P) : ℝ) : ℂ) •
    matrixCommutatorRepresentation (finitePauliMatrix P.1)

/-- Exact bounded-weight Pauli pencil is full on the traceless operator sector whenever its common
weight-one coefficient is strictly positive. Arbitrary nonnegative higher-weight coefficients remain
present and require no restriction beyond the defining square-root scaling. -/
theorem oneReplicaWeightedPauliPencil_subspace_finrank
    {n q : ℕ} (hq : 1 ≤ q)
    (v : OneReplicaBoundedPauliWord n q → ℝ)
    (v₁ : ℝ) (hv₁ : 0 < v₁)
    (hlocal : ∀ i a, v (oneReplicaLocalBoundedPauliWord hq i a) = v₁)
    (U V : Submodule ℂ (EuclideanSpace ℂ
      (FiniteQubitConfiguration (Fin n) × FiniteQubitConfiguration (Fin n))))
    (hU : U ≤ oneReplicaTracelessOperatorSubspace (σ := Fin n))
    (hUV : ∀ P x, x ∈ U → (oneReplicaWeightedPauliPencil v P).toEuclideanLin x ∈ V) :
    Module.finrank ℂ U ≤ Module.finrank ℂ V := by
  let c : Fin n × Fin 3 → ℂ := fun _ => ((Real.sqrt v₁ : ℝ) : ℂ)
  apply oneReplicaPauliPencil_subspace_finrank_of_contains_local
    (oneReplicaWeightedPauliPencil v)
    (fun p => oneReplicaLocalBoundedPauliWord hq p.1 p.2)
    c
  · intro p
    dsimp [c]
    exact_mod_cast Real.sqrt_ne_zero'.mpr hv₁
  · intro p
    rw [oneReplicaWeightedPauliPencil, hlocal]
    rfl
  · exact hU
  · exact hUV

end

end GaloisForLFunctions.HTGeometry
