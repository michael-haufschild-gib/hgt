import GaloisForLFunctions.HTGeometry.AllReplicaSiteString
import GaloisForLFunctions.HTGeometry.ReplicaConfigurationBridge

/-!
# Character grading of the collective edge images

Conjugation by an all-replica site string is a self-adjoint involution of the operator space that
fixes every sitewise singlet and multiplies the collective commutator of a physical Pauli label by
one single-site sign.  Images of labels with different signs are therefore orthogonal.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section ConjRep

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The matrix of conjugation by a fixed matrix, acting on vectorised operators. -/
def matrixConjRepresentation (Q : Matrix C C ℂ) : Matrix (C × C) (C × C) ℂ :=
  Matrix.kroneckerMap (fun x y => x * y) Qᵀ Q

theorem matrixConjRepresentation_mulVec_vec (Q X : Matrix C C ℂ) :
    matrixConjRepresentation Q *ᵥ Matrix.vec X = Matrix.vec (Q * X * Q) := by
  rw [matrixConjRepresentation, Matrix.kronecker_mulVec_vec, Matrix.transpose_transpose]

theorem matrixConjRepresentation_conjTranspose {Q : Matrix C C ℂ} (hQ : Qᴴ = Q) :
    (matrixConjRepresentation Q)ᴴ = matrixConjRepresentation Q := by
  ext p q
  show star (Qᵀ q.1 p.1 * Q q.2 p.2) = Qᵀ p.1 q.1 * Q p.2 q.2
  have h1 : star (Q p.1 q.1) = Q q.1 p.1 := by
    have := congrFun (congrFun hQ q.1) p.1
    rw [Matrix.conjTranspose_apply] at this
    exact this
  have h2 : star (Q q.2 p.2) = Q p.2 q.2 := by
    have := congrFun (congrFun hQ p.2) q.2
    rw [Matrix.conjTranspose_apply] at this
    exact this
  rw [star_mul', Matrix.transpose_apply, Matrix.transpose_apply, h1, h2, mul_comm]

end ConjRep

variable {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

theorem siteConjString_mul_self (v : I) (c : Fin 3) :
    siteConjString I R v c * siteConjString I R v c = 1 :=
  finitePauliMatrix_mul_self _

theorem siteConjString_conjTranspose (v : I) (c : Fin 3) :
    (siteConjString I R v c)ᴴ = siteConjString I R v c :=
  finitePauliMatrix_isHermitian _

/-- Conjugation by the all-replica site string fixes every sitewise singlet. -/
theorem siteConjString_conj_of_commute {v : I} {c : Fin 3}
    {X : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ}
    (hX : Commute (finiteReplicatedSiteCollectivePauli I R v c) X) :
    siteConjString I R v c * X * siteConjString I R v c = X := by
  have hcomm : Commute (siteConjString I R v c) X :=
    commute_allReplicaSiteString_of_commute_collective hX
  rw [siteConjString] at hcomm ⊢
  rw [hcomm.eq, Matrix.mul_assoc, finitePauliMatrix_mul_self, Matrix.mul_one]

/-- **The collective commutator of a label is graded by one single-site sign.** -/
theorem siteConjString_conj_commutator {v : I} {c : Fin 3} (p : I → Option (Fin 3))
    {X : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ}
    (hX : Commute (finiteReplicatedSiteCollectivePauli I R v c) X) :
    siteConjString I R v c *
        (collectivePauliString I R p * X - X * collectivePauliString I R p) *
        siteConjString I R v c =
      boolPauliConjugationSign (some c) (p v) •
        (collectivePauliString I R p * X - X * collectivePauliString I R p) := by
  have hQ := siteConjString_mul_self (I := I) (R := R) v c
  have hX' := siteConjString_conj_of_commute hX
  have hC := siteConjString_conj_collectivePauliString (I := I) (R := R) v c p
  have hstep : ∀ A B : Matrix (FiniteQubitConfiguration (I × R))
      (FiniteQubitConfiguration (I × R)) ℂ,
      (siteConjString I R v c * A * siteConjString I R v c) *
        (siteConjString I R v c * B * siteConjString I R v c) =
      siteConjString I R v c * (A * B) * siteConjString I R v c := by
    intro A B
    have hinner : siteConjString I R v c *
        (siteConjString I R v c * (B * siteConjString I R v c)) = B * siteConjString I R v c := by
      rw [← Matrix.mul_assoc, hQ, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [hinner]
  have hexp : (siteConjString I R v c * collectivePauliString I R p * siteConjString I R v c) *
        (siteConjString I R v c * X * siteConjString I R v c) -
      (siteConjString I R v c * X * siteConjString I R v c) *
        (siteConjString I R v c * collectivePauliString I R p * siteConjString I R v c) =
      siteConjString I R v c *
        (collectivePauliString I R p * X - X * collectivePauliString I R p) *
        siteConjString I R v c := by
    rw [hstep, hstep, ← Matrix.sub_mul, ← Matrix.mul_sub]
  rw [← hexp, hC, hX', Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]


section Transport

theorem toEuclideanLin_commutatorRep_vec
    (C X : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ) :
    (matrixCommutatorRepresentation C).toEuclideanLin
        (vecLinearEquiv (FiniteQubitConfiguration (I × R)) X) =
      vecLinearEquiv (FiniteQubitConfiguration (I × R)) (C * X - X * C) := by
  rw [Matrix.toLpLin_apply]
  exact congrArg (WithLp.toLp 2) (matrixCommutatorRepresentation_mulVec_vec C X)

theorem toEuclideanLin_conjRep_vec
    (Q X : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ) :
    (matrixConjRepresentation Q).toEuclideanLin
        (vecLinearEquiv (FiniteQubitConfiguration (I × R)) X) =
      vecLinearEquiv (FiniteQubitConfiguration (I × R)) (Q * X * Q) := by
  rw [Matrix.toLpLin_apply]
  exact congrArg (WithLp.toLp 2) (matrixConjRepresentation_mulVec_vec Q X)

theorem star_boolPauliConjugationSign (q p : Option (Fin 3)) :
    (starRingEnd ℂ) (boolPauliConjugationSign q p) = boolPauliConjugationSign q p := by
  classical
  rw [boolPauliConjugationSign]
  by_cases h : q = none ∨ p = none ∨ q = p
  · rw [if_pos h]
    simp
  · rw [if_neg h]
    simp

/-- **Collective commutators graded by different signs have orthogonal images on the singlet
sector.** -/
theorem inner_collectiveCommutator_eq_zero_of_sign_ne {v : I} {c : Fin 3}
    (p p' : I → Option (Fin 3))
    (hsign : boolPauliConjugationSign (some c) (p v) ≠ boolPauliConjugationSign (some c) (p' v))
    {x y : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ finiteAllReplicaCollectiveSingletSubspace I R)
    (hy : y ∈ finiteAllReplicaCollectiveSingletSubspace I R) :
    @inner ℂ _ _ ((matrixCommutatorRepresentation (collectivePauliString I R p)).toEuclideanLin x)
      ((matrixCommutatorRepresentation (collectivePauliString I R p')).toEuclideanLin y) = 0 := by
  classical
  set Cfg := FiniteQubitConfiguration (I × R)
  set X := (vecLinearEquiv Cfg).symm x with hX
  set Y := (vecLinearEquiv Cfg).symm y with hY
  have hxX : x = vecLinearEquiv Cfg X := ((vecLinearEquiv Cfg).apply_symm_apply x).symm
  have hyY : y = vecLinearEquiv Cfg Y := ((vecLinearEquiv Cfg).apply_symm_apply y).symm
  have hXcomm : Commute (finiteReplicatedSiteCollectivePauli I R v c) X := by
    have hzero := (mem_singlet_iff.mp hx) v c
    rw [hxX] at hzero
    exact (commutator_toEuclideanLin_eq_zero_iff _ _).mp hzero
  have hYcomm : Commute (finiteReplicatedSiteCollectivePauli I R v c) Y := by
    have hzero := (mem_singlet_iff.mp hy) v c
    rw [hyY] at hzero
    exact (commutator_toEuclideanLin_eq_zero_iff _ _).mp hzero
  have hself : LinearMap.adjoint
      (matrixConjRepresentation (siteConjString I R v c)).toEuclideanLin =
      (matrixConjRepresentation (siteConjString I R v c)).toEuclideanLin := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      matrixConjRepresentation_conjTranspose (siteConjString_conjTranspose v c)]
  have hleft : (matrixConjRepresentation (siteConjString I R v c)).toEuclideanLin
      ((matrixCommutatorRepresentation (collectivePauliString I R p)).toEuclideanLin x) =
      (boolPauliConjugationSign (some c) (p v)) •
        (matrixCommutatorRepresentation (collectivePauliString I R p)).toEuclideanLin x := by
    rw [hxX, toEuclideanLin_commutatorRep_vec, toEuclideanLin_conjRep_vec,
      siteConjString_conj_commutator p hXcomm, map_smul]
  have hright : (matrixConjRepresentation (siteConjString I R v c)).toEuclideanLin
      ((matrixCommutatorRepresentation (collectivePauliString I R p')).toEuclideanLin y) =
      (boolPauliConjugationSign (some c) (p' v)) •
        (matrixCommutatorRepresentation (collectivePauliString I R p')).toEuclideanLin y := by
    rw [hyY, toEuclideanLin_commutatorRep_vec, toEuclideanLin_conjRep_vec,
      siteConjString_conj_commutator p' hYcomm, map_smul]
  have hmove : @inner ℂ _ _
      ((matrixConjRepresentation (siteConjString I R v c)).toEuclideanLin
        ((matrixCommutatorRepresentation (collectivePauliString I R p)).toEuclideanLin x))
      ((matrixCommutatorRepresentation (collectivePauliString I R p')).toEuclideanLin y) =
      @inner ℂ _ _ ((matrixCommutatorRepresentation (collectivePauliString I R p)).toEuclideanLin x)
        ((matrixConjRepresentation (siteConjString I R v c)).toEuclideanLin
          ((matrixCommutatorRepresentation (collectivePauliString I R p')).toEuclideanLin y)) := by
    conv_lhs => rw [← hself]
    exact LinearMap.adjoint_inner_left _ _ _
  rw [hleft, hright, inner_smul_left, inner_smul_right, star_boolPauliConjugationSign] at hmove
  have hdiff : (boolPauliConjugationSign (some c) (p v) -
      boolPauliConjugationSign (some c) (p' v)) * (@inner ℂ _ _
        ((matrixCommutatorRepresentation (collectivePauliString I R p)).toEuclideanLin x)
        ((matrixCommutatorRepresentation (collectivePauliString I R p')).toEuclideanLin y)) = 0 := by
    linear_combination hmove
  exact (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero_of_ne hsign)


/-- The graded commutation of the conjugation with a collective commutator, with no hypothesis on
the operator being conjugated. -/
theorem siteConjString_conj_commutator_general {v : I} {c : Fin 3} (p : I → Option (Fin 3))
    (X : Matrix (FiniteQubitConfiguration (I × R)) (FiniteQubitConfiguration (I × R)) ℂ) :
    siteConjString I R v c *
        (collectivePauliString I R p * X - X * collectivePauliString I R p) *
        siteConjString I R v c =
      boolPauliConjugationSign (some c) (p v) •
        (collectivePauliString I R p * (siteConjString I R v c * X * siteConjString I R v c) -
          (siteConjString I R v c * X * siteConjString I R v c) *
            collectivePauliString I R p) := by
  have hQ := siteConjString_mul_self (I := I) (R := R) v c
  have hC := siteConjString_conj_collectivePauliString (I := I) (R := R) v c p
  have hstep : ∀ A B : Matrix (FiniteQubitConfiguration (I × R))
      (FiniteQubitConfiguration (I × R)) ℂ,
      (siteConjString I R v c * A * siteConjString I R v c) *
        (siteConjString I R v c * B * siteConjString I R v c) =
      siteConjString I R v c * (A * B) * siteConjString I R v c := by
    intro A B
    have hinner : siteConjString I R v c *
        (siteConjString I R v c * (B * siteConjString I R v c)) = B * siteConjString I R v c := by
      rw [← Matrix.mul_assoc, hQ, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [hinner]
  have hexp : (siteConjString I R v c * collectivePauliString I R p * siteConjString I R v c) *
        (siteConjString I R v c * X * siteConjString I R v c) -
      (siteConjString I R v c * X * siteConjString I R v c) *
        (siteConjString I R v c * collectivePauliString I R p * siteConjString I R v c) =
      siteConjString I R v c *
        (collectivePauliString I R p * X - X * collectivePauliString I R p) *
        siteConjString I R v c := by
    rw [hstep, hstep, ← Matrix.sub_mul, ← Matrix.mul_sub]
  rw [← hexp, hC, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]

/-- **The conjugation intertwines the collective commutator with its sign.** -/
theorem conjRep_mul_commutatorRep (v : I) (c : Fin 3) (p : I → Option (Fin 3)) :
    matrixConjRepresentation (siteConjString I R v c) *
        matrixCommutatorRepresentation (collectivePauliString I R p) =
      boolPauliConjugationSign (some c) (p v) •
        (matrixCommutatorRepresentation (collectivePauliString I R p) *
          matrixConjRepresentation (siteConjString I R v c)) := by
  rw [Matrix.ext_iff_mulVec]
  intro w
  obtain ⟨X, rfl⟩ := Matrix.vec_bijective.2 w
  rw [← Matrix.mulVec_mulVec, matrixCommutatorRepresentation_mulVec_vec,
    matrixConjRepresentation_mulVec_vec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    matrixConjRepresentation_mulVec_vec, matrixCommutatorRepresentation_mulVec_vec]
  have hmain := siteConjString_conj_commutator_general (v := v) (c := c) p X
  simp only [ringCommutator]
  rw [hmain]
  funext q
  rfl

end Transport

end GaloisForLFunctions.HTGeometry
