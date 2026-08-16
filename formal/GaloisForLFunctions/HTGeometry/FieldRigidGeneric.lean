import GaloisForLFunctions.HTGeometry.FieldRigidCoupling
import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Polynomial.Roots

/-!
# Field-rigid couplings are generic

The local-field commutator map of an edge coupling is a real matrix whose entries are linear in the
coupling.  Field rigidity is the nonvanishing of the determinant of the associated Gram matrix, so
it is an open condition, and since a diagonal witness exists it is also dense.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- The matrix of the local-field commutator map in the standard bases. -/
def fieldMatrix {R : Type*} [CommRing R] (J : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 3 × Fin 3) (Fin 3 ⊕ Fin 3) R :=
  fun p => Sum.elim
    (fun i => crossProduct (fun t => J t p.2) (Pi.single i 1) p.1)
    (fun g => crossProduct (fun t => J p.1 t) (Pi.single g 1) p.2)

theorem fieldMatrix_mulVec (J : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ)
    (p : Fin 3 × Fin 3) :
    (fieldMatrix J *ᵥ Sum.elim a b) p = fieldMap J a b p.1 p.2 := by
  classical
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  simp only [fieldMatrix, Sum.elim_inl, Sum.elim_inr, fieldMap, crossProduct]
  rcases fin3_cases p.1 with h1 | h1 | h1 <;> rcases fin3_cases p.2 with h2 | h2 | h2 <;>
    simp [h1, h2, Fin.sum_univ_three] <;> ring

theorem fieldRigid_iff_mulVec (J : Matrix (Fin 3) (Fin 3) ℝ) :
    FieldRigid J ↔ ∀ v : Fin 3 ⊕ Fin 3 → ℝ, fieldMatrix J *ᵥ v = 0 → v = 0 := by
  classical
  constructor
  · intro hJ v hv
    have hzero : fieldMap J (fun i => v (Sum.inl i)) (fun g => v (Sum.inr g)) = 0 := by
      refine Matrix.ext fun f q => ?_
      have := congrFun hv (f, q)
      rw [Matrix.zero_apply]
      have hsum : Sum.elim (fun i => v (Sum.inl i)) (fun g => v (Sum.inr g)) = v := by
        funext s
        cases s <;> rfl
      rw [← fieldMatrix_mulVec J (fun i => v (Sum.inl i)) (fun g => v (Sum.inr g)) (f, q), hsum]
      simpa using this
    obtain ⟨ha, hb⟩ := hJ _ _ hzero
    funext s
    cases s with
    | inl i => exact congrFun ha i
    | inr g => exact congrFun hb g
  · intro hker a b hab
    have hv : fieldMatrix J *ᵥ Sum.elim a b = 0 := by
      funext p
      rw [fieldMatrix_mulVec, Pi.zero_apply]
      have := congrFun (congrFun hab p.1) p.2
      simpa using this
    have := hker _ hv
    constructor
    · funext i
      have := congrFun this (Sum.inl i)
      simpa using this
    · funext g
      have := congrFun this (Sum.inr g)
      simpa using this

/-- The Gram determinant of the local-field commutator map. -/
def fieldGramDet {R : Type*} [CommRing R] (J : Matrix (Fin 3) (Fin 3) R) : R :=
  Matrix.det ((fieldMatrix J)ᵀ * fieldMatrix J)

/-- **Field rigidity is the nonvanishing of the Gram determinant.** -/
theorem fieldRigid_iff_gramDet_ne_zero (J : Matrix (Fin 3) (Fin 3) ℝ) :
    FieldRigid J ↔ fieldGramDet J ≠ 0 := by
  classical
  rw [fieldRigid_iff_mulVec, fieldGramDet]
  constructor
  · intro hker hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    refine hv0 (hker v ?_)
    have hquad : (fieldMatrix J *ᵥ v) ⬝ᵥ (fieldMatrix J *ᵥ v) = 0 := by
      have h1 : v ⬝ᵥ (((fieldMatrix J)ᵀ * fieldMatrix J) *ᵥ v) = 0 := by
        rw [hv, dotProduct_zero]
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at h1
      exact h1
    exact dotProduct_star_self_eq_zero.mp (by simpa using hquad)
  · intro hdet v hv
    by_contra hv0
    exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, by
      rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]⟩)


section Linearity

/-- The matrix of the local-field commutator map depends linearly on the coupling. -/
def fieldMatrixMap : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ]
    Matrix (Fin 3 × Fin 3) (Fin 3 ⊕ Fin 3) ℝ where
  toFun := fieldMatrix
  map_add' J J' := by
    funext p j
    cases j with
    | inl i =>
        show crossProduct (fun t => (J + J') t p.2) (Pi.single i 1) p.1 = _
        have hsplit : (fun t => (J + J') t p.2) =
            (fun t => J t p.2) + (fun t => J' t p.2) := rfl
        rw [hsplit, map_add]
        rfl
    | inr g =>
        show crossProduct (fun t => (J + J') p.1 t) (Pi.single g 1) p.2 = _
        have hsplit : (fun t => (J + J') p.1 t) =
            (fun t => J p.1 t) + (fun t => J' p.1 t) := rfl
        rw [hsplit, map_add]
        rfl
  map_smul' c J := by
    funext p j
    cases j with
    | inl i =>
        show crossProduct (fun t => (c • J) t p.2) (Pi.single i 1) p.1 = _
        have hsplit : (fun t => (c • J) t p.2) = c • (fun t => J t p.2) := rfl
        rw [hsplit, map_smul]
        rfl
    | inr g =>
        show crossProduct (fun t => (c • J) p.1 t) (Pi.single g 1) p.2 = _
        have hsplit : (fun t => (c • J) p.1 t) = c • (fun t => J p.1 t) := rfl
        rw [hsplit, map_smul]
        rfl

theorem continuous_fieldMatrix :
    Continuous (fieldMatrix : Matrix (Fin 3) (Fin 3) ℝ → Matrix (Fin 3 × Fin 3) (Fin 3 ⊕ Fin 3) ℝ) :=
  fieldMatrixMap.continuous_of_finiteDimensional

theorem continuous_fieldGramDet :
    Continuous (fieldGramDet : Matrix (Fin 3) (Fin 3) ℝ → ℝ) :=
  Continuous.matrix_det (continuous_fieldMatrix.matrix_transpose.matrix_mul continuous_fieldMatrix)

/-- **Field rigidity is an open condition.** -/
theorem isOpen_fieldRigid : IsOpen {J : Matrix (Fin 3) (Fin 3) ℝ | FieldRigid J} := by
  have hset : {J : Matrix (Fin 3) (Fin 3) ℝ | FieldRigid J} =
      fieldGramDet ⁻¹' {x : ℝ | x ≠ 0} := by
    ext J
    exact fieldRigid_iff_gramDet_ne_zero J
  rw [hset]
  exact continuous_fieldGramDet.isOpen_preimage _ isOpen_ne

end Linearity


section Density

/-- A diagonal coupling with distinct nonzero squares. -/
def fieldRigidWitness : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, 2, 4]

theorem fieldRigid_witness : FieldRigid fieldRigidWitness := by
  refine fieldRigid_diagonal ?_
  intro i j hij
  rcases fin3_cases i with hi | hi | hi <;> rcases fin3_cases j with hj | hj | hj <;>
    subst hi <;> subst hj <;> simp_all <;> norm_num

theorem fieldMatrix_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (J : Matrix (Fin 3) (Fin 3) R) :
    (fieldMatrix J).map f = fieldMatrix (J.map f) := by
  funext p j
  rcases fin3_cases p.1 with h1 | h1 | h1 <;> rcases fin3_cases p.2 with h2 | h2 | h2 <;>
    cases j with
    | inl i =>
        rcases fin3_cases i with hi | hi | hi <;>
          simp [Matrix.map_apply, fieldMatrix, crossProduct, Pi.single_apply, h1, h2, hi]
    | inr g =>
        rcases fin3_cases g with hg | hg | hg <;>
          simp [Matrix.map_apply, fieldMatrix, crossProduct, Pi.single_apply, h1, h2, hg]

theorem fieldGramDet_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (J : Matrix (Fin 3) (Fin 3) R) :
    f (fieldGramDet J) = fieldGramDet (J.map f) := by
  rw [fieldGramDet, fieldGramDet, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul,
    Matrix.transpose_map, fieldMatrix_map]

/-- The affine path from a coupling towards the witness, over the polynomial ring. -/
def fieldPathPoly (J K : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) (Polynomial ℝ) :=
  fun i j => Polynomial.C (J i j) + Polynomial.X * Polynomial.C (K i j)

theorem fieldPathPoly_map_eval (J K : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    (fieldPathPoly J K).map (Polynomial.evalRingHom t) = J + t • K := by
  funext i j
  simp only [Matrix.map_apply, fieldPathPoly, Matrix.add_apply, Matrix.smul_apply,
    Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, smul_eq_mul]

theorem eval_fieldGramDet_path (J K : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    Polynomial.eval t (fieldGramDet (fieldPathPoly J K)) = fieldGramDet (J + t • K) := by
  have hmap := fieldGramDet_map (Polynomial.evalRingHom t) (fieldPathPoly J K)
  rw [fieldPathPoly_map_eval] at hmap
  exact hmap

/-- **Field rigidity is a dense condition.** -/
theorem dense_fieldRigid : Dense {J : Matrix (Fin 3) (Fin 3) ℝ | FieldRigid J} := by
  classical
  intro J
  rw [mem_closure_iff_nhds]
  intro U hU
  set K := fieldRigidWitness - J with hK
  have hcont : Continuous fun t : ℝ => J + t • K :=
    continuous_const.add (continuous_id.smul continuous_const)
  have h0 : (fun t : ℝ => J + t • K) 0 = J := by simp
  have hnhds : (fun t : ℝ => J + t • K) ⁻¹' U ∈ nhds (0 : ℝ) := by
    refine hcont.continuousAt.preimage_mem_nhds ?_
    have hzero : J + (0 : ℝ) • K = J := by simp
    rw [hzero]
    exact hU
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hnhds
  have hP1 : Polynomial.eval 1 (fieldGramDet (fieldPathPoly J K)) ≠ 0 := by
    rw [eval_fieldGramDet_path]
    have hone : J + (1 : ℝ) • K = fieldRigidWitness := by
      rw [hK]
      module
    rw [hone]
    exact (fieldRigid_iff_gramDet_ne_zero _).mp fieldRigid_witness
  have hPne : fieldGramDet (fieldPathPoly J K) ≠ 0 := by
    intro hc
    rw [hc] at hP1
    exact hP1 (by simp)
  have hfin : {x : ℝ | (fieldGramDet (fieldPathPoly J K)).IsRoot x}.Finite :=
    Polynomial.finite_setOf_isRoot hPne
  have hinf : (Metric.ball (0 : ℝ) δ).Infinite := by
    rw [Real.ball_eq_Ioo]
    exact Set.Ioo_infinite (by linarith)
  obtain ⟨t, ht⟩ := (hinf.sdiff hfin).nonempty
  refine ⟨J + t • K, hsub ht.1, ?_⟩
  refine (fieldRigid_iff_gramDet_ne_zero _).mpr ?_
  rw [← eval_fieldGramDet_path]
  exact ht.2

end Density

end GaloisForLFunctions.HTGeometry
