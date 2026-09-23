import GaloisForLFunctions.HTGeometry.ProductStateObserverVisibleRank
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Local-unitary invariance of the observer-visible rank

Conjugating a Hermitian operator string by a product unitary keeps every
identity factor an identity factor and turns every traceless factor into a real
combination of traceless factors.  The `q`-local dictionary is therefore
invariant under local unitary conjugation, and the observer-visible rank of an
arbitrary product state equals the rank at the product ground state.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {D : ℕ} [NeZero D]

section Conjugation

variable {U : σ → Matrix (Fin D) (Fin D) ℂ}

omit [Fintype σ] [DecidableEq σ] [NeZero D] in
theorem conjugate_conjTranspose
    (A : Matrix (Fin D) (Fin D) ℂ) (hA : Aᴴ = A) (i : σ) :
    (U i * A * (U i)ᴴ)ᴴ = U i * A * (U i)ᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hA, mul_assoc]

omit [Fintype σ] [DecidableEq σ] [NeZero D] in
theorem trace_conjugate (hU : ∀ i, (U i)ᴴ * U i = 1) (A : Matrix (Fin D) (Fin D) ℂ)
    (i : σ) : (U i * A * (U i)ᴴ).trace = A.trace := by
  rw [Matrix.trace_mul_cycle, hU i, one_mul]

/-- **Local-unitary conjugation of a string.**  Conjugating a Hermitian string by
a product unitary produces a real combination of Hermitian strings with the same
support. -/
theorem conj_quditString_mem_span_sameSupport
    (hU : ∀ i, (U i)ᴴ * U i = 1) (hU' : ∀ i, U i * (U i)ᴴ = 1)
    (a : σ → Fin D × Fin D) :
    quditStringOf U * quditString a * (quditStringOf U)ᴴ
      ∈ Submodule.span ℝ
        (quditString '' {b : σ → Fin D × Fin D |
          quditStringSupport b = quditStringSupport a}) := by
  classical
  have hrep : ∀ i : σ, ∃ c : (Fin D × Fin D) → ℝ,
      (∀ p, c p ≠ 0 → (p = (0, 0) ↔ a i = (0, 0)))
      ∧ U i * quditHermUnit (a i) * (U i)ᴴ
          = ∑ p, ((c p : ℂ)) • quditHermUnit p := by
    intro i
    by_cases h : a i = (0, 0)
    · refine ⟨fun p => if p = (0, 0) then 1 else 0, ?_, ?_⟩
      · intro p hp
        refine ⟨fun _ => h, fun _ => ?_⟩
        by_contra hp0
        exact hp (by simp [hp0])
      · rw [h, quditHermUnit_zero, mul_one, hU' i,
          Finset.sum_eq_single ((0, 0) : Fin D × Fin D)
            (fun b _ hb => by simp [hb])
            (fun hmem => absurd (Finset.mem_univ _) hmem)]
        simp
    · have hherm : (U i * quditHermUnit (a i) * (U i)ᴴ)ᴴ
          = U i * quditHermUnit (a i) * (U i)ᴴ :=
        conjugate_conjTranspose (U := U) _ (quditHermUnit_conjTranspose (a i)) i
      have htr : (U i * quditHermUnit (a i) * (U i)ᴴ).trace = 0 := by
        rw [trace_conjugate hU _ i, trace_quditHermUnit, if_neg h]
      obtain ⟨c, hc0, hc⟩ := exists_real_repr_ground_zero_of_traceless hherm htr
      refine ⟨c, ?_, hc⟩
      intro p hp
      constructor
      · intro hpe
        exact absurd (hpe ▸ hc0) hp
      · intro he
        exact absurd he h
  choose c hc hcrep using hrep
  have hexp : quditStringOf U * quditString a * (quditStringOf U)ᴴ
      = ∑ b : σ → Fin D × Fin D, (∏ i, ((c i (b i) : ℂ))) • quditString b := by
    rw [quditString, quditStringOf_mul, quditStringOf_conjTranspose,
      quditStringOf_mul,
      show (fun i => U i * quditHermUnit (a i) * (U i)ᴴ)
          = (fun i => ∑ p, ((c i p : ℂ)) • quditHermUnit p) from funext hcrep]
    exact quditStringOf_sum _
  rw [hexp]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : quditStringSupport b = quditStringSupport a
  · have hsm : (∏ i, ((c i (b i) : ℂ))) • quditString b
        = (∏ i, c i (b i)) • quditString b := by
      rw [← Complex.ofReal_prod, Complex.coe_smul]
    rw [hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
  · obtain ⟨i, hi⟩ : ∃ i : σ, ¬ (i ∈ quditStringSupport b ↔ i ∈ quditStringSupport a) := by
      by_contra hcon
      exact hb (Finset.ext (fun i => not_not.mp (fun h => hcon ⟨i, h⟩)))
    have hzero : c i (b i) = 0 := by
      by_contra hne
      refine hi ?_
      rw [mem_quditStringSupport, mem_quditStringSupport]
      exact not_congr (hc i (b i) hne)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hzero]; simp), zero_smul]
    exact Submodule.zero_mem _

omit [NeZero D] in
/-- The adjoint of a product unitary is its inverse on the left. -/
theorem quditStringOf_conjTranspose_mul_self (hU : ∀ i, (U i)ᴴ * U i = 1) :
    (quditStringOf U)ᴴ * quditStringOf U = 1 := by
  rw [quditStringOf_conjTranspose, quditStringOf_mul,
    show (fun i => (U i)ᴴ * U i) = (fun _ : σ => (1 : Matrix (Fin D) (Fin D) ℂ))
      from funext hU, quditStringOf_one]

omit [NeZero D] in
/-- The adjoint of a product unitary is its inverse on the right. -/
theorem quditStringOf_mul_conjTranspose_self (hU' : ∀ i, U i * (U i)ᴴ = 1) :
    quditStringOf U * (quditStringOf U)ᴴ = 1 := by
  rw [quditStringOf_conjTranspose, quditStringOf_mul,
    show (fun i => U i * (U i)ᴴ) = (fun _ : σ => (1 : Matrix (Fin D) (Fin D) ℂ))
      from funext hU', quditStringOf_one]

/-- **Dictionary invariance.**  Local unitary conjugation maps the `q`-local
dictionary into itself. -/
theorem map_conj_qLocalDictionary_le (hU : ∀ i, (U i)ᴴ * U i = 1)
    (hU' : ∀ i, U i * (U i)ᴴ = 1) (q : ℕ) {A : Matrix (σ → Fin D) (σ → Fin D) ℂ}
    (hA : A ∈ qLocalDictionary σ D q) :
    quditStringOf U * A * (quditStringOf U)ᴴ ∈ qLocalDictionary σ D q := by
  classical
  set W := quditStringOf U with hW
  have hlin : ∀ B C : Matrix (σ → Fin D) (σ → Fin D) ℂ,
      W * (B + C) * Wᴴ = W * B * Wᴴ + W * C * Wᴴ := by
    intro B C
    rw [mul_add, add_mul]
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
  · rintro _ ⟨l, rfl⟩
    have hmem := conj_quditString_mem_span_sameSupport hU hU' l.1
    refine Submodule.span_le.mpr ?_ hmem
    rintro _ ⟨b, hb, rfl⟩
    exact Submodule.subset_span
      ⟨⟨b, by rw [hb]; exact l.2.1, by rw [hb]; exact l.2.2⟩, rfl⟩
  · simp
  · intro B C _ _ hB hC
    rw [hlin]
    exact Submodule.add_mem _ hB hC
  · intro r B _ hB
    have : W * (r • B) * Wᴴ = r • (W * B * Wᴴ) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [this]
    exact Submodule.smul_mem _ _ hB

end Conjugation

section RankTransport

variable {U : σ → Matrix (Fin D) (Fin D) ℂ}

/-- The observer action of an arbitrary state, as a real-linear map. -/
noncomputable def observerActionR (ψ : (σ → Fin D) → ℂ) :
    Matrix (σ → Fin D) (σ → Fin D) ℂ →ₗ[ℝ] ((σ → Fin D) → ℂ) :=
  (QuantumAlg.centeredLinear ψ).restrictScalars ℝ

omit [NeZero D] in
theorem observerActionR_apply (ψ : (σ → Fin D) → ℂ)
    (A : Matrix (σ → Fin D) (σ → Fin D) ℂ) :
    observerActionR ψ A = QuantumAlg.centered ψ A := rfl

/-- Multiplication of vectors by a fixed matrix, as a real-linear map. -/
noncomputable def mulVecR (W : Matrix (σ → Fin D) (σ → Fin D) ℂ) :
    ((σ → Fin D) → ℂ) →ₗ[ℝ] ((σ → Fin D) → ℂ) :=
  (Matrix.mulVecLin W).restrictScalars ℝ

omit [NeZero D] in
theorem mulVecR_apply (W : Matrix (σ → Fin D) (σ → Fin D) ℂ)
    (v : (σ → Fin D) → ℂ) : mulVecR W v = W *ᵥ v := rfl

/-- Conjugation transports the observer action of the ground state to the
observer action of the rotated state. -/
theorem centered_conj (hU : ∀ i, (U i)ᴴ * U i = 1)
    (A : Matrix (σ → Fin D) (σ → Fin D) ℂ) :
    QuantumAlg.centered (quditStringOf U *ᵥ (quditVacuum : (σ → Fin D) → ℂ))
        (quditStringOf U * A * (quditStringOf U)ᴴ)
      = quditStringOf U *ᵥ QuantumAlg.centered (quditVacuum : (σ → Fin D) → ℂ) A := by
  set W := quditStringOf U with hWdef
  have hWW : Wᴴ * W = 1 := quditStringOf_conjTranspose_mul_self hU
  have hact : (W * A * Wᴴ) *ᵥ (W *ᵥ (quditVacuum : (σ → Fin D) → ℂ))
      = W *ᵥ (A *ᵥ (quditVacuum : (σ → Fin D) → ℂ)) := by
    rw [Matrix.mulVec_mulVec, mul_assoc, hWW, mul_one, ← Matrix.mulVec_mulVec]
  have hexp : QuantumAlg.expval (W *ᵥ (quditVacuum : (σ → Fin D) → ℂ)) (W * A * Wᴴ)
      = QuantumAlg.expval (quditVacuum : (σ → Fin D) → ℂ) A := by
    rw [QuantumAlg.expval, QuantumAlg.expval, hact, Matrix.star_mulVec,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hWW, Matrix.one_mulVec]
  rw [QuantumAlg.centered, QuantumAlg.centered, hact, hexp, Matrix.mulVec_sub,
    Matrix.mulVec_smul]

omit [NeZero D] in
/-- Vectors are determined by their image under a product unitary. -/
theorem mulVecR_injective (hU : ∀ i, (U i)ᴴ * U i = 1) :
    Function.Injective (mulVecR (quditStringOf U)) := by
  intro v w hvw
  have hWW : (quditStringOf U)ᴴ * quditStringOf U = 1 :=
    quditStringOf_conjTranspose_mul_self hU
  have h := congrArg (fun x => (quditStringOf U)ᴴ *ᵥ x) hvw
  simpa [mulVecR_apply, Matrix.mulVec_mulVec, hWW] using h

/-- **Local-unitary invariance of the visible image.** -/
theorem map_qLocalDictionary_productState (hU : ∀ i, (U i)ᴴ * U i = 1)
    (hU' : ∀ i, U i * (U i)ᴴ = 1) (q : ℕ) :
    (qLocalDictionary σ D q).map
        (observerActionR (quditStringOf U *ᵥ (quditVacuum : (σ → Fin D) → ℂ)))
      = ((qLocalDictionary σ D q).map (vacuumObserverAction σ D)).map
        (mulVecR (quditStringOf U)) := by
  have hWW' : quditStringOf U * (quditStringOf U)ᴴ = 1 :=
    quditStringOf_mul_conjTranspose_self hU'
  have hUadj : ∀ i, ((U i)ᴴ)ᴴ * (U i)ᴴ = 1 := by
    intro i
    rw [Matrix.conjTranspose_conjTranspose]
    exact hU' i
  have hUadj' : ∀ i, (U i)ᴴ * ((U i)ᴴ)ᴴ = 1 := by
    intro i
    rw [Matrix.conjTranspose_conjTranspose]
    exact hU i
  apply le_antisymm
  · rintro _ ⟨A, hA, rfl⟩
    have hB : (quditStringOf U)ᴴ * A * quditStringOf U ∈ qLocalDictionary σ D q := by
      have h := map_conj_qLocalDictionary_le (U := fun i => (U i)ᴴ) hUadj hUadj' q hA
      rw [← quditStringOf_conjTranspose] at h
      simpa only [Matrix.conjTranspose_conjTranspose] using h
    have hAeq : quditStringOf U * ((quditStringOf U)ᴴ * A * quditStringOf U)
        * (quditStringOf U)ᴴ = A := by
      calc quditStringOf U * ((quditStringOf U)ᴴ * A * quditStringOf U)
            * (quditStringOf U)ᴴ
          = quditStringOf U * (quditStringOf U)ᴴ * A
            * (quditStringOf U * (quditStringOf U)ᴴ) := by
            simp only [mul_assoc]
        _ = A := by rw [hWW', one_mul, mul_one]
    refine ⟨QuantumAlg.centered (quditVacuum : (σ → Fin D) → ℂ)
        ((quditStringOf U)ᴴ * A * quditStringOf U),
      ⟨(quditStringOf U)ᴴ * A * quditStringOf U, hB, rfl⟩, ?_⟩
    rw [mulVecR_apply, ← centered_conj hU, hAeq]
    rfl
  · rintro _ ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    refine ⟨quditStringOf U * A * (quditStringOf U)ᴴ,
      map_conj_qLocalDictionary_le hU hU' q hA, ?_⟩
    rw [observerActionR_apply, centered_conj hU]
    rfl

/-- **Observer-visible rank of an arbitrary product state.**  Rotating the
product ground state by a product unitary does not change the rank of the
`q`-local dictionary action. -/
theorem finrank_map_qLocalDictionary_productState (hU : ∀ i, (U i)ᴴ * U i = 1)
    (hU' : ∀ i, U i * (U i)ᴴ = 1) (q : ℕ) :
    Module.finrank ℝ ↥((qLocalDictionary σ D q).map
        (observerActionR (quditStringOf U *ᵥ (quditVacuum : (σ → Fin D) → ℂ))))
      = 2 * ∑ k ∈ Finset.Icc 1 q, (Fintype.card σ).choose k * (D - 1) ^ k := by
  rw [map_qLocalDictionary_productState hU hU' q,
    ← (Submodule.equivMapOfInjective (mulVecR (quditStringOf U))
        (mulVecR_injective hU)
        ((qLocalDictionary σ D q).map (vacuumObserverAction σ D))).finrank_eq,
    finrank_map_qLocalDictionary]

/-- Every unit vector is the ground column of a unitary matrix. -/
theorem exists_unitary_col_zero {φ : Fin D → ℂ} (hφ : ∑ i, ‖φ i‖ ^ (2 : ℕ) = 1) :
    ∃ U : Matrix (Fin D) (Fin D) ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ ∀ r, U r 0 = φ r := by
  classical
  set w : EuclideanSpace ℂ (Fin D) := (EuclideanSpace.equiv (Fin D) ℂ).symm φ with hw
  have hnorm : ‖w‖ = 1 := by
    rw [EuclideanSpace.norm_eq, show ∑ i, ‖w i‖ ^ (2 : ℕ) = ∑ i, ‖φ i‖ ^ (2 : ℕ) from rfl, hφ]
    simp
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (Fin D)) = Fintype.card (Fin D) := by
    simp
  have horth : Orthonormal ℂ
      (Set.restrict ({0} : Set (Fin D)) (fun _ : Fin D => w)) := by
    constructor
    · intro i
      exact hnorm
    · intro i j hij
      exact absurd (Subsingleton.elim i j) hij
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  have hU : (Matrix.of fun r c => b c r)ᴴ * (Matrix.of fun r c => b c r)
      = (1 : Matrix (Fin D) (Fin D) ℂ) := by
    ext c c'
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hinner : (inner ℂ (b c) (b c') : ℂ) = if c = c' then 1 else 0 :=
      orthonormal_iff_ite.mp b.orthonormal c c'
    rw [PiLp.inner_apply] at hinner
    rw [← hinner]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply,
      RCLike.inner_apply]
    exact mul_comm _ _
  exact ⟨_, hU, mul_eq_one_comm.mp hU, fun r => by
    simp only [Matrix.of_apply]
    rw [hb 0 rfl]
    rfl⟩

/-- **Observer-visible rank of an arbitrary product state.**  For any choice of
local unit vectors, the `q`-local dictionary acts on the corresponding product
state with the same visible rank as at the product ground state. -/
theorem finrank_map_qLocalDictionary_productVector
    (φ : σ → (Fin D → ℂ)) (hφ : ∀ i, ∑ x, ‖φ i x‖ ^ (2 : ℕ) = 1) (q : ℕ) :
    Module.finrank ℝ ↥((qLocalDictionary σ D q).map
        (observerActionR (fun r : σ → Fin D => ∏ i, φ i (r i))))
      = 2 * ∑ k ∈ Finset.Icc 1 q, (Fintype.card σ).choose k * (D - 1) ^ k := by
  choose U hU hU' hUcol using fun i => exists_unitary_col_zero (hφ i)
  have hstate : quditStringOf U *ᵥ (quditVacuum : (σ → Fin D) → ℂ)
      = fun r : σ → Fin D => ∏ i, φ i (r i) := by
    funext r
    rw [quditStringOf_mulVec_vacuum_apply]
    exact Finset.prod_congr rfl fun i _ => hUcol i (r i)
  rw [← hstate]
  exact finrank_map_qLocalDictionary_productState hU hU' q

end RankTransport

end GaloisForLFunctions.HTGeometry
