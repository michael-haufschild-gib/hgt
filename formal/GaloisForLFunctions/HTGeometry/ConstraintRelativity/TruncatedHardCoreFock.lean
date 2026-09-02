import GaloisForLFunctions.HTGeometry.ConstraintRelativity.FactorFramedTensorJacobian

/-!
# Exact truncated hard-core Fock realization

The closed-horizon faces of the factor-framed Jacobian defect carry the finite hard-core Fock
model from card `(25)`--`(29)`. Creator monomials act by adjoining faces subject to the exact
`d - 2` truncation. One-site creators commute and square to zero, every surviving face ket is
created from the vacuum, and diagonal number phases conjugate every face creator by its exact
additive frequency.
-/

namespace HTGeometry.ConstraintRelativity

open scoped BigOperators

/-- Closed-horizon truncated hard-core Fock space. -/
abbrev TruncatedFaceFock (d : ℕ) := ClosedHorizonFace d → ℂ

def closedHorizonFaceDiff {d : ℕ} (U : ClosedHorizonFace d) (T : TensorFace d) :
    ClosedHorizonFace d :=
  ⟨U.1 \ T, (Finset.card_le_card Finset.sdiff_subset).trans U.2⟩

/-- Creator monomial attached to face `T`: remove `T` from output coordinates when `T` is
contained in the output, and vanish otherwise. -/
noncomputable def truncatedFaceCreator {d : ℕ} (T : TensorFace d) :
    TruncatedFaceFock d →ₗ[ℂ] TruncatedFaceFock d where
  toFun x U := if T ⊆ U.1 then x (closedHorizonFaceDiff U T) else 0
  map_add' x y := by ext U; by_cases h : T ⊆ U.1 <;> simp [h]
  map_smul' c x := by ext U; by_cases h : T ⊆ U.1 <;> simp [h]

/-- Empty closed-horizon face. -/
def emptyClosedHorizonFace (d : ℕ) : ClosedHorizonFace d := ⟨∅, by simp⟩

/-- Vacuum vector. -/
noncomputable def truncatedFaceVacuum (d : ℕ) : TruncatedFaceFock d :=
  Pi.single (emptyClosedHorizonFace d) 1

/-- Coordinate face ket. -/
noncomputable def truncatedFaceBasis {d : ℕ} (T : ClosedHorizonFace d) :
    TruncatedFaceFock d :=
  Pi.single T 1

/-- Every surviving closed-horizon face ket is produced by its creator monomial from vacuum. -/
theorem truncatedFaceCreator_vacuum {d : ℕ} (T : ClosedHorizonFace d) :
    truncatedFaceCreator T.1 (truncatedFaceVacuum d) = truncatedFaceBasis T := by
  classical
  ext U
  change (if T.1 ⊆ U.1 then
      (Pi.single (emptyClosedHorizonFace d) (1 : ℂ) : TruncatedFaceFock d)
        (closedHorizonFaceDiff U T.1) else 0) =
    (Pi.single T (1 : ℂ) : TruncatedFaceFock d) U
  by_cases hTU : T.1 ⊆ U.1
  · rw [if_pos hTU]
    by_cases hUT : U.1 ⊆ T.1
    · have hEq : U = T := Subtype.ext (Finset.Subset.antisymm hUT hTU)
      subst U
      have hdiff0 : closedHorizonFaceDiff T T.1 = emptyClosedHorizonFace d := by
        apply Subtype.ext
        simp [closedHorizonFaceDiff, emptyClosedHorizonFace]
      rw [hdiff0]
      simp
    · have hdiff : U.1 \ T.1 ≠ ∅ := (Finset.sdiff_nonempty.mpr hUT).ne_empty
      have hface : closedHorizonFaceDiff U T.1 ≠ emptyClosedHorizonFace d := by
        intro h
        have hval := congrArg Subtype.val h
        change U.1 \ T.1 = ∅ at hval
        exact hdiff hval
      have hUne : U ≠ T := fun h => hUT (by rw [h])
      simp [hface, hUne]
  · rw [if_neg hTU]
    have hUne : U ≠ T := fun h => hTU (by rw [h])
    simp [hUne]

/-- One-site compressed hard-core creator. -/
noncomputable def truncatedCreator {d : ℕ} (i : Fin d) :
    TruncatedFaceFock d →ₗ[ℂ] TruncatedFaceFock d :=
  truncatedFaceCreator {i}

/-- Card `(26)`: every compressed one-site creator is square-zero. -/
theorem truncatedCreator_sq_zero {d : ℕ} (i : Fin d) (x : TruncatedFaceFock d) :
    truncatedCreator i (truncatedCreator i x) = 0 := by
  classical
  ext U
  simp only [truncatedCreator, truncatedFaceCreator, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Finset.singleton_subset_iff]
  by_cases hi : i ∈ U.1
  · have hiErase : i ∉ U.1 \ {i} := by simp
    change (if i ∈ U.1 then
      (if i ∈ (U.1 \ {i}) then _ else 0) else 0) = 0
    simp [hi, hiErase]
  · change (if i ∈ U.1 then _ else 0) = 0
    simp [hi]

/-- Card `(26)`: compressed creators commute. -/
theorem truncatedCreator_comm {d : ℕ} (i j : Fin d) (x : TruncatedFaceFock d) :
    truncatedCreator i (truncatedCreator j x) =
      truncatedCreator j (truncatedCreator i x) := by
  classical
  ext U
  simp only [truncatedCreator, truncatedFaceCreator, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Finset.singleton_subset_iff]
  by_cases hi : i ∈ U.1 <;> by_cases hj : j ∈ U.1
  · by_cases hij : i = j
    · subst j
      rfl
    · change (if i ∈ U.1 then
        (if j ∈ U.1 \ {i} then
          x (closedHorizonFaceDiff (closedHorizonFaceDiff U {i}) {j}) else 0) else 0) =
        (if j ∈ U.1 then
          (if i ∈ U.1 \ {j} then
            x (closedHorizonFaceDiff (closedHorizonFaceDiff U {j}) {i}) else 0) else 0)
      have hji : j ∈ U.1 \ {i} := by simp [hj, Ne.symm hij]
      have hij' : i ∈ U.1 \ {j} := by simp [hi, hij]
      simp only [hi, hj, hji, hij', if_pos]
      congr 1
      apply Subtype.ext
      change (U.1 \ {i}) \ {j} = (U.1 \ {j}) \ {i}
      ext k
      simp [and_left_comm, and_comm]
  · change (if i ∈ U.1 then
        (if j ∈ U.1 \ {i} then _ else 0) else 0) =
        (if j ∈ U.1 then _ else 0)
    simp [hi, hj]
  · change (if i ∈ U.1 then _ else 0) =
        (if j ∈ U.1 then (if i ∈ U.1 \ {j} then _ else 0) else 0)
    simp [hi, hj]
  · change (if i ∈ U.1 then _ else 0) = (if j ∈ U.1 then _ else 0)
    simp [hi, hj]

/-- Products of disjoint creator monomials are exactly creator monomials of face unions. -/
theorem truncatedFaceCreator_comp_of_disjoint {d : ℕ} {T S : TensorFace d}
    (hTS : Disjoint T S) (x : TruncatedFaceFock d) :
    truncatedFaceCreator T (truncatedFaceCreator S x) =
      truncatedFaceCreator (T ∪ S) x := by
  classical
  ext U
  simp only [truncatedFaceCreator, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hunion : T ∪ S ⊆ U.1
  · have hTU : T ⊆ U.1 := Finset.subset_union_left.trans hunion
    have hSU : S ⊆ U.1 := Finset.subset_union_right.trans hunion
    have hSdiff : S ⊆ U.1 \ T := by
      intro i hiS
      exact Finset.mem_sdiff.mpr
        ⟨hSU hiS, fun hiT => (Finset.disjoint_left.mp hTS) hiT hiS⟩
    have hSdiff' : S ⊆ (closedHorizonFaceDiff U T).1 := hSdiff
    rw [if_pos hTU, if_pos hSdiff', if_pos hunion]
    congr 1
    apply Subtype.ext
    change (U.1 \ T) \ S = U.1 \ (T ∪ S)
    ext i
    simp [and_assoc, and_left_comm, and_comm]
  · rw [if_neg hunion]
    by_cases hTU : T ⊆ U.1
    · rw [if_pos hTU]
      have hSnotU : ¬S ⊆ U.1 := fun hSU => hunion (Finset.union_subset hTU hSU)
      have hSdiff : ¬S ⊆ (closedHorizonFaceDiff U T).1 :=
        fun h => hSnotU (h.trans Finset.sdiff_subset)
      rw [if_neg hSdiff]
    · rw [if_neg hTU]

/-- Every creator whose face lies above the `(d - 3)` skeleton vanishes identically. In
particular, each product of `d - 1` distinct one-site creators is zero. -/
theorem truncatedFaceCreator_eq_zero_of_large {d : ℕ} (T : TensorFace d)
    (hT : d - 2 < T.card) : truncatedFaceCreator T = 0 := by
  classical
  ext x U
  simp only [truncatedFaceCreator]
  have hnot : ¬T ⊆ U.1 := by
    intro h
    have := Finset.card_le_card h
    omega
  simp [hnot]

/-- Creator monomials with an overlapping face factor multiply to zero. -/
theorem truncatedFaceCreator_comp_eq_zero_of_not_disjoint {d : ℕ}
    {T S : TensorFace d} (hTS : ¬Disjoint T S) (x : TruncatedFaceFock d) :
    truncatedFaceCreator T (truncatedFaceCreator S x) = 0 := by
  classical
  ext U
  simp only [truncatedFaceCreator, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hTU : T ⊆ U.1
  · rw [if_pos hTU]
    have hSdiff : ¬S ⊆ U.1 \ T := by
      intro h
      apply hTS
      rw [Finset.disjoint_left]
      intro i hiT hiS
      exact (Finset.mem_sdiff.mp (h hiS)).2 hiT
    have hSdiff' : ¬S ⊆ (closedHorizonFaceDiff U T).1 := hSdiff
    rw [if_neg hSdiff']
    simp
  · rw [if_neg hTU]
    rfl

@[simp] theorem truncatedFaceCreator_empty {d : ℕ} :
    truncatedFaceCreator (∅ : TensorFace d) = LinearMap.id := by
  ext x U
  simp [truncatedFaceCreator, closedHorizonFaceDiff]

/-- Span of all surviving creator monomials. -/
def truncatedFaceCreatorSpan (d : ℕ) :
    Submodule ℂ (Module.End ℂ (TruncatedFaceFock d)) :=
  Submodule.span ℂ (Set.range fun T : ClosedHorizonFace d => truncatedFaceCreator T.1)

theorem truncatedFaceCreator_mem_span {d : ℕ} (T : ClosedHorizonFace d) :
    truncatedFaceCreator T.1 ∈ truncatedFaceCreatorSpan d :=
  Submodule.subset_span (Set.mem_range_self T)

theorem truncatedFaceCreatorSpan_one_mem (d : ℕ) :
    (1 : Module.End ℂ (TruncatedFaceFock d)) ∈ truncatedFaceCreatorSpan d := by
  rw [show (1 : Module.End ℂ (TruncatedFaceFock d)) =
    truncatedFaceCreator (emptyClosedHorizonFace d).1 by
      ext x U
      simp [truncatedFaceCreator, emptyClosedHorizonFace, closedHorizonFaceDiff]]
  exact truncatedFaceCreator_mem_span (emptyClosedHorizonFace d)

theorem truncatedFaceCreator_mul_mem_span {d : ℕ} (T S : ClosedHorizonFace d) :
    truncatedFaceCreator T.1 * truncatedFaceCreator S.1 ∈ truncatedFaceCreatorSpan d := by
  classical
  by_cases hTS : Disjoint T.1 S.1
  · by_cases hcard : (T.1 ∪ S.1).card ≤ d - 2
    · let U : ClosedHorizonFace d := ⟨T.1 ∪ S.1, hcard⟩
      rw [show truncatedFaceCreator T.1 * truncatedFaceCreator S.1 =
          truncatedFaceCreator U.1 by
        apply LinearMap.ext
        intro x
        exact truncatedFaceCreator_comp_of_disjoint hTS x]
      exact truncatedFaceCreator_mem_span U
    · have hlarge : d - 2 < (T.1 ∪ S.1).card := Nat.lt_of_not_ge hcard
      rw [show truncatedFaceCreator T.1 * truncatedFaceCreator S.1 =
          truncatedFaceCreator (T.1 ∪ S.1) by
        apply LinearMap.ext
        intro x
        exact truncatedFaceCreator_comp_of_disjoint hTS x,
        truncatedFaceCreator_eq_zero_of_large _ hlarge]
      exact (truncatedFaceCreatorSpan d).zero_mem
  · rw [show truncatedFaceCreator T.1 * truncatedFaceCreator S.1 = 0 by
      apply LinearMap.ext
      intro x
      exact truncatedFaceCreator_comp_eq_zero_of_not_disjoint hTS x]
    exact (truncatedFaceCreatorSpan d).zero_mem

/-- The creator span is closed under composition. -/
theorem truncatedFaceCreatorSpan_mul_mem {d : ℕ}
    {A B : Module.End ℂ (TruncatedFaceFock d)}
    (hA : A ∈ truncatedFaceCreatorSpan d) (hB : B ∈ truncatedFaceCreatorSpan d) :
    A * B ∈ truncatedFaceCreatorSpan d := by
  refine Submodule.span_induction₂
    (p := fun X Y _ _ => X * Y ∈ truncatedFaceCreatorSpan d)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hA hB
  · rintro _ _ ⟨T, rfl⟩ ⟨S, rfl⟩
    exact truncatedFaceCreator_mul_mem_span T S
  · intro _ _
    simpa using (truncatedFaceCreatorSpan d).zero_mem
  · intro _ _
    simpa using (truncatedFaceCreatorSpan d).zero_mem
  · intro X Y Z _ _ _ hX hY
    simpa [add_mul] using (truncatedFaceCreatorSpan d).add_mem hX hY
  · intro X Y Z _ _ _ hX hY
    simpa [mul_add] using (truncatedFaceCreatorSpan d).add_mem hX hY
  · intro c X Y _ _ hXY
    simpa [smul_mul_assoc] using (truncatedFaceCreatorSpan d).smul_mem c hXY
  · intro c X Y _ _ hXY
    simpa [mul_smul_comm] using (truncatedFaceCreatorSpan d).smul_mem c hXY

/-- Algebra generated by the compressed one-site creators, presented by surviving face
monomials. -/
def truncatedFaceCreatorAlgebra (d : ℕ) :
    Subalgebra ℂ (Module.End ℂ (TruncatedFaceFock d)) where
  carrier := truncatedFaceCreatorSpan d
  zero_mem' := (truncatedFaceCreatorSpan d).zero_mem
  add_mem' := (truncatedFaceCreatorSpan d).add_mem
  mul_mem' := truncatedFaceCreatorSpan_mul_mem
  one_mem' := truncatedFaceCreatorSpan_one_mem d
  algebraMap_mem' c := by
    change c • (1 : Module.End ℂ (TruncatedFaceFock d)) ∈ truncatedFaceCreatorSpan d
    exact (truncatedFaceCreatorSpan d).smul_mem c (truncatedFaceCreatorSpan_one_mem d)

/-- The literal unital algebra generated by compressed one-site creators. -/
def compressedCreatorAlgebra (d : ℕ) :
    Subalgebra ℂ (Module.End ℂ (TruncatedFaceFock d)) :=
  Algebra.adjoin ℂ (Set.range (truncatedCreator (d := d)))

theorem truncatedCreator_mem_faceCreatorAlgebra {d : ℕ} (i : Fin d) :
    truncatedCreator i ∈ truncatedFaceCreatorAlgebra d := by
  by_cases hcard : ({i} : TensorFace d).card ≤ d - 2
  · exact truncatedFaceCreator_mem_span ⟨{i}, hcard⟩
  · have hlarge : d - 2 < ({i} : TensorFace d).card := Nat.lt_of_not_ge hcard
    change truncatedFaceCreator {i} ∈ truncatedFaceCreatorSpan d
    rw [truncatedFaceCreator_eq_zero_of_large _ hlarge]
    exact (truncatedFaceCreatorSpan d).zero_mem

theorem truncatedFaceCreator_mem_compressedCreatorAlgebra {d : ℕ}
    (T : TensorFace d) (hT : T.card ≤ d - 2) :
    truncatedFaceCreator T ∈ compressedCreatorAlgebra d := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      rw [truncatedFaceCreator_empty]
      exact (compressedCreatorAlgebra d).one_mem
  | @insert i S hi ih =>
      have hS : S.card ≤ d - 2 := (Finset.card_le_card (Finset.subset_insert i S)).trans hT
      have hsingle : truncatedCreator i ∈ compressedCreatorAlgebra d :=
        Algebra.subset_adjoin (Set.mem_range_self i)
      have hprod := (compressedCreatorAlgebra d).mul_mem hsingle (ih hS)
      change truncatedFaceCreator {i} * truncatedFaceCreator S ∈ compressedCreatorAlgebra d at hprod
      have hdisjoint : Disjoint ({i} : TensorFace d) S := by simp [hi]
      rw [show truncatedFaceCreator {i} * truncatedFaceCreator S =
          truncatedFaceCreator (insert i S) by
        apply LinearMap.ext
        intro x
        simpa using truncatedFaceCreator_comp_of_disjoint hdisjoint x] at hprod
      exact hprod

/-- **Card `(27)`, generated-algebra clause.** Surviving face monomials span exactly the unital
algebra generated by the compressed one-site creators. -/
theorem compressedCreatorAlgebra_eq_faceCreatorAlgebra (d : ℕ) :
    compressedCreatorAlgebra d = truncatedFaceCreatorAlgebra d := by
  apply le_antisymm
  · rw [compressedCreatorAlgebra, Algebra.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact truncatedCreator_mem_faceCreatorAlgebra i
  · intro A hA
    change A ∈ truncatedFaceCreatorSpan d at hA
    refine Submodule.span_induction
      (p := fun X _ => X ∈ compressedCreatorAlgebra d) ?_ ?_ ?_ ?_ hA
    · rintro _ ⟨T, rfl⟩
      exact truncatedFaceCreator_mem_compressedCreatorAlgebra T.1 T.2
    · exact (compressedCreatorAlgebra d).zero_mem
    · intro X Y _ _ hX hY
      exact (compressedCreatorAlgebra d).add_mem hX hY
    · intro c X _ hX
      exact (compressedCreatorAlgebra d).smul_mem hX c

/-- Face coefficients sent to their creator-monomial linear combination. -/
noncomputable def faceCoefficientOperator (d : ℕ) :
    TruncatedFaceFock d →ₗ[ℂ] Module.End ℂ (TruncatedFaceFock d) where
  toFun x := ∑ T, x T • truncatedFaceCreator T.1
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro T _
    rw [smul_smul]

theorem faceCoefficientOperator_mem_span {d : ℕ} (x : TruncatedFaceFock d) :
    faceCoefficientOperator d x ∈ truncatedFaceCreatorSpan d := by
  change (∑ T, x T • truncatedFaceCreator T.1) ∈ truncatedFaceCreatorSpan d
  exact Submodule.sum_mem _ fun T _ =>
    (truncatedFaceCreatorSpan d).smul_mem (x T) (truncatedFaceCreator_mem_span T)

/-- Vacuum evaluation recovers every face coefficient. -/
theorem faceCoefficientOperator_vacuum {d : ℕ} (x : TruncatedFaceFock d) :
    faceCoefficientOperator d x (truncatedFaceVacuum d) = x := by
  classical
  ext U
  simp [faceCoefficientOperator, truncatedFaceCreator_vacuum, truncatedFaceBasis,
    Pi.single_apply]

theorem faceCoefficientOperator_injective (d : ℕ) :
    Function.Injective (faceCoefficientOperator d) := by
  intro x y hxy
  have := congrArg (fun A : Module.End ℂ (TruncatedFaceFock d) =>
    A (truncatedFaceVacuum d)) hxy
  simpa [faceCoefficientOperator_vacuum] using this

@[simp] theorem faceCoefficientOperator_basis {d : ℕ} (T : ClosedHorizonFace d) :
    faceCoefficientOperator d (truncatedFaceBasis T) = truncatedFaceCreator T.1 := by
  classical
  change (∑ U, (Pi.single T (1 : ℂ) : TruncatedFaceFock d) U •
      truncatedFaceCreator U.1) = truncatedFaceCreator T.1
  rw [Finset.sum_eq_single T]
  · simp
  · intro U _ hUT
    simp [Pi.single_apply, hUT]
  · intro hT
    exact (hT (Finset.mem_univ T)).elim

/-- Creator span consists of exactly the face-coefficient operators. -/
theorem faceCoefficientOperator_range_eq_span (d : ℕ) :
    LinearMap.range (faceCoefficientOperator d) = truncatedFaceCreatorSpan d := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact faceCoefficientOperator_mem_span x
  · rw [truncatedFaceCreatorSpan, Submodule.span_le]
    rintro _ ⟨T, rfl⟩
    refine ⟨truncatedFaceBasis T, ?_⟩
    exact faceCoefficientOperator_basis T

/-- **Card `(27)`, vector-space and operator-algebra realization.** Closed-horizon face
coefficients are linearly equivalent to the full algebra generated by compressed creators. -/
noncomputable def closedHorizonFaceEquivCreatorAlgebra (d : ℕ) :
    TruncatedFaceFock d ≃ₗ[ℂ] truncatedFaceCreatorAlgebra d :=
  LinearEquiv.ofBijective
    ((faceCoefficientOperator d).codRestrict
      (truncatedFaceCreatorAlgebra d).toSubmodule faceCoefficientOperator_mem_span)
    ⟨fun x y h => faceCoefficientOperator_injective d (congrArg Subtype.val h), by
      rintro ⟨A, hA⟩
      change A ∈ truncatedFaceCreatorSpan d at hA
      rw [← faceCoefficientOperator_range_eq_span d] at hA
      obtain ⟨x, rfl⟩ := hA
      exact ⟨x, rfl⟩⟩

/-- Closed-horizon squarefree face algebra. Its underlying coefficient space is the surviving
`(d - 3)`-skeleton, and multiplication is the faithful compressed-creator product. -/
structure ClosedHorizonFaceAlgebra (d : ℕ) where
  coeff : TruncatedFaceFock d

def closedHorizonFaceCoefficientEquiv (d : ℕ) :
    ClosedHorizonFaceAlgebra d ≃ TruncatedFaceFock d where
  toFun := ClosedHorizonFaceAlgebra.coeff
  invFun := ClosedHorizonFaceAlgebra.mk
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rfl

noncomputable def closedHorizonFaceOperatorEquiv (d : ℕ) :
    ClosedHorizonFaceAlgebra d ≃ truncatedFaceCreatorAlgebra d :=
  (closedHorizonFaceCoefficientEquiv d).trans
    (closedHorizonFaceEquivCreatorAlgebra d).toEquiv

noncomputable instance closedHorizonFaceAlgebraRing (d : ℕ) :
    Ring (ClosedHorizonFaceAlgebra d) :=
  (closedHorizonFaceOperatorEquiv d).ring

noncomputable instance closedHorizonFaceAlgebraAlgebra (d : ℕ) :
    Algebra ℂ (ClosedHorizonFaceAlgebra d) :=
  (closedHorizonFaceOperatorEquiv d).algebra ℂ

/-- **Card `(27)`, literal algebra isomorphism.** The closed-horizon squarefree face algebra is
the complete compressed-creator algebra. Together with
`compressedCreatorAlgebra_eq_faceCreatorAlgebra`, the target is exactly
`Alg(A₁, ..., A_d)`. -/
noncomputable def closedHorizonFaceAlgEquivCreatorAlgebra (d : ℕ) :
    ClosedHorizonFaceAlgebra d ≃ₐ[ℂ] truncatedFaceCreatorAlgebra d where
  toEquiv := closedHorizonFaceOperatorEquiv d
  map_add' := by
    intro x y
    change closedHorizonFaceOperatorEquiv d
      ((closedHorizonFaceOperatorEquiv d).symm
        (closedHorizonFaceOperatorEquiv d x + closedHorizonFaceOperatorEquiv d y)) = _
    exact (closedHorizonFaceOperatorEquiv d).apply_symm_apply _
  map_mul' := by
    intro x y
    change closedHorizonFaceOperatorEquiv d
      ((closedHorizonFaceOperatorEquiv d).symm
        (closedHorizonFaceOperatorEquiv d x * closedHorizonFaceOperatorEquiv d y)) = _
    exact (closedHorizonFaceOperatorEquiv d).apply_symm_apply _
  commutes' := by
    intro c
    change closedHorizonFaceOperatorEquiv d
      ((closedHorizonFaceOperatorEquiv d).symm
        ((algebraMap ℂ (truncatedFaceCreatorAlgebra d)) c)) = _
    exact (closedHorizonFaceOperatorEquiv d).apply_symm_apply _

/-- Coordinate face element in the closed-horizon algebra. -/
noncomputable def closedHorizonFaceElement {d : ℕ} (T : ClosedHorizonFace d) :
    ClosedHorizonFaceAlgebra d :=
  ⟨truncatedFaceBasis T⟩

@[simp] theorem closedHorizonFaceAlgEquiv_faceElement {d : ℕ}
    (T : ClosedHorizonFace d) :
    closedHorizonFaceAlgEquivCreatorAlgebra d (closedHorizonFaceElement T) =
      ⟨truncatedFaceCreator T.1, truncatedFaceCreator_mem_span T⟩ := by
  apply Subtype.ext
  exact faceCoefficientOperator_basis T

/-- Disjoint closed faces multiply by union whenever the union remains in the skeleton. -/
theorem closedHorizonFaceElement_mul_of_disjoint {d : ℕ}
    (T S : ClosedHorizonFace d) (hTS : Disjoint T.1 S.1)
    (hcard : (T.1 ∪ S.1).card ≤ d - 2) :
    closedHorizonFaceElement T * closedHorizonFaceElement S =
      closedHorizonFaceElement ⟨T.1 ∪ S.1, hcard⟩ := by
  apply (closedHorizonFaceAlgEquivCreatorAlgebra d).injective
  simp only [map_mul, closedHorizonFaceAlgEquiv_faceElement]
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  exact truncatedFaceCreator_comp_of_disjoint hTS x

/-- Overlapping closed faces multiply to zero, encoding `f_i² = 0`. -/
theorem closedHorizonFaceElement_mul_eq_zero_of_not_disjoint {d : ℕ}
    (T S : ClosedHorizonFace d) (hTS : ¬Disjoint T.1 S.1) :
    closedHorizonFaceElement T * closedHorizonFaceElement S = 0 := by
  apply (closedHorizonFaceAlgEquivCreatorAlgebra d).injective
  simp only [map_mul, map_zero, closedHorizonFaceAlgEquiv_faceElement]
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  exact truncatedFaceCreator_comp_eq_zero_of_not_disjoint hTS x

/-- Diagonal number-Hamiltonian phase flow on the truncated face basis. -/
noncomputable def truncatedFockPhase {d : ℕ} (weights : Fin d → ℝ) (t : ℝ) :
    TruncatedFaceFock d →ₗ[ℂ] TruncatedFaceFock d where
  toFun x U := Complex.exp
    (Complex.I * (t : ℂ) * (∑ i ∈ U.1, (weights i : ℂ))) * x U
  map_add' x y := by ext U; simp [mul_add]
  map_smul' c x := by ext U; simp [mul_assoc, mul_left_comm]

/-- **Card `(29)`.** Exact phase conjugation of every creator monomial. -/
theorem truncatedFockPhase_faceCreator {d : ℕ} (weights : Fin d → ℝ) (t : ℝ)
    (T : TensorFace d) (x : TruncatedFaceFock d) :
    truncatedFockPhase weights t
        (truncatedFaceCreator T (truncatedFockPhase weights (-t) x)) =
      Complex.exp (Complex.I * (t : ℂ) * (∑ i ∈ T, (weights i : ℂ))) •
        truncatedFaceCreator T x := by
  classical
  ext U
  simp only [truncatedFockPhase, truncatedFaceCreator, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.smul_apply, smul_eq_mul]
  by_cases hTU : T ⊆ U.1
  · have hsum : (∑ i ∈ U.1 \ T, (weights i : ℂ)) + ∑ i ∈ T, (weights i : ℂ) =
        ∑ i ∈ U.1, (weights i : ℂ) := Finset.sum_sdiff hTU
    simp only [hTU, if_pos, closedHorizonFaceDiff]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 1
    rw [← hsum]
    push_cast
    ring
  · simp [hTU]

end HTGeometry.ConstraintRelativity
