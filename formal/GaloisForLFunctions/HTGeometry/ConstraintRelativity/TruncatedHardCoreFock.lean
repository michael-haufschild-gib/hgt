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
    rw [if_neg hSdiff]
    rfl
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
        ext x
        exact truncatedFaceCreator_comp_of_disjoint hTS x]
      exact truncatedFaceCreator_mem_span U
    · have hlarge : d - 2 < (T.1 ∪ S.1).card := Nat.lt_of_not_ge hcard
      rw [show truncatedFaceCreator T.1 * truncatedFaceCreator S.1 =
          truncatedFaceCreator (T.1 ∪ S.1) by
        ext x
        exact truncatedFaceCreator_comp_of_disjoint hTS x,
        truncatedFaceCreator_eq_zero_of_large _ hlarge]
      exact (truncatedFaceCreatorSpan d).zero_mem
  · rw [show truncatedFaceCreator T.1 * truncatedFaceCreator S.1 = 0 by
      ext x
      exact truncatedFaceCreator_comp_eq_zero_of_not_disjoint hTS x]
    exact (truncatedFaceCreatorSpan d).zero_mem

/-- The creator span is closed under composition. -/
theorem truncatedFaceCreatorSpan_mul_mem {d : ℕ}
    {A B : Module.End ℂ (TruncatedFaceFock d)}
    (hA : A ∈ truncatedFaceCreatorSpan d) (hB : B ∈ truncatedFaceCreatorSpan d) :
    A * B ∈ truncatedFaceCreatorSpan d := by
  refine Submodule.span_induction hA ?_ ?_ ?_ ?_
  · rintro _ ⟨T, rfl⟩
    refine Submodule.span_induction hB ?_ ?_ ?_ ?_
    · rintro _ ⟨S, rfl⟩
      exact truncatedFaceCreator_mul_mem_span T S
    · simpa using (truncatedFaceCreatorSpan d).zero_mem
    · intro X Y hX hY
      simpa [mul_add] using (truncatedFaceCreatorSpan d).add_mem hX hY
    · intro c X hX
      simpa [mul_smul_comm] using (truncatedFaceCreatorSpan d).smul_mem c hX
  · simpa using (truncatedFaceCreatorSpan d).zero_mem
  · intro X Y hX hY
    simpa [add_mul] using (truncatedFaceCreatorSpan d).add_mem hX hY
  · intro c X hX
    simpa [smul_mul_assoc] using (truncatedFaceCreatorSpan d).smul_mem c hX

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

/-- Face coefficients sent to their creator-monomial linear combination. -/
noncomputable def faceCoefficientOperator (d : ℕ) :
    TruncatedFaceFock d →ₗ[ℂ] Module.End ℂ (TruncatedFaceFock d) where
  toFun x := ∑ T, x T • truncatedFaceCreator T.1
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [mul_smul]

theorem faceCoefficientOperator_mem_span {d : ℕ} (x : TruncatedFaceFock d) :
    faceCoefficientOperator d x ∈ truncatedFaceCreatorSpan d := by
  exact Submodule.sum_mem _ fun T _ =>
    (truncatedFaceCreatorSpan d).smul_mem (x T) (truncatedFaceCreator_mem_span T)

/-- Vacuum evaluation recovers every face coefficient. -/
theorem faceCoefficientOperator_vacuum {d : ℕ} (x : TruncatedFaceFock d) :
    faceCoefficientOperator d x (truncatedFaceVacuum d) = x := by
  classical
  ext U
  simp only [faceCoefficientOperator, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, truncatedFaceCreator_vacuum, truncatedFaceBasis,
    Pi.single_apply]
  rw [Finset.sum_eq_single U]
  · simp
  · intro T _ hTU
    simp [hTU]
  · intro hU
    exact (hU (Finset.mem_univ U)).elim

theorem faceCoefficientOperator_injective (d : ℕ) :
    Function.Injective (faceCoefficientOperator d) := by
  intro x y hxy
  have := congrArg (fun A : Module.End ℂ (TruncatedFaceFock d) =>
    A (truncatedFaceVacuum d)) hxy
  simpa [faceCoefficientOperator_vacuum] using this

/-- Creator span consists of exactly the face-coefficient operators. -/
theorem faceCoefficientOperator_range_eq_span (d : ℕ) :
    LinearMap.range (faceCoefficientOperator d) = truncatedFaceCreatorSpan d := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact faceCoefficientOperator_mem_span x
  · rw [truncatedFaceCreatorSpan, Submodule.span_le]
    rintro _ ⟨T, rfl⟩
    refine ⟨truncatedFaceBasis T, ?_⟩
    apply (faceCoefficientOperator_injective d)
    rw [faceCoefficientOperator_vacuum]
    rw [truncatedFaceCreator_vacuum]

/-- **Card `(27)`, vector-space and operator-algebra realization.** Closed-horizon face
coefficients are linearly equivalent to the full algebra generated by compressed creators. -/
noncomputable def closedHorizonFaceEquivCreatorAlgebra (d : ℕ) :
    TruncatedFaceFock d ≃ₗ[ℂ] truncatedFaceCreatorAlgebra d :=
  LinearEquiv.ofBijective
    { toFun := fun x => ⟨faceCoefficientOperator d x, faceCoefficientOperator_mem_span x⟩
      map_add' := by intro x y; ext; exact (faceCoefficientOperator d).map_add x y
      map_smul' := by intro c x; ext; exact (faceCoefficientOperator d).map_smul c x }
    ⟨fun x y h => faceCoefficientOperator_injective d (congrArg Subtype.val h), by
      rintro ⟨A, hA⟩
      rw [← faceCoefficientOperator_range_eq_span d] at hA
      obtain ⟨x, rfl⟩ := hA
      exact ⟨x, rfl⟩⟩

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
