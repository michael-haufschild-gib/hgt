import GaloisForLFunctions.HTGeometry.UnitaryCompactCommutant
import GaloisForLFunctions.HTGeometry.HilbertSchmidtColumns
import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator
import GaloisForLFunctions.HTGeometry.ShiftTransgressionPrimitive
import GaloisForLFunctions.HTGeometry.PhaseResonanceProjection
import GaloisForLFunctions.HTGeometry.CompactAdjoint

/-!
# Atomic and continuous parts of a unitary

For a unitary `U` on a complex Hilbert space let `H_λ = ker (U - λ)`.  Eigenspaces of distinct
eigenvalues are orthogonal, nonzero ones occur only for `|λ| = 1`, and in a separable space the set
`A(U)` of eigenvalues is countable.  The **atomic subspace** `H_at` is the closed span of all
eigenspaces and the **continuous subspace** is `H_c = H_atᗮ`.  Both are invariant under `U` and
`U*`; the restriction of `U` to `H_c` is a unitary without eigenvectors.

* **Compact commutant (Lemma 3.1).**  A compact operator on `H_c` commuting with `U|H_c` vanishes.
* **Commutant structure.**  An operator commuting with `U` preserves every eigenspace and commutes
  with every eigenprojection `P_λ`, with `P_at` and `P_c`; if it is compact it vanishes on `H_c`.
* **Adapted Hilbert basis.**  Hilbert bases of the eigenspaces and of `H_c` combine into a Hilbert
  basis of `H` on which every `P_λ` and `P_c` act diagonally.
-/

open Filter Topology Set
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : H ≃ₗᵢ[ℂ] H)

/-! ### Eigenspaces -/

/-- The eigenspace `H_λ = ker (U - λ)`. -/
def unitaryEigenspace (c : ℂ) : Submodule ℂ H :=
  LinearMap.ker ((unitaryCLM U - c • (1 : H →L[ℂ] H) : H →L[ℂ] H) : H →ₗ[ℂ] H)

variable {U}

omit [CompleteSpace H] in
theorem mem_unitaryEigenspace {c : ℂ} {x : H} : x ∈ unitaryEigenspace U c ↔ U x = c • x := by
  rw [unitaryEigenspace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply, smul_apply,
    one_apply_eq_self, unitaryCLM_apply, sub_eq_zero]

omit [CompleteSpace H] in
theorem isClosed_unitaryEigenspace (c : ℂ) : IsClosed (unitaryEigenspace U c : Set H) :=
  ContinuousLinearMap.isClosed_ker _

instance (c : ℂ) : CompleteSpace (unitaryEigenspace U c) :=
  (isClosed_unitaryEigenspace c).completeSpace_coe

instance (c : ℂ) : (unitaryEigenspace U c).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

omit [CompleteSpace H] in
theorem unitary_symm_apply_of_mem {c : ℂ} {x : H} (hx : x ∈ unitaryEigenspace U c)
    (hc : ‖c‖ = 1) : U.symm x = (starRingEnd ℂ) c • x := by
  have hUx := mem_unitaryEigenspace.mp hx
  have : x = U ((starRingEnd ℂ) c • x) := by
    rw [map_smul, hUx, smul_smul, conj_mul_self_of_norm_eq_one hc, one_smul]
  conv_lhs => rw [this]
  exact U.symm_apply_apply _

omit [CompleteSpace H] in
/-- Nonzero eigenspaces occur only on the unit circle. -/
theorem norm_eq_one_of_mem_unitaryEigenspace {c : ℂ} {x : H} (hx : x ∈ unitaryEigenspace U c)
    (hx0 : x ≠ 0) : ‖c‖ = 1 := by
  have h := U.norm_map x
  rw [mem_unitaryEigenspace.mp hx, norm_smul] at h
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  nlinarith

omit [CompleteSpace H] in
/-- Eigenspaces of distinct eigenvalues are orthogonal. -/
theorem unitaryEigenspace_isOrtho {c d : ℂ} (hcd : c ≠ d) :
    unitaryEigenspace U c ⟂ unitaryEigenspace U d := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro x hx y hy
  by_cases hx0 : x = 0
  · rw [hx0, inner_zero_left]
  by_cases hy0 : y = 0
  · rw [hy0, inner_zero_right]
  have hc := norm_eq_one_of_mem_unitaryEigenspace hx hx0
  have h := U.inner_map_map x y
  rw [mem_unitaryEigenspace.mp hx, mem_unitaryEigenspace.mp hy, inner_smul_left,
    inner_smul_right, ← mul_assoc] at h
  have hne : (starRingEnd ℂ) c * d ≠ 1 := fun h1 => hcd ((conj_mul_eq_one_iff hc).mp h1)
  have h2 : ((starRingEnd ℂ) c * d - 1) * ⟪x, y⟫_ℂ = 0 := by rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)

/-- The **point spectrum** `A(U)`: the eigenvalues. -/
def unitaryPointSpectrum (U : H ≃ₗᵢ[ℂ] H) : Set ℂ := {c | unitaryEigenspace U c ≠ ⊥}

omit [CompleteSpace H] in
theorem norm_eq_one_of_mem_pointSpectrum {c : ℂ} (hc : c ∈ unitaryPointSpectrum U) : ‖c‖ = 1 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  exact norm_eq_one_of_mem_unitaryEigenspace hx hx0

omit [CompleteSpace H] in
/-- In a separable Hilbert space the point spectrum is countable. -/
theorem countable_unitaryPointSpectrum [TopologicalSpace.SeparableSpace H] :
    (unitaryPointSpectrum U).Countable := by
  have hchoice : ∀ c : unitaryPointSpectrum U, ∃ x ∈ unitaryEigenspace U c, ‖x‖ = 1 := by
    rintro ⟨c, hc⟩
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
    refine ⟨(‖x‖⁻¹ : ℂ) • x, Submodule.smul_mem _ _ hx, ?_⟩
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]
  choose v hv hv1 using hchoice
  have hon : Orthonormal ℂ v := by
    refine ⟨hv1, fun i j hij => ?_⟩
    exact (Submodule.isOrtho_iff_inner_eq.mp (unitaryEigenspace_isOrtho
      fun h => hij (Subtype.ext h))) _ (hv i) _ (hv j)
  haveI := hon.countable_index
  exact Set.countable_coe_iff.mp inferInstance

/-! ### Atomic and continuous subspaces -/

variable (U)

/-- The atomic subspace `H_at`: the closed span of the eigenspaces. -/
def atomicSubspace : Submodule ℂ H := (⨆ c, unitaryEigenspace U c).topologicalClosure

/-- The continuous subspace `H_c = H_atᗮ`. -/
def continuousSubspace : Submodule ℂ H := (atomicSubspace U)ᗮ

variable {U}

instance : CompleteSpace (atomicSubspace U) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

instance : (atomicSubspace U).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

instance : CompleteSpace (continuousSubspace U) :=
  (Submodule.isClosed_orthogonal _).completeSpace_coe

instance : (continuousSubspace U).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

omit [CompleteSpace H] in
theorem unitaryEigenspace_le_atomic (c : ℂ) : unitaryEigenspace U c ≤ atomicSubspace U :=
  (le_iSup (fun c => unitaryEigenspace U c) c).trans (Submodule.le_topologicalClosure _)

omit [CompleteSpace H] in
/-- A continuous linear map preserving every eigenspace preserves the atomic subspace. -/
theorem mapsTo_atomic_of_mapsTo_eigenspace (T : H →L[ℂ] H)
    (hT : ∀ c, ∀ x ∈ unitaryEigenspace U c, T x ∈ unitaryEigenspace U c) :
    ∀ x ∈ atomicSubspace U, T x ∈ atomicSubspace U := by
  have hsup : ⨆ c, unitaryEigenspace U c ≤
      (atomicSubspace U).comap (T : H →ₗ[ℂ] H) := by
    refine iSup_le fun c x hx => ?_
    exact unitaryEigenspace_le_atomic c (hT c x hx)
  have hclosed : IsClosed (((atomicSubspace U).comap (T : H →ₗ[ℂ] H)) : Set H) :=
    (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  intro x hx
  exact Submodule.topologicalClosure_minimal _ hsup hclosed hx

/-- An operator preserving a closed subspace whose adjoint also preserves it commutes with the
orthogonal projection. -/
theorem commute_starProjection_of_mapsTo (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (T : H →L[ℂ] H) (hT : ∀ x ∈ K, T x ∈ K)
    (hT' : ∀ x ∈ K, ContinuousLinearMap.adjoint T x ∈ K) :
    T ∘L K.starProjection = K.starProjection ∘L T := by
  have horth : ∀ y ∈ Kᗮ, T y ∈ Kᗮ := by
    intro y hy
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact (Submodule.mem_orthogonal _ _).mp hy _ (hT' u hu)
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [ContinuousLinearMap.comp_apply]
  have hdec : x = K.starProjection x + (x - K.starProjection x) := by abel
  have h1 : K.starProjection (T (K.starProjection x)) = T (K.starProjection x) :=
    Submodule.starProjection_eq_self_iff.mpr (hT _ (Submodule.starProjection_apply_mem K x))
  have h2 : K.starProjection (T (x - K.starProjection x)) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff K).mpr
      (horth _ (Submodule.sub_starProjection_mem_orthogonal x))
  conv_rhs => rw [hdec, map_add, map_add, h1, h2, add_zero]

/-! ### Invariance and the continuous restriction -/

omit [CompleteSpace H] in
theorem unitary_mapsTo_eigenspace (c : ℂ) :
    ∀ x ∈ unitaryEigenspace U c, U x ∈ unitaryEigenspace U c := by
  intro x hx
  rw [mem_unitaryEigenspace] at hx ⊢
  rw [hx, map_smul, hx]

omit [CompleteSpace H] in
theorem unitary_symm_mapsTo_eigenspace (c : ℂ) :
    ∀ x ∈ unitaryEigenspace U c, U.symm x ∈ unitaryEigenspace U c := by
  intro x hx
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
    exact Submodule.zero_mem _
  rw [unitary_symm_apply_of_mem hx (norm_eq_one_of_mem_unitaryEigenspace hx hx0)]
  exact Submodule.smul_mem _ _ hx

omit [CompleteSpace H] in
theorem unitary_mapsTo_atomic : ∀ x ∈ atomicSubspace U, U x ∈ atomicSubspace U :=
  mapsTo_atomic_of_mapsTo_eigenspace (unitaryCLM U) unitary_mapsTo_eigenspace

omit [CompleteSpace H] in
theorem unitary_symm_mapsTo_atomic : ∀ x ∈ atomicSubspace U, U.symm x ∈ atomicSubspace U :=
  mapsTo_atomic_of_mapsTo_eigenspace (unitaryCLM U.symm) unitary_symm_mapsTo_eigenspace

omit [CompleteSpace H] in
theorem unitary_mapsTo_continuous : ∀ x ∈ continuousSubspace U, U x ∈ continuousSubspace U := by
  intro x hx
  rw [continuousSubspace, Submodule.mem_orthogonal] at hx ⊢
  intro u hu
  rw [← U.apply_symm_apply u, U.inner_map_map]
  exact hx _ (unitary_symm_mapsTo_atomic u hu)

omit [CompleteSpace H] in
theorem unitary_symm_mapsTo_continuous :
    ∀ x ∈ continuousSubspace U, U.symm x ∈ continuousSubspace U := by
  intro x hx
  rw [continuousSubspace, Submodule.mem_orthogonal] at hx ⊢
  intro u hu
  rw [← U.symm.apply_symm_apply u, U.symm.inner_map_map, LinearIsometryEquiv.symm_symm]
  exact hx _ (unitary_mapsTo_atomic u hu)

variable (U)

/-- The restriction of `U` to the continuous subspace, a unitary of `H_c`. -/
def continuousRestrict : continuousSubspace U ≃ₗᵢ[ℂ] continuousSubspace U where
  toFun x := ⟨U (x : H), unitary_mapsTo_continuous (x : H) x.2⟩
  invFun x := ⟨U.symm (x : H), unitary_symm_mapsTo_continuous (x : H) x.2⟩
  left_inv x := Subtype.ext (U.symm_apply_apply (x : H))
  right_inv x := Subtype.ext (U.apply_symm_apply (x : H))
  map_add' x y := Subtype.ext (map_add U (x : H) (y : H))
  map_smul' c x := Subtype.ext (map_smul U c (x : H))
  norm_map' x := U.norm_map (x : H)

variable {U}

omit [CompleteSpace H] in
@[simp] theorem continuousRestrict_coe (x : continuousSubspace U) :
    ((continuousRestrict U x : continuousSubspace U) : H) = U x := rfl

omit [CompleteSpace H] in
/-- **`U|H_c` has no eigenvectors.** -/
theorem hasNoEigenvectors_continuousRestrict : HasNoEigenvectors (continuousRestrict U) := by
  intro x c hx
  have hmem : (x : H) ∈ unitaryEigenspace U c := by
    rw [mem_unitaryEigenspace]
    exact congrArg Subtype.val hx
  have hat := unitaryEigenspace_le_atomic c hmem
  have h0 : (x : H) = 0 := by
    have := (Submodule.mem_orthogonal _ _).mp x.2 _ hat
    exact inner_self_eq_zero.mp this
  exact Subtype.ext h0

/-- **Lemma 3.1.**  A compact operator on `H_c` commuting with `U|H_c` vanishes. -/
theorem eq_zero_of_compact_comm_continuousRestrict
    {K : continuousSubspace U →L[ℂ] continuousSubspace U} (hK : IsCompactOperator K)
    (hcomm : ∀ x, K (continuousRestrict U x) = continuousRestrict U (K x)) : K = 0 :=
  eq_zero_of_isCompactOperator_of_comm hasNoEigenvectors_continuousRestrict hK hcomm

/-! ### The commutant -/

section Commutant

variable {T : H →L[ℂ] H} (hT : ∀ x, T (U x) = U (T x))
include hT

omit [CompleteSpace H] in
theorem commute_mapsTo_eigenspace (c : ℂ) :
    ∀ x ∈ unitaryEigenspace U c, T x ∈ unitaryEigenspace U c := by
  intro x hx
  rw [mem_unitaryEigenspace] at hx ⊢
  rw [← hT, hx, map_smul]

theorem commute_adjoint_mapsTo_eigenspace (c : ℂ) :
    ∀ x ∈ unitaryEigenspace U c, ContinuousLinearMap.adjoint T x ∈ unitaryEigenspace U c := by
  intro x hx
  rw [mem_unitaryEigenspace] at hx ⊢
  rw [← adjoint_comm_of_comm U hT, hx, map_smul]

/-- An operator commuting with `U` commutes with every eigenprojection. -/
theorem commute_eigenprojection (c : ℂ) :
    T ∘L (unitaryEigenspace U c).starProjection = (unitaryEigenspace U c).starProjection ∘L T :=
  commute_starProjection_of_mapsTo _ T (commute_mapsTo_eigenspace hT c)
    (commute_adjoint_mapsTo_eigenspace hT c)

omit [CompleteSpace H] in
theorem commute_mapsTo_atomic : ∀ x ∈ atomicSubspace U, T x ∈ atomicSubspace U :=
  mapsTo_atomic_of_mapsTo_eigenspace T (commute_mapsTo_eigenspace hT)

theorem commute_adjoint_mapsTo_atomic :
    ∀ x ∈ atomicSubspace U, ContinuousLinearMap.adjoint T x ∈ atomicSubspace U :=
  mapsTo_atomic_of_mapsTo_eigenspace _ (commute_adjoint_mapsTo_eigenspace hT)

/-- An operator commuting with `U` commutes with `P_at`. -/
theorem commute_atomicProjection :
    T ∘L (atomicSubspace U).starProjection = (atomicSubspace U).starProjection ∘L T :=
  commute_starProjection_of_mapsTo _ T (commute_mapsTo_atomic hT)
    (commute_adjoint_mapsTo_atomic hT)

theorem commute_mapsTo_continuous : ∀ x ∈ continuousSubspace U, T x ∈ continuousSubspace U := by
  intro x hx
  rw [continuousSubspace, Submodule.mem_orthogonal] at hx ⊢
  intro u hu
  rw [← ContinuousLinearMap.adjoint_inner_left]
  exact hx _ (commute_adjoint_mapsTo_atomic hT u hu)

/-- **The compact commutant vanishes on the continuous part.**  A compact operator commuting with
`U` is zero on `H_c`. -/
theorem compact_comm_apply_continuous_eq_zero (hcpt : IsCompactOperator T) :
    ∀ x ∈ continuousSubspace U, T x = 0 := by
  set K : continuousSubspace U →L[ℂ] continuousSubspace U :=
    (T ∘L (continuousSubspace U).subtypeL).codRestrict (continuousSubspace U)
      fun x => commute_mapsTo_continuous hT x x.2
  have hKcpt : IsCompactOperator K := by
    obtain ⟨S, hS, hpre⟩ := hcpt.comp_clm (continuousSubspace U).subtypeL
    exact ⟨Subtype.val ⁻¹' S,
      (Submodule.isClosed_orthogonal _).isClosedEmbedding_subtypeVal.isCompact_preimage hS, hpre⟩
  have hK0 : K = 0 := eq_zero_of_compact_comm_continuousRestrict hKcpt fun x =>
    Subtype.ext (hT x)
  intro x hx
  have := congrArg (fun L : continuousSubspace U →L[ℂ] continuousSubspace U =>
    ((L ⟨x, hx⟩ : continuousSubspace U) : H)) hK0
  simpa [K] using this

/-- **Theorem 3.2, block structure.**  A compact operator commuting with `U` satisfies
`T P_c = 0` and `P_c T = 0`. -/
theorem compact_comm_continuousProjection (hcpt : IsCompactOperator T) :
    T ∘L (continuousSubspace U).starProjection = 0 ∧
      (continuousSubspace U).starProjection ∘L T = 0 := by
  have h1 := compact_comm_apply_continuous_eq_zero hT hcpt
  have hadj : ∀ x, ContinuousLinearMap.adjoint T (U x) = U (ContinuousLinearMap.adjoint T x) :=
    adjoint_comm_of_comm U hT
  have h2 := compact_comm_apply_continuous_eq_zero hadj
    (isCompactOperator_adjoint_rectangular T hcpt)
  refine ⟨ContinuousLinearMap.ext fun x => ?_, ContinuousLinearMap.ext fun x => ?_⟩
  · exact h1 _ (Submodule.starProjection_apply_mem _ x)
  · simp only [ContinuousLinearMap.comp_apply, zero_apply]
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
    intro u hu
    rw [← ContinuousLinearMap.adjoint_inner_left, h2 u hu, inner_zero_left]

end Commutant

/-! ### An adapted Hilbert basis -/

section AdaptedBasis

variable (U)

/-- The index set of a chosen Hilbert basis of the eigenspace `H_λ`. -/
def eigenBasisIndex (c : ℂ) : Set (unitaryEigenspace U c) :=
  (exists_hilbertBasis ℂ (unitaryEigenspace U c)).choose

/-- A chosen Hilbert basis of the eigenspace `H_λ`. -/
def eigenBasis (c : ℂ) : HilbertBasis (eigenBasisIndex U c) ℂ (unitaryEigenspace U c) :=
  (exists_hilbertBasis ℂ (unitaryEigenspace U c)).choose_spec.choose

/-- The index set of a chosen Hilbert basis of `H_c`. -/
def continuousBasisIndex : Set (continuousSubspace U) :=
  (exists_hilbertBasis ℂ (continuousSubspace U)).choose

/-- A chosen Hilbert basis of `H_c`. -/
def continuousBasis : HilbertBasis (continuousBasisIndex U) ℂ (continuousSubspace U) :=
  (exists_hilbertBasis ℂ (continuousSubspace U)).choose_spec.choose

/-- The adapted index set: eigenvectors of every eigenvalue, then a basis of `H_c`. -/
abbrev AdaptedIndex : Type _ := (Σ c : ℂ, eigenBasisIndex U c) ⊕ continuousBasisIndex U

/-- The adapted vectors. -/
def adaptedVec : AdaptedIndex U → H
  | Sum.inl i => (eigenBasis U i.1 i.2 : H)
  | Sum.inr k => (continuousBasis U k : H)

variable {U}

theorem adaptedVec_inl_mem (c : ℂ) (k : eigenBasisIndex U c) :
    adaptedVec U (Sum.inl ⟨c, k⟩) ∈ unitaryEigenspace U c := (eigenBasis U c k).2

theorem adaptedVec_inr_mem (k : continuousBasisIndex U) :
    adaptedVec U (Sum.inr k) ∈ continuousSubspace U := (continuousBasis U k).2

theorem orthonormal_adaptedVec : Orthonormal ℂ (adaptedVec U) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rcases i with ⟨c, k⟩ | k
    · exact (eigenBasis U c).orthonormal.1 k
    · exact (continuousBasis U).orthonormal.1 k
  · rcases i with ⟨c, k⟩ | k <;> rcases j with ⟨d, l⟩ | l
    · by_cases hcd : c = d
      · subst hcd
        have hkl : k ≠ l := fun h => hij (by rw [h])
        show ⟪((eigenBasis U c k : unitaryEigenspace U c) : H), (eigenBasis U c l : H)⟫_ℂ = 0
        rw [← Submodule.coe_inner]
        exact (eigenBasis U c).orthonormal.2 hkl
      · exact (Submodule.isOrtho_iff_inner_eq.mp (unitaryEigenspace_isOrtho hcd)) _
          (adaptedVec_inl_mem c k) _ (adaptedVec_inl_mem d l)
    · exact Submodule.inner_right_of_mem_orthogonal
        (unitaryEigenspace_le_atomic c (adaptedVec_inl_mem c k)) (adaptedVec_inr_mem l)
    · exact Submodule.inner_left_of_mem_orthogonal
        (unitaryEigenspace_le_atomic d (adaptedVec_inl_mem d l)) (adaptedVec_inr_mem k)
    · have hkl : k ≠ l := fun h => hij (by rw [h])
      show ⟪((continuousBasis U k : continuousSubspace U) : H), (continuousBasis U l : H)⟫_ℂ = 0
      rw [← Submodule.coe_inner]
      exact (continuousBasis U).orthonormal.2 hkl

omit [CompleteSpace H] in
/-- Every vector of a closed subspace spanned densely by part of a family lies in the closure of
the span of the family. -/
theorem mem_closure_span_of_hilbertBasis {K : Submodule ℂ H} {κ : Type*}
    (b : HilbertBasis κ ℂ K) {S : Submodule ℂ H} (hS : IsClosed (S : Set H))
    (hb : ∀ k, (b k : H) ∈ S) {x : H} (hx : x ∈ K) : x ∈ S := by
  have hsum := (b.hasSum_repr ⟨x, hx⟩).mapL K.subtypeL
  refine hS.mem_of_tendsto hsum (Eventually.of_forall fun s => ?_)
  simp only [Submodule.subtypeL_apply, Submodule.coe_smul]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hb k)

theorem adaptedVec_dense :
    ⊤ ≤ (Submodule.span ℂ (Set.range (adaptedVec U))).topologicalClosure := by
  set S := (Submodule.span ℂ (Set.range (adaptedVec U))).topologicalClosure
  have hS : IsClosed (S : Set H) := Submodule.isClosed_topologicalClosure _
  have hvec : ∀ i, adaptedVec U i ∈ S := fun i =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
  have heig : ∀ c, unitaryEigenspace U c ≤ S := fun c x hx =>
    mem_closure_span_of_hilbertBasis (eigenBasis U c) hS (fun k => hvec (Sum.inl ⟨c, k⟩)) hx
  have hcont : continuousSubspace U ≤ S := fun x hx =>
    mem_closure_span_of_hilbertBasis (continuousBasis U) hS (fun k => hvec (Sum.inr k)) hx
  have hat : atomicSubspace U ≤ S := Submodule.topologicalClosure_minimal _ (iSup_le heig) hS
  rw [← Submodule.sup_orthogonal_of_hasOrthogonalProjection (K := atomicSubspace U)]
  exact sup_le hat hcont

/-- **The adapted Hilbert basis**: eigenvectors of all eigenvalues together with a basis of
`H_c`. -/
def adaptedBasis (U : H ≃ₗᵢ[ℂ] H) : HilbertBasis (AdaptedIndex U) ℂ H :=
  HilbertBasis.mk orthonormal_adaptedVec adaptedVec_dense

theorem adaptedBasis_apply (i : AdaptedIndex U) : adaptedBasis U i = adaptedVec U i :=
  congrFun (HilbertBasis.coe_mk _ _) i

/-- `P_λ` on the adapted basis. -/
theorem eigenprojection_adaptedVec (c : ℂ) (i : AdaptedIndex U) :
    (unitaryEigenspace U c).starProjection (adaptedVec U i) =
      match i with
      | Sum.inl j => if j.1 = c then adaptedVec U i else 0
      | Sum.inr _ => 0 := by
  rcases i with ⟨d, k⟩ | k
  · simp only
    split_ifs with hdc
    · subst hdc
      exact Submodule.starProjection_eq_self_iff.mpr (adaptedVec_inl_mem _ k)
    · refine (Submodule.starProjection_apply_eq_zero_iff _).mpr ?_
      exact (Submodule.isOrtho_iff_le.mp (unitaryEigenspace_isOrtho hdc)) (adaptedVec_inl_mem d k)
  · refine (Submodule.starProjection_apply_eq_zero_iff _).mpr ?_
    rw [Submodule.mem_orthogonal]
    intro u hu
    exact Submodule.inner_right_of_mem_orthogonal (unitaryEigenspace_le_atomic c hu)
      (adaptedVec_inr_mem k)

/-- `P_c` on the adapted basis. -/
theorem continuousProjection_adaptedVec (i : AdaptedIndex U) :
    (continuousSubspace U).starProjection (adaptedVec U i) =
      match i with
      | Sum.inl _ => 0
      | Sum.inr _ => adaptedVec U i := by
  rcases i with ⟨d, k⟩ | k
  · refine (Submodule.starProjection_apply_eq_zero_iff _).mpr ?_
    show _ ∈ (atomicSubspace U)ᗮᗮ
    rw [Submodule.orthogonal_orthogonal]
    exact unitaryEigenspace_le_atomic d (adaptedVec_inl_mem d k)
  · exact Submodule.starProjection_eq_self_iff.mpr (adaptedVec_inr_mem k)

end AdaptedBasis

end GaloisForLFunctions.HTGeometry
