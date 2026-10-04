import Mathlib

/-!
# Bounded Fredholm operators: Grushin bordering, stability and compact perturbations

For bounded operators between complex Hilbert spaces, `T` is **Fredholm** when its kernel is
finite-dimensional, its range is closed, and its cokernel `F ⧸ range T` is finite-dimensional; its
**index** is `dim ker T - dim coker T`.

* **Grushin bordering.**  If `(x, y) ↦ (T x + E₊ y, E₋ x)` is an isomorphism `E × M ≃ F × N` with
  `N, M` finite-dimensional, then `T` is Fredholm of index `dim N - dim M`
  (`isFredholmOp_of_grushin`).  Every Fredholm operator admits such a bordering, through
  `N = ker T`, `M = (range T)ᗮ` (`IsFredholmOp.exists_bordering`).
* **Stability.**  The Fredholm operators are open and the index is locally constant
  (`IsFredholmOp.exists_stable`).
* **Compact perturbations (Atkinson).**  Compact operators are norm limits of finite-rank ones
  (`IsCompactOperator.exists_finiteRank_approx`); `1 + C` has finite-dimensional kernel and closed
  finite-codimensional range for compact `C`; hence `T + R` is Fredholm for compact `R`, with the
  same index (`IsFredholmOp.add_compact`, `fredholmIndex_add_compact`).
-/

open Filter Topology Module
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A bounded operator is **Fredholm** when its kernel is finite-dimensional, its range is closed
and its cokernel is finite-dimensional. -/
structure IsFredholmOp (T : E →L[ℂ] F) : Prop where
  finiteDimensional_ker : FiniteDimensional ℂ (LinearMap.ker (T : E →ₗ[ℂ] F))
  isClosed_range : IsClosed (LinearMap.range (T : E →ₗ[ℂ] F) : Set F)
  finiteDimensional_coker : FiniteDimensional ℂ (F ⧸ LinearMap.range (T : E →ₗ[ℂ] F))

/-- The **Fredholm index** `dim ker T - dim coker T`. -/
def fredholmIndex (T : E →L[ℂ] F) : ℤ :=
  (finrank ℂ (LinearMap.ker (T : E →ₗ[ℂ] F)) : ℤ) -
    (finrank ℂ (F ⧸ LinearMap.range (T : E →ₗ[ℂ] F)) : ℤ)

/-! ### Grushin bordering -/

section Grushin

variable {N M : Type*} [NormedAddCommGroup N] [InnerProductSpace ℂ N] [FiniteDimensional ℂ N]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The Grushin lemma.**  If the bordered operator `(x, y) ↦ (T x + E₊ y, E₋ x)` is an
isomorphism `E × M ≃ F × N`, then `T` is Fredholm with index `dim N - dim M`. -/
theorem isFredholmOp_of_grushin (T : E →L[ℂ] F) (Em : E →L[ℂ] N) (Ep : M →L[ℂ] F)
    (G : (E × M) ≃L[ℂ] (F × N)) (hG : ∀ x y, G (x, y) = (T x + Ep y, Em x)) :
    IsFredholmOp T ∧ fredholmIndex T = (finrank ℂ N : ℤ) - (finrank ℂ M : ℤ) := by
  -- the four blocks of the inverse
  set F0 : F →L[ℂ] E := ContinuousLinearMap.fst ℂ E M ∘L (G.symm : F × N →L[ℂ] E × M) ∘L
    ContinuousLinearMap.inl ℂ F N
  set Fp : N →L[ℂ] E := ContinuousLinearMap.fst ℂ E M ∘L (G.symm : F × N →L[ℂ] E × M) ∘L
    ContinuousLinearMap.inr ℂ F N
  set Fm : F →L[ℂ] M := ContinuousLinearMap.snd ℂ E M ∘L (G.symm : F × N →L[ℂ] E × M) ∘L
    ContinuousLinearMap.inl ℂ F N
  set Fmp : N →L[ℂ] M := ContinuousLinearMap.snd ℂ E M ∘L (G.symm : F × N →L[ℂ] E × M) ∘L
    ContinuousLinearMap.inr ℂ F N
  have hsymm : ∀ k n, G.symm (k, n) = (F0 k + Fp n, Fm k + Fmp n) := by
    intro k n
    have h : (k, n) = ((k, 0) : F × N) + (0, n) := by simp
    rw [h, map_add]
    rfl
  have hGsymm : ∀ x y, G.symm (T x + Ep y, Em x) = (x, y) := by
    intro x y
    rw [← hG, ContinuousLinearEquiv.symm_apply_apply]
  have hGG : ∀ k n, T (F0 k + Fp n) + Ep (Fm k + Fmp n) = k ∧ Em (F0 k + Fp n) = n := by
    intro k n
    have h := G.apply_symm_apply (k, n)
    rw [hsymm, hG] at h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  -- kernel isomorphism
  have hker1 : ∀ x, T x = 0 → Fmp (Em x) = 0 ∧ Fp (Em x) = x := by
    intro x hx
    have h := hGsymm x 0
    rw [map_zero, add_zero, hx, hsymm] at h
    simp only [map_zero, zero_add] at h
    exact ⟨congrArg Prod.snd h, congrArg Prod.fst h⟩
  have hker2 : ∀ n, Fmp n = 0 → T (Fp n) = 0 ∧ Em (Fp n) = n := by
    intro n hn
    have h := hGG 0 n
    simp only [map_zero, zero_add, hn, add_zero] at h
    exact h
  let kerT := LinearMap.ker (T : E →ₗ[ℂ] F)
  let kerF := LinearMap.ker (Fmp : N →ₗ[ℂ] M)
  have ekerT : kerT ≃ₗ[ℂ] kerF :=
    LinearEquiv.ofLinear
      (((Em : E →ₗ[ℂ] N).comp kerT.subtype).codRestrict kerF fun x => (hker1 x x.2).1)
      (((Fp : N →ₗ[ℂ] E).comp kerF.subtype).codRestrict kerT fun n => (hker2 n n.2).1)
      (by
        ext n
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.codRestrict_apply,
          Submodule.coe_subtype, LinearMap.id_coe, id_eq]
        exact (hker2 n n.2).2)
      (by
        ext x
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.codRestrict_apply,
          Submodule.coe_subtype, LinearMap.id_coe, id_eq]
        exact (hker1 x x.2).2)
  -- cokernel isomorphism
  have hFmT : ∀ x, Fm (T x) = -Fmp (Em x) := by
    intro x
    have h := hGsymm x 0
    rw [map_zero, add_zero, hsymm] at h
    have h2 := congrArg Prod.snd h
    simp only at h2
    exact eq_neg_of_add_eq_zero_left h2
  have hrange : ∀ k, k ∈ LinearMap.range (T : E →ₗ[ℂ] F) ↔
      Fm k ∈ LinearMap.range (Fmp : N →ₗ[ℂ] M) := by
    intro k
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨-Em x, ?_⟩
      show Fmp (-Em x) = Fm (T x)
      rw [map_neg, hFmT]
    · rintro ⟨n, hn⟩
      refine ⟨F0 k - Fp n, ?_⟩
      have h1 := (hGG k 0).1
      have h2 := (hGG 0 n).1
      simp only [map_zero, add_zero, zero_add] at h1 h2
      have hn' : Fmp n = Fm k := hn
      have e1 : T (F0 k) = k - Ep (Fm k) := eq_sub_of_add_eq h1
      have e2 : T (Fp n) = -Ep (Fmp n) := eq_neg_of_add_eq_zero_left h2
      show T (F0 k - Fp n) = k
      rw [map_sub, e1, e2, hn']
      abel
  have hsurj : Function.Surjective
      ((LinearMap.range (Fmp : N →ₗ[ℂ] M)).mkQ ∘ₗ (Fm : F →ₗ[ℂ] M)) := by
    intro q
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ q
    refine ⟨Ep m, ?_⟩
    have h := hGsymm 0 m
    rw [map_zero, zero_add, map_zero, hsymm] at h
    have h2 := congrArg Prod.snd h
    simp only [map_zero, add_zero] at h2
    show (LinearMap.range (Fmp : N →ₗ[ℂ] M)).mkQ (Fm (Ep m)) = _
    rw [h2]
  have hkerφ : LinearMap.ker ((LinearMap.range (Fmp : N →ₗ[ℂ] M)).mkQ ∘ₗ (Fm : F →ₗ[ℂ] M)) =
      LinearMap.range (T : E →ₗ[ℂ] F) := by
    ext k
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, hrange]
    rfl
  have ecoker : (F ⧸ LinearMap.range (T : E →ₗ[ℂ] F)) ≃ₗ[ℂ]
      (M ⧸ LinearMap.range (Fmp : N →ₗ[ℂ] M)) :=
    (Submodule.quotEquivOfEq _ _ hkerφ.symm).trans (LinearMap.quotKerEquivOfSurjective _ hsurj)
  have hclosed : IsClosed (LinearMap.range (T : E →ₗ[ℂ] F) : Set F) := by
    have hR : IsClosed (LinearMap.range (Fmp : N →ₗ[ℂ] M) : Set M) :=
      Submodule.closed_of_finiteDimensional _
    have heq : (LinearMap.range (T : E →ₗ[ℂ] F) : Set F) =
        Fm ⁻¹' (LinearMap.range (Fmp : N →ₗ[ℂ] M) : Set M) := by
      ext k
      exact hrange k
    rw [heq]
    exact hR.preimage Fm.continuous
  refine ⟨⟨ekerT.symm.finiteDimensional, hclosed, ecoker.symm.finiteDimensional⟩, ?_⟩
  rw [fredholmIndex, ekerT.finrank_eq, ecoker.finrank_eq]
  have h1 : finrank ℂ (LinearMap.range (Fmp : N →ₗ[ℂ] M)) + finrank ℂ kerF = finrank ℂ N :=
    LinearMap.finrank_range_add_finrank_ker _
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range (Fmp : N →ₗ[ℂ] M))
  omega

end Grushin

/-! ### The canonical bordering and stability -/

section Stability

variable {T : E →L[ℂ] F}

omit [CompleteSpace E] in
theorem IsFredholmOp.hasOrthogonalProjection_range (hT : IsFredholmOp T) :
    (LinearMap.range (T : E →ₗ[ℂ] F)).HasOrthogonalProjection := by
  haveI : CompleteSpace (LinearMap.range (T : E →ₗ[ℂ] F)) := hT.isClosed_range.completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

omit [CompleteSpace E] in
theorem IsFredholmOp.finiteDimensional_orthogonal_range (hT : IsFredholmOp T) :
    FiniteDimensional ℂ (LinearMap.range (T : E →ₗ[ℂ] F))ᗮ := by
  haveI := hT.hasOrthogonalProjection_range
  haveI := hT.finiteDimensional_coker
  exact (Submodule.quotientEquivOfIsCompl _ _
    (Submodule.isCompl_orthogonal (LinearMap.range (T : E →ₗ[ℂ] F)))).finiteDimensional

omit [CompleteSpace E] in
theorem IsFredholmOp.finrank_orthogonal_range (hT : IsFredholmOp T) :
    finrank ℂ (LinearMap.range (T : E →ₗ[ℂ] F))ᗮ =
      finrank ℂ (F ⧸ LinearMap.range (T : E →ₗ[ℂ] F)) := by
  haveI := hT.hasOrthogonalProjection_range
  exact (Submodule.quotientEquivOfIsCompl _ _
    (Submodule.isCompl_orthogonal (LinearMap.range (T : E →ₗ[ℂ] F)))).finrank_eq.symm

/-- **The canonical Grushin bordering** of a Fredholm operator through `N = ker T` and
`M = (range T)ᗮ`: `(x, y) ↦ (T x + y, P_N x)` is an isomorphism. -/
theorem IsFredholmOp.exists_bordering (hT : IsFredholmOp T) :
    haveI := hT.finiteDimensional_ker
    ∃ G : (E × (LinearMap.range (T : E →ₗ[ℂ] F))ᗮ) ≃L[ℂ]
        (F × LinearMap.ker (T : E →ₗ[ℂ] F)),
      ∀ x y, G (x, y) = (T x + (y : F),
        (LinearMap.ker (T : E →ₗ[ℂ] F)).orthogonalProjectionOnto x) := by
  haveI := hT.finiteDimensional_ker
  haveI := hT.hasOrthogonalProjection_range
  set R := LinearMap.range (T : E →ₗ[ℂ] F)
  set N := LinearMap.ker (T : E →ₗ[ℂ] F)
  set G0 : (E × Rᗮ) →L[ℂ] (F × N) :=
    (T ∘L ContinuousLinearMap.fst ℂ E Rᗮ + Rᗮ.subtypeL ∘L ContinuousLinearMap.snd ℂ E Rᗮ).prod
      (N.orthogonalProjectionOnto ∘L ContinuousLinearMap.fst ℂ E Rᗮ)
  have hG0 : ∀ x y, G0 (x, y) = (T x + (y : F), N.orthogonalProjectionOnto x) := fun x y => rfl
  have hker : LinearMap.ker (G0 : (E × Rᗮ) →ₗ[ℂ] (F × N)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨x, y⟩ h
    have h' : G0 (x, y) = 0 := h
    rw [hG0, Prod.mk_eq_zero] at h'
    obtain ⟨h1, h2⟩ := h'
    have hyR : (y : F) ∈ R := ⟨-x, by
      show T (-x) = (y : F)
      rw [map_neg]
      exact (neg_eq_of_add_eq_zero_right h1)⟩
    have hy0 : (y : F) = 0 := by
      have := Submodule.mem_inf.mpr ⟨hyR, y.2⟩
      rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at this
    have hTx : T x = 0 := by rwa [hy0, add_zero] at h1
    have hxN : x ∈ N := hTx
    have hx0 : x = 0 := by
      have := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := N) ⟨x, hxN⟩
      rw [h2] at this
      exact congrArg Subtype.val this.symm
    rw [Prod.mk_eq_zero]
    exact ⟨hx0, Subtype.ext hy0⟩
  have hrange : LinearMap.range (G0 : (E × Rᗮ) →ₗ[ℂ] (F × N)) = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨k, n⟩
    obtain ⟨x0, hx0⟩ : (R.starProjection k) ∈ R := by
      rw [Submodule.starProjection_apply]
      exact (R.orthogonalProjectionOnto k).2
    have hx0' : T x0 = R.starProjection k := hx0
    refine ⟨(x0 - (N.starProjection x0) + (n : E), ⟨k - R.starProjection k,
      Submodule.sub_starProjection_mem_orthogonal k⟩), ?_⟩
    show G0 _ = _
    rw [hG0]
    have hPN : ∀ v : N, T (v : E) = 0 := fun v => v.2
    have hPx : T (N.starProjection x0) = 0 := by
      rw [Submodule.starProjection_apply]
      exact hPN _
    refine Prod.ext ?_ ?_
    · simp only
      rw [map_add, map_sub, hPx, hPN n, hx0']
      abel
    · simp only
      rw [map_add, map_sub, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
        Submodule.starProjection_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
      abel
  exact ⟨ContinuousLinearEquiv.ofBijective G0 hker hrange, fun x y => rfl⟩

omit [CompleteSpace E] in
/-- The index of a Fredholm operator is `dim ker T - dim (range T)ᗮ`. -/
theorem IsFredholmOp.fredholmIndex_eq (hT : IsFredholmOp T) :
    fredholmIndex T = (finrank ℂ (LinearMap.ker (T : E →ₗ[ℂ] F)) : ℤ) -
      (finrank ℂ (LinearMap.range (T : E →ₗ[ℂ] F))ᗮ : ℤ) := by
  rw [fredholmIndex, hT.finrank_orthogonal_range]

/-- **Stability.**  The Fredholm operators form an open set and the index is locally constant:
around every Fredholm `T` there is a ball of perturbations `S` keeping `T + S` Fredholm of the same
index. -/
theorem IsFredholmOp.exists_stable (hT : IsFredholmOp T) :
    ∃ δ > 0, ∀ S : E →L[ℂ] F, ‖S‖ < δ →
      IsFredholmOp (T + S) ∧ fredholmIndex (T + S) = fredholmIndex T := by
  haveI := hT.finiteDimensional_ker
  haveI := hT.hasOrthogonalProjection_range
  haveI := hT.finiteDimensional_orthogonal_range
  set R := LinearMap.range (T : E →ₗ[ℂ] F)
  set N := LinearMap.ker (T : E →ₗ[ℂ] F)
  obtain ⟨G, hG⟩ := hT.exists_bordering
  have hopen := ContinuousLinearEquiv.isOpen (𝕜 := ℂ) (E := E × Rᗮ) (F := F × N)
  obtain ⟨ε, hε, hball⟩ := (NormedAddCommGroup.nhds_basis_norm_lt
    (G : (E × Rᗮ) →L[ℂ] (F × N))).mem_iff.mp (hopen.mem_nhds ⟨G, rfl⟩)
  refine ⟨ε, hε, fun S hS => ?_⟩
  set Δ : (E × Rᗮ) →L[ℂ] (F × N) :=
    ContinuousLinearMap.inl ℂ F N ∘L S ∘L ContinuousLinearMap.fst ℂ E Rᗮ
  have hΔ : ‖Δ‖ ≤ ‖S‖ := by
    calc ‖Δ‖ ≤ ‖ContinuousLinearMap.inl ℂ F N‖ * ‖S ∘L ContinuousLinearMap.fst ℂ E Rᗮ‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (‖S‖ * ‖ContinuousLinearMap.fst ℂ E Rᗮ‖) := by
          gcongr
          · exact ContinuousLinearMap.norm_inl_le_one ℂ F N
          · exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (‖S‖ * 1) := by
          gcongr
          exact ContinuousLinearMap.norm_fst_le ℂ E Rᗮ
      _ = ‖S‖ := by ring
  have hmem : (G : (E × Rᗮ) →L[ℂ] (F × N)) + Δ ∈
      {y | ‖y - (G : (E × Rᗮ) →L[ℂ] (F × N))‖ < ε} := by
    show ‖(G : (E × Rᗮ) →L[ℂ] (F × N)) + Δ - G‖ < ε
    rw [add_sub_cancel_left]
    exact lt_of_le_of_lt hΔ hS
  obtain ⟨e, he⟩ := hball hmem
  have he' : ∀ x y, e (x, y) = ((T + S) x + (y : F), N.orthogonalProjectionOnto x) := by
    intro x y
    have h := congrArg (fun L : (E × Rᗮ) →L[ℂ] (F × N) => L (x, y)) he
    simp only [ContinuousLinearEquiv.coe_coe] at h
    rw [h, add_apply, ContinuousLinearEquiv.coe_coe, hG]
    simp only [Δ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, add_apply]
    exact Prod.ext (by abel_nf) rfl
  have hT' := (isFredholmOp_of_grushin T N.orthogonalProjectionOnto Rᗮ.subtypeL G hG).2
  obtain ⟨hTS, hTSind⟩ :=
    isFredholmOp_of_grushin (T + S) N.orthogonalProjectionOnto Rᗮ.subtypeL e he'
  exact ⟨hTS, hTSind.trans hT'.symm⟩

end Stability

/-! ### Finite codimension and invertible compositions -/

section Codimension

/-- A subspace containing a closed finite-codimensional subspace is closed and
finite-codimensional. -/
theorem isClosed_and_finiteDimensional_quotient_of_le {U V : Submodule ℂ E} (hUV : U ≤ V)
    (hU : IsClosed (U : Set E)) (hUfin : FiniteDimensional ℂ (E ⧸ U)) :
    IsClosed (V : Set E) ∧ FiniteDimensional ℂ (E ⧸ V) := by
  haveI : CompleteSpace U := hU.completeSpace_coe
  haveI : U.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace U
  haveI : FiniteDimensional ℂ Uᗮ :=
    (Submodule.quotientEquivOfIsCompl _ _ (Submodule.isCompl_orthogonal U)).finiteDimensional
  set W : Submodule ℂ E := V ⊓ Uᗮ
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le inf_le_right
  have hW : IsClosed (W : Set E) := Submodule.closed_of_finiteDimensional W
  have hset : (V : Set E) =
      (ContinuousLinearMap.id ℂ E - U.starProjection) ⁻¹' (W : Set E) := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe, FunLike.coe_sub,
      ContinuousLinearMap.coe_id', Pi.sub_apply, id_eq]
    have hPU : U.starProjection x ∈ V := by
      rw [Submodule.starProjection_apply]
      exact hUV (U.orthogonalProjectionOnto x).2
    constructor
    · intro hx
      exact Submodule.mem_inf.mpr ⟨V.sub_mem hx hPU, Submodule.sub_starProjection_mem_orthogonal x⟩
    · intro hx
      have h := V.add_mem (Submodule.mem_inf.mp hx).1 hPU
      rwa [sub_add_cancel] at h
  refine ⟨hset ▸ hW.preimage (ContinuousLinearMap.continuous _), ?_⟩
  exact Module.Finite.of_surjective (U.mapQ V LinearMap.id hUV) fun q => by
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective V q
    exact ⟨Submodule.Quotient.mk x, rfl⟩

variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace F'] in
/-- Composing on the left with an isomorphism preserves Fredholmness and the index. -/
theorem IsFredholmOp.equiv_comp {T : E →L[ℂ] F} (hT : IsFredholmOp T) (e : F ≃L[ℂ] F') :
    IsFredholmOp ((e : F →L[ℂ] F') ∘L T) ∧
      fredholmIndex ((e : F →L[ℂ] F') ∘L T) = fredholmIndex T := by
  have hker : LinearMap.ker (((e : F →L[ℂ] F') ∘L T : E →L[ℂ] F') : E →ₗ[ℂ] F') =
      LinearMap.ker (T : E →ₗ[ℂ] F) := by
    ext x
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, map_eq_zero_iff _ e.injective]
  have hrange : LinearMap.range (((e : F →L[ℂ] F') ∘L T : E →L[ℂ] F') : E →ₗ[ℂ] F') =
      (LinearMap.range (T : E →ₗ[ℂ] F)).map (e.toLinearEquiv : F →ₗ[ℂ] F') := by
    show LinearMap.range (((e : F →L[ℂ] F') : F →ₗ[ℂ] F').comp (T : E →ₗ[ℂ] F)) = _
    rw [LinearMap.range_comp]
    rfl
  let eq : (F' ⧸ LinearMap.range (((e : F →L[ℂ] F') ∘L T : E →L[ℂ] F') : E →ₗ[ℂ] F')) ≃ₗ[ℂ]
      (F ⧸ LinearMap.range (T : E →ₗ[ℂ] F)) :=
    ((Submodule.Quotient.equiv _ _ e.toLinearEquiv rfl).trans
      (Submodule.quotEquivOfEq _ _ hrange.symm)).symm
  have hcl : IsClosed (LinearMap.range (((e : F →L[ℂ] F') ∘L T : E →L[ℂ] F') : E →ₗ[ℂ] F') :
      Set F') := by
    rw [hrange, Submodule.map_coe]
    exact (e.toHomeomorph.isClosed_image).mpr hT.isClosed_range
  haveI := hT.finiteDimensional_ker
  haveI := hT.finiteDimensional_coker
  refine ⟨⟨hker ▸ inferInstance, hcl, eq.symm.finiteDimensional⟩, ?_⟩
  rw [fredholmIndex, fredholmIndex, eq.finrank_eq, hker]

end Codimension

/-! ### Compact perturbations -/

section CompactPerturbation

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Finite-rank approximation of compact operators** on Hilbert space. -/
theorem IsCompactOperator.exists_finiteRank_approx {R : E →L[ℂ] F} (hR : IsCompactOperator R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : E →L[ℂ] F, FiniteDimensional ℂ (LinearMap.range (G : E →ₗ[ℂ] F)) ∧ ‖R - G‖ ≤ ε := by
  obtain ⟨t, -, htfin, hcover⟩ :=
    (hR.isCompact_closure_image_closedBall 1).finite_cover_balls hε
  set V : Submodule ℂ F := Submodule.span ℂ t
  haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ htfin
  refine ⟨V.starProjection ∘L R, ?_, ?_⟩
  · have hle : LinearMap.range ((V.starProjection ∘L R : E →L[ℂ] F) : E →ₗ[ℂ] F) ≤ V := by
      rintro _ ⟨x, rfl⟩
      show V.starProjection (R x) ∈ V
      rw [Submodule.starProjection_apply]
      exact (V.orthogonalProjectionOnto (R x)).2
    exact Submodule.finiteDimensional_of_le hle
  · refine ContinuousLinearMap.opNorm_le_of_unit_norm hε.le fun x hx => ?_
    have hmem : R x ∈ closure (R '' Metric.closedBall 0 1) :=
      subset_closure ⟨x, by simp [hx], rfl⟩
    obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.mp (hcover hmem)
    have hyV : y ∈ V := Submodule.subset_span hyt
    rw [sub_apply, ContinuousLinearMap.comp_apply]
    have hmin := Submodule.starProjection_minimal (U := V) (R x)
    have hle : ‖R x - V.starProjection (R x)‖ ≤ ‖R x - y‖ := by
      rw [hmin]
      exact ciInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩ (⟨y, hyV⟩ : V)
    rw [Metric.mem_ball, dist_eq_norm] at hy
    linarith

omit [CompleteSpace E] in
/-- Operators into a finite-dimensional space are compact. -/
theorem isCompactOperator_of_finiteDimensional_codomain {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℂ N] [FiniteDimensional ℂ N] (T : E →L[ℂ] N) : IsCompactOperator T :=
  isCompactOperator_of_locallyCompactSpace_dom T

omit [CompleteSpace E] [CompleteSpace F] in
/-- Finite-rank operators are compact. -/
theorem isCompactOperator_of_finiteDimensional_range {G : E →L[ℂ] F}
    (hG : FiniteDimensional ℂ (LinearMap.range (G : E →ₗ[ℂ] F))) : IsCompactOperator G := by
  set W := LinearMap.range (G : E →ₗ[ℂ] F)
  have h := (isCompactOperator_of_finiteDimensional_codomain
    (G.codRestrict W fun x => ⟨x, rfl⟩)).clm_comp W.subtypeL
  have heq : (G : E → F) = (W.subtypeL : W → F) ∘ (G.codRestrict W fun x => ⟨x, rfl⟩) := by
    funext x
    rfl
  rw [heq]
  exact h

/-- `1 + G` is Fredholm for finite-rank `G`. -/
theorem isFredholmOp_one_add_finiteRank {G : E →L[ℂ] E}
    (hG : FiniteDimensional ℂ (LinearMap.range (G : E →ₗ[ℂ] E))) :
    IsFredholmOp (1 + G) := by
  have hker : LinearMap.ker ((1 + G : E →L[ℂ] E) : E →ₗ[ℂ] E) ≤
      LinearMap.range (G : E →ₗ[ℂ] E) := by
    intro x hx
    have hx' : x + G x = 0 := hx
    have h2 : G x = -x := by
      rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
      exact hx'
    exact ⟨-x, by
      show G (-x) = x
      rw [map_neg, h2, neg_neg]⟩
  have hle : LinearMap.ker (G : E →ₗ[ℂ] E) ≤ LinearMap.range ((1 + G : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
    intro x hx
    exact ⟨x, by
      show x + G x = x
      rw [show G x = 0 from hx, add_zero]⟩
  have hclosed : IsClosed (LinearMap.ker (G : E →ₗ[ℂ] E) : Set E) := G.isClosed_ker
  have hfin : FiniteDimensional ℂ (E ⧸ LinearMap.ker (G : E →ₗ[ℂ] E)) :=
    (LinearMap.quotKerEquivRange (G : E →ₗ[ℂ] E)).symm.finiteDimensional
  obtain ⟨h1, h2⟩ := isClosed_and_finiteDimensional_quotient_of_le hle hclosed hfin
  exact ⟨Submodule.finiteDimensional_of_le hker, h1, h2⟩

/-- **Riesz theory**: `1 + C` is Fredholm for compact `C`. -/
theorem isFredholmOp_one_add_compact {C : E →L[ℂ] E} (hC : IsCompactOperator C) :
    IsFredholmOp (1 + C) := by
  obtain ⟨G, hGfin, hGnorm⟩ := IsCompactOperator.exists_finiteRank_approx hC
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hsmall : ‖-(C - G)‖ < 1 := by rw [norm_neg]; linarith
  set u := Units.oneSub (-(C - G)) hsmall
  have hu : (u : E →L[ℂ] E) = 1 + (C - G) := by
    rw [Units.val_oneSub, sub_neg_eq_add]
  set G' : E →L[ℂ] E := (↑u⁻¹ : E →L[ℂ] E) ∘L G
  have hG'fin : FiniteDimensional ℂ (LinearMap.range (G' : E →ₗ[ℂ] E)) := by
    show FiniteDimensional ℂ
      (LinearMap.range (((↑u⁻¹ : E →L[ℂ] E) : E →ₗ[ℂ] E).comp (G : E →ₗ[ℂ] E)))
    rw [LinearMap.range_comp]
    exact Module.Finite.map _ _
  have hinv : ∀ y, (u : E →L[ℂ] E) ((↑u⁻¹ : E →L[ℂ] E) y) = y := by
    intro y
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, Units.mul_inv]
    rfl
  have hfac : (1 + C : E →L[ℂ] E) = (u : E →L[ℂ] E) ∘L (1 + G') := by
    refine ContinuousLinearMap.ext fun x => ?_
    show x + C x = (u : E →L[ℂ] E) (x + (↑u⁻¹ : E →L[ℂ] E) (G x))
    rw [map_add, hinv, hu]
    show x + C x = (x + (C x - G x)) + G x
    abel
  set e : E ≃L[ℂ] E := ContinuousLinearEquiv.unitsEquiv ℂ E u
  have he : (e : E →L[ℂ] E) = u := rfl
  rw [hfac, ← he]
  exact ((isFredholmOp_one_add_finiteRank hG'fin).equiv_comp e).1

/-- **Atkinson stability.**  A compact perturbation of a Fredholm operator is Fredholm. -/
theorem IsFredholmOp.add_compact {T R : E →L[ℂ] F} (hT : IsFredholmOp T)
    (hR : IsCompactOperator R) : IsFredholmOp (T + R) := by
  haveI := hT.finiteDimensional_ker
  haveI := hT.hasOrthogonalProjection_range
  haveI := hT.finiteDimensional_orthogonal_range
  set Rg := LinearMap.range (T : E →ₗ[ℂ] F)
  set N := LinearMap.ker (T : E →ₗ[ℂ] F)
  obtain ⟨G, hG⟩ := hT.exists_bordering
  set Gi : F × N →L[ℂ] E × Rgᗮ := (G.symm : F × N →L[ℂ] E × Rgᗮ)
  set F0 : F →L[ℂ] E := ContinuousLinearMap.fst ℂ E Rgᗮ ∘L Gi ∘L ContinuousLinearMap.inl ℂ F N
  set Fm : F →L[ℂ] Rgᗮ := ContinuousLinearMap.snd ℂ E Rgᗮ ∘L Gi ∘L ContinuousLinearMap.inl ℂ F N
  set Fp : N →L[ℂ] E := ContinuousLinearMap.fst ℂ E Rgᗮ ∘L Gi ∘L ContinuousLinearMap.inr ℂ F N
  have hsymm : ∀ k (n : N), G.symm (k, n) = (F0 k + Fp n,
      (ContinuousLinearMap.snd ℂ E Rgᗮ ∘L Gi ∘L ContinuousLinearMap.inl ℂ F N) k +
      (ContinuousLinearMap.snd ℂ E Rgᗮ ∘L Gi ∘L ContinuousLinearMap.inr ℂ F N) n) := by
    intro k n
    have h : (k, n) = ((k, 0) : F × N) + (0, n) := by simp
    rw [h, map_add]
    rfl
  -- left parametrix: `F0 T = 1 - Fp P_N`
  have hleft : F0 ∘L T = 1 - Fp ∘L N.orthogonalProjectionOnto := by
    refine ContinuousLinearMap.ext fun x => ?_
    have h : G.symm (T x + ((0 : Rgᗮ) : F), N.orthogonalProjectionOnto x) = (x, 0) := by
      rw [← hG, ContinuousLinearEquiv.symm_apply_apply]
    rw [Submodule.coe_zero, add_zero, hsymm] at h
    have h1 := congrArg Prod.fst h
    simp only at h1
    simp only [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self]
    exact eq_sub_of_add_eq h1
  -- right parametrix: `T F0 = 1 - ι Fm`
  have hright : T ∘L F0 = 1 - Rgᗮ.subtypeL ∘L Fm := by
    refine ContinuousLinearMap.ext fun k => ?_
    have h := G.apply_symm_apply (k, 0)
    rw [hsymm, hG, map_zero, add_zero] at h
    have h1 := congrArg Prod.fst h
    simp only [map_zero, add_zero] at h1
    simp only [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self,
      Submodule.subtypeL_apply]
    exact eq_sub_of_add_eq h1
  have hK1 : IsCompactOperator (-(Fp ∘L N.orthogonalProjectionOnto) + F0 ∘L R) :=
    ((isCompactOperator_of_finiteDimensional_codomain
      N.orthogonalProjectionOnto).clm_comp Fp).neg.add (hR.clm_comp F0)
  have hK2 : IsCompactOperator (-(Rgᗮ.subtypeL ∘L Fm) + R ∘L F0) :=
    ((isCompactOperator_of_finiteDimensional_codomain Fm).clm_comp Rgᗮ.subtypeL).neg.add
      (hR.comp_clm F0)
  have hL : F0 ∘L (T + R) = 1 + (-(Fp ∘L N.orthogonalProjectionOnto) + F0 ∘L R) := by
    rw [ContinuousLinearMap.comp_add, hleft]
    abel
  have hRt : (T + R) ∘L F0 = 1 + (-(Rgᗮ.subtypeL ∘L Fm) + R ∘L F0) := by
    rw [ContinuousLinearMap.add_comp, hright]
    abel
  have hF1 := isFredholmOp_one_add_compact hK1
  have hF2 := isFredholmOp_one_add_compact hK2
  have hker : LinearMap.ker ((T + R : E →L[ℂ] F) : E →ₗ[ℂ] F) ≤
      LinearMap.ker (((1 : E →L[ℂ] E) + (-(Fp ∘L N.orthogonalProjectionOnto) + F0 ∘L R) :
        E →L[ℂ] E) : E →ₗ[ℂ] E) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← hL]
    show F0 ((T + R) x) = 0
    rw [show ((T + R) x) = 0 from hx, map_zero]
  have hrange : LinearMap.range (((1 : F →L[ℂ] F) + (-(Rgᗮ.subtypeL ∘L Fm) + R ∘L F0) :
        F →L[ℂ] F) : F →ₗ[ℂ] F) ≤ LinearMap.range ((T + R : E →L[ℂ] F) : E →ₗ[ℂ] F) := by
    rintro _ ⟨k, rfl⟩
    refine ⟨F0 k, ?_⟩
    rw [← hRt]
    rfl
  haveI := hF1.finiteDimensional_ker
  obtain ⟨h1, h2⟩ := isClosed_and_finiteDimensional_quotient_of_le hrange hF2.isClosed_range
    hF2.finiteDimensional_coker
  exact ⟨Submodule.finiteDimensional_of_le hker, h1, h2⟩

/-- **Index invariance under compact perturbation.** -/
theorem fredholmIndex_add_compact {T R : E →L[ℂ] F} (hT : IsFredholmOp T)
    (hR : IsCompactOperator R) : fredholmIndex (T + R) = fredholmIndex T := by
  set f : ℝ → ℤ := fun t => fredholmIndex (T + (t : ℂ) • R)
  have hFred : ∀ t : ℝ, IsFredholmOp (T + (t : ℂ) • R) := fun t =>
    hT.add_compact (R := (t : ℂ) • R) (hR.smul (t : ℂ))
  have hloc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    obtain ⟨δ, hδ, hstab⟩ := (hFred t₀).exists_stable
    have hRpos : 0 < ‖R‖ + 1 := by positivity
    filter_upwards [Metric.ball_mem_nhds t₀ (div_pos hδ hRpos)] with t ht
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have hS : ‖((t : ℂ) - t₀) • R‖ < δ := by
      rw [norm_smul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      calc |t - t₀| * ‖R‖ ≤ |t - t₀| * (‖R‖ + 1) := by gcongr; linarith
        _ < δ / (‖R‖ + 1) * (‖R‖ + 1) := by gcongr
        _ = δ := by field_simp
    have h := (hstab _ hS).2
    have heq : T + (t₀ : ℂ) • R + ((t : ℂ) - t₀) • R = T + (t : ℂ) • R := by
      rw [sub_smul]
      abel
    simp only [f]
    rw [← heq, h]
  have h := hloc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ 1)
    (Set.mem_univ 0)
  simp only [f, Complex.ofReal_one, one_smul, Complex.ofReal_zero, zero_smul, add_zero] at h
  exact h

/-- Fredholmness is invariant under compact perturbation in both directions. -/
theorem isFredholmOp_add_compact_iff {T R : E →L[ℂ] F} (hR : IsCompactOperator R) :
    IsFredholmOp (T + R) ↔ IsFredholmOp T := by
  refine ⟨fun h => ?_, fun h => h.add_compact hR⟩
  have := h.add_compact (R := -R) hR.neg
  rwa [add_neg_cancel_right] at this

end CompactPerturbation

end GaloisForLFunctions.HTGeometry
