import GaloisForLFunctions.HTGeometry.FriedrichsClosedSum
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Closed-range transgression

For composable bounded maps with closed local ranges, the composite has closed range exactly when
the sum of the first range and the second kernel is closed, equivalently when the law-history
transgression into the cokernel has closed range.  A finite history is proper at every prefix
exactly when every prefix transgression is strict, and terminal closedness alone does not imply
that.
-/

open Submodule

namespace GaloisForLFunctions.HTGeometry

section Quotient

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M]

omit [TopologicalSpace M] [IsTopologicalAddGroup M] in
theorem preimage_image_mkQ (P N : Submodule R M) :
    P.mkQ ⁻¹' (P.mkQ '' (N : Set M)) = ((N ⊔ P : Submodule R M) : Set M) := by
  ext x
  constructor
  · rintro ⟨n, hn, hx⟩
    have hsub : x - n ∈ P := by
      have : P.mkQ (x - n) = 0 := by
        rw [map_sub, hx]
        exact sub_self _
      simpa using (Submodule.Quotient.mk_eq_zero P).1 this
    have hxe : x = n + (x - n) := by abel
    rw [hxe]
    exact Submodule.mem_sup.2 ⟨n, hn, x - n, hsub, rfl⟩
  · intro hx
    obtain ⟨n, hn, p, hp, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨n, hn, ?_⟩
    have : P.mkQ p = 0 := (Submodule.Quotient.mk_eq_zero P).2 hp
    rw [map_add, this, add_zero]

/-- **Lemma 2.1** (CRP.5).  The quotient image of a subspace is closed exactly when the saturated
sum is closed. -/
theorem isClosed_image_mkQ_iff (P N : Submodule R M) :
    IsClosed (P.mkQ '' (N : Set M)) ↔ IsClosed ((N ⊔ P : Submodule R M) : Set M) := by
  have hpre := preimage_image_mkQ P N
  have hcont : Continuous (P.mkQ) := continuous_quot_mk
  constructor
  · intro h
    have := h.preimage hcont
    rwa [hpre] at this
  · intro h
    rw [← isOpen_compl_iff] at h ⊢
    have hmem : ∀ x : M, (P.mkQ x ∈ P.mkQ '' (N : Set M))
        ↔ x ∈ ((N ⊔ P : Submodule R M) : Set M) := by
      intro x
      rw [← hpre]
      rfl
    have himg : (P.mkQ '' (N : Set M))ᶜ = P.mkQ '' (((N ⊔ P : Submodule R M) : Set M)ᶜ) := by
      ext q
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective P q
      constructor
      · intro hq
        exact ⟨x, fun hx => hq ((hmem x).2 hx), rfl⟩
      · rintro ⟨y, hy, hxy⟩ hq
        refine hy ?_
        rw [← hmem y, hxy]
        exact hq
    rw [himg]
    exact (isOpenMap_mkQ P) _ h

end Quotient

/-! ## Products of closed-range maps -/

section Product

open scoped InnerProductSpace

variable {𝕜 Y Z : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]
variable [NormedAddCommGroup Z] [InnerProductSpace 𝕜 Z] [CompleteSpace Z]

variable (g : Y →L[𝕜] Z)

omit [CompleteSpace Y] [CompleteSpace Z] in
theorem isClosed_ker_coe : IsClosed ((LinearMap.ker (g : Y →ₗ[𝕜] Z) : Submodule 𝕜 Y) : Set Y) :=
  g.isClosed_ker

instance hasOrthogonalProjection_ker :
    (LinearMap.ker (g : Y →ₗ[𝕜] Z)).HasOrthogonalProjection := by
  haveI : CompleteSpace (LinearMap.ker (g : Y →ₗ[𝕜] Z)) :=
    (isClosed_ker_coe g).completeSpace_coe
  infer_instance

omit [CompleteSpace Z] in
/-- Restricting a bounded map to the orthogonal complement of its kernel loses nothing. -/
theorem apply_starProjection_ker (y : Y) :
    g ((LinearMap.ker (g : Y →ₗ[𝕜] Z))ᗮ.starProjection y) = g y := by
  have hsplit := (LinearMap.ker (g : Y →ₗ[𝕜] Z)).starProjection_add_starProjection_orthogonal y
  conv_rhs => rw [← hsplit]
  rw [map_add]
  have hzero : g ((LinearMap.ker (g : Y →ₗ[𝕜] Z)).starProjection y) = 0 :=
    ((LinearMap.ker (g : Y →ₗ[𝕜] Z)).orthogonalProjectionOnto y).2
  rw [hzero, zero_add]

omit [CompleteSpace Z] in
theorem starProjection_ker_orthogonal_mem (y : Y) :
    (LinearMap.ker (g : Y →ₗ[𝕜] Z))ᗮ.starProjection y ∈ (LinearMap.ker (g : Y →ₗ[𝕜] Z))ᗮ :=
  ((LinearMap.ker (g : Y →ₗ[𝕜] Z))ᗮ.orthogonalProjectionOnto y).2

omit [CompleteSpace Z] in
theorem map_eq_map_starProjection (A : Submodule 𝕜 Y) :
    A.map (g : Y →ₗ[𝕜] Z)
      = (A.map ((LinearMap.ker (g : Y →ₗ[𝕜] Z))ᗮ.starProjection : Y →ₗ[𝕜] Y)).map
        (g : Y →ₗ[𝕜] Z) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(LinearMap.ker (g : Y →ₗ[𝕜] Z))ᗮ.starProjection y, ⟨y, hy, rfl⟩,
      apply_starProjection_ker g y⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (apply_starProjection_ker g x).symm⟩

omit [CompleteSpace Z] in
/-- The projected subspace and the kernel span the same sum as the original. -/
theorem sup_ker_eq_sup_ker_starProjection (A : Submodule 𝕜 Y) :
    (A ⊔ LinearMap.ker (g : Y →ₗ[𝕜] Z) : Submodule 𝕜 Y)
      = (A.map ((LinearMap.ker (g : Y →ₗ[𝕜] Z))ᗮ.starProjection : Y →ₗ[𝕜] Y))
        ⊔ LinearMap.ker (g : Y →ₗ[𝕜] Z) := by
  refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
  · intro y hy
    have hsplit :=
      (LinearMap.ker (g : Y →ₗ[𝕜] Z)).starProjection_add_starProjection_orthogonal y
    have h1 : (LinearMap.ker (g : Y →ₗ[𝕜] Z))ᗮ.starProjection y
        ∈ A.map ((LinearMap.ker (g : Y →ₗ[𝕜] Z))ᗮ.starProjection : Y →ₗ[𝕜] Y) := ⟨y, hy, rfl⟩
    have h2 : (LinearMap.ker (g : Y →ₗ[𝕜] Z)).starProjection y
        ∈ LinearMap.ker (g : Y →ₗ[𝕜] Z) :=
      ((LinearMap.ker (g : Y →ₗ[𝕜] Z)).orthogonalProjectionOnto y).2
    have hy2 : y = (LinearMap.ker (g : Y →ₗ[𝕜] Z))ᗮ.starProjection y
        + (LinearMap.ker (g : Y →ₗ[𝕜] Z)).starProjection y :=
      ((add_comm ((LinearMap.ker (g : Y →ₗ[𝕜] Z))ᗮ.starProjection y)
        ((LinearMap.ker (g : Y →ₗ[𝕜] Z)).starProjection y)).trans hsplit).symm
    rw [hy2]
    exact Submodule.mem_sup.2 ⟨_, h1, _, h2, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hsplit :=
      (LinearMap.ker (g : Y →ₗ[𝕜] Z)).starProjection_add_starProjection_orthogonal y
    have h2 : (LinearMap.ker (g : Y →ₗ[𝕜] Z)).starProjection y
        ∈ LinearMap.ker (g : Y →ₗ[𝕜] Z) :=
      ((LinearMap.ker (g : Y →ₗ[𝕜] Z)).orthogonalProjectionOnto y).2
    have hval : (LinearMap.ker (g : Y →ₗ[𝕜] Z))ᗮ.starProjection y
        = y - (LinearMap.ker (g : Y →ₗ[𝕜] Z)).starProjection y := by
      rw [eq_sub_iff_add_eq, add_comm]
      exact hsplit
    show (LinearMap.ker (g : Y →ₗ[𝕜] Z))ᗮ.starProjection y
      ∈ (A ⊔ LinearMap.ker (g : Y →ₗ[𝕜] Z) : Submodule 𝕜 Y)
    rw [hval]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hy) (Submodule.mem_sup_right h2)

section ClosedRange

variable (hg : IsClosed ((LinearMap.range (g : Y →ₗ[𝕜] Z) : Submodule 𝕜 Z) : Set Z))

include hg in
/-- On the orthogonal complement of its kernel, a bounded map with closed range is a closed
embedding. -/
theorem isClosedEmbedding_on_ker_orthogonal :
    Topology.IsClosedEmbedding
      (fun s : (LinearMap.ker (g : Y →ₗ[𝕜] Z))ᗮ => g (s : Y)) := by
  haveI hRc : CompleteSpace (LinearMap.range (g : Y →ₗ[𝕜] Z)) := hg.completeSpace_coe
  haveI hSc : CompleteSpace ((LinearMap.ker (g : Y →ₗ[𝕜] Z))ᗮ : Submodule 𝕜 Y) :=
    (LinearMap.ker (g : Y →ₗ[𝕜] Z)).isClosed_orthogonal.completeSpace_coe
  set S : Submodule 𝕜 Y := (LinearMap.ker (g : Y →ₗ[𝕜] Z))ᗮ with hS
  set R : Submodule 𝕜 Z := LinearMap.range (g : Y →ₗ[𝕜] Z) with hR
  set gS : S →L[𝕜] R :=
    ContinuousLinearMap.codRestrict (g ∘L S.subtypeL) R (fun s => ⟨(s : Y), rfl⟩) with hgS
  have hker : LinearMap.ker (gS : S →ₗ[𝕜] R) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro s hs
    have h0 : g (s : Y) = 0 := by
      have := congrArg (Subtype.val) hs
      simpa [hgS] using this
    have hmem : (s : Y) ∈ LinearMap.ker (g : Y →ₗ[𝕜] Z) := h0
    have hperp : (s : Y) ∈ S := s.2
    have hinf : (s : Y) ∈ LinearMap.ker (g : Y →ₗ[𝕜] Z)
        ⊓ (LinearMap.ker (g : Y →ₗ[𝕜] Z))ᗮ := ⟨hmem, hperp⟩
    rw [Submodule.inf_orthogonal_eq_bot] at hinf
    exact Subtype.ext (by simpa using hinf)
  have hran : LinearMap.range (gS : S →ₗ[𝕜] R) = ⊤ := by
    rw [Submodule.eq_top_iff']
    rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := hz
    refine ⟨⟨S.starProjection y, starProjection_ker_orthogonal_mem g y⟩, ?_⟩
    refine Subtype.ext ?_
    show g (S.starProjection y) = g y
    exact apply_starProjection_ker g y
  let e : S ≃L[𝕜] R := ContinuousLinearEquiv.ofBijective gS hker hran
  have hcomp : (fun s : S => g (s : Y)) = (Subtype.val : R → Z) ∘ e := by
    funext s
    rfl
  rw [hcomp]
  exact (Topology.IsClosedEmbedding.subtypeVal hg).comp e.toHomeomorph.isClosedEmbedding

include hg in
/-- **Lemma 3.1 core.**  The image of a subspace under a closed-range map is closed exactly when
the subspace and the kernel have closed sum. -/
theorem isClosed_map_iff_isClosed_sup_ker (A : Submodule 𝕜 Y) :
    IsClosed ((A.map (g : Y →ₗ[𝕜] Z) : Submodule 𝕜 Z) : Set Z)
      ↔ IsClosed ((A ⊔ LinearMap.ker (g : Y →ₗ[𝕜] Z) : Submodule 𝕜 Y) : Set Y) := by
  haveI hSc : CompleteSpace ((LinearMap.ker (g : Y →ₗ[𝕜] Z))ᗮ : Submodule 𝕜 Y) :=
    (LinearMap.ker (g : Y →ₗ[𝕜] Z)).isClosed_orthogonal.completeSpace_coe
  set S : Submodule 𝕜 Y := (LinearMap.ker (g : Y →ₗ[𝕜] Z))ᗮ with hS
  set B : Submodule 𝕜 Y := A.map (S.starProjection : Y →ₗ[𝕜] Y) with hB
  have hBle : B ≤ S := by
    rintro _ ⟨y, _, rfl⟩
    exact (S.orthogonalProjectionOnto y).2
  have hmapB : A.map (g : Y →ₗ[𝕜] Z) = B.map (g : Y →ₗ[𝕜] Z) := map_eq_map_starProjection g A
  have hsupB : (A ⊔ LinearMap.ker (g : Y →ₗ[𝕜] Z) : Submodule 𝕜 Y)
      = B ⊔ LinearMap.ker (g : Y →ₗ[𝕜] Z) := sup_ker_eq_sup_ker_starProjection g A
  have hemb := isClosedEmbedding_on_ker_orthogonal g hg
  have hsubemb : Topology.IsClosedEmbedding ((↑) : S → Y) :=
    Topology.IsClosedEmbedding.subtypeVal (LinearMap.ker (g : Y →ₗ[𝕜] Z)).isClosed_orthogonal
  have hpre : ((↑) : S → Y) '' (((↑) : S → Y) ⁻¹' (B : Set Y)) = (B : Set Y) := by
    refine Set.image_preimage_eq_of_subset ?_
    intro y hy
    exact ⟨⟨y, hBle hy⟩, rfl⟩
  have himg : ((B.map (g : Y →ₗ[𝕜] Z) : Submodule 𝕜 Z) : Set Z)
      = (fun s : S => g (s : Y)) '' (((↑) : S → Y) ⁻¹' (B : Set Y)) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hBle hy⟩, hy, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨(s : Y), hs, rfl⟩
  rw [hmapB, hsupB, himg]
  constructor
  · intro h
    have hB' : IsClosed (((↑) : S → Y) ⁻¹' (B : Set Y)) := hemb.isClosed_iff_image_isClosed.2 h
    have := hsubemb.isClosed_iff_image_isClosed.1 hB'
    rw [hpre] at this
    rw [sup_comm]
    exact (isClosed_sup_orthogonal_iff (isClosed_ker_coe g) hBle).2 this
  · intro h
    rw [sup_comm] at h
    have hBc : IsClosed ((B : Submodule 𝕜 Y) : Set Y) :=
      (isClosed_sup_orthogonal_iff (isClosed_ker_coe g) hBle).1 h
    have hpreB : IsClosed (((↑) : S → Y) ⁻¹' (B : Set Y)) := hBc.preimage continuous_subtype_val
    exact hemb.isClosed_iff_image_isClosed.1 hpreB

end ClosedRange

/-! ## The closed-range transgression theorem -/

section Transgression

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- **Theorem 4.1** (CRP.8).  With closed local ranges, composite closedness, sum closedness and
transgression closedness are the same condition. -/
theorem closedRange_transgression_tfae (f : X →L[𝕜] Y) (g : Y →L[𝕜] Z)
    (hg : IsClosed ((LinearMap.range (g : Y →ₗ[𝕜] Z) : Submodule 𝕜 Z) : Set Z)) :
    List.TFAE
      [ IsClosed ((LinearMap.range ((g.comp f) : X →ₗ[𝕜] Z) : Submodule 𝕜 Z) : Set Z),
        IsClosed ((LinearMap.range (f : X →ₗ[𝕜] Y) ⊔ LinearMap.ker (g : Y →ₗ[𝕜] Z)
          : Submodule 𝕜 Y) : Set Y),
        IsClosed ((LinearMap.range (f : X →ₗ[𝕜] Y)).mkQ ''
          ((LinearMap.ker (g : Y →ₗ[𝕜] Z) : Submodule 𝕜 Y) : Set Y)) ] := by
  have hcomp : (LinearMap.range ((g.comp f) : X →ₗ[𝕜] Z) : Submodule 𝕜 Z)
      = (LinearMap.range (f : X →ₗ[𝕜] Y)).map (g : Y →ₗ[𝕜] Z) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨f x, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
  tfae_have 1 ↔ 2 := by
    rw [hcomp]
    exact isClosed_map_iff_isClosed_sup_ker g hg _
  tfae_have 2 ↔ 3 := by
    rw [isClosed_image_mkQ_iff, sup_comm]
  tfae_finish

omit [CompleteSpace X] in
/-- **Corollary (CRP.10).**  Composite closedness is the strict Friedrichs angle between the first
range and the second kernel. -/
theorem friedrichsCosine_lt_one_iff_isClosed_range_comp (f : X →L[𝕜] Y) (g : Y →L[𝕜] Z)
    (hf : IsClosed ((LinearMap.range (f : X →ₗ[𝕜] Y) : Submodule 𝕜 Y) : Set Y))
    (hg : IsClosed ((LinearMap.range (g : Y →ₗ[𝕜] Z) : Submodule 𝕜 Z) : Set Z)) :
    friedrichsCosine (LinearMap.range (f : X →ₗ[𝕜] Y)) (LinearMap.ker (g : Y →ₗ[𝕜] Z)) < 1
      ↔ IsClosed ((LinearMap.range ((g.comp f) : X →ₗ[𝕜] Z) : Submodule 𝕜 Z) : Set Z) := by
  rw [friedrichsCosine_lt_one_iff_isClosed_sup hf (isClosed_ker_coe g)]
  exact ((closedRange_transgression_tfae f g hg).out 1 0)

end Transgression

end Product

/-! ## Finite histories and global formation properness -/

section History

variable {𝕜 : Type*} [RCLike 𝕜]
variable (V : ℕ → Type*) [∀ n, NormedAddCommGroup (V n)] [∀ n, InnerProductSpace 𝕜 (V n)]
  [∀ n, CompleteSpace (V n)]
variable (a : ∀ n : ℕ, V n →L[𝕜] V (n + 1))

/-- The prefix composites of a history (CRP.12). -/
def prefixMap : ∀ n : ℕ, V 0 →L[𝕜] V n
  | 0 => ContinuousLinearMap.id 𝕜 (V 0)
  | (n + 1) => (a n).comp (prefixMap n)

omit [∀ (n : ℕ), CompleteSpace (V n)] in
@[simp] theorem prefixMap_zero : prefixMap V a 0 = ContinuousLinearMap.id 𝕜 (V 0) := rfl

omit [∀ (n : ℕ), CompleteSpace (V n)] in
@[simp] theorem prefixMap_succ (n : ℕ) :
    prefixMap V a (n + 1) = (a n).comp (prefixMap V a n) := rfl

/-- The prefix transgression (CRP.13): the class of a later kernel in the earlier cokernel. -/
def prefixTransgressionRange (n : ℕ) : Set (V n ⧸ LinearMap.range (prefixMap V a n : V 0 →ₗ[𝕜] V n)) :=
  (LinearMap.range (prefixMap V a n : V 0 →ₗ[𝕜] V n)).mkQ ''
    ((LinearMap.ker (a n : V n →ₗ[𝕜] V (n + 1)) : Submodule 𝕜 (V n)) : Set (V n))

/-- One step of the properness induction. -/
theorem isClosed_range_prefixMap_succ_iff (n : ℕ)
    (ha : IsClosed ((LinearMap.range (a n : V n →ₗ[𝕜] V (n + 1))
      : Submodule 𝕜 (V (n + 1))) : Set (V (n + 1)))) :
    IsClosed ((LinearMap.range (prefixMap V a (n + 1) : V 0 →ₗ[𝕜] V (n + 1))
        : Submodule 𝕜 (V (n + 1))) : Set (V (n + 1)))
      ↔ IsClosed (prefixTransgressionRange V a n) := by
  have h := closedRange_transgression_tfae (prefixMap V a n) (a n) ha
  exact h.out 0 2

/-- **Theorem 6.2.**  A finite history is globally formation-proper exactly when every prefix
transgression has closed range. -/
theorem globally_proper_iff_transgressions_closed
    (ha : ∀ n : ℕ, IsClosed ((LinearMap.range (a n : V n →ₗ[𝕜] V (n + 1))
      : Submodule 𝕜 (V (n + 1))) : Set (V (n + 1)))) :
    (∀ j : ℕ, IsClosed ((LinearMap.range (prefixMap V a j : V 0 →ₗ[𝕜] V j)
        : Submodule 𝕜 (V j)) : Set (V j)))
      ↔ ∀ j : ℕ, IsClosed (prefixTransgressionRange V a j) := by
  constructor
  · intro h j
    exact (isClosed_range_prefixMap_succ_iff V a j (ha j)).1 (h (j + 1))
  · intro h j
    induction j with
    | zero =>
        have htop : (LinearMap.range (prefixMap V a 0 : V 0 →ₗ[𝕜] V 0) : Submodule 𝕜 (V 0)) = ⊤ := by
          rw [Submodule.eq_top_iff']
          intro x
          exact ⟨x, rfl⟩
        rw [htop]
        simp
    | succ n _ =>
        exact (isClosed_range_prefixMap_succ_iff V a n (ha n)).2 (h n)

end History

end GaloisForLFunctions.HTGeometry
