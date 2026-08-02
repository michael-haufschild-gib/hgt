import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Relative dimension of a pair of subspaces

For subspaces `A` and `B` of a vector space, `quotDim A B` is the dimension of `B` modulo `A`,
that is, of the image of `B` in `V ⧸ A`; equivalently the dimension of `B / (A ⊓ B)`.  The
associated relative index

`relIndex A B = quotDim A B - quotDim B A`

is the invariant that measures a pair of commensurable lattices against each other.

The lemma proved here is the one that makes the index estimate uniform in the second lattice:
intersecting a nested pair `A ≤ B` with an arbitrary subspace can only shrink the relative
dimension, because `(B ⊓ N) / (A ⊓ N)` embeds into `B / A`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The dimension of `B` modulo `A`: the dimension of the image of `B` in `V ⧸ A`. -/
noncomputable def quotDim (A B : Submodule K V) : ℕ := Module.finrank K (B.map A.mkQ)

/-- The relative index of a pair of subspaces. -/
noncomputable def relIndex (A B : Submodule K V) : ℤ := (quotDim A B : ℤ) - (quotDim B A : ℤ)

theorem relIndex_antisymm (A B : Submodule K V) : relIndex A B = - relIndex B A := by
  rw [relIndex, relIndex]
  omega

@[simp] theorem quotDim_of_le {A B : Submodule K V} (h : B ≤ A) : quotDim A B = 0 := by
  have hzero : B.map A.mkQ = ⊥ := by
    refine le_antisymm ?_ bot_le
    rintro _ ⟨x, hx, rfl⟩
    have hxA : x ∈ A := h hx
    have hmk : (A.mkQ) x = 0 := (Submodule.Quotient.mk_eq_zero A).mpr hxA
    simp [hmk]
  rw [quotDim, hzero]
  simp

/-- The comparison map `V ⧸ (A ⊓ N) → V ⧸ A`. -/
noncomputable def quotComparison (A N : Submodule K V) :
    (V ⧸ (A ⊓ N)) →ₗ[K] (V ⧸ A) :=
  Submodule.mapQ (A ⊓ N) A LinearMap.id (by
    intro x hx
    exact hx.1)

@[simp] theorem quotComparison_mk (A N : Submodule K V) (x : V) :
    quotComparison A N (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

/-- Intersecting a nested pair of subspaces with an arbitrary subspace can only shrink the
relative dimension. -/
theorem quotDim_inf_le (A B N : Submodule K V)
    [FiniteDimensional K (B.map A.mkQ)] :
    quotDim (A ⊓ N) (B ⊓ N) ≤ quotDim A B := by
  classical
  -- the comparison map sends the small relative space into the large one
  have hmaps : ∀ x ∈ (B ⊓ N).map (A ⊓ N).mkQ, quotComparison A N x ∈ B.map A.mkQ := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx.1, rfl⟩
  set f : ((B ⊓ N).map (A ⊓ N).mkQ) →ₗ[K] (B.map A.mkQ) :=
    (quotComparison A N).restrict hmaps with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨y, hy⟩ hzero
    obtain ⟨x, hx, rfl⟩ := hy
    have hmem : (Submodule.Quotient.mk x : V ⧸ A) = 0 := by
      have := congrArg Subtype.val hzero
      simpa [hf, LinearMap.restrict_apply] using this
    have hxA : x ∈ A := (Submodule.Quotient.mk_eq_zero A).mp hmem
    have hxAN : x ∈ A ⊓ N := ⟨hxA, hx.2⟩
    apply Subtype.ext
    have : (Submodule.Quotient.mk x : V ⧸ (A ⊓ N)) = 0 :=
      (Submodule.Quotient.mk_eq_zero (A ⊓ N)).mpr hxAN
    simpa using this
  exact f.finrank_le_finrank_of_injective hinj


/-- The comparison map `V ⧸ X → V ⧸ Y` for `X ≤ Y`. -/
noncomputable def quotDown {X Y : Submodule K V} (h : X ≤ Y) : (V ⧸ X) →ₗ[K] (V ⧸ Y) :=
  Submodule.mapQ X Y LinearMap.id (fun _ hx => h hx)

@[simp] theorem quotDown_mk {X Y : Submodule K V} (h : X ≤ Y) (x : V) :
    quotDown h (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

/-- Relative dimensions add along a chain of subspaces. -/
theorem quotDim_chain {X Y Z : Submodule K V} (hXY : X ≤ Y) (hYZ : Y ≤ Z)
    [FiniteDimensional K (Z.map X.mkQ)] :
    quotDim X Z = quotDim Y Z + quotDim X Y := by
  classical
  have hmaps : ∀ x ∈ Z.map X.mkQ, quotDown hXY x ∈ Z.map Y.mkQ := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  set f : (Z.map X.mkQ) →ₗ[K] (Z.map Y.mkQ) := (quotDown hXY).restrict hmaps with hf
  have hsurj : Function.Surjective f := by
    rintro ⟨_, ⟨z, hz, rfl⟩⟩
    exact ⟨⟨X.mkQ z, ⟨z, hz, rfl⟩⟩, rfl⟩
  have hrange : Module.finrank K (LinearMap.range f) = quotDim Y Z := by
    rw [LinearMap.range_eq_top.mpr hsurj, quotDim]
    exact finrank_top K _
  have hkermap : (LinearMap.ker f).map (Z.map X.mkQ).subtype = Y.map X.mkQ := by
    apply le_antisymm
    · rintro _ ⟨⟨w, hw⟩, hkerw, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hw
      have hzero : (Y.mkQ z) = 0 := congrArg Subtype.val hkerw
      exact ⟨z, (Submodule.Quotient.mk_eq_zero Y).mp hzero, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨⟨X.mkQ y, ⟨y, hYZ hy, rfl⟩⟩, ?_, rfl⟩
      apply Subtype.ext
      exact (Submodule.Quotient.mk_eq_zero Y).mpr hy
  have hkerfin : Module.finrank K (LinearMap.ker f) = quotDim X Y := by
    rw [quotDim, ← hkermap]
    exact (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).finrank_eq
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hkerfin] at hsum
  rw [quotDim]
  omega


/-- The comparison map identifies the image of `N` modulo `A ⊓ N` with its image modulo `A`. -/
noncomputable def quotDimInfEquiv (A N : Submodule K V) :
    (N.map (A ⊓ N).mkQ) ≃ₗ[K] (N.map A.mkQ) := by
  have hmaps : ∀ x ∈ N.map (A ⊓ N).mkQ, quotComparison A N x ∈ N.map A.mkQ := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  refine LinearEquiv.ofBijective ((quotComparison A N).restrict hmaps) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    rintro ⟨y, hy⟩ hzero
    obtain ⟨x, hx, rfl⟩ := hy
    have hmem : (Submodule.Quotient.mk x : V ⧸ A) = 0 := by
      simpa [LinearMap.restrict_apply] using congrArg Subtype.val hzero
    have hxA : x ∈ A := (Submodule.Quotient.mk_eq_zero A).mp hmem
    apply Subtype.ext
    have hz : (Submodule.Quotient.mk x : V ⧸ (A ⊓ N)) = 0 :=
      (Submodule.Quotient.mk_eq_zero (A ⊓ N)).mpr ⟨hxA, hx⟩
    simpa using hz
  · rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨(A ⊓ N).mkQ x, ⟨x, hx, rfl⟩⟩, rfl⟩

theorem quotDim_inf_left (A N : Submodule K V) : quotDim (A ⊓ N) N = quotDim A N :=
  (quotDimInfEquiv A N).finrank_eq

/-- Dimension splits along a subspace and its relative complement dimension. -/
theorem finrank_add_quotDim {P Q : Submodule K V} (h : P ≤ Q) [FiniteDimensional K Q] :
    Module.finrank K P + quotDim P Q = Module.finrank K Q := by
  have hmaps : ∀ x ∈ Q, P.mkQ x ∈ Q.map P.mkQ := fun x hx => ⟨x, hx, rfl⟩
  set f : Q →ₗ[K] (Q.map P.mkQ) := (P.mkQ).restrict hmaps with hf
  have hsurj : Function.Surjective f := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hrange : Module.finrank K (LinearMap.range f) = quotDim P Q := by
    rw [LinearMap.range_eq_top.mpr hsurj, quotDim]
    exact finrank_top K _
  have hkermap : (LinearMap.ker f).map Q.subtype = P := by
    apply le_antisymm
    · rintro _ ⟨⟨x, hx⟩, hker, rfl⟩
      have hzero : (P.mkQ x) = 0 := by
        simpa [hf, LinearMap.restrict_apply] using congrArg Subtype.val hker
      exact (Submodule.Quotient.mk_eq_zero P).mp hzero
    · intro x hx
      refine ⟨⟨x, h hx⟩, ?_, rfl⟩
      apply Subtype.ext
      simpa [hf, LinearMap.restrict_apply] using (Submodule.Quotient.mk_eq_zero P).mpr hx
  have hkerfin : Module.finrank K (LinearMap.ker f) = Module.finrank K P := by
    have e := Submodule.equivMapOfInjective Q.subtype (Submodule.injective_subtype Q)
      (LinearMap.ker f)
    rw [hkermap] at e
    exact e.finrank_eq
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  omega

/-- Passing to a quotient can only shrink a relative dimension. -/
theorem quotDim_map_mkQ_le (A B N : Submodule K V)
    [FiniteDimensional K (B.map A.mkQ)] :
    quotDim (A.map N.mkQ) (B.map N.mkQ) ≤ quotDim A B := by
  have hle : A ≤ Submodule.comap N.mkQ (A.map N.mkQ) := by
    intro a ha
    exact ⟨a, ha, rfl⟩
  set φ : (V ⧸ A) →ₗ[K] ((V ⧸ N) ⧸ (A.map N.mkQ)) :=
    Submodule.mapQ A (A.map N.mkQ) N.mkQ hle with hφ
  have hmaps : ∀ x ∈ B.map A.mkQ, φ x ∈ (B.map N.mkQ).map (A.map N.mkQ).mkQ := by
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨N.mkQ b, ⟨b, hb, rfl⟩, rfl⟩
  set g : (B.map A.mkQ) →ₗ[K] ((B.map N.mkQ).map (A.map N.mkQ).mkQ) := φ.restrict hmaps with hg
  have hsurj : Function.Surjective g := by
    rintro ⟨_, ⟨_, ⟨b, hb, rfl⟩, rfl⟩⟩
    exact ⟨⟨A.mkQ b, ⟨b, hb, rfl⟩⟩, rfl⟩
  have hsum := LinearMap.finrank_range_add_finrank_ker g
  have hrange : Module.finrank K (LinearMap.range g)
      = quotDim (A.map N.mkQ) (B.map N.mkQ) := by
    rw [LinearMap.range_eq_top.mpr hsurj, quotDim]
    exact finrank_top K _
  rw [hrange] at hsum
  have hgoal : quotDim A B = Module.finrank K (B.map A.mkQ) := rfl
  omega

/-- **The uniform index comparison.**  For a nested pair `A ≤ B` and an arbitrary subspace `N`,
the relative indices against `N` differ by at most twice the relative dimension of the pair. -/
theorem relIndex_sub_bounds {A B : Submodule K V} (hAB : A ≤ B) (N : Submodule K V)
    [FiniteDimensional K (B.map A.mkQ)] [FiniteDimensional K (N.map A.mkQ)]
    [FiniteDimensional K (B.map N.mkQ)] :
    0 ≤ relIndex A N - relIndex B N ∧
      relIndex A N - relIndex B N ≤ 2 * (quotDim A B : ℤ) := by
  classical
  haveI : FiniteDimensional K (N.map (A ⊓ N).mkQ) :=
    (quotDimInfEquiv A N).symm.finiteDimensional
  -- first bracket: the images of `N` differ by the intersected pair
  have hchain : quotDim (A ⊓ N) N = quotDim (B ⊓ N) N + quotDim (A ⊓ N) (B ⊓ N) :=
    quotDim_chain (inf_le_inf_right N hAB) inf_le_right
  have hb1 : quotDim A N = quotDim B N + quotDim (A ⊓ N) (B ⊓ N) := by
    rw [← quotDim_inf_left A N, ← quotDim_inf_left B N]
    exact hchain
  have hb1le : quotDim (A ⊓ N) (B ⊓ N) ≤ quotDim A B := quotDim_inf_le A B N
  -- second bracket: the images in the quotient by `N`
  have hmaple : A.map N.mkQ ≤ B.map N.mkQ := Submodule.map_mono hAB
  have hb2 : Module.finrank K (A.map N.mkQ) + quotDim (A.map N.mkQ) (B.map N.mkQ)
      = Module.finrank K (B.map N.mkQ) := finrank_add_quotDim hmaple
  have hb2le : quotDim (A.map N.mkQ) (B.map N.mkQ) ≤ quotDim A B :=
    quotDim_map_mkQ_le A B N
  have hNA : quotDim N A = Module.finrank K (A.map N.mkQ) := rfl
  have hNB : quotDim N B = Module.finrank K (B.map N.mkQ) := rfl
  rw [relIndex, relIndex, hNA, hNB]
  omega

end GaloisForLFunctions.HTGeometry
