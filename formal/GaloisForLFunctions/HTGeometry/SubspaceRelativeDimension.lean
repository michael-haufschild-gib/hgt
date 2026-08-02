import Mathlib.Data.Int.ConditionallyCompleteOrder
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

/-- The embedding `(B ⊓ N) / (A ⊓ N) ↪ B / A`. -/
noncomputable def quotDimInfHom (A B N : Submodule K V) :
    ((B ⊓ N).map (A ⊓ N).mkQ) →ₗ[K] (B.map A.mkQ) :=
  (quotComparison A N).restrict (by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx.1, rfl⟩)

theorem quotDimInfHom_injective (A B N : Submodule K V) :
    Function.Injective (quotDimInfHom A B N) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨y, hy⟩ hzero
  obtain ⟨x, hx, rfl⟩ := hy
  have hmem : (Submodule.Quotient.mk x : V ⧸ A) = 0 := by
    simpa [quotDimInfHom, LinearMap.restrict_apply] using congrArg Subtype.val hzero
  have hxA : x ∈ A := (Submodule.Quotient.mk_eq_zero A).mp hmem
  apply Subtype.ext
  have hz : (Submodule.Quotient.mk x : V ⧸ (A ⊓ N)) = 0 :=
    (Submodule.Quotient.mk_eq_zero (A ⊓ N)).mpr ⟨hxA, hx.2⟩
  simpa using hz

/-- Intersecting a nested pair of subspaces with an arbitrary subspace can only shrink the
relative dimension. -/
theorem quotDim_inf_le (A B N : Submodule K V) [FiniteDimensional K (B.map A.mkQ)] :
    quotDim (A ⊓ N) (B ⊓ N) ≤ quotDim A B :=
  (quotDimInfHom A B N).finrank_le_finrank_of_injective (quotDimInfHom_injective A B N)

instance finiteDimensional_inf_map (A B N : Submodule K V)
    [FiniteDimensional K (B.map A.mkQ)] :
    FiniteDimensional K ((B ⊓ N).map (A ⊓ N).mkQ) :=
  FiniteDimensional.of_injective (quotDimInfHom A B N) (quotDimInfHom_injective A B N)

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


/-- **Uniform comparison of lattice indices after an arbitrary cut.**  For a nested pair of
lattices `L₁ ≤ L₂`, the index against any lattice `M`, computed inside any subspace `W`, changes by
at most twice the relative dimension of the pair — a constant that depends on neither `M` nor
`W`. -/
theorem relIndex_inf_sub_bounds {L₁ L₂ : Submodule K V} (h : L₁ ≤ L₂) (M W : Submodule K V)
    [FiniteDimensional K (L₂.map L₁.mkQ)]
    [FiniteDimensional K ((M ⊓ W).map (L₁ ⊓ W).mkQ)]
    [FiniteDimensional K ((L₂ ⊓ W).map (M ⊓ W).mkQ)] :
    0 ≤ relIndex (L₁ ⊓ W) (M ⊓ W) - relIndex (L₂ ⊓ W) (M ⊓ W) ∧
      relIndex (L₁ ⊓ W) (M ⊓ W) - relIndex (L₂ ⊓ W) (M ⊓ W)
        ≤ 2 * (quotDim L₁ L₂ : ℤ) := by
  have hAB : L₁ ⊓ W ≤ L₂ ⊓ W := inf_le_inf_right W h
  obtain ⟨h0, h2⟩ := relIndex_sub_bounds hAB (M ⊓ W)
  refine ⟨h0, le_trans h2 ?_⟩
  have hcut := quotDim_inf_le L₁ L₂ W
  omega


/-- Two families of integers whose members differ by at most `c` have suprema differing by at most
`c`. -/
theorem sSup_range_sub_bounds {ι : Type*} [Nonempty ι] (f g : ι → ℤ) (c : ℤ)
    (hbf : BddAbove (Set.range f)) (hbg : BddAbove (Set.range g))
    (hle : ∀ i, g i ≤ f i) (hc : ∀ i, f i ≤ g i + c) :
    sSup (Set.range g) ≤ sSup (Set.range f) ∧
      sSup (Set.range f) ≤ sSup (Set.range g) + c := by
  constructor
  · refine csSup_le (Set.range_nonempty g) ?_
    rintro _ ⟨i, rfl⟩
    exact le_trans (hle i) (le_csSup hbf ⟨i, rfl⟩)
  · refine csSup_le (Set.range_nonempty f) ?_
    rintro _ ⟨i, rfl⟩
    have hg : g i ≤ sSup (Set.range g) := le_csSup hbg ⟨i, rfl⟩
    have hf := hc i
    omega

/-- The prefix invariant of a pair of lattices attached to a family of cuts: the largest relative
index attained on a cut of the family. -/
noncomputable def relIndexSup {ι : Type*} (cut : ι → Submodule K V) (L M : Submodule K V) : ℤ :=
  sSup (Set.range fun i => relIndex (L ⊓ cut i) (M ⊓ cut i))

/-- **Uniform comparison of prefix invariants.**  Replacing a lattice by a commensurable larger one
changes every prefix invariant by at most twice the relative dimension of the pair, whatever the
family of cuts and whatever the moving lattice. -/
theorem relIndexSup_sub_bounds {ι : Type*} [Nonempty ι] (cut : ι → Submodule K V)
    {L₁ L₂ : Submodule K V} (h : L₁ ≤ L₂) (M : Submodule K V)
    [FiniteDimensional K (L₂.map L₁.mkQ)]
    (hfin₁ : ∀ i, FiniteDimensional K ((M ⊓ cut i).map (L₁ ⊓ cut i).mkQ))
    (hfin₂ : ∀ i, FiniteDimensional K ((L₂ ⊓ cut i).map (M ⊓ cut i).mkQ))
    (hbdd₁ : BddAbove (Set.range fun i => relIndex (L₁ ⊓ cut i) (M ⊓ cut i)))
    (hbdd₂ : BddAbove (Set.range fun i => relIndex (L₂ ⊓ cut i) (M ⊓ cut i))) :
    0 ≤ relIndexSup cut L₁ M - relIndexSup cut L₂ M ∧
      relIndexSup cut L₁ M - relIndexSup cut L₂ M ≤ 2 * (quotDim L₁ L₂ : ℤ) := by
  have hpoint : ∀ i,
      relIndex (L₂ ⊓ cut i) (M ⊓ cut i) ≤ relIndex (L₁ ⊓ cut i) (M ⊓ cut i) ∧
        relIndex (L₁ ⊓ cut i) (M ⊓ cut i)
          ≤ relIndex (L₂ ⊓ cut i) (M ⊓ cut i) + 2 * (quotDim L₁ L₂ : ℤ) := by
    intro i
    haveI := hfin₁ i
    haveI := hfin₂ i
    obtain ⟨h0, h2⟩ := relIndex_inf_sub_bounds h M (cut i)
    constructor
    · omega
    · omega
  obtain ⟨hA, hB⟩ := sSup_range_sub_bounds
    (fun i => relIndex (L₁ ⊓ cut i) (M ⊓ cut i))
    (fun i => relIndex (L₂ ⊓ cut i) (M ⊓ cut i)) (2 * (quotDim L₁ L₂ : ℤ))
    hbdd₁ hbdd₂ (fun i => (hpoint i).1) (fun i => (hpoint i).2)
  rw [relIndexSup, relIndexSup]
  constructor
  · omega
  · omega


section Transport

variable {V' : Type*} [AddCommGroup V'] [Module K V']

/-- Relative dimension is invariant under an injective linear map. -/
theorem quotDim_map_injective (f : V →ₗ[K] V') (hf : Function.Injective f) (L M : Submodule K V) :
    quotDim (L.map f) (M.map f) = quotDim L M := by
  have hle : L ≤ Submodule.comap f (L.map f) := fun x hx => ⟨x, hx, rfl⟩
  set q : (V ⧸ L) →ₗ[K] (V' ⧸ L.map f) := Submodule.mapQ L (L.map f) f hle with hq
  have hqinj : Function.Injective q := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      have hmem : f x ∈ L.map f := by
        have : (Submodule.Quotient.mk (f x) : V' ⧸ L.map f) = 0 := hz
        exact (Submodule.Quotient.mk_eq_zero _).mp this
      obtain ⟨y, hy, hxy⟩ := hmem
      have hxL : x ∈ L := by
        rwa [hf hxy] at hy
      exact (Submodule.Quotient.mk_eq_zero L).mpr hxL
  have hcomp : (L.map f).mkQ.comp f = q.comp L.mkQ := by
    ext x
    rfl
  have himg : (M.map f).map (L.map f).mkQ = (M.map L.mkQ).map q := by
    rw [← Submodule.map_comp, ← Submodule.map_comp, hcomp]
  rw [quotDim, quotDim, himg]
  exact ((Submodule.equivMapOfInjective _ hqinj _).finrank_eq).symm

/-- The relative index is invariant under an injective linear map. -/
theorem relIndex_map_injective (f : V →ₗ[K] V') (hf : Function.Injective f) (L M : Submodule K V) :
    relIndex (L.map f) (M.map f) = relIndex L M := by
  rw [relIndex, relIndex, quotDim_map_injective f hf L M, quotDim_map_injective f hf M L]

/-- Prefix invariants are invariant under an injective linear map transporting the cuts. -/
theorem relIndexSup_map_injective {ι : Type*} (f : V →ₗ[K] V') (hf : Function.Injective f)
    (cut : ι → Submodule K V) (L M : Submodule K V) :
    relIndexSup (fun i => (cut i).map f) (L.map f) (M.map f) = relIndexSup cut L M := by
  have hinf : ∀ (P : Submodule K V) (i : ι),
      (P ⊓ cut i).map f = P.map f ⊓ (cut i).map f := fun P i => Submodule.map_inf _ hf
  rw [relIndexSup, relIndexSup]
  congr 1
  refine congrArg Set.range (funext fun i => ?_)
  rw [← hinf L i, ← hinf M i, relIndex_map_injective f hf]

/-- Relative dimension is invariant under a linear equivalence. -/
theorem quotDim_map_equiv (e : V ≃ₗ[K] V') (L M : Submodule K V) :
    quotDim (L.map (e : V →ₗ[K] V')) (M.map (e : V →ₗ[K] V')) = quotDim L M :=
  quotDim_map_injective _ e.injective L M

/-- The relative index is invariant under a linear equivalence. -/
theorem relIndex_map_equiv (e : V ≃ₗ[K] V') (L M : Submodule K V) :
    relIndex (L.map (e : V →ₗ[K] V')) (M.map (e : V →ₗ[K] V')) = relIndex L M :=
  relIndex_map_injective _ e.injective L M

/-- Prefix invariants are invariant under a linear equivalence transporting the cuts. -/
theorem relIndexSup_map_equiv {ι : Type*} (e : V ≃ₗ[K] V') (cut : ι → Submodule K V)
    (L M : Submodule K V) :
    relIndexSup (fun i => (cut i).map (e : V →ₗ[K] V')) (L.map (e : V →ₗ[K] V'))
        (M.map (e : V →ₗ[K] V'))
      = relIndexSup cut L M :=
  relIndexSup_map_injective _ e.injective cut L M

end Transport

end GaloisForLFunctions.HTGeometry
