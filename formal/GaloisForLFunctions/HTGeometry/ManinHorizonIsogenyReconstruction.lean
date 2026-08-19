import GaloisForLFunctions.HTGeometry.DGroupHorizonStabilizer

/-!
# The embedded Manin horizon and isogeny reconstruction

The translation stabilizer of an embedded multiplication tail is the sharp subgroup of the
ambient commutative `D`-group — the Manin kernel in the abelian case.  This file gives the
nonorthogonality relation between two such horizon symmetries a concrete group-theoretic form,
proves the direction of Manin-kernel rigidity which is elementary, and assembles the
reconstruction criterion.

`Nonorthogonal S S'` asks for a subgroup of the product projecting onto both factors with finite
kernels: an isogeny correspondence between `S` and `S'`.  A homomorphism of `D`-groups carries
sharp points to sharp points, so an isogeny of `D`-groups produces such a correspondence; that is
the elementary half.  The converse for Manin kernels of simple abelian varieties not descending to
the constants is Hrushovski's dichotomy and is carried as a named hypothesis, exactly as the paper
proof carries it.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-! ### Nonorthogonality as an isogeny correspondence -/

/-- Two sets of group elements are **nonorthogonal** when some subgroup of the product lies over
both, projects onto both, and has finite kernel in each direction: an isogeny correspondence. -/
def Nonorthogonal {G H : Type*} [Group G] [Group H] (S : Set G) (S' : Set H) : Prop :=
  ∃ Γ : Subgroup (G × H),
    (∀ p : G × H, p ∈ Γ → p.1 ∈ S ∧ p.2 ∈ S') ∧
    (∀ g ∈ S, ∃ h : H, (g, h) ∈ Γ) ∧
    (∀ h ∈ S', ∃ g : G, (g, h) ∈ Γ) ∧
    Finite {h : H // ((1 : G), h) ∈ Γ} ∧
    Finite {g : G // (g, (1 : H)) ∈ Γ}

/-- Nonorthogonality is symmetric: transpose the correspondence. -/
theorem Nonorthogonal.symm {G H : Type*} [Group G] [Group H] {S : Set G} {S' : Set H}
    (h : Nonorthogonal S S') : Nonorthogonal S' S := by
  obtain ⟨Γ, hmem, hfst, hsnd, hker₁, hker₂⟩ := h
  let e : G × H ≃* H × G := MulEquiv.prodComm
  have hiff : ∀ p : H × G, p ∈ Γ.map e.toMonoidHom ↔ (p.2, p.1) ∈ Γ := by
    rintro ⟨y, x⟩
    constructor
    · rintro ⟨⟨u, v⟩, huv, hmapped⟩
      have h1 : v = y := congrArg Prod.fst hmapped
      have h2 : u = x := congrArg Prod.snd hmapped
      subst h1
      subst h2
      exact huv
    · intro hp
      exact ⟨(x, y), hp, rfl⟩
  refine ⟨Γ.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨y, x⟩ hp
    have hp' : (x, y) ∈ Γ := (hiff (y, x)).mp hp
    exact ⟨(hmem (x, y) hp').2, (hmem (x, y) hp').1⟩
  · intro y hy
    obtain ⟨x, hx⟩ := hsnd y hy
    exact ⟨x, (hiff (y, x)).mpr hx⟩
  · intro x hx
    obtain ⟨y, hy⟩ := hfst x hx
    exact ⟨y, (hiff (y, x)).mpr hy⟩
  · haveI := hker₂
    exact Finite.of_injective
      (fun p : {g : G // ((1 : H), g) ∈ Γ.map e.toMonoidHom} =>
        (⟨p.1, (hiff ((1 : H), p.1)).mp p.2⟩ : {g : G // (g, (1 : H)) ∈ Γ}))
      (fun x y hxy =>
        Subtype.ext (congrArg (fun z : {g : G // (g, (1 : H)) ∈ Γ} => (z : G)) hxy))
  · haveI := hker₁
    exact Finite.of_injective
      (fun p : {h : H // (h, (1 : G)) ∈ Γ.map e.toMonoidHom} =>
        (⟨p.1, (hiff (p.1, (1 : G))).mp p.2⟩ : {h : H // ((1 : G), h) ∈ Γ}))
      (fun x y hxy =>
        Subtype.ext (congrArg (fun z : {h : H // ((1 : G), h) ∈ Γ} => (z : H)) hxy))

/-- **An isogeny produces a correspondence.**  A group homomorphism carrying `S` into `S'`,
surjective from `S` onto `S'` and with finite kernel on `S`, makes `S` and `S'` nonorthogonal. -/
theorem nonorthogonal_of_monoidHom {G H : Type*} [Group G] [Group H]
    (S : Subgroup G) (S' : Set H) (φ : G →* H)
    (hmaps : ∀ g ∈ S, φ g ∈ S')
    (hsurj : ∀ h ∈ S', ∃ g ∈ S, φ g = h)
    (hfin : Finite {g : G // g ∈ S ∧ φ g = 1}) :
    Nonorthogonal (S : Set G) S' := by
  classical
  refine ⟨S.map ((MonoidHom.id G).prod φ), ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨x, y⟩ ⟨g, hg, hgp⟩
    have h1 : g = x := congrArg Prod.fst hgp
    have h2 : φ g = y := congrArg Prod.snd hgp
    subst h1
    subst h2
    exact ⟨hg, hmaps _ hg⟩
  · intro g hg
    exact ⟨φ g, ⟨g, hg, rfl⟩⟩
  · intro h hh
    obtain ⟨g, hg, hgh⟩ := hsurj h hh
    exact ⟨g, ⟨g, hg, by simp [MonoidHom.prod_apply, hgh]⟩⟩
  · have hsub : ∀ h : H, ((1 : G), h) ∈ S.map ((MonoidHom.id G).prod φ) → h = 1 := by
      rintro h ⟨g, hg, hgp⟩
      have h1 : g = 1 := congrArg Prod.fst hgp
      have h2 : φ g = h := congrArg Prod.snd hgp
      rw [← h2, h1, map_one]
    exact Finite.of_injective (fun p => (⟨⟩ : Unit)) (by
      intro x y _
      exact Subtype.ext ((hsub _ x.2).trans (hsub _ y.2).symm))
  · refine Finite.of_injective
      (fun p : {g : G // (g, (1 : H)) ∈ S.map ((MonoidHom.id G).prod φ)} =>
        (⟨p.1, ?_⟩ : {g : G // g ∈ S ∧ φ g = 1})) ?_
    · obtain ⟨g, hg, hgp⟩ := p.2
      have h1 : g = (p.1 : G) := congrArg Prod.fst hgp
      have h2 : φ g = 1 := congrArg Prod.snd hgp
      rw [← h1]
      exact ⟨hg, h2⟩
    · intro x y hxy
      exact Subtype.ext (congrArg (fun z : {g : G // g ∈ S ∧ φ g = 1} => (z : G)) hxy)

/-- Nonorthogonality is reflexive on a subgroup: the diagonal is a correspondence. -/
theorem nonorthogonal_self {G : Type*} [Group G] (S : Subgroup G) :
    Nonorthogonal (S : Set G) (S : Set G) :=
  nonorthogonal_of_monoidHom S (S : Set G) (MonoidHom.id G) (fun _ hg => hg)
    (fun h hh => ⟨h, hh, rfl⟩)
    (Finite.of_injective (fun _ : {g : G // g ∈ S ∧ (MonoidHom.id G) g = 1} => (() : Unit))
      (fun x y _ => Subtype.ext (x.2.2.trans y.2.2.symm)))


/-! ### `D`-group morphisms and the elementary half of rigidity -/

universe u

/-- A homomorphism of commutative `D`-groups: a group homomorphism whose logarithmic coordinates
transform linearly.  For abelian varieties this is an isogeny together with the induced map of
universal vectorial extensions. -/
structure DGroupHom {G H : Type*} [CommGroup G] [CommGroup H] {K L : Type u}
    [Field K] [Field L] [Algebra K L] [Differential K] [Differential L]
    [DifferentialAlgebra K L] {n d n' d' : ℕ}
    (P : DGroupPresentation G K L n d) (Q : DGroupPresentation H K L n' d') where
  /-- The underlying group homomorphism. -/
  toMonoidHom : G →* H
  /-- The matrix through which logarithmic coordinates transform. -/
  linear : Matrix (Fin d') (Fin d) L
  /-- Compatibility of the two logarithmic derivatives. -/
  ell_comp : ∀ g : G, Q.ell (toMonoidHom g) = linear.mulVec (P.ell g)

/-- A `D`-group homomorphism carries sharp points to sharp points. -/
theorem DGroupHom.map_dGroupSharp {G H : Type*} [CommGroup G] [CommGroup H] {K L : Type u}
    [Field K] [Field L] [Algebra K L] [Differential K] [Differential L]
    [DifferentialAlgebra K L] {n d n' d' : ℕ}
    {P : DGroupPresentation G K L n d} {Q : DGroupPresentation H K L n' d'}
    (φ : DGroupHom P Q) {g : G} (hg : g ∈ dGroupSharp P) :
    φ.toMonoidHom g ∈ dGroupSharp Q := by
  show Q.ell (φ.toMonoidHom g) = 0
  rw [φ.ell_comp, show P.ell g = 0 from hg, Matrix.mulVec_zero]

/-- **The elementary half of Manin-kernel rigidity.**  An isogeny of commutative `D`-groups —
a `D`-group homomorphism which is onto the sharp points of the target and has finite kernel among
the sharp points of the source — makes the two sharp subgroups nonorthogonal. -/
theorem nonorthogonal_dGroupSharp_of_dGroupHom {G H : Type*} [CommGroup G] [CommGroup H]
    {K L : Type u} [Field K] [Field L] [Algebra K L] [Differential K] [Differential L]
    [DifferentialAlgebra K L] {n d n' d' : ℕ}
    {P : DGroupPresentation G K L n d} {Q : DGroupPresentation H K L n' d'}
    (φ : DGroupHom P Q)
    (hsurj : ∀ h ∈ dGroupSharp Q, ∃ g ∈ dGroupSharpSubgroup P, φ.toMonoidHom g = h)
    (hfin : Finite {g : G // g ∈ dGroupSharpSubgroup P ∧ φ.toMonoidHom g = 1}) :
    Nonorthogonal (dGroupSharp P) (dGroupSharp Q) :=
  nonorthogonal_of_monoidHom (dGroupSharpSubgroup P) (dGroupSharp Q) φ.toMonoidHom
    (fun _ hg => φ.map_dGroupSharp hg) hsurj hfin

/-! ### Theorem A and Theorem B -/

/-- **Theorem A, in the form the card states it.**  The translation stabilizer of the embedded
multiplication tail — the differential field generated by the logarithmic (Manin) coordinates of a
point — is exactly the sharp subgroup, the Manin kernel. -/
theorem multiplicationTail_translationStabilizer_eq_dGroupSharp
    {G : Type*} [CommGroup G] {K L : Type u}
    [Field K] [Field L] [Algebra K L] [Differential K] [Differential L]
    [DifferentialAlgebra K L] {n d : ℕ}
    (P : DGroupPresentation G K L n d) (a : G)
    (translation : G → DifferentialAlgEquiv K L)
    (hequiv : ∀ (h : G) (j : Fin d),
      (translation h).toAlgEquiv (P.ell a j) = P.ell (a * h) j)
    (tail : IntermediateField K L)
    (htail : tail = differentialAdjoin K (Set.range (P.ell a))) :
    differentialTranslationStabilizer translation tail = dGroupSharp P := by
  rw [htail]
  exact differentialTranslationStabilizer_ell_eq_dGroupSharp P a translation hequiv

/-- **Theorem B: the horizon Torelli criterion.**  Once each embedded horizon symmetry is
identified with its Manin kernel, kernel rigidity transfers verbatim: the two embedded horizon
symmetries are nonorthogonal exactly when the bulks are isogenous.

The rigidity input `hrigidity` is the classical Manin-kernel dichotomy for simple abelian
varieties not descending to the constants; every other step is proved here. -/
theorem embeddedManinHorizon_nonorthogonal_iff_isogenous
    {G H : Type*} [CommGroup G] [CommGroup H] {K L₁ L₂ : Type u}
    [Field K] [Field L₁] [Field L₂] [Algebra K L₁] [Algebra K L₂]
    [Differential K] [Differential L₁] [Differential L₂]
    [DifferentialAlgebra K L₁] [DifferentialAlgebra K L₂]
    {n d n' d' : ℕ}
    (P : DGroupPresentation G K L₁ n d) (Q : DGroupPresentation H K L₂ n' d')
    (a : G) (b : H)
    (translA : G → DifferentialAlgEquiv K L₁) (translB : H → DifferentialAlgEquiv K L₂)
    (hA : ∀ (h : G) (j : Fin d), (translA h).toAlgEquiv (P.ell a j) = P.ell (a * h) j)
    (hB : ∀ (h : H) (j : Fin d'), (translB h).toAlgEquiv (Q.ell b j) = Q.ell (b * h) j)
    (tailA : IntermediateField K L₁) (tailB : IntermediateField K L₂)
    (htailA : tailA = differentialAdjoin K (Set.range (P.ell a)))
    (htailB : tailB = differentialAdjoin K (Set.range (Q.ell b)))
    (Isogenous : Prop)
    (hrigidity : Nonorthogonal (dGroupSharp P) (dGroupSharp Q) ↔ Isogenous) :
    Nonorthogonal
        (differentialTranslationStabilizer translA tailA)
        (differentialTranslationStabilizer translB tailB)
      ↔ Isogenous := by
  rw [multiplicationTail_translationStabilizer_eq_dGroupSharp P a translA hA tailA htailA,
    multiplicationTail_translationStabilizer_eq_dGroupSharp Q b translB hB tailB htailB]
  exact hrigidity

/-- **The exact abstract/embedded dichotomy.**  For two bulks of the same Manin rank whose Manin
coordinates are differentially independent, the abstract tail fields are canonically isomorphic —
the boundary carries no hair — while the embedded horizon symmetries are nonorthogonal exactly
when the bulks are isogenous.  The first component is the no-hair theorem, the second is Theorem B.
-/
theorem manin_horizon_abstract_embedded_dichotomy
    {G H : Type*} [CommGroup G] [CommGroup H] {K L₁ L₂ : Type u}
    [Field K] [Field L₁] [Field L₂] [Algebra K L₁] [Algebra K L₂]
    [Differential K] [Differential L₁] [Differential L₂]
    [DifferentialAlgebra K L₁] [DifferentialAlgebra K L₂]
    {n d n' : ℕ}
    (P : DGroupPresentation G K L₁ n d) (Q : DGroupPresentation H K L₂ n' d)
    (a : G) (b : H)
    (translA : G → DifferentialAlgEquiv K L₁) (translB : H → DifferentialAlgEquiv K L₂)
    (hA : ∀ (h : G) (j : Fin d), (translA h).toAlgEquiv (P.ell a j) = P.ell (a * h) j)
    (hB : ∀ (h : H) (j : Fin d), (translB h).toAlgEquiv (Q.ell b j) = Q.ell (b * h) j)
    (hfreeA : DifferentialIndependent K (P.ell a))
    (hfreeB : DifferentialIndependent K (Q.ell b))
    (Isogenous : Prop)
    (hrigidity : Nonorthogonal (dGroupSharp P) (dGroupSharp Q) ↔ Isogenous) :
    Nonempty (differentialAdjoin K (Set.range (P.ell a)) ≃ₐ[K]
        differentialAdjoin K (Set.range (Q.ell b))) ∧
      (Nonorthogonal
        (differentialTranslationStabilizer translA
          (differentialAdjoin K (Set.range (P.ell a))))
        (differentialTranslationStabilizer translB
          (differentialAdjoin K (Set.range (Q.ell b)))) ↔ Isogenous) :=
  ⟨⟨differentialQuotientFreeAlgEquiv (P.ell a) (Q.ell b) hfreeA hfreeB⟩,
    embeddedManinHorizon_nonorthogonal_iff_isogenous P Q a b translA translB hA hB
      (differentialAdjoin K (Set.range (P.ell a)))
      (differentialAdjoin K (Set.range (Q.ell b))) rfl rfl Isogenous hrigidity⟩


end

end GaloisForLFunctions.HTGeometry
