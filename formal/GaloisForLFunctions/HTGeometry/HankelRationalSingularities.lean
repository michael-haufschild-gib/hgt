import GaloisForLFunctions.HTGeometry.HankelResolutionBirational

/-!
# The Hankel secant varieties have rational singularities

**Definition** (Kempf's formulation for an affine variety `X = Spec A` over a field `K`): `X` has
rational singularities if there is a resolution `f : Y → X` — `Y` smooth over `K`, `f` proper and
birational — with `f^# : A → Γ(Y, 𝒪_Y)` an isomorphism and `H^i(Y, 𝒪_Y) = 0` for `i > 0`.  For an
affine target these are `f_* 𝒪_Y = 𝒪_X` and `R^i f_* 𝒪_Y = 0` (both sheaves are quasi-coherent on
`X`, with global sections `Γ(Y, 𝒪_Y)` and `H^i(Y, 𝒪_Y)`).  Sheaf cohomology is the `Ext` cohomology
`RHTower.deningerSheafCohomology` of the abelian sheaf underlying `𝒪_Y`.

**Theorem.**  For `K` of characteristic zero and `2r ≤ N`, the Hankel secant ring
`A = K[x_0, …, x_{N-1}] / I_r` (`I_r` the `(r+1)`-minors of the Hankel matrix) has rational
singularities: the incidence variety `Y = {(G, v) : G ∈ ℙ^r, ⟨G X^j, v⟩ = 0, j < N - r}` resolves it.

* `HTGeometry.HasRationalSingularities`.
* `HTGeometry.HasRationalSingularities.of_algEquiv` : invariance under `K`-algebra isomorphisms.
* `HTGeometry.secantRingUpTo_hasRationalSingularities` : with free moments adjoined.
* `HTGeometry.hankelSecantRing_hasRationalSingularities`.
-/

namespace HTGeometry

open AlgebraicGeometry CategoryTheory

universe u

/-- **Rational singularities** of `Spec A` over `K`: a smooth `K`-scheme `Y` with a proper birational
`f : Y → Spec A` such that `f^#` is an isomorphism on global sections and `𝒪_Y` has no higher
cohomology. -/
def HasRationalSingularities (K : Type u) [Field K] (A : Type u) [CommRing A] [Algebra K A] :
    Prop :=
  ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of A)),
    Smooth (f ≫ Spec.map (CommRingCat.ofHom (algebraMap K A))) ∧ IsProper f ∧
      Scheme.BirationalOver f (𝟙 _) ∧ IsIso f.appTop ∧
      ∀ (q : ℕ) (x : RHTower.deningerSheafCohomology.{u} ⊤ (schemeAbSheaf Y) (q + 1)), x = 0

/-- **Rational singularities are invariant under `K`-algebra isomorphisms.** -/
theorem HasRationalSingularities.of_algEquiv {K : Type u} [Field K] {A B : Type u} [CommRing A]
    [CommRing B] [Algebra K A] [Algebra K B] (e : A ≃ₐ[K] B) (hA : HasRationalSingularities K A) :
    HasRationalSingularities K B := by
  obtain ⟨Y, f, hsm, hpr, hbir, hiso, hcoh⟩ := hA
  let φ : CommRingCat.of B ≅ CommRingCat.of A := e.symm.toRingEquiv.toCommRingCatIso
  let g : Spec (CommRingCat.of A) ≅ Spec (CommRingCat.of B) := Scheme.Spec.mapIso φ.op
  refine ⟨Y, f ≫ g.hom, ?_, ?_, ?_, ?_, hcoh⟩
  · have hg : g.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K B))
        = Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
      change Spec.map φ.hom ≫ _ = _
      rw [← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (RingHom.ext fun c => e.symm.commutes c)
    rw [Category.assoc, hg]
    exact hsm
  · infer_instance
  · obtain ⟨p, hp⟩ := hbir
    refine ⟨p.trans (Scheme.PartialIso.ofIso g), Scheme.PartialIso.IsOver.trans (sY := g.hom) ?_ ?_⟩
    · change p.iso.hom ≫ p.target.ι ≫ g.hom = p.source.ι ≫ f ≫ g.hom
      have hp' : p.iso.hom ≫ p.target.ι ≫ 𝟙 _ = p.source.ι ≫ f := hp
      rw [Category.comp_id] at hp'
      rw [← Category.assoc, hp', Category.assoc]
    · change (Scheme.topIso _ ≪≫ g ≪≫ (Scheme.topIso _).symm).hom ≫ (⊤ : Scheme.Opens _).ι ≫ 𝟙 _
        = (⊤ : Scheme.Opens _).ι ≫ g.hom
      simp
  · have hg : IsIso g.hom.appTop := by
      change IsIso (Spec.map φ.hom).appTop
      have h : (Spec.map φ.hom).appTop
          = (Scheme.ΓSpecIso _).hom ≫ φ.hom ≫ (Scheme.ΓSpecIso _).inv := by
        rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
      rw [h]
      infer_instance
    rw [Scheme.Hom.comp_appTop]
    infer_instance

/-- **The secant rings of the first `j + r` moments have rational singularities**: for `K` of
characteristic zero, `r ≤ j` and `j + r ≤ N`, the ring `K[x_0, …, x_{N-1}] / secantIdealUpTo` (the
Hankel secant ring of `x_0, …, x_{j+r-1}` with `N - j - r` free variables adjoined) has rational
singularities, resolved by the incidence variety `Proj B_j`. -/
theorem secantRingUpTo_hasRationalSingularities (K : Type) [Field K] [CharZero K] {N r j : ℕ}
    (hrj : r ≤ j) (hj : j + r ≤ N) :
    HasRationalSingularities K (MvPolynomial (Fin N) K ⧸ secantIdealUpTo K N r j) := by
  refine ⟨HankelY K r N j, hankelResolution K r N hj, ?_, hankelResolution_isProper _,
    hankelResolution_birational hrj hj, hankelResolution_appTop_isIso _,
    fun q x => hankelY_cohomology_vanishing hj q x⟩
  rw [hankelResolution_over]
  exact hankelYStruct_smooth hj

/-- **The Hankel secant varieties have rational singularities**: for `K` of characteristic zero
and `2r ≤ N`, `K[x_0, …, x_{N-1}] / I_r` has rational singularities, resolved by the Hankel incidence
variety. -/
theorem hankelSecantRing_hasRationalSingularities (K : Type) [Field K] [CharZero K] {N r : ℕ}
    (hrN : 2 * r ≤ N) :
    HasRationalSingularities K (MvPolynomial (Fin N) K ⧸ RHTower.finiteHankelSecantIdeal K N r) :=
  (secantRingUpTo_hasRationalSingularities K (j := N - r) (by omega) (by omega)).of_algEquiv
    (Ideal.quotientEquivAlgOfEq K secantIdealUpTo_self)

end HTGeometry
