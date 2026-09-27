import GaloisForLFunctions.HTGeometry.AlgebraicGroupRationalPointEvaluation
import GaloisForLFunctions.HTGeometry.CompactKernelFunctionFieldCapacity
import GaloisForLFunctions.HTGeometry.FunctionFieldJetExtension
import Mathlib.FieldTheory.Extension

/-!
# An isogeny is the quotient by its kernel, at the level of function fields

Let `G` be an integral commutative algebraic group over an algebraically closed field `C` of
characteristic zero and `α : G → G` an isogeny: a surjective homomorphism whose kernel
`α⁻¹(e)` is finite over `C`.  Then for every `n`

`α^(n*) C(G) = C(G)^(Γ_n)`,  `Γ_n = ker(α^n)(C)`.

The inclusion `⊆` is translation invariance of `α^n`.  For `⊇`, let `σ` be any embedding of `C(G)`
into an algebraic closure fixing `α^(n*) C(G)`, and `g` the generic point.  The point
`h_σ = g_σ · g⁻¹` is killed by `α^n`; a point of a finite `C`-scheme with values in a field is a
constant point, and `α` is onto on rational points, so `h_σ` is a constant `c ∈ Γ_n`.  Hence
`g_σ = g · c = g ∘ Spec(σ_c)`, so `σ = σ_c`: every such embedding fixes the elements fixed by
`Γ_n`, and those elements lie in `α^(n*) C(G)`.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-! ### Elements fixed by every embedding -/

/-- In an algebraic extension in characteristic zero, an element fixed by every embedding into an
algebraically closed field lies in the base. -/
theorem mem_range_of_forall_algHom_eq {E F N : Type*} [Field E] [Field F] [Field N]
    [Algebra E F] [Algebra F N] [Algebra E N] [IsScalarTower E F N] [IsAlgClosed N]
    [Algebra.IsAlgebraic E F] [CharZero E] (f : F)
    (h : ∀ σ : F →ₐ[E] N, σ f = algebraMap F N f) : f ∈ Set.range (algebraMap E F) := by
  classical
  have hsplit : ∀ x : F, ((minpoly E x).map (algebraMap E N)).Splits :=
    fun x => IsAlgClosed.splits _
  have hrange := Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly_of_splits N hsplit f
  have hsub : (minpoly E f).rootSet N ⊆ {algebraMap F N f} := by
    rw [← hrange]
    rintro _ ⟨σ, rfl⟩
    exact h σ
  have hint := Algebra.IsIntegral.isIntegral (R := E) f
  have hsep : (minpoly E f).Separable := (minpoly.irreducible hint).separable
  have hcard := Polynomial.card_rootSet_eq_natDegree hsep (hsplit f)
  have hle : Fintype.card ((minpoly E f).rootSet N) ≤ 1 :=
    Fintype.card_le_one_iff_subsingleton.mpr
      ((Set.subsingleton_singleton.anti hsub).coe_sort)
  have hpos := minpoly.natDegree_pos hint
  have hone : (minpoly E f).natDegree = 1 := by omega
  obtain ⟨e, he⟩ := minpoly.natDegree_eq_one_iff.mp hone
  exact ⟨e, he⟩

variable {C : Type u} [Field C]

/-! ### Field-valued points of finite `C`-schemes are constant -/

omit [Field C] in
/-- A field extension `N / C` is an epimorphism on `C`-points of `Spec C`. -/
theorem specMap_algebraMap_cancel [Field C] {N : Type u} [Field N] [Algebra C N]
    {a b : Spec (.of C) ⟶ Spec (.of C)}
    (h : Spec.map (CommRingCat.ofHom (algebraMap C N)) ≫ a =
      Spec.map (CommRingCat.ofHom (algebraMap C N)) ≫ b) : a = b := by
  obtain ⟨χa, rfl⟩ := Spec.map_surjective a
  obtain ⟨χb, rfl⟩ := Spec.map_surjective b
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext c
  exact (algebraMap C N).injective (congrArg (fun q : CommRingCat.of C ⟶ CommRingCat.of N =>
    q c) h')

/-- **A field-valued point of a finite `C`-scheme is a constant rational point.** -/
theorem exists_rationalPoint_of_isFinite [IsAlgClosed C] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of C)) [IsFinite p] {N : Type u} [Field N] [Algebra C N]
    (s : Spec (.of N) ⟶ X) (hs : s ≫ p = Spec.map (CommRingCat.ofHom (algebraMap C N))) :
    ∃ c : Spec (.of C) ⟶ X, c ≫ p = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap C N)) ≫ c = s := by
  haveI : IsAffine X := isAffine_of_isAffineHom p
  let φ : Γ(X, ⊤) ⟶ CommRingCat.of N := s.appTop ≫ (Scheme.ΓSpecIso (.of N)).hom
  have hsφ : s = Spec.map φ ≫ X.isoSpec.inv := by
    rw [Iso.eq_comp_inv, ← Scheme.isoSpec_hom_naturality, Scheme.isoSpec_Spec_hom,
      ← Spec.map_comp]
  have hcomp : p.appTop ≫ φ =
      (Scheme.ΓSpecIso (.of C)).hom ≫ CommRingCat.ofHom (algebraMap C N) := by
    change p.appTop ≫ s.appTop ≫ _ = _
    rw [← Category.assoc, ← Scheme.Hom.comp_appTop, hs, Scheme.ΓSpecIso_naturality]
  -- every value of `φ` is integral over `C`, hence a constant
  letI : Algebra Γ(Spec (.of C), ⊤) Γ(X, ⊤) := p.appTop.hom.toAlgebra
  have hint : ∀ a : Γ(X, ⊤), φ a ∈ Set.range (algebraMap C N) := by
    intro a
    have ha : IsIntegral Γ(Spec (.of C), ⊤) a := (p.finite_appTop).to_isIntegral a
    have hN : IsIntegral C (φ a) := IsIntegral.map_of_comp_eq (Scheme.ΓSpecIso (.of C)).hom.hom
      φ.hom (congrArg CommRingCat.Hom.hom hcomp).symm ha
    have hone := IsAlgClosed.degree_eq_one_of_irreducible C (minpoly.irreducible hN)
    obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.mp (Polynomial.natDegree_eq_of_degree_eq_some
      hone)
    exact ⟨c, hc⟩
  choose ψf hψf using hint
  let ψ : Γ(X, ⊤) →+* C :=
    { toFun := ψf
      map_one' := (algebraMap C N).injective (by rw [hψf, map_one, map_one])
      map_mul' := fun a b => (algebraMap C N).injective (by rw [hψf, map_mul, map_mul, hψf, hψf])
      map_zero' := (algebraMap C N).injective (by rw [hψf, map_zero, map_zero])
      map_add' := fun a b => (algebraMap C N).injective (by rw [hψf, map_add, map_add, hψf, hψf]) }
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap C N) = φ := by
    ext a
    exact hψf a
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ X.isoSpec.inv, ?_, ?_⟩
  · apply specMap_algebraMap_cancel (N := N)
    rw [Category.comp_id, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, hψ, ← hsφ, hs]
  · rw [← Category.assoc, ← Spec.map_comp, hψ, ← hsφ]

section Group

variable (G : Over (Spec (.of C))) [GrpObj G]

/-- The identity section `e : Spec C → G`. -/
abbrev identitySection : Spec (.of C) ⟶ G.left := (η[G] : 𝟙_ (Over (Spec (.of C))) ⟶ G).left

/-- An isogeny of an algebraic group: a surjective homomorphism with finite kernel. -/
class IsIsogeny (α : G ⟶ G) : Prop extends IsMonHom α where
  surjective : Surjective α.left
  finite_kernel : IsFinite (pullback.snd α.left (identitySection G))

variable {G}

theorem toUnit_left (S : Over (Spec (.of C))) : (toUnit S).left = S.hom := by
  simp

variable [IsAlgClosed C]

/-- **A field-valued point in the kernel of an isogeny is a constant rational point.** -/
theorem exists_const_of_comp_isogeny_eq_one (α : G ⟶ G) [IsIsogeny G α] {N : Type u} [Field N]
    [Algebra C N] (h : algebraicPointSource (K := C) (R := N) ⟶ G) (hα : h ≫ α = 1) :
    ∃ c : 𝟙_ (Over (Spec (.of C))) ⟶ G, c ≫ α = 1 ∧ h = toUnit _ ≫ c := by
  haveI := IsIsogeny.finite_kernel (G := G) (α := α)
  have hw : h.left ≫ α.left = Spec.map (CommRingCat.ofHom (algebraMap C N)) ≫ identitySection G := by
    have h1 : h.left ≫ α.left = (1 : algebraicPointSource (K := C) (R := N) ⟶ G).left :=
      congrArg CommaMorphism.left hα
    rw [h1, Hom.one_def, Over.comp_left, toUnit_left]
    rfl
  let s : Spec (.of N) ⟶ pullback α.left (identitySection G) := pullback.lift h.left _ hw
  obtain ⟨c', hc'p, hc's⟩ := exists_rationalPoint_of_isFinite
    (pullback.snd α.left (identitySection G)) s (pullback.lift_snd _ _ _)
  have hfst : pullback.fst α.left (identitySection G) ≫ G.hom =
      pullback.snd α.left (identitySection G) := by
    have hcond := pullback.condition (f := α.left) (g := identitySection G)
    have h1 := congrArg (· ≫ G.hom) hcond
    simp only [Category.assoc] at h1
    rw [Over.w α, show identitySection G ≫ G.hom = 𝟙 _ from Over.w η[G]] at h1
    rw [h1, Category.comp_id]
  refine ⟨Over.homMk (c' ≫ pullback.fst _ _) (by
    change (c' ≫ pullback.fst _ _) ≫ G.hom = 𝟙 _
    rw [Category.assoc, hfst, hc'p]), ?_, ?_⟩
  · apply Over.OverMorphism.ext
    have key : (c' ≫ pullback.fst _ _) ≫ α.left = identitySection G := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hc'p, Category.id_comp]
    rw [Over.comp_left, Hom.one_def, Over.comp_left, toUnit_left]
    exact key.trans (Category.id_comp _).symm
  · apply Over.OverMorphism.ext
    rw [Over.comp_left, toUnit_left]
    change h.left = Spec.map (CommRingCat.ofHom (algebraMap C N)) ≫ c' ≫ pullback.fst _ _
    rw [← Category.assoc, hc's, pullback.lift_fst]

variable [LocallyOfFiniteType G.hom]

/-- **An isogeny is onto on rational points.**  The fibre over a rational point is a nonempty
closed subset of a Jacobson scheme, so it contains a closed point, which is rational. -/
theorem exists_comp_isogeny_eq (α : G ⟶ G) [IsIsogeny G α] (y : 𝟙_ (Over (Spec (.of C))) ⟶ G) :
    ∃ x : 𝟙_ (Over (Spec (.of C))) ⟶ G, x ≫ α = y := by
  haveI : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  haveI := IsIsogeny.surjective (G := G) (α := α)
  set q := y.left (IsLocalRing.closedPoint C)
  have hq : IsClosed {q} := ((pointEquivClosedPoint G.hom) ⟨y.left, Over.w y⟩).2
  obtain ⟨p₀, hp₀⟩ := Surjective.surj (f := α.left) q
  obtain ⟨p, hpZ, hpc'⟩ := nonempty_inter_closedPoints (Z := α.left.base ⁻¹' {q}) ⟨p₀, hp₀⟩
    (hq.preimage α.left.base.hom.continuous).isLocallyClosed
  have hpc : IsClosed {p} := hpc'
  refine ⟨rationalPointOfClosedPoint G p hpc, ?_⟩
  apply Over.OverMorphism.ext
  change rationalPointHom G (rationalPointOfClosedPoint G p hpc ≫ α) = rationalPointHom G y
  refine ext_of_apply_closedPoint_eq G.hom (rationalPoint_comp_hom G _)
    (rationalPoint_comp_hom G _) ?_
  change α.left (rationalPointHom G (rationalPointOfClosedPoint G p hpc)
    (IsLocalRing.closedPoint C)) = q
  rw [rationalPointOfClosedPoint_apply]
  exact hpZ

/-- The iterates `α^n`. -/
def isogenyPow (α : G ⟶ G) : ℕ → (G ⟶ G)
  | 0 => 𝟙 G
  | n + 1 => isogenyPow α n ≫ α

omit [IsAlgClosed C] [GrpObj G] [LocallyOfFiniteType G.hom] in
@[simp]
theorem isogenyPow_zero (α : G ⟶ G) : isogenyPow α 0 = 𝟙 G := rfl

omit [IsAlgClosed C] [GrpObj G] [LocallyOfFiniteType G.hom] in
theorem isogenyPow_succ (α : G ⟶ G) (n : ℕ) : isogenyPow α (n + 1) = isogenyPow α n ≫ α := rfl

omit [IsAlgClosed C] [LocallyOfFiniteType G.hom] in
instance isMonHom_isogenyPow (α : G ⟶ G) [IsMonHom α] (n : ℕ) : IsMonHom (isogenyPow α n) := by
  induction n with
  | zero => exact inferInstanceAs (IsMonHom (𝟙 G))
  | succ n ih => exact inferInstanceAs (IsMonHom (isogenyPow α n ≫ α))

omit [IsAlgClosed C] [GrpObj G] [LocallyOfFiniteType G.hom] in
instance isDominant_isogenyPow (α : G ⟶ G) [IsDominant α.left] (n : ℕ) :
    IsDominant (isogenyPow α n).left := by
  induction n with
  | zero => exact inferInstanceAs (IsDominant (𝟙 G.left))
  | succ n ih => exact inferInstanceAs (IsDominant ((isogenyPow α n).left ≫ α.left))

instance (α : G ⟶ G) [IsIsogeny G α] : IsDominant α.left := by
  haveI := IsIsogeny.surjective (G := G) (α := α)
  infer_instance

theorem exists_comp_isogenyPow_eq (α : G ⟶ G) [IsIsogeny G α] (n : ℕ)
    (y : 𝟙_ (Over (Spec (.of C))) ⟶ G) :
    ∃ x : 𝟙_ (Over (Spec (.of C))) ⟶ G, x ≫ isogenyPow α n = y := by
  induction n generalizing y with
  | zero => exact ⟨y, Category.comp_id y⟩
  | succ n ih =>
      obtain ⟨z, hz⟩ := exists_comp_isogeny_eq α y
      obtain ⟨x, hx⟩ := ih z
      exact ⟨x, by rw [isogenyPow_succ, ← Category.assoc, hx, hz]⟩

/-- **Field-valued points in the kernel of `α^n` are constant rational points.** -/
theorem exists_const_of_comp_isogenyPow_eq_one (α : G ⟶ G) [IsIsogeny G α] [IsCommMonObj G]
    (n : ℕ) {N : Type u} [Field N] [Algebra C N] (h : algebraicPointSource (K := C) (R := N) ⟶ G)
    (hα : h ≫ isogenyPow α n = 1) :
    ∃ c : 𝟙_ (Over (Spec (.of C))) ⟶ G, c ≫ isogenyPow α n = 1 ∧ h = toUnit _ ≫ c := by
  induction n generalizing h with
  | zero =>
      refine ⟨1, Category.comp_id _, ?_⟩
      rw [isogenyPow_zero, Category.comp_id] at hα
      rw [hα, MonObj.comp_one]
  | succ n ih =>
      rw [isogenyPow_succ, ← Category.assoc] at hα
      obtain ⟨c₁, hc₁α, hc₁⟩ := exists_const_of_comp_isogeny_eq_one α _ hα
      obtain ⟨c₂, hc₂⟩ := exists_comp_isogenyPow_eq α n c₁
      have hker : (h * (toUnit _ ≫ c₂)⁻¹) ≫ isogenyPow α n = 1 := by
        have hmap := (IsMonHom.monoidHom (isogenyPow α n)
          (algebraicPointSource (K := C) (R := N))).map_mul h (toUnit _ ≫ c₂)⁻¹
        change (h * (toUnit _ ≫ c₂)⁻¹) ≫ isogenyPow α n = _ at hmap
        rw [hmap, map_inv]
        change h ≫ isogenyPow α n * ((toUnit _ ≫ c₂) ≫ isogenyPow α n)⁻¹ = 1
        rw [hc₁, Category.assoc, hc₂, mul_inv_cancel]
      obtain ⟨c₃, hc₃α, hc₃⟩ := ih _ hker
      refine ⟨c₃ * c₂, ?_, ?_⟩
      · rw [isogenyPow_succ, ← Category.assoc, MonObj.mul_comp, hc₃α, hc₂, _root_.one_mul, hc₁α]
      · rw [MonObj.comp_mul, ← hc₃, inv_mul_cancel_right]

end Group

/-! ### Finite transcendence degree -/

/-- A transcendence basis is insensitive to replacing the base by an isomorphic copy. -/
theorem isTranscendenceBasis_iff_of_ringEquiv {R S A : Type*} [CommRing R] [CommRing S]
    [CommRing A] [Algebra R A] [Algebra S A] (e : R ≃+* S)
    (h : (algebraMap S A).comp e.toRingHom = algebraMap R A) {κ : Type*} (x : κ → A) :
    IsTranscendenceBasis S x ↔ IsTranscendenceBasis R x := by
  have hcomp : (algebraMap S A).comp (e : R →+* S) = (RingHom.id A).comp (algebraMap R A) := by
    ext a
    rw [← h]
    rfl
  have h1 : AlgebraicIndependent S x ↔ AlgebraicIndependent R x :=
    algebraicIndependent_ringHom_iff_of_comp_eq e (RingHom.id A) Function.injective_id hcomp
  have h2 : ∀ s : Set A, AlgebraicIndepOn S id s ↔ AlgebraicIndepOn R id s := fun s =>
    algebraicIndependent_ringHom_iff_of_comp_eq e (RingHom.id A) (x := fun i : s => id (i : A))
      Function.injective_id hcomp
  unfold IsTranscendenceBasis
  rw [h1]
  exact and_congr_right fun _ => forall_congr' fun s => imp_congr (h2 s) Iff.rfl

section TranscendenceBasis

variable (X : Over (Spec (.of C))) [IsIntegral X.left] [LocallyOfFiniteType X.hom]

/-- **The function field of an integral scheme of finite type over `C` has a finite transcendence
basis.** -/
theorem exists_fin_isTranscendenceBasis :
    ∃ (d : ℕ) (t : Fin d → X.left.functionField), IsTranscendenceBasis C t := by
  haveI : FaithfulSMul C X.left.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap C _).injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis C X.left.functionField
  letI := X.hom.functionFieldAlgebra
  letI := Scheme.specFunctionFieldAlgebra C
  have hs' : IsTranscendenceBasis (Spec (.of C)).functionField ((↑) : s → X.left.functionField) :=
    (isTranscendenceBasis_iff_of_ringEquiv (Scheme.specFunctionFieldAlgEquiv C).toRingEquiv
      rfl _).mpr hs
  have hfin : Cardinal.mk s < Cardinal.aleph0 := by
    have h1 := hs'.lift_cardinalMk_eq_trdeg
    have h2 := X.hom.functionField_trdeg_lt_aleph0
    rw [Cardinal.lift_id, Cardinal.lift_id] at h1
    rw [h1]
    exact h2
  haveI : Finite s := Cardinal.lt_aleph0_iff_finite.mp hfin
  haveI := Fintype.ofFinite s
  let e := Fintype.equivFin s
  exact ⟨Fintype.card s, fun i => (e.symm i : X.left.functionField),
    (hs.comp_equiv e.symm)⟩

end TranscendenceBasis

/-! ### The level theorem -/

section Level

variable [IsAlgClosed C] (G : Over (Spec (.of C))) [GrpObj G] [IsIntegral G.left]
  [LocallyOfFiniteType G.hom] (α : G ⟶ G) [IsIsogeny G α]

omit [IsAlgClosed C] [LocallyOfFiniteType G.hom] in
/-- Pullback along `α^n` is the `n`-th power of pullback along `α`. -/
theorem overFunctionFieldPullback_isogenyPow (n : ℕ) :
    overFunctionFieldPullback G (isogenyPow α n) = (overFunctionFieldPullback G α) ^ n := by
  induction n with
  | zero =>
      ext a
      rw [pow_zero, AlgHom.one_apply, overFunctionFieldPullback_apply]
      rw [Scheme.Hom.functionFieldPullback_congr (isogenyPow α 0).left (𝟙 G.left) rfl,
        Scheme.Hom.functionFieldPullback_id]
      rfl
  | succ n ih =>
      ext a
      rw [pow_succ, AlgHom.mul_apply, ← ih, overFunctionFieldPullback_apply,
        overFunctionFieldPullback_apply, overFunctionFieldPullback_apply]
      rw [Scheme.Hom.functionFieldPullback_congr (isogenyPow α (n + 1)).left
        ((isogenyPow α n).left ≫ α.left) rfl, Scheme.Hom.functionFieldPullback_comp]
      rfl

omit [IsAlgClosed C] [LocallyOfFiniteType G.hom] in
/-- **Translation by a kernel point fixes the pullback field.** -/
theorem translationAlgEquiv_overFunctionFieldPullback (φ : G ⟶ G) [IsMonHom φ] [IsDominant φ.left]
    (c : 𝟙_ (Over (Spec (.of C))) ⟶ G) (hc : c ≫ φ = 1) (a : G.left.functionField) :
    translationAlgEquiv G c (overFunctionFieldPullback G φ a) = overFunctionFieldPullback G φ a := by
  have hinv : (GrpObj.mulRight c).hom ≫ φ = φ := by
    rw [← Category.id_comp ((GrpObj.mulRight c).hom), comp_mulRight_hom_eq_mul, MonObj.mul_comp,
      Category.assoc, hc, MonObj.comp_one, _root_.mul_one, Category.id_comp]
  simp only [translationAlgEquiv_apply, overFunctionFieldPullback_apply]
  have h := Scheme.Hom.functionFieldPullback_congr ((GrpObj.mulRight c).hom.left ≫ φ.left) φ.left
    (congrArg CommaMorphism.left hinv)
  rw [Scheme.Hom.functionFieldPullback_comp] at h
  exact congrArg (fun q : G.left.functionField ⟶ G.left.functionField => q a) h

variable [CharZero C] [IsCommMonObj G]

/-- **The isogeny level theorem**: `α^(n*) C(G) = C(G)^(ker(α^n)(C))`. -/
theorem mem_range_isogenyPullback_pow_iff (n : ℕ) (f : G.left.functionField) :
    f ∈ Set.range ⇑((overFunctionFieldPullback G α) ^ n) ↔
      ∀ c : 𝟙_ (Over (Spec (.of C))) ⟶ G, c ≫ isogenyPow α n = 1 →
        translationAlgEquiv G c f = f := by
  rw [← overFunctionFieldPullback_isogenyPow]
  set φ := overFunctionFieldPullback G (isogenyPow α n) with hφ
  constructor
  · rintro ⟨a, rfl⟩ c hc
    exact translationAlgEquiv_overFunctionFieldPullback G (isogenyPow α n) c hc a
  · intro hfix
    obtain ⟨d, t, ht⟩ := exists_fin_isTranscendenceBasis G
    let F := G.left.functionField
    let E : IntermediateField C F := φ.fieldRange
    let N := AlgebraicClosure F
    haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap C E).injective
    -- `F` is algebraic over `E`, which contains `C(φ(t))`
    have hφt := isTranscendenceBasis_comp_algHom ht φ
    haveI : Algebra.IsAlgebraic (IntermediateField.adjoin C (Set.range (φ ∘ t))) F :=
      hφt.isAlgebraic_field
    have hle : IntermediateField.adjoin C (Set.range (φ ∘ t)) ≤ E := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact ⟨t i, rfl⟩
    haveI : Algebra.IsAlgebraic E F := by
      letI : Algebra (IntermediateField.adjoin C (Set.range (φ ∘ t))) E :=
        (IntermediateField.inclusion hle).toAlgebra
      haveI : IsScalarTower (IntermediateField.adjoin C (Set.range (φ ∘ t))) E F :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      exact ⟨fun x => (Algebra.IsAlgebraic.isAlgebraic x).extendScalars
        (IntermediateField.inclusion_injective hle)⟩
    obtain ⟨⟨_, a, rfl⟩, hea⟩ := mem_range_of_forall_algHom_eq (E := E) (N := N) f fun σ => by
      let σC : F →ₐ[C] N := σ.restrictScalars C
      let ιC : F →ₐ[C] N := IsScalarTower.toAlgHom C F N
      have hσφ : σC.comp φ = ιC.comp φ := by
        ext a
        exact σ.commutes ⟨φ a, a, rfl⟩
      let g := genericPointHom G
      let h := (pointSourceMap σC ≫ g) * (pointSourceMap ιC ≫ g)⁻¹
      have hP : ∀ ψ : F →ₐ[C] N, (pointSourceMap ψ ≫ g) ≫ isogenyPow α n =
          pointSourceMap (ψ.comp φ) ≫ g := by
        intro ψ
        rw [Category.assoc, genericPointHom_comp, ← Category.assoc, ← pointSourceMap_comp]
      have hα : h ≫ isogenyPow α n = 1 := by
        have hm := (IsMonHom.monoidHom (isogenyPow α n)
          (algebraicPointSource (K := C) (R := N))).map_mul (pointSourceMap σC ≫ g)
            (pointSourceMap ιC ≫ g)⁻¹
        rw [map_inv] at hm
        change h ≫ isogenyPow α n = (pointSourceMap σC ≫ g) ≫ isogenyPow α n *
          ((pointSourceMap ιC ≫ g) ≫ isogenyPow α n)⁻¹ at hm
        rw [hm, hP, hP, hσφ, mul_inv_cancel]
      obtain ⟨c, hc, hhc⟩ := exists_const_of_comp_isogenyPow_eq_one α n h hα
      have hσ : pointSourceMap σC ≫ g = pointSourceMap (ιC.comp (translationAlgEquiv G c).toAlgHom) ≫ g := by
        have h1 : pointSourceMap σC ≫ g = (toUnit _ ≫ c) * (pointSourceMap ιC ≫ g) := by
          rw [← hhc, inv_mul_cancel_right]
        rw [h1, mul_comm, pointSourceMap_comp, Category.assoc, ← genericPointHom_mul_const,
          MonObj.comp_mul, ← Category.assoc, show pointSourceMap ιC ≫ toUnit _ = toUnit _ from
            toUnit_unique _ _]
      have hσeq := pointSourceMap_genericPointHom_injective G hσ
      change σC f = _
      rw [hσeq, AlgHom.comp_apply]
      change ιC (translationAlgEquiv G c f) = _
      rw [hfix c hc]
      rfl
    exact ⟨a, hea⟩

end Level

end

end GaloisForLFunctions.HTGeometry
