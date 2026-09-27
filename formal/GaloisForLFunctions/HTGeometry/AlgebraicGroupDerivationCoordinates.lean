import GaloisForLFunctions.HTGeometry.AlgebraicGroupTangentMap

/-!
# Tangent coordinates of derivations of the function field of an algebraic group

Let `G` be an integral commutative algebraic group over `C` with function field `F`, identity `e`
and generic point `g`.  To a `C`-derivation `D` of `F` attach the tangent vector
`u_D = g_D · g_0⁻¹` at the identity and its coordinates

`Θ(D)_i = (χ_D(m_i))_ε`,

the `ε`-parts of the values of the lift `χ_D : O_(G,e) → F[ε]` on generators `m_i` of the maximal
ideal of `O_(G,e)`.  Then:

* `Θ` is `F`-linear (the group law on lifts is addition of derivations);
* `Θ` is injective (a point derivation at `e` is determined on generators of `m_e`);
* `Θ` is equivariant: for a rational point `x`, `Θ(σ_x ∘ D ∘ σ_x⁻¹) = σ_x(Θ(D))` coordinatewise,
  because `σ_x` acts on `F[ε]`-points by `g ↦ g · x` and fixes the constant evaluation at `e`.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {C : Type u} [Field C] (G : Over (Spec (.of C))) [GrpObj G]

/-- Pushing points forward along a map of `C`-algebras, as a group homomorphism. -/
def pointPush {R S : Type u} [CommRing R] [CommRing S] [Algebra C R] [Algebra C S]
    (f : R →ₐ[C] S) :
    (algebraicPointSource (K := C) (R := R) ⟶ G) →* (algebraicPointSource (K := C) (R := S) ⟶ G) where
  toFun p := pointSourceMap f ≫ p
  map_one' := MonObj.comp_one _
  map_mul' := MonObj.comp_mul _

@[simp]
theorem pointPush_apply {R S : Type u} [CommRing R] [CommRing S] [Algebra C R] [Algebra C S]
    (f : R →ₐ[C] S) (p : algebraicPointSource (K := C) (R := R) ⟶ G) :
    pointPush G f p = pointSourceMap f ≫ p := rfl

variable [IsIntegral G.left]

omit [GrpObj G] in
theorem dualGraph_zero :
    dualGraph G 0 = dualInl (C := C) (L := G.left.functionField) :=
  AlgHom.ext fun _ => TrivSqZeroExt.ext rfl rfl

/-- The tangent vector `u_D = g_D · g_0⁻¹` of a derivation, a lift of the identity. -/
def tangentLift (D : Derivation C G.left.functionField G.left.functionField) :
    algebraicPointSource (K := C) (R := DualL G.left.functionField) ⟶ G :=
  genericLift G D * (genericLift G 0)⁻¹

theorem sqzFst_tangentLift (D : Derivation C G.left.functionField G.left.functionField) :
    pointSourceMap (sqzFst (C := C) (L := G.left.functionField) (M := G.left.functionField)) ≫
      tangentLift G D = 1 := by
  have h := (pointPush G (sqzFst (C := C) (L := G.left.functionField)
    (M := G.left.functionField))).map_mul (genericLift G D) (genericLift G 0)⁻¹
  rw [map_inv, pointPush_apply, pointPush_apply, pointPush_apply, sqzFst_genericLift,
    sqzFst_genericLift, mul_inv_cancel] at h
  exact h

theorem exists_tangentChi (D : Derivation C G.left.functionField G.left.functionField) :
    ∃ (χ : G.left.presheaf.stalk (identityCenter G) ⟶
        CommRingCat.of (DualL G.left.functionField))
      (hχ : stalkConstants G (identityCenter G) ≫ χ =
        CommRingCat.ofHom (algebraMap C (DualL G.left.functionField))),
      χ ≫ CommRingCat.ofHom (sqzFst (C := C) (L := G.left.functionField)
        (M := G.left.functionField)).toRingHom = identityEvalAt G G.left.functionField ∧
      tangentLift G D = stalkPoint G (identityCenter G) χ hχ :=
  exists_stalkPoint_of_lift G _ _ (identityEvalAt_const G _) (tangentLift G D)
    (by rw [sqzFst_tangentLift, one_eq_stalkPoint])

/-- The lift `χ_D : O_(G,e) → F[ε]` of the evaluation at the identity. -/
def tangentChi (D : Derivation C G.left.functionField G.left.functionField) :
    G.left.presheaf.stalk (identityCenter G) ⟶ CommRingCat.of (DualL G.left.functionField) :=
  (exists_tangentChi G D).choose

theorem tangentChi_const (D : Derivation C G.left.functionField G.left.functionField) :
    stalkConstants G (identityCenter G) ≫ tangentChi G D =
      CommRingCat.ofHom (algebraMap C (DualL G.left.functionField)) :=
  (exists_tangentChi G D).choose_spec.choose

theorem tangentChi_fst (D : Derivation C G.left.functionField G.left.functionField) :
    tangentChi G D ≫ CommRingCat.ofHom (sqzFst (C := C) (L := G.left.functionField)
      (M := G.left.functionField)).toRingHom = identityEvalAt G G.left.functionField :=
  (exists_tangentChi G D).choose_spec.choose_spec.1

theorem tangentLift_eq (D : Derivation C G.left.functionField G.left.functionField) :
    tangentLift G D = stalkPoint G (identityCenter G) (tangentChi G D) (tangentChi_const G D) :=
  (exists_tangentChi G D).choose_spec.choose_spec.2

instance isLocalHom_tangentChi (D : Derivation C G.left.functionField G.left.functionField) :
    IsLocalHom (tangentChi G D).hom :=
  isLocalHom_of_comp_sqzFst G _ (tangentChi_fst G D)

/-! ### Linearity -/

omit [GrpObj G] in
theorem dualGraph_const (D : Derivation C G.left.functionField G.left.functionField) :
    stalkConstants G (genericPoint G.left) ≫ CommRingCat.ofHom (dualGraph G D).toRingHom =
      CommRingCat.ofHom (algebraMap C (DualL G.left.functionField)) := by
  rw [stalkConstants_genericPoint]
  exact CommRingCat.hom_ext (RingHom.ext fun c => (dualGraph G D).commutes c)

omit [GrpObj G] in
theorem dualGraph_comp_sqzFst (D : Derivation C G.left.functionField G.left.functionField) :
    CommRingCat.ofHom (dualGraph G D).toRingHom ≫ CommRingCat.ofHom (sqzFst (C := C)
      (L := G.left.functionField) (M := G.left.functionField)).toRingHom = genericStalkId G :=
  rfl

/-- **`u_(D₁+D₂) = u_(D₁) u_(D₂)`**: the tangent vector of a sum is the product. -/
theorem tangentLift_add (D₁ D₂ : Derivation C G.left.functionField G.left.functionField) :
    tangentLift G (D₁ + D₂) = tangentLift G D₁ * tangentLift G D₂ := by
  haveI : IsLocalHom (genericStalkId G).hom := inferInstanceAs (IsLocalHom (RingHom.id _))
  have hp : (1 : algebraicPointSource (K := C) (R := G.left.functionField) ⟶ G) *
      genericPointHom G = stalkPoint G (genericPoint G.left) (genericStalkId G)
        (stalkConstants_genericPoint_comp_id G) := by
    rw [_root_.one_mul, genericPointHom_eq_stalkPoint]
  have hg0 : pointSourceMap (dualInl (C := C) (L := G.left.functionField)) ≫ genericPointHom G =
      genericLift G 0 := by rw [genericLift, dualGraph_zero]
  obtain ⟨ψ, hψ, hψφ, hψsnd, hmul⟩ := exists_stalkPoint_mul_of_lifts G (genericPoint G.left)
    (genericStalkId G) (stalkConstants_genericPoint_comp_id G) 1 (genericPointHom G) hp
    (tangentLift G D₁) (genericLift G D₂) (sqzFst_tangentLift G D₁) (sqzFst_genericLift G D₂)
    (CommRingCat.ofHom (dualGraph G D₁).toRingHom) (CommRingCat.ofHom (dualGraph G D₂).toRingHom)
    (dualGraph_const G D₁) (dualGraph_const G D₂)
    (dualGraph_comp_sqzFst G D₁) (dualGraph_comp_sqzFst G D₂)
    (by rw [hg0, tangentLift, inv_mul_cancel_right, genericLift_eq_stalkPoint])
    (by rw [MonObj.comp_one, _root_.one_mul, genericLift_eq_stalkPoint])
  have hψD : ψ = CommRingCat.ofHom (dualGraph G (D₁ + D₂)).toRingHom :=
    CommRingCat.hom_ext (RingHom.ext fun a => TrivSqZeroExt.ext
      (congrArg (fun q : _ ⟶ CommRingCat.of G.left.functionField => q a) hψφ) (hψsnd a))
  have hsum : tangentLift G D₁ * genericLift G D₂ = genericLift G (D₁ + D₂) := by
    rw [hmul, genericLift_eq_stalkPoint]
    exact stalkPoint_congr G _ hψD _ _
  rw [tangentLift, ← hsum, tangentLift, tangentLift, _root_.mul_assoc]

/-- The derivation `a • D` has tangent vector `u_D` rescaled in the `ε`-direction. -/
abbrev dualScale (a : G.left.functionField) :
    DualL G.left.functionField →ₐ[C] DualL G.left.functionField :=
  (TrivSqZeroExt.map (a • LinearMap.id)).restrictScalars C

omit [GrpObj G] in
theorem dualScale_comp_dualGraph (a : G.left.functionField)
    (D : Derivation C G.left.functionField G.left.functionField) :
    (dualScale G a).comp (dualGraph G D) = dualGraph G (a • D) :=
  AlgHom.ext fun b => TrivSqZeroExt.ext (by simp) (by simp)

omit [GrpObj G] in
theorem pointSourceMap_dualScale_genericLift (a : G.left.functionField)
    (D : Derivation C G.left.functionField G.left.functionField) :
    pointSourceMap (dualScale G a) ≫ genericLift G D = genericLift G (a • D) := by
  rw [genericLift, genericLift, ← Category.assoc, ← pointSourceMap_comp,
    dualScale_comp_dualGraph]

theorem pointSourceMap_dualScale_tangentLift (a : G.left.functionField)
    (D : Derivation C G.left.functionField G.left.functionField) :
    pointSourceMap (dualScale G a) ≫ tangentLift G D = tangentLift G (a • D) := by
  have h := (pointPush G (dualScale G a)).map_mul (genericLift G D) (genericLift G 0)⁻¹
  rw [map_inv, pointPush_apply, pointPush_apply, pointPush_apply,
    pointSourceMap_dualScale_genericLift, pointSourceMap_dualScale_genericLift, smul_zero] at h
  exact h

variable [LocallyOfFiniteType G.hom]

/-- **The tangent coordinates `Θ(D)` of a derivation.** -/
def tangentCoords (D : Derivation C G.left.functionField G.left.functionField) :
    Fin (tangentRank G) → G.left.functionField :=
  fun i => (tangentChi G D (tangentGenerators G i)).snd

/-- **`Θ` is additive.** -/
theorem tangentCoords_add (D₁ D₂ : Derivation C G.left.functionField G.left.functionField) :
    tangentCoords G (D₁ + D₂) = tangentCoords G D₁ + tangentCoords G D₂ := by
  have hp : (1 : algebraicPointSource (K := C) (R := G.left.functionField) ⟶ G) * 1 =
      stalkPoint G (identityCenter G) (identityEvalAt G _) (identityEvalAt_const G _) := by
    rw [_root_.one_mul, one_eq_stalkPoint]
  obtain ⟨ψ, hψ, hψφ, hψsnd, hmul⟩ := exists_stalkPoint_mul_of_lifts G (identityCenter G)
    (identityEvalAt G _) (identityEvalAt_const G _) 1 1 hp
    (tangentLift G D₁) (tangentLift G D₂) (sqzFst_tangentLift G D₁) (sqzFst_tangentLift G D₂)
    _ _ (tangentChi_const G D₁) (tangentChi_const G D₂) (tangentChi_fst G D₁) (tangentChi_fst G D₂)
    (by rw [MonObj.comp_one, _root_.mul_one, tangentLift_eq])
    (by rw [MonObj.comp_one, _root_.one_mul, tangentLift_eq])
  haveI := isLocalHom_of_comp_sqzFst G ψ hψφ
  have hχ : tangentChi G (D₁ + D₂) = ψ := by
    apply stalkPoint_injective G (hψ₁ := tangentChi_const G (D₁ + D₂)) (hψ₂ := hψ)
    rw [← tangentLift_eq, tangentLift_add, hmul]
  funext i
  simp only [tangentCoords, Pi.add_apply, hχ, hψsnd]



/-- **`Θ` is `F`-homogeneous.** -/
theorem tangentCoords_smul (a : G.left.functionField)
    (D : Derivation C G.left.functionField G.left.functionField) :
    tangentCoords G (a • D) = a • tangentCoords G D := by
  have hsf : CommRingCat.ofHom (dualScale G a).toRingHom ≫
      CommRingCat.ofHom (sqzFst (C := C) (L := G.left.functionField)
        (M := G.left.functionField)).toRingHom =
      CommRingCat.ofHom (sqzFst (C := C) (L := G.left.functionField)
        (M := G.left.functionField)).toRingHom :=
    CommRingCat.hom_ext (RingHom.ext fun b => by simp)
  have hfst : tangentChi G D ≫ CommRingCat.ofHom (dualScale G a).toRingHom ≫
      CommRingCat.ofHom (sqzFst (C := C) (L := G.left.functionField)
        (M := G.left.functionField)).toRingHom = identityEvalAt G G.left.functionField := by
    rw [hsf, tangentChi_fst]
  haveI := isLocalHom_of_comp_sqzFst G
    (tangentChi G D ≫ CommRingCat.ofHom (dualScale G a).toRingHom)
    (φ := identityEvalAt G G.left.functionField) (by rw [Category.assoc]; exact hfst)
  have hχ : tangentChi G (a • D) = tangentChi G D ≫ CommRingCat.ofHom (dualScale G a).toRingHom := by
    have e : pointSourceMap (dualScale G a) ≫ tangentLift G D =
        pointSourceMap (dualScale G a) ≫
          stalkPoint G (identityCenter G) (tangentChi G D) (tangentChi_const G D) := by
      rw [← tangentLift_eq]
    rw [pointSourceMap_dualScale_tangentLift, tangentLift_eq,
      pointSourceMap_comp_stalkPoint] at e
    exact stalkPoint_injective G e
  funext i
  simp only [tangentCoords, Pi.smul_apply, hχ]
  change (dualScale G a (tangentChi G D (tangentGenerators G i))).snd = _
  simp

/-- **`Θ` is injective.** -/
theorem eq_zero_of_tangentCoords_eq_zero
    (D : Derivation C G.left.functionField G.left.functionField) (h : tangentCoords G D = 0) :
    D = 0 := by
  set χ₀ := identityEvalAt G G.left.functionField ≫
    CommRingCat.ofHom (dualInl (C := C) (L := G.left.functionField)).toRingHom
  have hχ₀ : stalkConstants G (identityCenter G) ≫ χ₀ =
      CommRingCat.ofHom (algebraMap C (DualL G.left.functionField)) := by
    rw [← Category.assoc, identityEvalAt_const]
    exact CommRingCat.hom_ext (RingHom.ext fun c =>
      (dualInl (C := C) (L := G.left.functionField)).commutes c)
  have hχ : tangentChi G D = χ₀ :=
    lift_ext_of_generators G _ (tangentChi_const G D) hχ₀ (tangentChi_fst G D) rfl
      fun i => (congrFun h i).trans rfl
  have hone : tangentLift G D = 1 := by
    rw [tangentLift_eq, stalkPoint_congr G _ hχ _ (by rw [← hχ]; exact tangentChi_const G D),
      ← pointSourceMap_comp_stalkPoint (hψ := identityEvalAt_const G _), ← one_eq_stalkPoint,
      MonObj.comp_one]
  have hlift : genericLift G D = genericLift G 0 := by
    rw [← mul_inv_eq_one]
    exact hone
  exact genericLift_injective G hlift

/-- **The tangent coordinates, as an `F`-linear map.** -/
def tangentCoordsLinear :
    Derivation C G.left.functionField G.left.functionField →ₗ[G.left.functionField]
      (Fin (tangentRank G) → G.left.functionField) where
  toFun := tangentCoords G
  map_add' := tangentCoords_add G
  map_smul' := tangentCoords_smul G

theorem tangentCoordsLinear_injective : Function.Injective (tangentCoordsLinear G) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  exact eq_zero_of_tangentCoords_eq_zero G

/-! ### Equivariance -/

section Equivariance

variable {G}

/-- `F[ε] → F[ε]`, `a + εb ↦ σa + εσb`. -/
def dualMapEquiv (σ : G.left.functionField ≃ₐ[C] G.left.functionField) :
    DualL G.left.functionField →ₐ[C] DualL G.left.functionField where
  toFun p := TrivSqZeroExt.inl (σ p.fst) + TrivSqZeroExt.inr (σ p.snd)
  map_one' := TrivSqZeroExt.ext (by simp) (by simp)
  map_mul' p q := TrivSqZeroExt.ext (by simp) (by
    simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, add_zero, zero_add, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, map_add, map_mul])
  map_zero' := TrivSqZeroExt.ext (by simp) (by simp)
  map_add' p q := TrivSqZeroExt.ext (by simp) (by simp)
  commutes' c := TrivSqZeroExt.ext (by
    change σ (algebraMap C G.left.functionField c) + 0 = algebraMap C G.left.functionField c
    rw [AlgEquiv.commutes, add_zero]) (by
    change 0 + σ 0 = 0
    simp)

omit [GrpObj G] [LocallyOfFiniteType G.hom] in
@[simp]
theorem dualMapEquiv_fst (σ : G.left.functionField ≃ₐ[C] G.left.functionField)
    (p : DualL G.left.functionField) : (dualMapEquiv σ p).fst = σ p.fst := by
  simp [dualMapEquiv]

omit [GrpObj G] [LocallyOfFiniteType G.hom] in
@[simp]
theorem dualMapEquiv_snd (σ : G.left.functionField ≃ₐ[C] G.left.functionField)
    (p : DualL G.left.functionField) : (dualMapEquiv σ p).snd = σ p.snd := by
  simp [dualMapEquiv]

/-- The conjugate derivation `σ ∘ D ∘ σ⁻¹`. -/
def conjDerivation (σ : G.left.functionField ≃ₐ[C] G.left.functionField)
    (D : Derivation C G.left.functionField G.left.functionField) :
    Derivation C G.left.functionField G.left.functionField :=
  Derivation.mk' (σ.toLinearMap.comp (D.toLinearMap.comp σ.symm.toLinearMap)) fun a b => by
    change σ (D (σ.symm (a * b))) = a • σ (D (σ.symm b)) + b • σ (D (σ.symm a))
    rw [map_mul, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
      AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, smul_eq_mul, smul_eq_mul]

omit [GrpObj G] [LocallyOfFiniteType G.hom] in
@[simp]
theorem conjDerivation_apply (σ : G.left.functionField ≃ₐ[C] G.left.functionField)
    (D : Derivation C G.left.functionField G.left.functionField) (a : G.left.functionField) :
    conjDerivation σ D a = σ (D (σ.symm a)) := rfl

omit [GrpObj G] [LocallyOfFiniteType G.hom] in
theorem dualMapEquiv_comp_dualGraph (σ : G.left.functionField ≃ₐ[C] G.left.functionField)
    (D : Derivation C G.left.functionField G.left.functionField) :
    (dualMapEquiv σ).comp (dualGraph G D) = (dualGraph G (conjDerivation σ D)).comp σ.toAlgHom :=
  AlgHom.ext fun a => TrivSqZeroExt.ext (by simp) (by simp)

variable (G)

omit [LocallyOfFiniteType G.hom] in
/-- **Twisting coefficients by a translation conjugates the derivation.** -/
theorem pointSourceMap_dualMapEquiv_genericLift (x : 𝟙_ (Over (Spec (.of C))) ⟶ G)
    (D : Derivation C G.left.functionField G.left.functionField) :
    pointSourceMap (dualMapEquiv (translationAlgEquiv G x)) ≫ genericLift G D =
      genericLift G (conjDerivation (translationAlgEquiv G x) D) * (toUnit _ ≫ x) := by
  rw [genericLift, ← Category.assoc, ← pointSourceMap_comp, dualMapEquiv_comp_dualGraph,
    pointSourceMap_comp, Category.assoc, ← genericPointHom_mul_const, MonObj.comp_mul,
    ← Category.assoc (pointSourceMap _) (toUnit _),
    show pointSourceMap (dualGraph G (conjDerivation (translationAlgEquiv G x) D)) ≫ toUnit _ =
      toUnit _ from toUnit_unique _ _]
  rfl

omit [LocallyOfFiniteType G.hom] in
theorem pointSourceMap_dualMapEquiv_tangentLift [IsCommMonObj G] (x : 𝟙_ (Over (Spec (.of C))) ⟶ G)
    (D : Derivation C G.left.functionField G.left.functionField) :
    pointSourceMap (dualMapEquiv (translationAlgEquiv G x)) ≫ tangentLift G D =
      tangentLift G (conjDerivation (translationAlgEquiv G x) D) := by
  have h := (pointPush G (dualMapEquiv (translationAlgEquiv G x))).map_mul (genericLift G D)
    (genericLift G 0)⁻¹
  rw [map_inv, pointPush_apply, pointPush_apply, pointPush_apply,
    pointSourceMap_dualMapEquiv_genericLift, pointSourceMap_dualMapEquiv_genericLift] at h
  change pointSourceMap (dualMapEquiv (translationAlgEquiv G x)) ≫
    (genericLift G D * (genericLift G 0)⁻¹) = _
  have h0 : conjDerivation (translationAlgEquiv G x) 0 = 0 := by
    ext a
    simp
  rw [h, h0, tangentLift, _root_.mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel,
    _root_.mul_one]

/-- **`Θ` is equivariant**: `Θ(σ_x ∘ D ∘ σ_x⁻¹) = σ_x(Θ D)` coordinatewise. -/
theorem tangentCoords_conjDerivation [IsCommMonObj G] (x : 𝟙_ (Over (Spec (.of C))) ⟶ G)
    (D : Derivation C G.left.functionField G.left.functionField) (i : Fin (tangentRank G)) :
    tangentCoords G (conjDerivation (translationAlgEquiv G x) D) i =
      translationAlgEquiv G x (tangentCoords G D i) := by
  set σ := translationAlgEquiv G x
  have hsf : CommRingCat.ofHom (dualMapEquiv σ).toRingHom ≫
      CommRingCat.ofHom (sqzFst (C := C) (L := G.left.functionField)
        (M := G.left.functionField)).toRingHom =
      CommRingCat.ofHom (sqzFst (C := C) (L := G.left.functionField)
        (M := G.left.functionField)).toRingHom ≫ CommRingCat.ofHom σ.toAlgHom.toRingHom :=
    CommRingCat.hom_ext (RingHom.ext fun p => by simp)
  have hev : identityEvalAt G G.left.functionField ≫ CommRingCat.ofHom σ.toAlgHom.toRingHom =
      identityEvalAt G G.left.functionField :=
    CommRingCat.hom_ext (RingHom.ext fun a => σ.commutes _)
  have hfst : (tangentChi G D ≫ CommRingCat.ofHom (dualMapEquiv σ).toRingHom) ≫
      CommRingCat.ofHom (sqzFst (C := C) (L := G.left.functionField)
        (M := G.left.functionField)).toRingHom = identityEvalAt G G.left.functionField := by
    rw [Category.assoc, hsf, ← Category.assoc, tangentChi_fst, hev]
  haveI := isLocalHom_of_comp_sqzFst G _ (φ := identityEvalAt G G.left.functionField) hfst
  have hχ : tangentChi G (conjDerivation σ D) =
      tangentChi G D ≫ CommRingCat.ofHom (dualMapEquiv σ).toRingHom := by
    have e : pointSourceMap (dualMapEquiv σ) ≫ tangentLift G D =
        pointSourceMap (dualMapEquiv σ) ≫
          stalkPoint G (identityCenter G) (tangentChi G D) (tangentChi_const G D) := by
      rw [← tangentLift_eq]
    rw [pointSourceMap_dualMapEquiv_tangentLift, tangentLift_eq,
      pointSourceMap_comp_stalkPoint] at e
    exact stalkPoint_injective G e
  simp only [tangentCoords, hχ]
  change (dualMapEquiv σ (tangentChi G D (tangentGenerators G i))).snd = _
  simp

end Equivariance

end

end GaloisForLFunctions.HTGeometry
