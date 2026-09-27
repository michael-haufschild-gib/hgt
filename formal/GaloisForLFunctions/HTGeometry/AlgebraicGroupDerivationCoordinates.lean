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

variable [IsIntegral G.left] (L : Type u) [Field L] [Algebra C L] [Algebra G.left.functionField L]
  [IsScalarTower C G.left.functionField L]

omit [GrpObj G] in
theorem dualGraph_zero :
    (dualInl (C := C) (L := L)).comp (IsScalarTower.toAlgHom C G.left.functionField L) =
      dualGraph G L 0 :=
  AlgHom.ext fun _ => TrivSqZeroExt.ext rfl rfl

/-- The tangent vector `u_D = g_D · g_0⁻¹` of a derivation, a lift of the identity. -/
def tangentLift (D : Derivation C G.left.functionField L) :
    algebraicPointSource (K := C) (R := DualL L) ⟶ G :=
  genericLift G L D * (genericLift G L 0)⁻¹

theorem sqzFst_tangentLift (D : Derivation C G.left.functionField L) :
    pointSourceMap (sqzFst (C := C) (L := L) (M := L)) ≫
      tangentLift G L D = 1 := by
  have h := (pointPush G (sqzFst (C := C) (L := L) (M := L))).map_mul (genericLift G L D) (genericLift G L 0)⁻¹
  rw [map_inv, pointPush_apply, pointPush_apply, pointPush_apply, sqzFst_genericLift,
    sqzFst_genericLift, mul_inv_cancel] at h
  exact h

theorem exists_tangentChi (D : Derivation C G.left.functionField L) :
    ∃ (χ : G.left.presheaf.stalk (identityCenter G) ⟶
        CommRingCat.of (DualL L))
      (hχ : stalkConstants G (identityCenter G) ≫ χ =
        CommRingCat.ofHom (algebraMap C (DualL L))),
      χ ≫ CommRingCat.ofHom (sqzFst (C := C) (L := L) (M := L)).toRingHom = identityEvalAt G L ∧
      tangentLift G L D = stalkPoint G (identityCenter G) χ hχ :=
  exists_stalkPoint_of_lift G _ _ (identityEvalAt_const G _) (tangentLift G L D)
    (by rw [sqzFst_tangentLift, one_eq_stalkPoint])

/-- The lift `χ_D : O_(G,e) → F[ε]` of the evaluation at the identity. -/
def tangentChi (D : Derivation C G.left.functionField L) :
    G.left.presheaf.stalk (identityCenter G) ⟶ CommRingCat.of (DualL L) :=
  (exists_tangentChi G L D).choose

theorem tangentChi_const (D : Derivation C G.left.functionField L) :
    stalkConstants G (identityCenter G) ≫ tangentChi G L D =
      CommRingCat.ofHom (algebraMap C (DualL L)) :=
  (exists_tangentChi G L D).choose_spec.choose

theorem tangentChi_fst (D : Derivation C G.left.functionField L) :
    tangentChi G L D ≫ CommRingCat.ofHom (sqzFst (C := C) (L := L) (M := L)).toRingHom = identityEvalAt G L :=
  (exists_tangentChi G L D).choose_spec.choose_spec.1

theorem tangentLift_eq (D : Derivation C G.left.functionField L) :
    tangentLift G L D = stalkPoint G (identityCenter G) (tangentChi G L D) (tangentChi_const G L D) :=
  (exists_tangentChi G L D).choose_spec.choose_spec.2

instance isLocalHom_tangentChi (D : Derivation C G.left.functionField L) :
    IsLocalHom (tangentChi G L D).hom :=
  isLocalHom_of_comp_sqzFst G _ (tangentChi_fst G L D)

/-! ### Linearity -/

/-- **`u_(D₁+D₂) = u_(D₁) u_(D₂)`**: the tangent vector of a sum is the product. -/
theorem tangentLift_add (D₁ D₂ : Derivation C G.left.functionField L) :
    tangentLift G L (D₁ + D₂) = tangentLift G L D₁ * tangentLift G L D₂ := by
  have hp : (1 : algebraicPointSource (K := C) (R := L) ⟶ G) *
      genericPointAt G L = stalkPoint G (genericPoint G.left) (genericStalkAt G L)
        (genericStalkAt_const G L) := by
    rw [_root_.one_mul, genericPointAt_eq_stalkPoint]
  have hg0 : pointSourceMap (dualInl (C := C) (L := L)) ≫ genericPointAt G L =
      genericLift G L 0 := by
    rw [genericLift, genericPointAt, ← Category.assoc, ← pointSourceMap_comp, dualGraph_zero]
  obtain ⟨ψ, hψ, hψφ, hψsnd, hmul⟩ := exists_stalkPoint_mul_of_lifts G (genericPoint G.left)
    (genericStalkAt G L) (genericStalkAt_const G L) 1 (genericPointAt G L) hp
    (tangentLift G L D₁) (genericLift G L D₂) (sqzFst_tangentLift G L D₁) (sqzFst_genericLift G L D₂)
    (CommRingCat.ofHom (dualGraph G L D₁).toRingHom) (CommRingCat.ofHom (dualGraph G L D₂).toRingHom)
    (dualGraph_const G L D₁) (dualGraph_const G L D₂)
    (dualGraph_comp_sqzFst G L D₁) (dualGraph_comp_sqzFst G L D₂)
    (by rw [hg0, tangentLift, inv_mul_cancel_right, genericLift_eq_stalkPoint])
    (by rw [MonObj.comp_one, _root_.one_mul, genericLift_eq_stalkPoint])
  have hψD : ψ = CommRingCat.ofHom (dualGraph G L (D₁ + D₂)).toRingHom :=
    CommRingCat.hom_ext (RingHom.ext fun a => TrivSqZeroExt.ext
      (congrArg (fun q : _ ⟶ CommRingCat.of L => q a) hψφ) (hψsnd a))
  have hsum : tangentLift G L D₁ * genericLift G L D₂ = genericLift G L (D₁ + D₂) := by
    rw [hmul, genericLift_eq_stalkPoint]
    exact stalkPoint_congr G _ hψD _ _
  rw [tangentLift, ← hsum, tangentLift, tangentLift, _root_.mul_assoc]

/-- The derivation `a • D` has tangent vector `u_D` rescaled in the `ε`-direction. -/
abbrev dualScale (a : L) : DualL L →ₐ[C] DualL L :=
  (TrivSqZeroExt.map (a • LinearMap.id)).restrictScalars C

omit [GrpObj G] in
theorem dualScale_comp_dualGraph (a : L)
    (D : Derivation C G.left.functionField L) :
    (dualScale (C := C) L a).comp (dualGraph G L D) = dualGraph G L (a • D) :=
  AlgHom.ext fun b => TrivSqZeroExt.ext (by simp) (by simp)

omit [GrpObj G] in
theorem pointSourceMap_dualScale_genericLift (a : L)
    (D : Derivation C G.left.functionField L) :
    pointSourceMap (dualScale (C := C) L a) ≫ genericLift G L D = genericLift G L (a • D) := by
  rw [genericLift, genericLift, ← Category.assoc, ← pointSourceMap_comp,
    dualScale_comp_dualGraph]

theorem pointSourceMap_dualScale_tangentLift (a : L)
    (D : Derivation C G.left.functionField L) :
    pointSourceMap (dualScale (C := C) L a) ≫ tangentLift G L D = tangentLift G L (a • D) := by
  have h := (pointPush G (dualScale (C := C) L a)).map_mul (genericLift G L D) (genericLift G L 0)⁻¹
  rw [map_inv, pointPush_apply, pointPush_apply, pointPush_apply,
    pointSourceMap_dualScale_genericLift, pointSourceMap_dualScale_genericLift, smul_zero] at h
  exact h

variable [LocallyOfFiniteType G.hom]

/-- **The tangent coordinates `Θ(D)` of a derivation.** -/
def tangentCoords (D : Derivation C G.left.functionField L) :
    Fin (tangentRank G) → L :=
  fun i => (tangentChi G L D (tangentGenerators G i)).snd

/-- **`Θ` is additive.** -/
theorem tangentCoords_add (D₁ D₂ : Derivation C G.left.functionField L) :
    tangentCoords G L (D₁ + D₂) = tangentCoords G L D₁ + tangentCoords G L D₂ := by
  have hp : (1 : algebraicPointSource (K := C) (R := L) ⟶ G) * 1 =
      stalkPoint G (identityCenter G) (identityEvalAt G _) (identityEvalAt_const G _) := by
    rw [_root_.one_mul, one_eq_stalkPoint]
  obtain ⟨ψ, hψ, hψφ, hψsnd, hmul⟩ := exists_stalkPoint_mul_of_lifts G (identityCenter G)
    (identityEvalAt G _) (identityEvalAt_const G _) 1 1 hp
    (tangentLift G L D₁) (tangentLift G L D₂) (sqzFst_tangentLift G L D₁) (sqzFst_tangentLift G L D₂)
    _ _ (tangentChi_const G L D₁) (tangentChi_const G L D₂) (tangentChi_fst G L D₁) (tangentChi_fst G L D₂)
    (by rw [MonObj.comp_one, _root_.mul_one, tangentLift_eq])
    (by rw [MonObj.comp_one, _root_.one_mul, tangentLift_eq])
  haveI := isLocalHom_of_comp_sqzFst G ψ hψφ
  have hχ : tangentChi G L (D₁ + D₂) = ψ := by
    apply stalkPoint_injective G (hψ₁ := tangentChi_const G L (D₁ + D₂)) (hψ₂ := hψ)
    rw [← tangentLift_eq, tangentLift_add, hmul]
  funext i
  simp only [tangentCoords, Pi.add_apply, hχ, hψsnd]



/-- **`Θ` is `F`-homogeneous.** -/
theorem tangentCoords_smul (a : L)
    (D : Derivation C G.left.functionField L) :
    tangentCoords G L (a • D) = a • tangentCoords G L D := by
  have hsf : CommRingCat.ofHom (dualScale (C := C) L a).toRingHom ≫
      CommRingCat.ofHom (sqzFst (C := C) (L := L) (M := L)).toRingHom =
      CommRingCat.ofHom (sqzFst (C := C) (L := L) (M := L)).toRingHom :=
    CommRingCat.hom_ext (RingHom.ext fun b => by simp)
  have hfst : tangentChi G L D ≫ CommRingCat.ofHom (dualScale (C := C) L a).toRingHom ≫
      CommRingCat.ofHom (sqzFst (C := C) (L := L) (M := L)).toRingHom = identityEvalAt G L := by
    rw [hsf, tangentChi_fst]
  haveI := isLocalHom_of_comp_sqzFst G
    (tangentChi G L D ≫ CommRingCat.ofHom (dualScale (C := C) L a).toRingHom)
    (φ := identityEvalAt G L) (by rw [Category.assoc]; exact hfst)
  have hχ : tangentChi G L (a • D) = tangentChi G L D ≫ CommRingCat.ofHom (dualScale (C := C) L a).toRingHom := by
    have e : pointSourceMap (dualScale (C := C) L a) ≫ tangentLift G L D =
        pointSourceMap (dualScale (C := C) L a) ≫
          stalkPoint G (identityCenter G) (tangentChi G L D) (tangentChi_const G L D) := by
      rw [← tangentLift_eq]
    rw [pointSourceMap_dualScale_tangentLift, tangentLift_eq,
      pointSourceMap_comp_stalkPoint] at e
    exact stalkPoint_injective G e
  funext i
  simp only [tangentCoords, Pi.smul_apply, hχ]
  change (dualScale (C := C) L a (tangentChi G L D (tangentGenerators G i))).snd = _
  simp

/-- **`Θ` is injective.** -/
theorem eq_zero_of_tangentCoords_eq_zero
    (D : Derivation C G.left.functionField L) (h : tangentCoords G L D = 0) :
    D = 0 := by
  set χ₀ := identityEvalAt G L ≫
    CommRingCat.ofHom (dualInl (C := C) (L := L)).toRingHom
  have hχ₀ : stalkConstants G (identityCenter G) ≫ χ₀ =
      CommRingCat.ofHom (algebraMap C (DualL L)) := by
    rw [← Category.assoc, identityEvalAt_const]
    exact CommRingCat.hom_ext (RingHom.ext fun c =>
      (dualInl (C := C) (L := L)).commutes c)
  have hχ : tangentChi G L D = χ₀ :=
    lift_ext_of_generators G _ (tangentChi_const G L D) hχ₀ (tangentChi_fst G L D) rfl
      fun i => (congrFun h i).trans rfl
  have hone : tangentLift G L D = 1 := by
    rw [tangentLift_eq, stalkPoint_congr G _ hχ _ (by rw [← hχ]; exact tangentChi_const G L D),
      ← pointSourceMap_comp_stalkPoint (hψ := identityEvalAt_const G _), ← one_eq_stalkPoint,
      MonObj.comp_one]
  have hlift : genericLift G L D = genericLift G L 0 := by
    rw [← mul_inv_eq_one]
    exact hone
  exact genericLift_injective G L hlift

/-- **The tangent coordinates, as an `L`-linear map.** -/
def tangentCoordsLinear :
    Derivation C G.left.functionField L →ₗ[L] (Fin (tangentRank G) → L) where
  toFun := tangentCoords G L
  map_add' := tangentCoords_add G L
  map_smul' := tangentCoords_smul G L

theorem tangentCoordsLinear_injective : Function.Injective (tangentCoordsLinear G L) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  exact eq_zero_of_tangentCoords_eq_zero G L

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
    (dualMapEquiv σ).comp (dualGraph G G.left.functionField D) = (dualGraph G G.left.functionField (conjDerivation σ D)).comp σ.toAlgHom :=
  AlgHom.ext fun a => TrivSqZeroExt.ext (by simp) (by simp)

variable (G)

omit [LocallyOfFiniteType G.hom] in
/-- **Twisting coefficients by a translation conjugates the derivation.** -/
theorem pointSourceMap_dualMapEquiv_genericLift (x : 𝟙_ (Over (Spec (.of C))) ⟶ G)
    (D : Derivation C G.left.functionField G.left.functionField) :
    pointSourceMap (dualMapEquiv (translationAlgEquiv G x)) ≫ genericLift G G.left.functionField D =
      genericLift G G.left.functionField (conjDerivation (translationAlgEquiv G x) D) * (toUnit _ ≫ x) := by
  rw [genericLift, ← Category.assoc, ← pointSourceMap_comp, dualMapEquiv_comp_dualGraph,
    pointSourceMap_comp, Category.assoc, ← genericPointHom_mul_const, MonObj.comp_mul,
    ← Category.assoc (pointSourceMap _) (toUnit _),
    show pointSourceMap (dualGraph G G.left.functionField (conjDerivation (translationAlgEquiv G x) D)) ≫ toUnit _ =
      toUnit _ from toUnit_unique _ _]
  rfl

omit [LocallyOfFiniteType G.hom] in
theorem pointSourceMap_dualMapEquiv_tangentLift [IsCommMonObj G] (x : 𝟙_ (Over (Spec (.of C))) ⟶ G)
    (D : Derivation C G.left.functionField G.left.functionField) :
    pointSourceMap (dualMapEquiv (translationAlgEquiv G x)) ≫ tangentLift G G.left.functionField D =
      tangentLift G G.left.functionField (conjDerivation (translationAlgEquiv G x) D) := by
  have h := (pointPush G (dualMapEquiv (translationAlgEquiv G x))).map_mul (genericLift G G.left.functionField D)
    (genericLift G G.left.functionField 0)⁻¹
  rw [map_inv, pointPush_apply, pointPush_apply, pointPush_apply,
    pointSourceMap_dualMapEquiv_genericLift, pointSourceMap_dualMapEquiv_genericLift] at h
  change pointSourceMap (dualMapEquiv (translationAlgEquiv G x)) ≫
    (genericLift G G.left.functionField D * (genericLift G G.left.functionField 0)⁻¹) = _
  have h0 : conjDerivation (translationAlgEquiv G x) 0 = 0 := by
    ext a
    simp
  rw [h, h0, tangentLift, _root_.mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel,
    _root_.mul_one]

/-- **`Θ` is equivariant**: `Θ(σ_x ∘ D ∘ σ_x⁻¹) = σ_x(Θ D)` coordinatewise. -/
theorem tangentCoords_conjDerivation [IsCommMonObj G] (x : 𝟙_ (Over (Spec (.of C))) ⟶ G)
    (D : Derivation C G.left.functionField G.left.functionField) (i : Fin (tangentRank G)) :
    tangentCoords G G.left.functionField (conjDerivation (translationAlgEquiv G x) D) i =
      translationAlgEquiv G x (tangentCoords G G.left.functionField D i) := by
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
  have hfst : (tangentChi G G.left.functionField D ≫ CommRingCat.ofHom (dualMapEquiv σ).toRingHom) ≫
      CommRingCat.ofHom (sqzFst (C := C) (L := G.left.functionField)
        (M := G.left.functionField)).toRingHom = identityEvalAt G G.left.functionField := by
    rw [Category.assoc, hsf, ← Category.assoc, tangentChi_fst, hev]
  haveI := isLocalHom_of_comp_sqzFst G _ (φ := identityEvalAt G G.left.functionField) hfst
  have hχ : tangentChi G G.left.functionField (conjDerivation σ D) =
      tangentChi G G.left.functionField D ≫ CommRingCat.ofHom (dualMapEquiv σ).toRingHom := by
    have e : pointSourceMap (dualMapEquiv σ) ≫ tangentLift G G.left.functionField D =
        pointSourceMap (dualMapEquiv σ) ≫
          stalkPoint G (identityCenter G) (tangentChi G G.left.functionField D) (tangentChi_const G G.left.functionField D) := by
      rw [← tangentLift_eq]
    rw [pointSourceMap_dualMapEquiv_tangentLift, tangentLift_eq,
      pointSourceMap_comp_stalkPoint] at e
    exact stalkPoint_injective G e
  simp only [tangentCoords, hχ]
  change (dualMapEquiv σ (tangentChi G G.left.functionField D (tangentGenerators G i))).snd = _
  simp

end Equivariance

end

end GaloisForLFunctions.HTGeometry
