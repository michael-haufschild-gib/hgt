import GaloisForLFunctions.RHTower.DeningerTreeVanishing

/-!
# Homology of the regular representation and transfer along isomorphisms

The permutation representation on the trivial subgroup is the regular representation, so its
homology vanishes in positive degrees, and homology with trivial coefficients only depends on the
isomorphism class of the group.

* `deningerTrivialHomologyIso` : transfer along a group isomorphism.
* `deningerIsZero_regular` : the regular representation has no higher homology.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits

universe u

/-- Homology with trivial coefficients transfers along an isomorphism of groups. -/
noncomputable def deningerTrivialHomologyIso {G H : Type u} [Group G] [Group H] (e : G ≃* H)
    (k : Type u) [CommRing k] (n : ℕ) :
    groupHomology (Rep.trivial k G k) n ≅ groupHomology (Rep.trivial k H k) n :=
  groupHomology.mapIso e (LinearEquiv.refl k k) (fun _ => rfl) n

/-- **The regular representation has no homology in positive degrees.**  It is the permutation
representation on the cosets of the trivial subgroup, so Shapiro's lemma computes its homology as
that of the trivial group. -/
theorem deningerIsZero_regular (G k : Type u) [Group G] [CommRing k] [DecidableEq G] (n : ℕ) :
    IsZero (groupHomology (Rep.ofMulAction k G (G ⧸ (⊥ : Subgroup G))) (n + 1)) :=
  IsZero.of_iso (isZero_groupHomology_succ_of_subsingleton
      (Rep.trivial k (⊥ : Subgroup G) k) n)
    (deningerPermutationShapiro (⊥ : Subgroup G) (n + 1))

/-- The left regular representation has no homology in positive degrees. -/
theorem deningerIsZero_leftRegular (G k : Type u) [Group G] [CommRing k] [DecidableEq G] (n : ℕ) :
    IsZero (groupHomology (Rep.ofMulAction k G G) (n + 1)) :=
  IsZero.of_iso (deningerIsZero_regular G k n)
    ((groupHomology.functor k G (n + 1)).mapIso
      (deningerPermRepIsoOfEquiv k (QuotientGroup.quotientBot (G := G)).toEquiv.symm
        (fun _ _ => rfl)))

section Cyclic

variable {Z : Type u} [Group Z] (e : Z ≃* Multiplicative ℤ) (k : Type u) [CommRing k]

/-- The generator of an infinite cyclic group determined by an isomorphism with `ℤ`. -/
def deningerZGen : Z := e.symm (Multiplicative.ofAdd (1 : ℤ))

/-- The exponent of an element of an infinite cyclic group. -/
def deningerZVal (x : Z) : ℤ := Multiplicative.toAdd (e x)

theorem deningerZVal_mul_gen (x : Z) :
    deningerZVal e (x * deningerZGen e) = deningerZVal e x + 1 := by
  show Multiplicative.toAdd (e (x * e.symm (Multiplicative.ofAdd (1 : ℤ)))) = _
  rw [map_mul, MulEquiv.apply_symm_apply]
  rfl

theorem deningerZVal_injective : Function.Injective (deningerZVal e) := fun _ _ h =>
  e.injective (Multiplicative.toAdd.injective h)

/-- Right multiplication by `t - 1` on the group algebra of an infinite cyclic group. -/
noncomputable def deningerZBoundary : Rep.ofMulAction k Z Z ⟶ Rep.ofMulAction k Z Z :=
  deningerPermHom k
    (fun x => MonoidAlgebra.single (x * deningerZGen e) (1 : k) -
      MonoidAlgebra.single x (1 : k))
    (fun (g : Z) x => by
      show MonoidAlgebra.single (g * x * deningerZGen e) (1 : k) -
          MonoidAlgebra.single (g * x) (1 : k) = _
      rw [map_sub, Representation.ofMulAction_single, Representation.ofMulAction_single]
      simp [smul_eq_mul, mul_assoc])

/-- The augmentation of the group algebra of an infinite cyclic group. -/
noncomputable def deningerZAug : Rep.ofMulAction k Z Z ⟶ Rep.trivial k Z k :=
  Rep.ofHom ⟨Finsupp.lift k k Z (fun _ => (1 : k)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap, fun g => by
    refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
    show Finsupp.lift k k Z (fun _ => (1 : k))
        ((MonoidAlgebra.coeffLinearEquiv k)
          (Representation.ofMulAction k Z Z g (MonoidAlgebra.single x (1 : k)))) = _
    rw [Representation.ofMulAction_single]
    show Finsupp.lift k k Z (fun _ => (1 : k)) (Finsupp.single (g * x) (1 : k)) =
      (Rep.trivial k Z k).ρ g
        (Finsupp.lift k k Z (fun _ => (1 : k)) (Finsupp.single x (1 : k)))
    rw [Finsupp.lift_apply, Finsupp.lift_apply, Finsupp.sum_single_index (by simp),
      Finsupp.sum_single_index (by simp)]
    rfl⟩

theorem deningerZAug_single (x : Z) (c : k) :
    (deningerZAug (Z := Z) k).hom (MonoidAlgebra.single x c) = c := by
  show Finsupp.lift k k Z (fun _ => (1 : k)) (Finsupp.single x c) = c
  rw [Finsupp.lift_apply, Finsupp.sum_single_index (by simp)]
  simp

theorem deningerZBoundary_single (x : Z) (c : k) :
    (deningerZBoundary e k).hom (MonoidAlgebra.single x c) =
      c • (MonoidAlgebra.single (x * deningerZGen e) (1 : k) -
        MonoidAlgebra.single x (1 : k)) :=
  deningerPermLift_single k _ x c

theorem deningerZAug_comp_boundary :
    deningerZBoundary e k ≫ deningerZAug (Z := Z) k = 0 := by
  ext x
  show (deningerZAug (Z := Z) k).hom ((deningerZBoundary e k).hom (MonoidAlgebra.single x (1 : k))) = 0
  rw [deningerZBoundary_single, map_smul, map_sub, deningerZAug_single, deningerZAug_single]
  simp

theorem deningerZAug_surjective : Function.Surjective (deningerZAug (Z := Z) k).hom := fun c =>
  ⟨MonoidAlgebra.single (1 : Z) c, deningerZAug_single (Z := Z) k _ c⟩

/-- The coefficient of a basis element in the image of a chain under a map defined on the basis. -/
theorem deningerPermLift_coeff {X X' : Type u} (F : X → MonoidAlgebra k X')
    (f : MonoidAlgebra k X) (y : X') :
    (MonoidAlgebra.coeffLinearEquiv k) (deningerPermLift k F f) y =
      (MonoidAlgebra.coeffLinearEquiv k f).sum
        (fun x c => c * (MonoidAlgebra.coeffLinearEquiv k (F x)) y) := by
  have key : (Finsupp.lapply (R := k) y ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap) ∘ₗ
        deningerPermLift k F =
      Finsupp.lift k k X (fun x => (MonoidAlgebra.coeffLinearEquiv k (F x)) y) ∘ₗ
        (MonoidAlgebra.coeffLinearEquiv k).toLinearMap := by
    refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
    show (MonoidAlgebra.coeffLinearEquiv k)
        (deningerPermLift k F (MonoidAlgebra.single x (1 : k))) y =
      Finsupp.lift k k X (fun x => (MonoidAlgebra.coeffLinearEquiv k (F x)) y)
        ((MonoidAlgebra.coeffLinearEquiv k) (MonoidAlgebra.single x (1 : k)))
    rw [deningerPermLift_single, one_smul,
      show (MonoidAlgebra.coeffLinearEquiv k) (MonoidAlgebra.single x (1 : k)) =
        Finsupp.single x (1 : k) from rfl,
      Finsupp.lift_apply, Finsupp.sum_single_index (by simp), one_smul]
  have hkey := DFunLike.congr_fun key f
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lapply_apply,
    LinearEquiv.coe_coe] at hkey
  rw [hkey, Finsupp.lift_apply]
  exact Finsupp.sum_congr fun x _ => by rw [smul_eq_mul]

/-- The `t - 1` map on the group algebra of an infinite cyclic group is injective. -/
theorem deningerZBoundary_injective :
    Function.Injective (deningerZBoundary e k).hom := by
  classical
  intro f₁ f₂ hf
  by_contra hne
  set f := f₁ - f₂ with hfdef
  have hf0 : (deningerZBoundary e k).hom f = 0 := by rw [hfdef, map_sub, hf, sub_self]
  have hfne : f ≠ 0 := fun h => hne (sub_eq_zero.1 h)
  set F := (MonoidAlgebra.coeffLinearEquiv k) f with hF
  have hFne : F ≠ 0 := fun h => hfne ((MonoidAlgebra.coeffLinearEquiv k).map_eq_zero_iff.1 h)
  obtain ⟨x₀, hx₀, hmax⟩ := F.support.exists_max_image (deningerZVal e)
    (Finsupp.support_nonempty_iff.2 hFne)
  have hx₀ne : F x₀ ≠ 0 := Finsupp.mem_support_iff.1 hx₀
  set y := x₀ * deningerZGen e with hy
  have hval : deningerZVal e y = deningerZVal e x₀ + 1 := deningerZVal_mul_gen e x₀
  have hgone : y ∉ F.support := fun hmem => by
    have hle := hmax _ hmem
    omega
  have hne0 : x₀ ≠ y := fun hc => by
    have hcv := congrArg (deningerZVal e) hc
    omega
  set Fn : Z → MonoidAlgebra k Z := fun x =>
    MonoidAlgebra.single (x * deningerZGen e) (1 : k) - MonoidAlgebra.single x (1 : k) with hFn
  have hcoeff := deningerPermLift_coeff k Fn f y
  rw [show deningerPermLift k Fn f = (deningerZBoundary e k).hom f from rfl, hf0, ← hF] at hcoeff
  have hsum : F.sum (fun x c => c * (MonoidAlgebra.coeffLinearEquiv k (Fn x)) y) =
      F x₀ * (MonoidAlgebra.coeffLinearEquiv k (Fn x₀)) y :=
    Finsupp.sum_eq_single x₀ (fun x hx hxne => by
      have h1 : x * deningerZGen e ≠ y := fun hc => hxne (mul_right_cancel hc)
      have h2 : x ≠ y := fun hc => hgone (hc ▸ Finsupp.mem_support_iff.2 hx)
      simp [hFn, map_sub, h1, h2]) (fun _ => by simp)
  have hone : (MonoidAlgebra.coeffLinearEquiv k (Fn x₀)) y = 1 := by
    simp [hFn, map_sub, hne0, ← hy]
  rw [hsum, hone, mul_one] at hcoeff
  exact hx₀ne (by simpa using hcoeff.symm)

/-- The powers of the generator. -/
def deningerZPow (n : ℤ) : Z := e.symm (Multiplicative.ofAdd n)

theorem deningerZPow_succ (n : ℤ) :
    deningerZPow e (n + 1) = deningerZPow e n * deningerZGen e := by
  show e.symm (Multiplicative.ofAdd (n + 1)) = _
  rw [show (Multiplicative.ofAdd (n + 1)) =
    Multiplicative.ofAdd n * Multiplicative.ofAdd (1 : ℤ) from rfl, map_mul]
  rfl

theorem deningerZPow_zero : deningerZPow e 0 = 1 := by
  show e.symm (Multiplicative.ofAdd (0 : ℤ)) = 1
  rw [show (Multiplicative.ofAdd (0 : ℤ)) = 1 from rfl, map_one]

theorem deningerZPow_val (x : Z) : deningerZPow e (deningerZVal e x) = x := by
  show e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (e x))) = x
  rw [show (Multiplicative.ofAdd (Multiplicative.toAdd (e x))) = e x from rfl,
    MulEquiv.symm_apply_apply]

theorem deningerZ_pow_sub_one (n : ℤ) :
    MonoidAlgebra.single (deningerZPow e n) (1 : k) - MonoidAlgebra.single (1 : Z) (1 : k) ∈
      LinearMap.range (deningerZBoundary e k).hom.toLinearMap := by
  induction n using Int.induction_on with
  | zero =>
    rw [deningerZPow_zero, sub_self]
    exact Submodule.zero_mem _
  | succ m ih =>
    have hb : (deningerZBoundary e k).hom.toLinearMap
          (MonoidAlgebra.single (deningerZPow e m) (1 : k)) =
        MonoidAlgebra.single (deningerZPow e ((m : ℤ) + 1)) (1 : k) -
          MonoidAlgebra.single (deningerZPow e m) (1 : k) := by
      rw [show (deningerZBoundary e k).hom.toLinearMap
        (MonoidAlgebra.single (deningerZPow e m) (1 : k)) =
          (deningerZBoundary e k).hom (MonoidAlgebra.single (deningerZPow e m) (1 : k)) from rfl,
        deningerZBoundary_single, one_smul, deningerZPow_succ]
    have hmem := Submodule.add_mem _ (LinearMap.mem_range.2 ⟨_, hb⟩) ih
    convert hmem using 1
    abel
  | pred m ih =>
    have hsucc : deningerZPow e (-(m : ℤ) - 1) * deningerZGen e = deningerZPow e (-(m : ℤ)) := by
      rw [← deningerZPow_succ]
      congr 1
      omega
    have hb : (deningerZBoundary e k).hom.toLinearMap
          (MonoidAlgebra.single (deningerZPow e (-(m : ℤ) - 1)) (1 : k)) =
        MonoidAlgebra.single (deningerZPow e (-(m : ℤ))) (1 : k) -
          MonoidAlgebra.single (deningerZPow e (-(m : ℤ) - 1)) (1 : k) := by
      rw [show (deningerZBoundary e k).hom.toLinearMap
        (MonoidAlgebra.single (deningerZPow e (-(m : ℤ) - 1)) (1 : k)) =
          (deningerZBoundary e k).hom
            (MonoidAlgebra.single (deningerZPow e (-(m : ℤ) - 1)) (1 : k)) from rfl,
        deningerZBoundary_single, one_smul, hsucc]
    have hmem := Submodule.sub_mem _ ih (LinearMap.mem_range.2 ⟨_, hb⟩)
    convert hmem using 1
    abel

theorem deningerZ_single_sub_one (x : Z) :
    MonoidAlgebra.single x (1 : k) - MonoidAlgebra.single (1 : Z) (1 : k) ∈
      LinearMap.range (deningerZBoundary e k).hom.toLinearMap := by
  have := deningerZ_pow_sub_one e k (deningerZVal e x)
  rwa [deningerZPow_val] at this

/-- **The augmentation kernel is the image of `t - 1`.** -/
theorem deningerZ_exact (f : MonoidAlgebra k Z) (hf : (deningerZAug (Z := Z) k).hom f = 0) :
    f ∈ LinearMap.range (deningerZBoundary e k).hom.toLinearMap := by
  have general : ∀ g : MonoidAlgebra k Z,
      g - (deningerZAug (Z := Z) k).hom g • MonoidAlgebra.single (1 : Z) (1 : k) ∈
        LinearMap.range (deningerZBoundary e k).hom.toLinearMap := by
    intro g
    obtain ⟨g', rfl⟩ := (MonoidAlgebra.coeffLinearEquiv k).symm.surjective g
    refine Finsupp.induction_linear g' ?_ ?_ ?_
    · simp
    · intro a b ha hb
      rw [map_add, map_add, add_smul]
      have hmem := Submodule.add_mem _ ha hb
      convert hmem using 1
      abel
    · intro x c
      rw [show (MonoidAlgebra.coeffLinearEquiv k).symm (Finsupp.single x c) =
        MonoidAlgebra.single x c from rfl, deningerZAug_single]
      have hmem := Submodule.smul_mem _ c (deningerZ_single_sub_one e k x)
      convert hmem using 1
      simp [smul_sub, MonoidAlgebra.smul_single]
  have hmem := general f
  rwa [hf, zero_smul, sub_zero] at hmem

/-- The length one resolution of the trivial representation over the group algebra of an infinite
cyclic group. -/
noncomputable def deningerZShortComplex : ShortComplex (Rep k Z) :=
  ShortComplex.mk (deningerZBoundary e k) (deningerZAug (Z := Z) k)
    (deningerZAug_comp_boundary e k)

theorem deningerZShortComplex_shortExact : (deningerZShortComplex e k).ShortExact where
  exact := (forget₂ (Rep k Z) (ModuleCat k)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun x hx =>
      LinearMap.mem_range.1 (deningerZ_exact e k x hx)
  mono_f := (Rep.mono_iff_injective _).2 (deningerZBoundary_injective e k)
  epi_g := (Rep.epi_iff_surjective _).2 (deningerZAug_surjective (Z := Z) k)

/-- **The homology of an infinite cyclic group vanishes above degree one.**  Both neighbouring
terms of the long exact sequence are the homology of the regular representation. -/
theorem deningerZ_isZero (e' : Z ≃* Multiplicative ℤ) [DecidableEq Z] (n : ℕ) :
    IsZero (groupHomology (Rep.trivial k Z k) (n + 2)) :=
  deningerGroupHomology_isZero_X₃ (deningerZShortComplex_shortExact e' k) (n + 2) (n + 1) rfl
    (deningerIsZero_leftRegular Z k (n + 1)) (deningerIsZero_leftRegular Z k n)

end Cyclic

end RHTower
