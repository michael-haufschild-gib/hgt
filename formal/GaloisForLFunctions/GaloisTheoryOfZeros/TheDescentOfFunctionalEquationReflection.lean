import GaloisForLFunctions.GaloisTheoryOfZeros.TheIntegralZeroMotive

/-!
# Descent of functional-equation reflection

Integer combinations of original zeros retain a coefficient weight after
passing to their augmented group in `ℂ × ℤ`. Functional-equation reflection
acts on this group unconditionally. Its descent to the original relation
group is obstructed exactly by the weights of zero-valued relations.

Killing the embedded integer defect produces the universal quotient carrying
reflection. The defect vanishes exactly when coefficient weight descends,
or when the central half-weight subgroup meets the rotated centered integer
span trivially. A nonzero real-time exponential character admits reflection
exactly when this entire defect vanishes.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- Integer zero combinations with their coefficient weight retained. -/
def augmentedZeroRelationGroup : AddSubgroup (ℂ × ℤ) :=
  AddSubgroup.closure (Set.range fun q : XiZeroCopy => ((q.1 : ℂ),(1 : ℤ)))

/-- A zero with its unit coefficient weight. -/
def augmentedZeroRoot (q : XiZeroCopy) : augmentedZeroRelationGroup :=
  ⟨((q.1 : ℂ),1),AddSubgroup.subset_closure ⟨q,rfl⟩⟩

private theorem augmented_value_mem (x : ℂ × ℤ) (hx : x ∈ augmentedZeroRelationGroup) :
    x.1 ∈ rawZeroRelationGroup := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨q,rfl⟩ := hx
    exact (rawZeroRelationRoot q).property
  | zero => exact rawZeroRelationGroup.zero_mem
  | add x y _ _ hx hy => exact rawZeroRelationGroup.add_mem hx hy
  | neg x _ hx => exact rawZeroRelationGroup.neg_mem hx

/-- Forgetting coefficient weight recovers the original relation group. -/
def augmentedZeroProjection : augmentedZeroRelationGroup →+ rawZeroRelationGroup where
  toFun x := ⟨x.1.1,augmented_value_mem x x.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Total coefficient weight is well-defined on the augmented group. -/
def augmentedZeroWeight : augmentedZeroRelationGroup →+ ℤ where
  toFun x := x.1.2
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Every original zero combination has an augmented lift. -/
theorem augmentedZeroProjection_surjective : Function.Surjective augmentedZeroProjection := by
  have h (z : ℂ) (hz : z ∈ rawZeroRelationGroup) :
      ∃ n : ℤ, (z,n) ∈ augmentedZeroRelationGroup := by
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨q,rfl⟩ := hz
      exact ⟨1,(augmentedZeroRoot q).property⟩
    | zero => exact ⟨0,augmentedZeroRelationGroup.zero_mem⟩
    | add x y _ _ hx hy =>
      obtain ⟨m,hm⟩ := hx
      obtain ⟨n,hn⟩ := hy
      exact ⟨m+n,augmentedZeroRelationGroup.add_mem hm hn⟩
    | neg x _ hx =>
      obtain ⟨m,hm⟩ := hx
      exact ⟨-m,augmentedZeroRelationGroup.neg_mem hm⟩
  intro z
  obtain ⟨n,hn⟩ := h z z.property
  exact ⟨⟨((z : ℂ),n),hn⟩,rfl⟩

private def augmentedReflectionAmbient : (ℂ × ℤ) →+ (ℂ × ℤ) where
  toFun x := ((x.2 : ℂ)-x.1,x.2)
  map_zero' := by simp
  map_add' x y := by
    apply Prod.ext
    · change ((x.2+y.2 : ℤ) : ℂ)-(x.1+y.1) =
        ((x.2 : ℂ)-x.1)+((y.2 : ℂ)-y.1)
      rw [Int.cast_add]
      ring
    · rfl

private theorem augmented_reflection_mem (x : ℂ × ℤ)
    (hx : x ∈ augmentedZeroRelationGroup) :
    augmentedReflectionAmbient x ∈ augmentedZeroRelationGroup := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨q,rfl⟩ := hx
    change (((1 : ℤ) : ℂ)-(q.1 : ℂ),(1 : ℤ)) ∈ augmentedZeroRelationGroup
    rw [Int.cast_one]
    exact (augmentedZeroRoot (xiZeroCopyReflectEquiv q)).property
  | zero =>
    rw [map_zero]
    exact augmentedZeroRelationGroup.zero_mem
  | add x y _ _ hx hy =>
    rw [map_add]
    exact augmentedZeroRelationGroup.add_mem hx hy
  | neg x _ hx =>
    rw [map_neg]
    exact augmentedZeroRelationGroup.neg_mem hx

private theorem augmentedReflectionAmbient_square (x : ℂ × ℤ) :
    augmentedReflectionAmbient (augmentedReflectionAmbient x) = x := by
  apply Prod.ext
  · change (x.2 : ℂ)-((x.2 : ℂ)-x.1) = x.1
    ring
  · rfl

/-- Functional-equation reflection always acts on the augmented relation group. -/
def augmentedZeroReflection : augmentedZeroRelationGroup ≃+ augmentedZeroRelationGroup where
  toFun x := ⟨augmentedReflectionAmbient x,augmented_reflection_mem x x.property⟩
  invFun x := ⟨augmentedReflectionAmbient x,augmented_reflection_mem x x.property⟩
  left_inv x := Subtype.ext (augmentedReflectionAmbient_square x)
  right_inv x := Subtype.ext (augmentedReflectionAmbient_square x)
  map_add' x y := Subtype.ext (map_add augmentedReflectionAmbient (x : ℂ × ℤ) (y : ℂ × ℤ))

theorem augmentedZeroReflection_root (q : XiZeroCopy) :
    augmentedZeroReflection (augmentedZeroRoot q) = augmentedZeroRoot (xiZeroCopyReflectEquiv q) := by
  apply Subtype.ext
  apply Prod.ext
  · change ((1 : ℤ) : ℂ)-(q.1 : ℂ) = 1-(q.1 : ℂ)
    rw [Int.cast_one]
  · rfl

theorem augmentedZeroReflection_square (x : augmentedZeroRelationGroup) :
    augmentedZeroReflection (augmentedZeroReflection x) = x :=
  Subtype.ext (augmentedReflectionAmbient_square x)

/-- Integer values in the original relation group, generated by the functional-equation unit. -/
def rawZeroInteger : ℤ →+ rawZeroRelationGroup where
  toFun n := ⟨(n : ℂ),by
    simpa only [zsmul_eq_mul,Int.cast_one,mul_one] using
      rawZeroRelationGroup.zsmul_mem one_mem_rawZeroRelationGroup n⟩
  map_zero' := Subtype.ext (Int.cast_zero)
  map_add' m n := Subtype.ext (Int.cast_add m n)

/-- Reflection reverses value and retains the total coefficient weight. -/
theorem augmentedZeroReflection_value (x : augmentedZeroRelationGroup) :
    augmentedZeroProjection (augmentedZeroReflection x) =
      rawZeroInteger (augmentedZeroWeight x)-augmentedZeroProjection x := rfl

private def verticalInteger : ℤ →+ (ℂ × ℤ) where
  toFun n := (0,n)
  map_zero' := rfl
  map_add' _ _ := by simp

/-- Coefficient weights of all actual integer relations among the original zeros. -/
def zeroWeightDefect : AddSubgroup ℤ :=
  augmentedZeroRelationGroup.comap verticalInteger

/-- The same obstruction embedded as integer values in the original relation group. -/
def zeroReflectionDefect : AddSubgroup rawZeroRelationGroup :=
  zeroWeightDefect.map rawZeroInteger

private theorem weight_mem_defect (x : augmentedZeroRelationGroup)
    (hx : augmentedZeroProjection x = 0) : augmentedZeroWeight x ∈ zeroWeightDefect := by
  have hz : x.1.1 = 0 := congrArg (fun z : rawZeroRelationGroup => (z : ℂ)) hx
  change (0,x.1.2) ∈ augmentedZeroRelationGroup
  have he : (0,x.1.2) = x.1 := by exact Prod.ext hz.symm rfl
  rw [he]
  exact x.property

private theorem augmented_hom_ext {A : Type*} [AddGroup A]
    (f g : augmentedZeroRelationGroup →+ A)
    (h : ∀ q : XiZeroCopy, f (augmentedZeroRoot q) = g (augmentedZeroRoot q)) : f = g := by
  have he (x : ℂ × ℤ) (hx : x ∈ augmentedZeroRelationGroup) :
      f ⟨x,hx⟩ = g ⟨x,hx⟩ := by
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨q,rfl⟩ := hx
      exact h q
    | zero => exact (map_zero f).trans (map_zero g).symm
    | add x y hx hy hfx hfy =>
      change f (⟨x,hx⟩+⟨y,hy⟩) = g (⟨x,hx⟩+⟨y,hy⟩)
      rw [map_add,map_add,hfx,hfy]
    | neg x hx hfx =>
      change f (-⟨x,hx⟩) = g (-⟨x,hx⟩)
      rw [map_neg,map_neg,hfx]
  apply AddMonoidHom.ext
  intro x
  exact he x x.property

/-- Homomorphisms on the original zero group are determined by every zero generator. -/
theorem rawZeroHom_ext {A : Type*} [AddGroup A]
    (f g : rawZeroRelationGroup →+ A)
    (h : ∀ q : XiZeroCopy, f (rawZeroRelationRoot q) = g (rawZeroRelationRoot q)) : f = g := by
  have he : f.comp augmentedZeroProjection = g.comp augmentedZeroProjection :=
    augmented_hom_ext _ _ h
  apply AddMonoidHom.ext
  intro z
  obtain ⟨x,rfl⟩ := augmentedZeroProjection_surjective z
  exact DFunLike.congr_fun he x

/-- The kernel condition for reflection descent is exactly annihilation of the integer defect. -/
theorem zeroReflection_kernel_iff {A : Type*} [AddCommGroup A]
    (f : rawZeroRelationGroup →+ A) :
    augmentedZeroProjection.ker ≤
      ((f.comp augmentedZeroProjection).comp augmentedZeroReflection.toAddMonoidHom).ker ↔
      zeroReflectionDefect ≤ f.ker := by
  constructor
  · intro h z hz
    obtain ⟨n,hn,rfl⟩ := hz
    let x : augmentedZeroRelationGroup := ⟨(0,n),hn⟩
    have hx : augmentedZeroProjection x = 0 := rfl
    have he := h (show x ∈ augmentedZeroProjection.ker from hx)
    change f (augmentedZeroProjection (augmentedZeroReflection x)) = 0 at he
    rw [augmentedZeroReflection_value,hx,sub_zero] at he
    exact he
  · intro h x hx
    have hw := weight_mem_defect x hx
    have he : f (rawZeroInteger (augmentedZeroWeight x)) = 0 :=
      h ⟨augmentedZeroWeight x,hw,rfl⟩
    change f (augmentedZeroProjection (augmentedZeroReflection x)) = 0
    rw [augmentedZeroReflection_value,hx,sub_zero]
    exact he

/-- A map admits reflected zero values precisely when it kills the integer weight defect. -/
theorem zeroReflection_descent_iff {A : Type*} [AddCommGroup A]
    (f : rawZeroRelationGroup →+ A) :
    (∃ g : rawZeroRelationGroup →+ A, ∀ q : XiZeroCopy,
      g (rawZeroRelationRoot q) = f (rawZeroRelationRoot (xiZeroCopyReflectEquiv q))) ↔
      zeroReflectionDefect ≤ f.ker := by
  constructor
  · rintro ⟨g,hg⟩
    apply (zeroReflection_kernel_iff f).mp
    have he : g.comp augmentedZeroProjection =
        (f.comp augmentedZeroProjection).comp augmentedZeroReflection.toAddMonoidHom :=
      augmented_hom_ext _ _ (fun q => by
        change g (rawZeroRelationRoot q) =
          f (augmentedZeroProjection (augmentedZeroReflection (augmentedZeroRoot q)))
        rw [augmentedZeroReflection_root]
        exact hg q)
    intro x hx
    have h := DFunLike.congr_fun he x
    change g (augmentedZeroProjection x) =
      f (augmentedZeroProjection (augmentedZeroReflection x)) at h
    rw [show augmentedZeroProjection x = 0 from hx,map_zero] at h
    exact h.symm
  · intro h
    let F := (f.comp augmentedZeroProjection).comp augmentedZeroReflection.toAddMonoidHom
    have hk : augmentedZeroProjection.ker ≤ F.ker := (zeroReflection_kernel_iff f).mpr h
    let g := augmentedZeroProjection.liftOfSurjective augmentedZeroProjection_surjective ⟨F,hk⟩
    refine ⟨g,?_⟩
    intro q
    have he := AddMonoidHom.liftOfRightInverse_comp_apply augmentedZeroProjection
      (Function.surjInv augmentedZeroProjection_surjective)
      (Function.rightInverse_surjInv augmentedZeroProjection_surjective) ⟨F,hk⟩ (augmentedZeroRoot q)
    change g (rawZeroRelationRoot q) =
      f (augmentedZeroProjection (augmentedZeroReflection (augmentedZeroRoot q))) at he
    rw [augmentedZeroReflection_root] at he
    exact he

private theorem rawZeroRoot_reflect_twice (q : XiZeroCopy) :
    rawZeroRelationRoot (xiZeroCopyReflectEquiv (xiZeroCopyReflectEquiv q)) =
      rawZeroRelationRoot q := by
  apply Subtype.ext
  change 1-(1-(q.1 : ℂ)) = (q.1 : ℂ)
  ring

/-- A reflected map also kills the same defect, so reflection is closed on the admissible maps. -/
theorem reflectedZeroHom_annihilates {A : Type*} [AddCommGroup A]
    (f g : rawZeroRelationGroup →+ A)
    (hg : ∀ q : XiZeroCopy,
      g (rawZeroRelationRoot q) = f (rawZeroRelationRoot (xiZeroCopyReflectEquiv q))) :
    zeroReflectionDefect ≤ g.ker := by
  apply (zeroReflection_descent_iff g).mp
  refine ⟨f,?_⟩
  intro q
  rw [hg,rawZeroRoot_reflect_twice]

/-- The universal quotient retaining a well-defined functional-equation action. -/
abbrev ReflectionZeroQuotient := rawZeroRelationGroup ⧸ zeroReflectionDefect

/-- Projection to the universal reflection quotient. -/
def reflectionZeroProjection : rawZeroRelationGroup →+ ReflectionZeroQuotient :=
  QuotientAddGroup.mk' zeroReflectionDefect

private theorem reflectionZeroProjection_kills :
    zeroReflectionDefect ≤ reflectionZeroProjection.ker := by
  intro z hz
  exact (QuotientAddGroup.eq_zero_iff z).mpr hz

private def reflectedQuotientValues : rawZeroRelationGroup →+ ReflectionZeroQuotient :=
  ((zeroReflection_descent_iff reflectionZeroProjection).mpr reflectionZeroProjection_kills).choose

private theorem reflectedQuotientValues_root (q : XiZeroCopy) :
    reflectedQuotientValues (rawZeroRelationRoot q) =
      reflectionZeroProjection (rawZeroRelationRoot (xiZeroCopyReflectEquiv q)) :=
  ((zeroReflection_descent_iff reflectionZeroProjection).mpr reflectionZeroProjection_kills).choose_spec q

private def reflectionQuotientEnd : ReflectionZeroQuotient →+ ReflectionZeroQuotient :=
  QuotientAddGroup.lift zeroReflectionDefect reflectedQuotientValues
    (reflectedZeroHom_annihilates reflectionZeroProjection reflectedQuotientValues
      reflectedQuotientValues_root)

private theorem reflectionQuotientEnd_root (q : XiZeroCopy) :
    reflectionQuotientEnd (reflectionZeroProjection (rawZeroRelationRoot q)) =
      reflectionZeroProjection (rawZeroRelationRoot (xiZeroCopyReflectEquiv q)) :=
  reflectedQuotientValues_root q

private theorem reflectionQuotientEnd_square (x : ReflectionZeroQuotient) :
    reflectionQuotientEnd (reflectionQuotientEnd x) = x := by
  have he : (reflectionQuotientEnd.comp reflectionQuotientEnd).comp reflectionZeroProjection =
      reflectionZeroProjection := by
    apply rawZeroHom_ext
    intro q
    change reflectionQuotientEnd (reflectionQuotientEnd
      (reflectionZeroProjection (rawZeroRelationRoot q))) = _
    rw [reflectionQuotientEnd_root,reflectionQuotientEnd_root,rawZeroRoot_reflect_twice]
  induction x using QuotientAddGroup.induction_on with
  | H z => exact DFunLike.congr_fun he z

/-- Functional-equation reflection acts unconditionally on the universal quotient. -/
def zeroQuotientReflection : ReflectionZeroQuotient ≃+ ReflectionZeroQuotient where
  toFun := reflectionQuotientEnd
  invFun := reflectionQuotientEnd
  left_inv := reflectionQuotientEnd_square
  right_inv := reflectionQuotientEnd_square
  map_add' := map_add reflectionQuotientEnd

theorem zeroQuotientReflection_root (q : XiZeroCopy) :
    zeroQuotientReflection (reflectionZeroProjection (rawZeroRelationRoot q)) =
      reflectionZeroProjection (rawZeroRelationRoot (xiZeroCopyReflectEquiv q)) :=
  reflectionQuotientEnd_root q

/-- Every map admitting reflected zero values factors uniquely through the universal quotient. -/
theorem zeroReflectionQuotient_universal {A : Type*} [AddCommGroup A]
    (f : rawZeroRelationGroup →+ A) :
    (∃ g : rawZeroRelationGroup →+ A, ∀ q : XiZeroCopy,
      g (rawZeroRelationRoot q) = f (rawZeroRelationRoot (xiZeroCopyReflectEquiv q))) ↔
      ∃! h : ReflectionZeroQuotient →+ A, h.comp reflectionZeroProjection = f := by
  rw [zeroReflection_descent_iff]
  constructor
  · intro hf
    refine ⟨QuotientAddGroup.lift zeroReflectionDefect f hf,?_,?_⟩
    · rfl
    · intro h hh
      apply AddMonoidHom.ext
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H z => exact DFunLike.congr_fun hh z
  · rintro ⟨h,hh,_⟩
    intro z hz
    change f z = 0
    rw [← hh]
    change h (reflectionZeroProjection z) = 0
    rw [show reflectionZeroProjection z = 0 from reflectionZeroProjection_kills hz,map_zero]

/-- The defect vanishes exactly when coefficient weight descends to the original relation group. -/
theorem zeroWeightDefect_eq_bot_iff :
    zeroWeightDefect = ⊥ ↔
      ∃ d : rawZeroRelationGroup →+ ℤ, ∀ q : XiZeroCopy, d (rawZeroRelationRoot q) = 1 := by
  constructor
  · intro hD
    have hk : augmentedZeroProjection.ker ≤ augmentedZeroWeight.ker := by
      intro x hx
      have hw := weight_mem_defect x hx
      rw [hD] at hw
      exact hw
    let d := augmentedZeroProjection.liftOfSurjective augmentedZeroProjection_surjective
      ⟨augmentedZeroWeight,hk⟩
    refine ⟨d,?_⟩
    intro q
    exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ (augmentedZeroRoot q)
  · rintro ⟨d,hd⟩
    have he : d.comp augmentedZeroProjection = augmentedZeroWeight :=
      augmented_hom_ext _ _ hd
    apply le_antisymm
    · intro n hn
      let x : augmentedZeroRelationGroup := ⟨(0,n),hn⟩
      have hx := DFunLike.congr_fun he x
      change d 0 = n at hx
      rw [map_zero] at hx
      exact hx.symm
    · exact bot_le

private theorem rawZeroInteger_injective : Function.Injective rawZeroInteger := by
  intro m n h
  have he := congrArg (fun z : rawZeroRelationGroup => (z : ℂ)) h
  change (m : ℂ) = (n : ℂ) at he
  exact_mod_cast he

/-- The embedded reflection defect and the integer weight defect vanish together. -/
theorem zeroReflectionDefect_eq_bot_iff :
    zeroReflectionDefect = ⊥ ↔ zeroWeightDefect = ⊥ := by
  constructor
  · intro h
    apply le_antisymm
    · intro n hn
      have hm : rawZeroInteger n ∈ zeroReflectionDefect := ⟨n,hn,rfl⟩
      rw [h] at hm
      have hz : rawZeroInteger n = rawZeroInteger 0 := by
        rw [map_zero]
        exact hm
      exact rawZeroInteger_injective hz
    · exact bot_le
  · intro h
    apply le_antisymm
    · rintro z ⟨n,hn,rfl⟩
      rw [h] at hn
      change n = 0 at hn
      rw [hn,map_zero]
      exact (⊥ : AddSubgroup rawZeroRelationGroup).zero_mem
    · exact bot_le

/-- Reflection descends to the original integral zero group exactly when its weight defect vanishes. -/
theorem rawZeroReflection_exists_iff :
    (∃ τ : rawZeroRelationGroup ≃+ rawZeroRelationGroup, ∀ q : XiZeroCopy,
      τ (rawZeroRelationRoot q) = rawZeroRelationRoot (xiZeroCopyReflectEquiv q)) ↔
      zeroWeightDefect = ⊥ := by
  have hid : zeroReflectionDefect ≤ (AddMonoidHom.id rawZeroRelationGroup).ker ↔
      zeroReflectionDefect = ⊥ := by
    constructor
    · intro h
      exact le_antisymm h bot_le
    · intro h
      rw [h]
      exact bot_le
  rw [← zeroReflectionDefect_eq_bot_iff,← hid,← zeroReflection_descent_iff]
  constructor
  · rintro ⟨τ,hτ⟩
    exact ⟨τ.toAddMonoidHom,hτ⟩
  · rintro ⟨f,hf⟩
    change ∀ q : XiZeroCopy,
      f (rawZeroRelationRoot q) = rawZeroRelationRoot (xiZeroCopyReflectEquiv q) at hf
    have hs : f.comp f = AddMonoidHom.id rawZeroRelationGroup := by
      apply rawZeroHom_ext
      intro q
      change f (f (rawZeroRelationRoot q)) = rawZeroRelationRoot q
      rw [hf,hf,rawZeroRoot_reflect_twice]
    have hi : Function.Involutive f := fun x => DFunLike.congr_fun hs x
    refine ⟨{
      toFun := f
      invFun := f
      left_inv := hi
      right_inv := hi
      map_add' := map_add f },hf⟩

/-- Exactly the characters annihilating the integer defect support functional-equation reflection. -/
theorem rawMotive_reflection_iff (χ : RawZeroMotivePoint) :
    (∃ ψ : RawZeroMotivePoint, ∀ q : XiZeroCopy,
      ψ (rawZeroRelationRoot q) = χ (rawZeroRelationRoot (xiZeroCopyReflectEquiv q))) ↔
      ∀ n : ℤ, n ∈ zeroWeightDefect → χ (rawZeroInteger n) = 0 := by
  rw [zeroReflection_descent_iff]
  constructor
  · intro h n hn
    exact h ⟨n,hn,rfl⟩
  · intro h z hz
    obtain ⟨n,hn,rfl⟩ := hz
    exact h n hn

/-- The centered original value of an augmented zero combination. -/
def augmentedCenteredValue : augmentedZeroRelationGroup →+ ℂ where
  toFun x := x.1.1-(x.1.2 : ℂ)/2
  map_zero' := by simp
  map_add' x y := by
    change x.1.1+y.1.1-((x.1.2+y.1.2 : ℤ) : ℂ)/2 =
      (x.1.1-(x.1.2 : ℂ)/2)+(y.1.1-(y.1.2 : ℂ)/2)
    rw [Int.cast_add]
    ring

private theorem centered_root_value (q : XiZeroCopy) :
    centeredRelationRotation (zeroRelationRoot q) = (q.1 : ℂ)-1/2 := by
  have h := congrArg (fun z : halfWeightedZeroGroup => (z : ℂ)) (rawZeroInclusion_root q)
  change (q.1 : ℂ) = 1/2+centeredRelationRotation (zeroRelationRoot q) at h
  linear_combination -h

/-- Centering the augmented group gives exactly the full rotated centered integer span. -/
theorem augmentedCenteredValue_range :
    augmentedCenteredValue.range = centeredRelationRotation.range := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    have h (z : ℂ × ℤ) (hz : z ∈ augmentedZeroRelationGroup) :
        augmentedCenteredValue ⟨z,hz⟩ ∈ centeredRelationRotation.range := by
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨q,rfl⟩ := hz
        refine ⟨zeroRelationRoot q,?_⟩
        change centeredRelationRotation (zeroRelationRoot q) =
          (q.1 : ℂ)-((1 : ℤ) : ℂ)/2
        rw [Int.cast_one,centered_root_value]
      | zero =>
        change augmentedCenteredValue 0 ∈ centeredRelationRotation.range
        rw [map_zero]
        exact centeredRelationRotation.range.zero_mem
      | add x y hx hy hcx hcy =>
        change augmentedCenteredValue (⟨x,hx⟩+⟨y,hy⟩) ∈ _
        rw [map_add]
        exact centeredRelationRotation.range.add_mem hcx hcy
      | neg x hx hcx =>
        change augmentedCenteredValue (-⟨x,hx⟩) ∈ _
        rw [map_neg]
        exact centeredRelationRotation.range.neg_mem hcx
    exact h x x.property
  · rintro _ ⟨x,rfl⟩
    have h (z : fullFibreZeroExtension) (hz : z ∈ zeroRelationGroup) :
        centeredRelationRotation ⟨z,hz⟩ ∈ augmentedCenteredValue.range := by
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨q,rfl⟩ := hz
        refine ⟨augmentedZeroRoot q,?_⟩
        change (q.1 : ℂ)-((1 : ℤ) : ℂ)/2 = centeredRelationRotation (zeroRelationRoot q)
        rw [Int.cast_one,centered_root_value]
      | zero =>
        change centeredRelationRotation 0 ∈ augmentedCenteredValue.range
        rw [map_zero]
        exact augmentedCenteredValue.range.zero_mem
      | add x y hx hy hcx hcy =>
        change centeredRelationRotation (⟨x,hx⟩+⟨y,hy⟩) ∈ _
        rw [map_add]
        exact augmentedCenteredValue.range.add_mem hcx hcy
      | neg x hx hcx =>
        change centeredRelationRotation (-⟨x,hx⟩) ∈ _
        rw [map_neg]
        exact augmentedCenteredValue.range.neg_mem hcx
    exact h x x.property

private theorem augmented_unit_mem : ((1 : ℂ),(2 : ℤ)) ∈ augmentedZeroRelationGroup := by
  obtain ⟨ρ,hρ⟩ := xiDivisorSupport_infinite.nonempty
  let q : XiZeroCopy := ⟨⟨ρ,hρ⟩,⟨0,by
    have hp := xi_divisor_pos_on_support ⟨ρ,hρ⟩
    omega⟩⟩
  have h := augmentedZeroRelationGroup.add_mem (augmentedZeroRoot q).property
    (augmentedZeroRoot (xiZeroCopyReflectEquiv q)).property
  have he : ((q.1 : ℂ),(1 : ℤ))+(((xiZeroCopyReflectEquiv q).1 : ℂ),1) = (1,2) := by
    apply Prod.ext
    · change (q.1 : ℂ)+(1-(q.1 : ℂ)) = 1
      ring
    · rfl
  exact he ▸ h

/-- The exact obstruction is an intersection of the central half-weight with the centered integer span. -/
theorem zeroWeightDefect_eq_bot_iff_centered :
    zeroWeightDefect = ⊥ ↔
      ∀ m : ℤ, (m : ℂ)/2 ∈ centeredRelationRotation.range → m = 0 := by
  constructor
  · intro hD m hm
    rw [← augmentedCenteredValue_range] at hm
    obtain ⟨x,hx⟩ := hm
    change x.1.1-(x.1.2 : ℂ)/2 = (m : ℂ)/2 at hx
    have hr := augmentedZeroRelationGroup.sub_mem
      (augmentedZeroRelationGroup.zsmul_mem x.property (2 : ℤ))
      (augmentedZeroRelationGroup.zsmul_mem augmented_unit_mem (x.1.2+m))
    have he : (2 : ℤ) • x.1-(x.1.2+m) • ((1 : ℂ),(2 : ℤ)) = (0,-2*m) := by
      apply Prod.ext
      · change (2 : ℤ) • x.1.1-(x.1.2+m) • (1 : ℂ) = 0
        simp only [zsmul_eq_mul,Int.cast_ofNat,Int.cast_add,mul_one]
        linear_combination 2*hx
      · change (2 : ℤ) • x.1.2-(x.1.2+m) • (2 : ℤ) = -2*m
        simp only [zsmul_eq_mul,Int.cast_id]
        ring
    have hd : -2*m ∈ zeroWeightDefect := by
      change (0,-2*m) ∈ augmentedZeroRelationGroup
      rw [← he]
      exact hr
    rw [hD] at hd
    change -2*m = 0 at hd
    omega
  · intro h
    apply le_antisymm
    · intro n hn
      let x : augmentedZeroRelationGroup := ⟨(0,n),hn⟩
      have hm : (-n : ℂ)/2 ∈ centeredRelationRotation.range := by
        rw [← augmentedCenteredValue_range]
        refine ⟨x,?_⟩
        change (0 : ℂ)-(n : ℂ)/2 = (-n : ℂ)/2
        ring
      have hz : -n = 0 := h (-n) (by simpa only [Int.cast_neg] using hm)
      exact neg_eq_zero.mp hz
    · exact bot_le

private theorem rawZeroMotiveFlow_integer_zero_iff (u : ℝ) (n : ℤ) :
    rawZeroMotiveFlow u (rawZeroInteger n) = 0 ↔ u = 0 ∨ n = 0 := by
  have he : ((rawZeroMotiveFlow u (rawZeroInteger n)).toMul : ℂ) =
      (Real.exp (u*(n : ℝ)) : ℂ) := by
    change Complex.exp ((u : ℂ)*(n : ℂ)) = _
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  constructor
  · intro h
    have hc := congrArg (fun v : Additive ℂˣ => (v.toMul : ℂ)) h
    change ((rawZeroMotiveFlow u (rawZeroInteger n)).toMul : ℂ) = 1 at hc
    rw [he] at hc
    have hr : Real.exp (u*(n : ℝ)) = 1 := Complex.ofReal_injective hc
    rcases mul_eq_zero.mp ((Real.exp_eq_one_iff _).mp hr) with hu | hn
    · exact Or.inl hu
    · exact Or.inr (by exact_mod_cast hn)
  · rintro (rfl | rfl)
    · apply Additive.toMul.injective
      apply Units.ext
      change Complex.exp ((0 : ℂ)*(n : ℂ)) = 1
      rw [zero_mul,Complex.exp_zero]
    · rw [map_zero,map_zero]

/-- A nonzero real-time character admits reflection exactly when reflection descends on the full group. -/
theorem rawZeroMotiveFlow_reflection_iff (u : ℝ) :
    (∃ ψ : RawZeroMotivePoint, ∀ q : XiZeroCopy,
      ψ (rawZeroRelationRoot q) =
        rawZeroMotiveFlow u (rawZeroRelationRoot (xiZeroCopyReflectEquiv q))) ↔
      u = 0 ∨ zeroWeightDefect = ⊥ := by
  rw [rawMotive_reflection_iff]
  constructor
  · intro h
    by_cases hu : u = 0
    · exact Or.inl hu
    · right
      apply le_antisymm
      · intro n hn
        exact ((rawZeroMotiveFlow_integer_zero_iff u n).mp (h n hn)).resolve_left hu
      · exact bot_le
  · rintro (hu | hD) n hn
    · exact (rawZeroMotiveFlow_integer_zero_iff u n).mpr (Or.inl hu)
    · rw [hD] at hn
      exact (rawZeroMotiveFlow_integer_zero_iff u n).mpr (Or.inr hn)

end GaloisForLFunctions.GaloisTheoryOfZeros
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.augmentedZeroProjection_surjective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.augmentedZeroReflection
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroReflection_descent_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroQuotientReflection
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroReflectionQuotient_universal
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroWeightDefect_eq_bot_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rawZeroReflection_exists_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rawMotive_reflection_iff

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroWeightDefect_eq_bot_iff_centered

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rawZeroMotiveFlow_reflection_iff
