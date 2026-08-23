import GaloisForLFunctions.HTGeometry.ABHN.RatModIntTorsionDirectedSystem

/-!
# Hasse detection on the finite torsion layers of the circle group

Every element of `ℚ/ℤ` lies in a finite torsion layer.  Consequently, an additive invariant map
out of `ℚ/ℤ` is completely determined by its restrictions to all finite layers.  This packages the
directed torsion system as a faithful global-to-finite observation map.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- Restrict an additive map out of `ℚ/ℤ` to every finite torsion layer simultaneously. -/
def ratModIntTorsionRestrictionAddHom
    (A : Type*) [AddCommGroup A] :
    (RatModInt →+ A) →+ (∀ n : ℕ, ratModIntNTorsion n →+ A) where
  toFun f n := f.comp (ratModIntNTorsion n).subtype
  map_zero' := by
    ext n x
    rfl
  map_add' f g := by
    ext n x
    rfl

/-- Simultaneous restriction to all finite torsion layers is faithful. -/
theorem ratModIntTorsionRestrictionAddHom_injective
    (A : Type*) [AddCommGroup A] :
    Function.Injective (ratModIntTorsionRestrictionAddHom A) := by
  intro f g h
  apply ratModInt_addMonoidHom_ext_of_torsion f g
  intro n x
  exact DFunLike.congr_fun (congrFun h n) x

/-- Additive invariant maps out of `ℚ/ℤ` are equivalent to the finite-layer profiles they actually
realize. -/
noncomputable def ratModIntTorsionRestrictionHasseEquivRange
    (A : Type*) [AddCommGroup A] :
    (RatModInt →+ A) ≃+
      AddMonoidHom.range (ratModIntTorsionRestrictionAddHom A) :=
  AddEquiv.ofBijective
    (AddMonoidHom.rangeRestrict (ratModIntTorsionRestrictionAddHom A))
    ⟨fun _ _ h => ratModIntTorsionRestrictionAddHom_injective A
        (congrArg Subtype.val h),
      AddMonoidHom.rangeRestrict_surjective _⟩

/-- The realized-profile equivalence evaluates by simultaneous finite-layer restriction. -/
@[simp] theorem ratModIntTorsionRestrictionHasseEquivRange_apply
    (A : Type*) [AddCommGroup A] (f : RatModInt →+ A) :
    (ratModIntTorsionRestrictionHasseEquivRange A f).1 =
      ratModIntTorsionRestrictionAddHom A f := by
  rfl

/-- Two additive maps out of `ℚ/ℤ` agree exactly when they agree on every finite torsion layer. -/
theorem ratModInt_addMonoidHom_congr_hasse_iff
    {A : Type*} [AddGroup A] (f g : RatModInt →+ A) :
    (∀ (n : ℕ) (x : ratModIntNTorsion n), f x = g x) ↔ f = g := by
  constructor
  · exact ratModInt_addMonoidHom_ext_of_torsion f g
  · rintro rfl n x
    rfl

/-- An additive map out of `ℚ/ℤ` vanishes globally exactly when it vanishes on every finite torsion
layer. -/
theorem ratModInt_addMonoidHom_eq_zero_hasse_iff
    {A : Type*} [AddGroup A] (f : RatModInt →+ A) :
    (∀ (n : ℕ) (x : ratModIntNTorsion n), f x = 0) ↔ f = 0 := by
  rw [← ratModInt_addMonoidHom_congr_hasse_iff f 0]
  rfl

end


end GaloisForLFunctions.HTGeometry.ABHN
