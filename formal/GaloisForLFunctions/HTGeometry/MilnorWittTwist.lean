import GaloisForLFunctions.HTGeometry.MilnorWittFormAction
import Mathlib.Data.Finsupp.Basic

/-!
# Twisted Milnor--Witt `K`-theory

A Milnor--Witt class is only defined up to the unit forms `⟨u⟩`, so the coefficients of an oriented
theory are not `K_n^{MW}(F)` itself but its twist by a line: the coefficients are indexed by the
nonzero vectors of a one-dimensional space, and rescaling the index by `u` multiplies the
coefficient by `⟨u⟩`.  Formally the twist by an `Fˣ`-set `T` is the group of finitely supported
`T`-indexed families of Milnor--Witt classes modulo exactly those relations.

A base point of `T` on which `Fˣ` acts simply transitively — that is, a basis of the line —
trivializes the twist, and two base points differing by `u` give trivializations differing by
`⟨u⟩`.  This is the determinant twist of an oriented fundamental class: a chosen generator of the
determinant line makes the class an honest Milnor--Witt class, and changing the generator changes
it by the unit form of the ratio.

* `MWTwist` : **`K_n^{MW}(F)` twisted by an `Fˣ`-set.**
* `mwTwistMk_smul` : the defining relation.
* `mwTwistEquiv` : **a simply transitive base point trivializes the twist.**
* `mwTwistTriv_smul` : **changing the base point by `u` changes the trivialization by `⟨u⟩`.**
* `mwLineTwistEquiv` : the twist by the nonzero vectors of a line, trivialized by a basis vector.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Twist

variable (F : Type*) [Field F] (n : ℤ) (T : Type*) [MulAction Fˣ T]

/-- The relations of the twist: moving the index by `u` multiplies the coefficient by `⟨u⟩`. -/
def mwTwistRel : AddSubgroup (T →₀ MilnorWittKDeg F n) :=
  AddSubgroup.closure {x | ∃ (u : Fˣ) (t : T) (m : MilnorWittKDeg F n),
    x = Finsupp.single (u • t) m - Finsupp.single t (mwFormAct u n m)}

/-- **Milnor--Witt `K`-theory in degree `n`, twisted by an `Fˣ`-set.** -/
def MWTwist : Type _ := (T →₀ MilnorWittKDeg F n) ⧸ mwTwistRel F n T

instance : AddCommGroup (MWTwist F n T) := QuotientAddGroup.Quotient.addCommGroup _

/-- The coefficient `m` placed at the index `t`. -/
def mwTwistMk (t : T) (m : MilnorWittKDeg F n) : MWTwist F n T :=
  QuotientAddGroup.mk (Finsupp.single t m)

/-- Placing a coefficient at a fixed index is additive. -/
def mwTwistMkHom (t : T) : MilnorWittKDeg F n →+ MWTwist F n T where
  toFun := mwTwistMk F n T t
  map_zero' := by
    show QuotientAddGroup.mk (Finsupp.single t (0 : MilnorWittKDeg F n)) = 0
    rw [Finsupp.single_zero]
    rfl
  map_add' m m' := by
    show QuotientAddGroup.mk (Finsupp.single t (m + m')) = _
    rw [Finsupp.single_add]
    rfl

@[simp]
theorem mwTwistMkHom_apply (t : T) (m : MilnorWittKDeg F n) :
    mwTwistMkHom F n T t m = mwTwistMk F n T t m := rfl

/-- **The defining relation of the twist**: moving the index by `u` multiplies the coefficient by
the unit form `⟨u⟩`. -/
theorem mwTwistMk_smul (u : Fˣ) (t : T) (m : MilnorWittKDeg F n) :
    mwTwistMk F n T (u • t) m = mwTwistMk F n T t (mwFormAct u n m) := by
  have hmem : (Finsupp.single (u • t) m - Finsupp.single t (mwFormAct u n m))
      ∈ mwTwistRel F n T := AddSubgroup.subset_closure ⟨u, t, m, rfl⟩
  have hmap : (QuotientAddGroup.mk' (mwTwistRel F n T))
      (Finsupp.single (u • t) m - Finsupp.single t (mwFormAct u n m)) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).2 hmem
  rw [map_sub, sub_eq_zero] at hmap
  exact hmap

/-- **Extensionality**: two additive maps out of the twist agree once they agree on the
coefficients placed at each index. -/
theorem mwTwist_hom_ext {A : Type*} [AddCommGroup A] {f g : MWTwist F n T →+ A}
    (h : ∀ (t : T) (m : MilnorWittKDeg F n),
      f (mwTwistMk F n T t m) = g (mwTwistMk F n T t m)) : f = g := by
  refine AddMonoidHom.ext fun x => ?_
  refine QuotientAddGroup.induction_on x fun v => ?_
  have hfin : f.comp (QuotientAddGroup.mk' (mwTwistRel F n T))
      = g.comp (QuotientAddGroup.mk' (mwTwistRel F n T)) :=
    Finsupp.addHom_ext fun t m => h t m
  exact DFunLike.congr_fun hfin v

end Twist

section Trivialization

variable {F : Type*} [Field F] {n : ℤ} {T : Type*} [MulAction Fˣ T]
variable (t₀ : T) (hsurj : ∀ t : T, ∃ u : Fˣ, t = u • t₀)

/-- The unit carrying the base point to a given index. -/
def mwTwistCoord (t : T) : Fˣ := Classical.choose (hsurj t)

theorem mwTwistCoord_spec (t : T) : t = mwTwistCoord t₀ hsurj t • t₀ :=
  Classical.choose_spec (hsurj t)

theorem mwTwistCoord_base (hfree : ∀ u v : Fˣ, u • t₀ = v • t₀ → u = v) :
    mwTwistCoord t₀ hsurj t₀ = 1 := by
  refine hfree _ _ ?_
  rw [← mwTwistCoord_spec t₀ hsurj t₀, one_smul]

theorem mwTwistCoord_smul (hfree : ∀ u v : Fˣ, u • t₀ = v • t₀ → u = v) (u : Fˣ) (t : T) :
    mwTwistCoord t₀ hsurj (u • t) = u * mwTwistCoord t₀ hsurj t := by
  refine hfree _ _ ?_
  rw [← mwTwistCoord_spec t₀ hsurj (u • t), mul_smul, ← mwTwistCoord_spec t₀ hsurj t]

/-- The trivialization on finitely supported families. -/
def mwTwistTrivPre :
    (T →₀ MilnorWittKDeg F n) →+ MilnorWittKDeg F n :=
  Finsupp.liftAddHom fun t => mwFormAct (mwTwistCoord t₀ hsurj t) n

theorem mwTwistTrivPre_single (t : T) (m : MilnorWittKDeg F n) :
    mwTwistTrivPre t₀ hsurj (Finsupp.single t m) = mwFormAct (mwTwistCoord t₀ hsurj t) n m :=
  Finsupp.liftAddHom_apply_single _ _ _

/-- **The relations of the twist are killed by the trivialization**, because the coordinate of a
translated index is the translated coordinate and the unit forms compose multiplicatively. -/
theorem mwTwistTrivPre_rel (hfree : ∀ u v : Fˣ, u • t₀ = v • t₀ → u = v) :
    mwTwistRel F n T ≤ (mwTwistTrivPre t₀ hsurj).ker := by
  rw [mwTwistRel, AddSubgroup.closure_le]
  rintro x ⟨u, t, m, rfl⟩
  show mwTwistTrivPre t₀ hsurj
      (Finsupp.single (u • t) m - Finsupp.single t (mwFormAct u n m)) = 0
  rw [map_sub, mwTwistTrivPre_single, mwTwistTrivPre_single, sub_eq_zero,
    mwTwistCoord_smul t₀ hsurj hfree u t]
  have happ : mwFormAct (mwTwistCoord t₀ hsurj t) n (mwFormAct u n m)
      = mwFormAct (mwTwistCoord t₀ hsurj t * u) n m :=
    DFunLike.congr_fun (mwFormAct_mul (F := F) (mwTwistCoord t₀ hsurj t) u n) m
  rw [happ, mul_comm]

/-- **The trivialization of the twist determined by a base point.** -/
def mwTwistTriv (hfree : ∀ u v : Fˣ, u • t₀ = v • t₀ → u = v) :
    MWTwist F n T →+ MilnorWittKDeg F n :=
  QuotientAddGroup.lift _ (mwTwistTrivPre t₀ hsurj) (mwTwistTrivPre_rel t₀ hsurj hfree)

@[simp]
theorem mwTwistTriv_mk (hfree : ∀ u v : Fˣ, u • t₀ = v • t₀ → u = v)
    (t : T) (m : MilnorWittKDeg F n) :
    mwTwistTriv t₀ hsurj hfree (mwTwistMk F n T t m)
      = mwFormAct (mwTwistCoord t₀ hsurj t) n m := by
  show mwTwistTrivPre t₀ hsurj (Finsupp.single t m) = _
  rw [mwTwistTrivPre_single]

theorem mwTwistTriv_mk_base (hfree : ∀ u v : Fˣ, u • t₀ = v • t₀ → u = v)
    (m : MilnorWittKDeg F n) :
    mwTwistTriv t₀ hsurj hfree (mwTwistMk F n T t₀ m) = m := by
  rw [mwTwistTriv_mk, mwTwistCoord_base t₀ hsurj hfree, mwFormAct_one]
  rfl

/-- **A simply transitive base point trivializes the twist.** -/
def mwTwistEquiv (hfree : ∀ u v : Fˣ, u • t₀ = v • t₀ → u = v) :
    MWTwist F n T ≃+ MilnorWittKDeg F n where
  toFun := mwTwistTriv t₀ hsurj hfree
  invFun := mwTwistMk F n T t₀
  left_inv x := by
    have hext : (mwTwistMkHom F n T t₀).comp (mwTwistTriv t₀ hsurj hfree)
        = AddMonoidHom.id (MWTwist F n T) := by
      refine mwTwist_hom_ext F n T fun t m => ?_
      show mwTwistMk F n T t₀ (mwTwistTriv t₀ hsurj hfree (mwTwistMk F n T t m))
        = mwTwistMk F n T t m
      rw [mwTwistTriv_mk, ← mwTwistMk_smul, ← mwTwistCoord_spec t₀ hsurj t]
    exact DFunLike.congr_fun hext x
  right_inv m := mwTwistTriv_mk_base t₀ hsurj hfree m
  map_add' := map_add _

@[simp]
theorem mwTwistEquiv_apply (hfree : ∀ u v : Fˣ, u • t₀ = v • t₀ → u = v) (x : MWTwist F n T) :
    mwTwistEquiv t₀ hsurj hfree x = mwTwistTriv t₀ hsurj hfree x := rfl

/-- **Changing the base point by `u` changes the trivialization by the unit form `⟨u⟩`.**  This is
the determinant twist: a class is well defined only after a generator of the line is chosen, and
another generator changes it by the unit form of the ratio. -/
theorem mwTwistTriv_smul (hfree : ∀ u v : Fˣ, u • t₀ = v • t₀ → u = v)
    (u : Fˣ) (m : MilnorWittKDeg F n) :
    mwTwistTriv t₀ hsurj hfree (mwTwistMk F n T (u • t₀) m) = mwFormAct u n m := by
  rw [mwTwistMk_smul, mwTwistTriv_mk_base]

end Trivialization

section Line

/-- The nonzero vectors of an `F`-line, as an `Fˣ`-set. -/
structure MWLinePoints (F : Type*) [Field F] (L : Type*) [AddCommGroup L] [Module F L] where
  /-- The underlying vector. -/
  vec : L
  /-- It is nonzero. -/
  vec_ne_zero : vec ≠ 0

variable {F : Type*} [Field F] {L : Type*} [AddCommGroup L] [Module F L]

theorem MWLinePoints.ext_vec {t t' : MWLinePoints F L} (h : t.vec = t'.vec) : t = t' := by
  obtain ⟨v, hv⟩ := t
  obtain ⟨v', hv'⟩ := t'
  subst h
  rfl

instance : MulAction Fˣ (MWLinePoints F L) where
  smul u t := ⟨(u : F) • t.vec, fun h => t.vec_ne_zero (by
    have h2 : ((u⁻¹ : Fˣ) : F) • ((u : F) • t.vec) = 0 := by rw [h, smul_zero]
    rwa [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] at h2)⟩
  one_smul t := MWLinePoints.ext_vec (by
    show ((1 : Fˣ) : F) • t.vec = t.vec
    rw [Units.val_one, one_smul])
  mul_smul u u' t := MWLinePoints.ext_vec (by
    show ((u * u' : Fˣ) : F) • t.vec = (u : F) • ((u' : F) • t.vec)
    rw [Units.val_mul, mul_smul])

@[simp]
theorem MWLinePoints.smul_vec (u : Fˣ) (t : MWLinePoints F L) :
    (u • t).vec = (u : F) • t.vec := rfl

/-- A nonzero scalar multiple of a nonzero vector of a line is nonzero. -/
theorem MWLinePoints.smul_eq_zero_iff {c : F} {v : L} (hv : v ≠ 0) (h : c • v = 0) : c = 0 := by
  by_contra hc
  refine hv ?_
  have h2 : c⁻¹ • (c • v) = 0 := by rw [h, smul_zero]
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

/-- **A basis vector of a line acts simply transitively on the nonzero vectors.** -/
theorem MWLinePoints.exists_smul (e : L) (he : e ≠ 0) (hspan : ∀ v : L, ∃ c : F, v = c • e)
    (t : MWLinePoints F L) : ∃ u : Fˣ, t = u • (⟨e, he⟩ : MWLinePoints F L) := by
  obtain ⟨c, hc⟩ := hspan t.vec
  have hcne : c ≠ 0 := fun hzero => t.vec_ne_zero (by rw [hc, hzero, zero_smul])
  exact ⟨Units.mk0 c hcne, MWLinePoints.ext_vec hc⟩

theorem MWLinePoints.smul_left_injective (e : L) (he : e ≠ 0) (u v : Fˣ)
    (h : u • (⟨e, he⟩ : MWLinePoints F L) = v • (⟨e, he⟩ : MWLinePoints F L)) : u = v := by
  have hval : (u : F) • e = (v : F) • e := congrArg MWLinePoints.vec h
  have hsub : ((u : F) - (v : F)) • e = 0 := by rw [sub_smul, hval, sub_self]
  exact Units.ext (sub_eq_zero.1 (MWLinePoints.smul_eq_zero_iff he hsub))

/-- **`K_n^{MW}(F)` twisted by a line**, the coefficient group of an oriented theory. -/
def MWLineTwist (F : Type*) [Field F] (n : ℤ) (L : Type*) [AddCommGroup L] [Module F L] : Type _ :=
  MWTwist F n (MWLinePoints F L)

instance (F : Type*) [Field F] (n : ℤ) (L : Type*) [AddCommGroup L] [Module F L] :
    AddCommGroup (MWLineTwist F n L) := inferInstanceAs (AddCommGroup (MWTwist F n _))

/-- **A basis vector of the line trivializes the twist.** -/
def mwLineTwistEquiv {n : ℤ} (e : L) (he : e ≠ 0)
    (hspan : ∀ v : L, ∃ c : F, v = c • e) :
    MWLineTwist F n L ≃+ MilnorWittKDeg F n :=
  mwTwistEquiv (⟨e, he⟩ : MWLinePoints F L)
    (MWLinePoints.exists_smul e he hspan) (MWLinePoints.smul_left_injective e he)

/-- **Rescaling the basis vector by `u` rescales the trivialization by `⟨u⟩`.** -/
theorem mwLineTwistEquiv_smul {n : ℤ} (e : L) (he : e ≠ 0)
    (hspan : ∀ v : L, ∃ c : F, v = c • e) (u : Fˣ) (m : MilnorWittKDeg F n) :
    mwLineTwistEquiv e he hspan
        (mwTwistMk F n (MWLinePoints F L) (u • (⟨e, he⟩ : MWLinePoints F L)) m)
      = mwFormAct u n m :=
  mwTwistTriv_smul (⟨e, he⟩ : MWLinePoints F L) (MWLinePoints.exists_smul e he hspan)
    (MWLinePoints.smul_left_injective e he) u m

end Line

end

end GaloisForLFunctions.HTGeometry
