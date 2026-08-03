import GaloisForLFunctions.RHTower.DeningerFreeGroupH2

/-!
# `H⁰` and `H¹` of a free group

A `1`-cocycle is a section of the semidirect product, and over a free group a section is exactly an
arbitrary choice of values on the generators.  So the `1`-cocycles of a free group on `ι` are the
functions `ι → A`, and with trivial coefficients — where the coboundaries vanish — that is `H¹`.

Degree zero needs nothing: with a trivial action `H⁰` is the coefficient module.

* `deningerFreeGroupCocycles₁Equiv` : `Z¹(F_ι; A) ≃ (ι → A)` for every representation `A`.
* `deningerFreeGroup_H1_equiv` : `H¹(F_ι; M) ≃ (ι → M)` for a trivial module.
* `deningerTrivial_H0_equiv` : `H⁰(G; M) ≅ M` for a trivial module.
-/

namespace RHTower

open groupCohomology

section FreeGroupH1

variable {k ι : Type} [CommRing k] {A : Rep k (FreeGroup ι)}

/-- The zero cocycle, whose twisted extension is the semidirect product. -/
def deningerZeroCocycle (A : Rep k (FreeGroup ι)) : DeningerTwistedCocycle A where
  f _ := 0
  cocycle g _ _ := by
    show (0 : A) + 0 = A.ρ g 0 + 0
    rw [map_zero]
  one_fst _ := rfl
  one_snd _ := rfl

/-- The section of the semidirect product determined by values on the free generators. -/
noncomputable def deningerFreeSection (c : ι → A) :
    FreeGroup ι →* DeningerTwistedExt (deningerZeroCocycle A) :=
  FreeGroup.lift (fun i => DeningerTwistedExt.mk (c i) (FreeGroup.of i))

theorem deningerFreeSection_snd (c : ι → A) (g : FreeGroup ι) :
    (deningerFreeSection c g).snd = g := by
  have h : (DeningerTwistedExt.proj (deningerZeroCocycle A)).comp (deningerFreeSection c) =
      MonoidHom.id (FreeGroup ι) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    show DeningerTwistedExt.proj _ (deningerFreeSection c (FreeGroup.of i)) = FreeGroup.of i
    rw [deningerFreeSection, FreeGroup.lift_apply_of]
    rfl
  exact DFunLike.congr_fun h g

@[simp]
theorem deningerFreeSection_of (c : ι → A) (i : ι) :
    (deningerFreeSection c (FreeGroup.of i)).fst = c i := by
  rw [deningerFreeSection, FreeGroup.lift_apply_of]
  rfl

/-- A `1`-cocycle vanishes at the identity. -/
theorem deningerCocycles₁_map_one' (x : cocycles₁ A) : (x : FreeGroup ι → A) 1 = 0 := by
  have hx := (mem_cocycles₁_iff (A := A) (⇑x)).1 x.2 1 1
  rw [mul_one] at hx
  have hρ : A.ρ (1 : FreeGroup ι) ((x : FreeGroup ι → A) 1) = (x : FreeGroup ι → A) 1 := by
    rw [map_one]
    rfl
  rw [hρ] at hx
  have h2 : (x : FreeGroup ι → A) 1 + 0 =
      (x : FreeGroup ι → A) 1 + (x : FreeGroup ι → A) 1 := by
    rw [add_zero]
    exact hx
  exact (add_left_cancel h2).symm

/-- A `1`-cocycle, read as a section of the semidirect product. -/
noncomputable def deningerCocycleSection (x : cocycles₁ A) :
    FreeGroup ι →* DeningerTwistedExt (deningerZeroCocycle A) where
  toFun g := DeningerTwistedExt.mk ((x : FreeGroup ι → A) g) g
  map_one' := by
    show DeningerTwistedExt.mk ((x : FreeGroup ι → A) 1) 1 = 1
    rw [deningerCocycles₁_map_one']
    rfl
  map_mul' g h := by
    have hx := (mem_cocycles₁_iff (A := A) (⇑x)).1 x.2 g h
    show DeningerTwistedExt.mk ((x : FreeGroup ι → A) (g * h)) (g * h) =
      DeningerTwistedExt.mk ((x : FreeGroup ι → A) g) g *
        DeningerTwistedExt.mk ((x : FreeGroup ι → A) h) h
    rw [DeningerTwistedExt.mk_mul]
    refine congrArg₂ DeningerTwistedExt.mk ?_ rfl
    show (x : FreeGroup ι → A) (g * h) =
      (x : FreeGroup ι → A) g + A.ρ g ((x : FreeGroup ι → A) h) + (0 : A)
    rw [add_zero, hx]
    exact add_comm _ _

/-- **The `1`-cocycles of a free group are the functions on the generators.** -/
noncomputable def deningerFreeGroupCocycles₁Equiv :
    (cocycles₁ A) ≃ (ι → A) where
  toFun x i := (x : FreeGroup ι → A) (FreeGroup.of i)
  invFun c :=
    ⟨fun g => (deningerFreeSection c g).fst, by
      rw [mem_cocycles₁_iff]
      intro g h
      have hmul : (deningerFreeSection c (g * h)).fst =
          (deningerFreeSection c g).fst +
            A.ρ (deningerFreeSection c g).snd ((deningerFreeSection c h).fst) +
            (deningerZeroCocycle A).f
              ((deningerFreeSection c g).snd, (deningerFreeSection c h).snd) := by
        rw [(deningerFreeSection c).map_mul]
        exact DeningerTwistedExt.mul_fst _ _
      rw [deningerFreeSection_snd] at hmul
      show (deningerFreeSection c (g * h)).fst =
        A.ρ g ((deningerFreeSection c h).fst) + (deningerFreeSection c g).fst
      rw [hmul]
      show _ + A.ρ g _ + (0 : A) = _
      rw [add_zero]
      exact add_comm _ _⟩
  left_inv x := by
    have heq : deningerCocycleSection x =
        deningerFreeSection (fun i => (x : FreeGroup ι → A) (FreeGroup.of i)) := by
      refine FreeGroup.ext_hom _ _ fun i => ?_
      rw [deningerFreeSection, FreeGroup.lift_apply_of]
      rfl
    refine Subtype.ext (funext fun g => ?_)
    show (deningerFreeSection (fun i => (x : FreeGroup ι → A) (FreeGroup.of i)) g).fst =
      (x : FreeGroup ι → A) g
    rw [← heq]
    rfl
  right_inv c := funext fun i => deningerFreeSection_of c i

end FreeGroupH1

section TrivialLowDegree

variable {k G : Type} [CommRing k] [Group G] {M : Type} [AddCommGroup M] [Module k M]

/-- **`H⁰` of a trivial module is the module.** -/
noncomputable def deningerTrivial_H0_equiv :
    (H0 (Rep.trivial k G M)) ≅ ModuleCat.of k M :=
  H0IsoOfIsTrivial (Rep.trivial k G M)

/-- **With a trivial action the `1`-coboundaries vanish**, for any coefficient ring. -/
theorem deningerCoboundaries₁_trivial' :
    coboundaries₁ (Rep.trivial k G M) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro _ ⟨m, rfl⟩
  refine Submodule.mem_bot _ |>.2 (funext fun g => ?_)
  rw [d₀₁_hom_apply]
  show ((Rep.trivial k G M).ρ g) m - m = 0
  simp

theorem deningerTrivialH1π_injective :
    Function.Injective
      (CategoryTheory.ConcreteCategory.hom (H1π (Rep.trivial k G M))) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have h := (H1π_eq_zero_iff x).1 hx
  rw [deningerCoboundaries₁_trivial', Submodule.mem_bot] at h
  exact Subtype.ext h

theorem deningerTrivialH1π_surjective :
    Function.Surjective
      (CategoryTheory.ConcreteCategory.hom (H1π (Rep.trivial k G M))) :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- **`H¹` of a trivial module is the module of `1`-cocycles**, for any coefficient ring. -/
noncomputable def deningerTrivial_H1_equiv :
    (H1 (Rep.trivial k G M) : Type) ≃ (cocycles₁ (Rep.trivial k G M)) :=
  (Equiv.ofBijective _ ⟨deningerTrivialH1π_injective (k := k) (G := G) (M := M),
    deningerTrivialH1π_surjective (k := k) (G := G) (M := M)⟩).symm

end TrivialLowDegree

section FreeGroupTrivial

variable {k ι : Type} [CommRing k] {M : Type} [AddCommGroup M] [Module k M]

/-- **`H¹(F_ι; M) ≃ (ι → M)`** for a trivial module: the coboundaries vanish and a cocycle is a
free choice on the generators.  With `ι` of size `m` and `M = ℚ` this is the card's `ℚ^m`. -/
noncomputable def deningerFreeGroup_H1_equiv :
    (H1 (Rep.trivial k (FreeGroup ι) M) : Type) ≃ (ι → M) :=
  deningerTrivial_H1_equiv.trans deningerFreeGroupCocycles₁Equiv

end FreeGroupTrivial

end RHTower
