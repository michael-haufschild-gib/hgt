import GaloisForLFunctions.RHTower.Deninger.DeningerBaumslagH1

/-!
# `H²` of a free group vanishes, with arbitrary coefficients

A `2`-cocycle twists `A × G` into a group extension of `G` by `A`.  When `G` is free the extension
splits, because a section may be defined on the free generators and the composite with the
projection is then the identity; a section is exactly a `1`-cochain trivializing the cocycle.

Normalization costs nothing: subtracting the coboundary of the constant `f(1,1)` makes the cocycle
vanish on both boundary slots without changing its class.

* `DeningerTwistedCocycle`, `DeningerTwistedExt` : the twisted extension.
* `deningerFreeGroup_cocycle_trivial` : a normalized cocycle over a free group is a coboundary.
* `deningerFreeGroup_H2_eq_zero` : `H²(FreeGroup ι; A) = 0` for every representation `A`.
-/

namespace RHTower

open groupCohomology

section TwistedExtension

variable {k G : Type} [CommRing k] [Group G] {A : Rep k G}

/-- A normalized `2`-cocycle with values in a representation. -/
structure DeningerTwistedCocycle (A : Rep k G) where
  /-- The cocycle. -/
  f : G × G → A
  /-- The cocycle identity. -/
  cocycle : ∀ g h j : G, f (g * h, j) + f (g, h) = A.ρ g (f (h, j)) + f (g, h * j)
  /-- Normalization in the first slot. -/
  one_fst : ∀ g : G, f (1, g) = 0
  /-- Normalization in the second slot. -/
  one_snd : ∀ g : G, f (g, 1) = 0

/-- **The extension of `G` by `A` twisted by a normalized cocycle.** -/
def DeningerTwistedExt (_c : DeningerTwistedCocycle A) : Type _ := A × G

namespace DeningerTwistedExt

variable {c : DeningerTwistedCocycle A}

/-- An element of the extension. -/
def mk (m : A) (g : G) : DeningerTwistedExt c := (m, g)

/-- The `A`-component. -/
def fst (x : DeningerTwistedExt c) : A := Prod.fst x

/-- The `G`-component. -/
def snd (x : DeningerTwistedExt c) : G := Prod.snd x

@[simp] theorem fst_mk (m : A) (g : G) : (mk m g : DeningerTwistedExt c).fst = m := rfl
@[simp] theorem snd_mk (m : A) (g : G) : (mk m g : DeningerTwistedExt c).snd = g := rfl
theorem eta (x : DeningerTwistedExt c) : mk x.fst x.snd = x := rfl

theorem ext_iff {x y : DeningerTwistedExt c} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
  Prod.ext h1 h2

instance : Mul (DeningerTwistedExt c) :=
  ⟨fun x y => mk (x.fst + A.ρ x.snd (y.fst) + c.f (x.snd, y.snd)) (x.snd * y.snd)⟩

instance : One (DeningerTwistedExt c) := ⟨mk 0 1⟩

instance : Inv (DeningerTwistedExt c) :=
  ⟨fun x => mk (-A.ρ x.snd⁻¹ x.fst - c.f (x.snd⁻¹, x.snd)) x.snd⁻¹⟩

theorem mk_mul (m m' : A) (g g' : G) :
    (mk m g : DeningerTwistedExt c) * mk m' g' =
      mk (m + A.ρ g m' + c.f (g, g')) (g * g') := rfl

theorem one_eq : (1 : DeningerTwistedExt c) = mk 0 1 := rfl

theorem mk_inv (m : A) (g : G) :
    (mk m g : DeningerTwistedExt c)⁻¹ = mk (-A.ρ g⁻¹ m - c.f (g⁻¹, g)) g⁻¹ := rfl

@[simp] theorem mul_fst (x y : DeningerTwistedExt c) :
    (x * y).fst = x.fst + A.ρ x.snd (y.fst) + c.f (x.snd, y.snd) := rfl

@[simp] theorem mul_snd (x y : DeningerTwistedExt c) : (x * y).snd = x.snd * y.snd := rfl

instance : Group (DeningerTwistedExt c) where
  mul_assoc x y z := by
    rw [← eta x, ← eta y, ← eta z, mk_mul, mk_mul, mk_mul, mk_mul]
    refine congrArg₂ mk ?_ (mul_assoc _ _ _)
    have hcoc := c.cocycle x.snd y.snd z.snd
    have hρ : A.ρ (x.snd * y.snd) z.fst = A.ρ x.snd (A.ρ y.snd z.fst) := by
      rw [map_mul]
      rfl
    rw [map_add, map_add, hρ]
    calc x.fst + A.ρ x.snd y.fst + c.f (x.snd, y.snd) + A.ρ x.snd (A.ρ y.snd z.fst) +
          c.f (x.snd * y.snd, z.snd)
        = x.fst + A.ρ x.snd y.fst + A.ρ x.snd (A.ρ y.snd z.fst) +
            (c.f (x.snd * y.snd, z.snd) + c.f (x.snd, y.snd)) := by abel
      _ = x.fst + A.ρ x.snd y.fst + A.ρ x.snd (A.ρ y.snd z.fst) +
            (A.ρ x.snd (c.f (y.snd, z.snd)) + c.f (x.snd, y.snd * z.snd)) := by rw [hcoc]
      _ = x.fst + (A.ρ x.snd y.fst + A.ρ x.snd (A.ρ y.snd z.fst) +
            A.ρ x.snd (c.f (y.snd, z.snd))) + c.f (x.snd, y.snd * z.snd) := by abel
  one_mul x := by
    rw [← eta x, one_eq, mk_mul, c.one_fst, add_zero]
    have h : A.ρ (1 : G) x.fst = x.fst := by
      rw [map_one]
      rfl
    rw [h, zero_add, one_mul]
  mul_one x := by
    rw [← eta x, one_eq, mk_mul, c.one_snd, add_zero, map_zero, add_zero, mul_one]
  inv_mul_cancel x := by
    rw [← eta x, mk_inv, mk_mul, one_eq, inv_mul_cancel]
    refine congrArg₂ mk ?_ rfl
    have h : A.ρ x.snd⁻¹ x.fst = A.ρ x.snd⁻¹ x.fst := rfl
    abel

/-- The projection to the base. -/
def proj (c : DeningerTwistedCocycle A) : DeningerTwistedExt c →* G where
  toFun x := x.snd
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem proj_mk (m : A) (g : G) : proj c (mk m g) = g := rfl

end DeningerTwistedExt

end TwistedExtension

section FreeGroupH2

variable {k : Type} [CommRing k] {ι : Type} {A : Rep k (FreeGroup ι)}

/-- **A normalized cocycle over a free group is a coboundary.**  A section of the twisted extension
is defined on the free generators, and it is exactly a trivializing cochain. -/
theorem deningerFreeGroup_cocycle_trivial (c : DeningerTwistedCocycle A) :
    ∃ b : FreeGroup ι → A, ∀ g h, c.f (g, h) = b (g * h) - b g - A.ρ g (b h) := by
  set s : FreeGroup ι →* DeningerTwistedExt c :=
    FreeGroup.lift (fun i => DeningerTwistedExt.mk (0 : A) (FreeGroup.of i)) with hs
  have hproj : (DeningerTwistedExt.proj c).comp s = MonoidHom.id (FreeGroup ι) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    show DeningerTwistedExt.proj c (s (FreeGroup.of i)) = FreeGroup.of i
    rw [hs, FreeGroup.lift_apply_of]
    rfl
  have hsnd : ∀ g, (s g).snd = g := fun g => DFunLike.congr_fun hproj g
  refine ⟨fun g => (s g).fst, fun g h => ?_⟩
  show c.f (g, h) = (s (g * h)).fst - (s g).fst - A.ρ g ((s h).fst)
  have hmul : (s (g * h)).fst = (s g).fst + A.ρ (s g).snd ((s h).fst) + c.f ((s g).snd, (s h).snd) :=
    by rw [s.map_mul]; exact DeningerTwistedExt.mul_fst _ _
  rw [hsnd, hsnd] at hmul
  rw [hmul]
  abel

/-- **`H²(FreeGroup ι; A) = 0`** for every representation `A`: a free group has cohomological
dimension at most one in degree two. -/
theorem deningerFreeGroup_H2_eq_zero (x : (groupCohomology.H2 A)) : x = 0 := by
  refine groupCohomology.H2_induction_on x fun y => ?_
  refine (groupCohomology.H2π_eq_zero_iff y).2 ?_
  have hy := (groupCohomology.mem_cocycles₂_iff (A := A) (⇑y)).1 y.2
  set c₀ : A := y (1, 1) with hc₀
  set δ : FreeGroup ι × FreeGroup ι → A := fun p => A.ρ p.1 c₀ with hδ
  have hδcoc : δ = (d₁₂ A).hom (fun _ => c₀) := by
    refine funext fun p => ?_
    rw [d₁₂_hom_apply]
    show A.ρ p.1 c₀ = A.ρ p.1 c₀ - c₀ + c₀
    abel
  have hcocyc : ∀ g h j : FreeGroup ι,
      (y (g * h, j) - δ (g * h, j)) + (y (g, h) - δ (g, h)) =
        A.ρ g ((y (h, j) - δ (h, j))) + (y (g, h * j) - δ (g, h * j)) := by
    intro g h j
    have h1 := hy g h j
    have hδ1 : δ (g * h, j) + δ (g, h) = A.ρ g (δ (h, j)) + δ (g, h * j) := by
      show A.ρ (g * h) c₀ + A.ρ g c₀ = A.ρ g (A.ρ h c₀) + A.ρ g c₀
      rw [map_mul]
      rfl
    rw [map_sub]
    calc (y (g * h, j) - δ (g * h, j)) + (y (g, h) - δ (g, h))
        = (y (g * h, j) + y (g, h)) - (δ (g * h, j) + δ (g, h)) := by abel
      _ = (A.ρ g (y (h, j)) + y (g, h * j)) - (A.ρ g (δ (h, j)) + δ (g, h * j)) := by
          rw [h1, hδ1]
      _ = (A.ρ g (y (h, j)) - A.ρ g (δ (h, j))) + (y (g, h * j) - δ (g, h * j)) := by abel
  have hone1 : ∀ g : FreeGroup ι, y (1, g) - δ (1, g) = 0 := by
    intro g
    rw [groupCohomology.cocycles₂_map_one_fst]
    show c₀ - A.ρ (1 : FreeGroup ι) c₀ = 0
    rw [map_one]
    show c₀ - c₀ = 0
    exact sub_self _
  have hone2 : ∀ g : FreeGroup ι, y (g, 1) - δ (g, 1) = 0 := by
    intro g
    rw [groupCohomology.cocycles₂_map_one_snd]
    exact sub_self _
  obtain ⟨b, hb⟩ := deningerFreeGroup_cocycle_trivial
    { f := fun p => y p - δ p
      cocycle := hcocyc
      one_fst := hone1
      one_snd := hone2 }
  refine ⟨fun g => c₀ - b g, funext fun p => ?_⟩
  obtain ⟨g, h⟩ := p
  rw [d₁₂_hom_apply]
  have hbg : y (g, h) - δ (g, h) = b (g * h) - b g - A.ρ g (b h) := hb g h
  show A.ρ g (c₀ - b h) - (c₀ - b (g * h)) + (c₀ - b g) = y (g, h)
  rw [map_sub]
  calc A.ρ g c₀ - A.ρ g (b h) - (c₀ - b (g * h)) + (c₀ - b g)
      = (b (g * h) - b g - A.ρ g (b h)) + A.ρ g c₀ := by abel
    _ = (y (g, h) - δ (g, h)) + A.ρ g c₀ := by rw [← hbg]
    _ = y (g, h) := by
        show (y (g, h) - A.ρ g c₀) + A.ρ g c₀ = y (g, h)
        abel

end FreeGroupH2

end RHTower
