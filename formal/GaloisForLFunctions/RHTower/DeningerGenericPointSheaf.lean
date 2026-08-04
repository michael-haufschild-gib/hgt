import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.MonCat.Limits
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Sheaves of constants on a space with a generic point

On a space in which one point lies in every nonempty open set, a family of constant sections
subject to a pointwise condition is automatically a sheaf: two nonempty members of an open cover
both contain the generic point, so their constants agree there, and the common constant glues.

This is the mechanism that makes the sheaves on an integral one dimensional arithmetic base
elementary: every nonempty open contains the generic point, so a section is a single element of the
function field constrained pointwise.

* `DeningerConstSection` : the constant sections satisfying a pointwise condition.
* `deningerConstSection_existsUnique_gluing` : the unique gluing property.
* `DeningerMulCond.sheaf`, `DeningerAddCond.sheaf` : the resulting sheaves of commutative monoids
  and of abelian groups.
-/

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat CategoryTheory.Limits

universe u

section Generic

variable {X : TopCat.{u}} {M : Type u}

/-- The constant functions on an open set that satisfy a pointwise condition. -/
def DeningerConstSection (cond : X → M → Prop) (U : Opens X) : Set (↥U → M) :=
  {f | (∀ x y : ↥U, f x = f y) ∧ ∀ x : ↥U, cond (x : X) (f x)}

/-- Restriction of a function on an open set to a smaller open set. -/
def deningerConstRes {U V : Opens X} (h : U ≤ V) (f : ↥V → M) : ↥U → M :=
  fun x => f ⟨x, h x.2⟩

theorem deningerConstRes_mem {cond : X → M → Prop} {U V : Opens X} (h : U ≤ V)
    {f : ↥V → M} (hf : f ∈ DeningerConstSection cond V) :
    deningerConstRes h f ∈ DeningerConstSection cond U :=
  ⟨fun _ _ => hf.1 _ _, fun x => hf.2 ⟨x, h x.2⟩⟩

/-- A point lying in every nonempty open set. -/
def DeningerIsGenericPoint (g : X) : Prop := ∀ V : Opens X, (V : Set X).Nonempty → g ∈ V

/-- **Constant sections glue uniquely** on a space with a generic point: any two nonempty members
of a cover contain the generic point, so a compatible family has one common value. -/
theorem deningerConstSection_existsUnique_gluing {cond : X → M → Prop} {g : X}
    (hg : DeningerIsGenericPoint g) {ι : Type u} (U : ι → Opens X)
    (f : ∀ i, ↥(U i) → M)
    (hmem : ∀ i, f i ∈ DeningerConstSection cond (U i))
    (hcompat : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j), f i ⟨x, hi⟩ = f j ⟨x, hj⟩) :
    ∃! s : ↥(iSup U) → M, s ∈ DeningerConstSection cond (iSup U) ∧
      ∀ i (x : X) (hx : x ∈ U i), s ⟨x, Opens.mem_iSup.2 ⟨i, hx⟩⟩ = f i ⟨x, hx⟩ := by
  classical
  by_cases hne : ((iSup U : Opens X) : Set X).Nonempty
  · obtain ⟨y, hy⟩ := hne
    have hgU : g ∈ (iSup U : Opens X) := hg _ ⟨y, hy⟩
    obtain ⟨i₀, hi₀⟩ := Opens.mem_iSup.1 hgU
    set c : M := f i₀ ⟨g, hi₀⟩ with hc
    have key : ∀ i (x : X) (hx : x ∈ U i), f i ⟨x, hx⟩ = c := by
      intro i x hx
      have hgi : g ∈ U i := hg (U i) ⟨x, hx⟩
      have h1 : f i ⟨x, hx⟩ = f i ⟨g, hgi⟩ := (hmem i).1 ⟨x, hx⟩ ⟨g, hgi⟩
      rw [h1, hc]
      exact hcompat i i₀ g hgi hi₀
    refine ⟨fun _ => c, ⟨⟨fun _ _ => rfl, ?_⟩, ?_⟩, ?_⟩
    · intro x
      obtain ⟨i, hi⟩ := Opens.mem_iSup.1 x.2
      have hc' := (hmem i).2 ⟨(x : X), hi⟩
      rw [key i _ hi] at hc'
      exact hc'
    · intro i x hx
      exact (key i x hx).symm
    · rintro t ⟨_, ht⟩
      funext x
      obtain ⟨i, hi⟩ := Opens.mem_iSup.1 x.2
      have h1 : t x = f i ⟨(x : X), hi⟩ := ht i (x : X) hi
      rw [h1]
      exact key i _ hi
  · have hempty : IsEmpty ↥(iSup U : Opens X) := ⟨fun x => hne ⟨(x : X), x.2⟩⟩
    refine ⟨fun x => hempty.elim x, ⟨⟨fun x => hempty.elim x, fun x => hempty.elim x⟩, ?_⟩, ?_⟩
    · intro i x hx
      exact hempty.elim ⟨x, Opens.mem_iSup.2 ⟨i, hx⟩⟩
    · intro t _
      funext x
      exact hempty.elim x

end Generic

section MulSheaf

variable {X : TopCat.{u}}

/-- A pointwise condition on values in a commutative monoid, closed under multiplication. -/
structure DeningerMulCond (X : TopCat.{u}) (M : Type u) [CommMonoid M] where
  /-- The condition. -/
  cond : X → M → Prop
  /-- It holds for the unit. -/
  one_mem : ∀ x, cond x 1
  /-- It is closed under multiplication. -/
  mul_mem : ∀ {x : X} {a b : M}, cond x a → cond x b → cond x (a * b)

variable {M : Type u} [CommMonoid M]

/-- The submonoid of constant sections satisfying the condition. -/
def DeningerMulCond.sub (c : DeningerMulCond X M) (U : Opens X) : Submonoid (↥U → M) where
  carrier := DeningerConstSection c.cond U
  one_mem' := ⟨fun _ _ => rfl, fun _ => c.one_mem _⟩
  mul_mem' := fun {f} {g} hf hg =>
    ⟨fun x y => by
      show f x * g x = f y * g y
      rw [hf.1 x y, hg.1 x y], fun x => c.mul_mem (hf.2 x) (hg.2 x)⟩

theorem DeningerMulCond.mem_sub (c : DeningerMulCond X M) (U : Opens X) (f : ↥U → M) :
    f ∈ c.sub U ↔ (∀ x y : ↥U, f x = f y) ∧ ∀ x : ↥U, c.cond (x : X) (f x) := Iff.rfl

/-- Restriction of sections, as a monoid homomorphism. -/
def DeningerMulCond.resHom (c : DeningerMulCond X M) {U V : Opens X} (h : U ≤ V) :
    c.sub V →* c.sub U where
  toFun s := ⟨deningerConstRes h (s : ↥V → M), deningerConstRes_mem h s.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The presheaf of constant sections satisfying the condition. -/
def DeningerMulCond.presheaf (c : DeningerMulCond X M) : TopCat.Presheaf CommMonCat.{u} X where
  obj U := CommMonCat.of (c.sub U.unop)
  map h := CommMonCat.ofHom (c.resHom (leOfHom h.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Evaluation of a section at a point. -/
def DeningerMulCond.eval (c : DeningerMulCond X M) {U : Opens X} (s : c.sub U) (x : ↥U) : M :=
  (s : ↥U → M) x

theorem DeningerMulCond.eval_resHom (c : DeningerMulCond X M) {U V : Opens X} (h : U ≤ V)
    (s : c.sub V) (x : ↥U) : c.eval (c.resHom h s) x = c.eval s ⟨x, h x.2⟩ := rfl

theorem DeningerMulCond.presheaf_hom (c : DeningerMulCond X M) {U V : (Opens X)ᵒᵖ} (h : U ⟶ V) :
    CategoryTheory.ConcreteCategory.hom (c.presheaf.map h) = c.resHom (leOfHom h.unop) := rfl

/-- **The presheaf of constant sections is a sheaf** on a space with a generic point. -/
theorem DeningerMulCond.isSheaf (c : DeningerMulCond X M) {g : X}
    (hg : DeningerIsGenericPoint g) : c.presheaf.IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hcompat
  have hcompat' : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      c.eval (sf i) ⟨x, hi⟩ = c.eval (sf j) ⟨x, hj⟩ := by
    intro i j x hi hj
    have h := hcompat i j
    rw [DeningerMulCond.presheaf_hom, DeningerMulCond.presheaf_hom] at h
    exact congrArg (fun t : c.sub (U i ⊓ U j) => c.eval t ⟨x, ⟨hi, hj⟩⟩) h
  obtain ⟨s, ⟨hs, hres⟩, huniq⟩ :=
    deningerConstSection_existsUnique_gluing (cond := c.cond) hg U
      (fun i => c.eval (sf i)) (fun i => (sf i).2) hcompat'
  have hgoal : ∀ t : c.sub (iSup U),
      (∀ i, CategoryTheory.ConcreteCategory.hom
          (c.presheaf.map (Opens.leSupr U i).op) t = sf i) ↔
        ∀ i (x : X) (hx : x ∈ U i),
          c.eval t ⟨x, Opens.mem_iSup.2 ⟨i, hx⟩⟩ = c.eval (sf i) ⟨x, hx⟩ := by
    intro t
    constructor
    · intro h i x hx
      have h1 := h i
      rw [DeningerMulCond.presheaf_hom] at h1
      exact congrArg (fun w : c.sub (U i) => c.eval w ⟨x, hx⟩) h1
    · intro h i
      rw [DeningerMulCond.presheaf_hom]
      refine Subtype.ext ?_
      funext y
      exact h i (y : X) y.2
  refine ⟨(⟨s, hs⟩ : c.sub (iSup U)), ?_, ?_⟩
  · exact (hgoal ⟨s, hs⟩).2 (fun i x hx => hres i x hx)
  · intro t ht
    have ht' : ∀ i, CategoryTheory.ConcreteCategory.hom
        (c.presheaf.map (Opens.leSupr U i).op) t = sf i := ht
    refine Subtype.ext ?_
    exact huniq (c.eval (t : c.sub (iSup U))) ⟨t.2, (hgoal t).1 ht'⟩

/-- The sheaf of constant sections satisfying the condition. -/
def DeningerMulCond.sheaf (c : DeningerMulCond X M) {g : X} (hg : DeningerIsGenericPoint g) :
    TopCat.Sheaf CommMonCat.{u} X :=
  ⟨c.presheaf, c.isSheaf hg⟩

end MulSheaf

section AddSheaf

variable {X : TopCat.{u}}

/-- A pointwise condition on values in an abelian group, closed under the group operations. -/
structure DeningerAddCond (X : TopCat.{u}) (M : Type u) [AddCommGroup M] where
  /-- The condition. -/
  cond : X → M → Prop
  /-- It holds for zero. -/
  zero_mem : ∀ x, cond x 0
  /-- It is closed under addition. -/
  add_mem : ∀ {x : X} {a b : M}, cond x a → cond x b → cond x (a + b)
  /-- It is closed under negation. -/
  neg_mem : ∀ {x : X} {a : M}, cond x a → cond x (-a)

variable {M : Type u} [AddCommGroup M]

/-- The subgroup of constant sections satisfying the condition. -/
def DeningerAddCond.sub (c : DeningerAddCond X M) (U : Opens X) : AddSubgroup (↥U → M) where
  carrier := DeningerConstSection c.cond U
  zero_mem' := ⟨fun _ _ => rfl, fun _ => c.zero_mem _⟩
  add_mem' := fun {f} {g} hf hg =>
    ⟨fun x y => by
      show f x + g x = f y + g y
      rw [hf.1 x y, hg.1 x y], fun x => c.add_mem (hf.2 x) (hg.2 x)⟩
  neg_mem' := fun {f} hf =>
    ⟨fun x y => by
      show -f x = -f y
      rw [hf.1 x y], fun x => c.neg_mem (hf.2 x)⟩

theorem DeningerAddCond.mem_sub (c : DeningerAddCond X M) (U : Opens X) (f : ↥U → M) :
    f ∈ c.sub U ↔ (∀ x y : ↥U, f x = f y) ∧ ∀ x : ↥U, c.cond (x : X) (f x) := Iff.rfl

/-- Restriction of sections, as a group homomorphism. -/
def DeningerAddCond.resHom (c : DeningerAddCond X M) {U V : Opens X} (h : U ≤ V) :
    c.sub V →+ c.sub U where
  toFun s := ⟨deningerConstRes h (s : ↥V → M), deningerConstRes_mem h s.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The presheaf of constant sections satisfying the condition. -/
def DeningerAddCond.presheaf (c : DeningerAddCond X M) : TopCat.Presheaf AddCommGrpCat.{u} X where
  obj U := AddCommGrpCat.of (c.sub U.unop)
  map h := AddCommGrpCat.ofHom (c.resHom (leOfHom h.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Evaluation of a section at a point. -/
def DeningerAddCond.eval (c : DeningerAddCond X M) {U : Opens X} (s : c.sub U) (x : ↥U) : M :=
  (s : ↥U → M) x

theorem DeningerAddCond.eval_resHom (c : DeningerAddCond X M) {U V : Opens X} (h : U ≤ V)
    (s : c.sub V) (x : ↥U) : c.eval (c.resHom h s) x = c.eval s ⟨x, h x.2⟩ := rfl

theorem DeningerAddCond.presheaf_hom (c : DeningerAddCond X M) {U V : (Opens X)ᵒᵖ} (h : U ⟶ V) :
    CategoryTheory.ConcreteCategory.hom (c.presheaf.map h) = c.resHom (leOfHom h.unop) := rfl

/-- **The presheaf of constant sections is a sheaf** on a space with a generic point. -/
theorem DeningerAddCond.isSheaf (c : DeningerAddCond X M) {g : X}
    (hg : DeningerIsGenericPoint g) : c.presheaf.IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hcompat
  have hcompat' : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      c.eval (sf i) ⟨x, hi⟩ = c.eval (sf j) ⟨x, hj⟩ := by
    intro i j x hi hj
    have h := hcompat i j
    rw [DeningerAddCond.presheaf_hom, DeningerAddCond.presheaf_hom] at h
    exact congrArg (fun t : c.sub (U i ⊓ U j) => c.eval t ⟨x, ⟨hi, hj⟩⟩) h
  obtain ⟨s, ⟨hs, hres⟩, huniq⟩ :=
    deningerConstSection_existsUnique_gluing (cond := c.cond) hg U
      (fun i => c.eval (sf i)) (fun i => (sf i).2) hcompat'
  have hgoal : ∀ t : c.sub (iSup U),
      (∀ i, CategoryTheory.ConcreteCategory.hom
          (c.presheaf.map (Opens.leSupr U i).op) t = sf i) ↔
        ∀ i (x : X) (hx : x ∈ U i),
          c.eval t ⟨x, Opens.mem_iSup.2 ⟨i, hx⟩⟩ = c.eval (sf i) ⟨x, hx⟩ := by
    intro t
    constructor
    · intro h i x hx
      have h1 := h i
      rw [DeningerAddCond.presheaf_hom] at h1
      exact congrArg (fun w : c.sub (U i) => c.eval w ⟨x, hx⟩) h1
    · intro h i
      rw [DeningerAddCond.presheaf_hom]
      refine Subtype.ext ?_
      funext y
      exact h i (y : X) y.2
  refine ⟨(⟨s, hs⟩ : c.sub (iSup U)), ?_, ?_⟩
  · exact (hgoal ⟨s, hs⟩).2 (fun i x hx => hres i x hx)
  · intro t ht
    have ht' : ∀ i, CategoryTheory.ConcreteCategory.hom
        (c.presheaf.map (Opens.leSupr U i).op) t = sf i := ht
    refine Subtype.ext ?_
    exact huniq (c.eval (t : c.sub (iSup U))) ⟨t.2, (hgoal t).1 ht'⟩

/-- The sheaf of constant sections satisfying the condition. -/
def DeningerAddCond.sheaf (c : DeningerAddCond X M) {g : X} (hg : DeningerIsGenericPoint g) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  ⟨c.presheaf, c.isSheaf hg⟩

end AddSheaf

end RHTower

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat

universe u

/-- A pointwise condition implying another gives an inclusion of sections. -/
def DeningerAddCond.inclSub {X : TopCat.{u}} {M : Type u} [AddCommGroup M]
    (c d : DeningerAddCond X M) (h : ∀ (x : X) (a : M), c.cond x a → d.cond x a)
    (U : Opens X) : c.sub U →+ d.sub U where
  toFun s := ⟨(s : ↥U → M), s.2.1, fun x => h _ _ (s.2.2 x)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem DeningerAddCond.inclSub_coe {X : TopCat.{u}} {M : Type u} [AddCommGroup M]
    (c d : DeningerAddCond X M) (h : ∀ (x : X) (a : M), c.cond x a → d.cond x a)
    (U : Opens X) (s : c.sub U) :
    ((c.inclSub d h U s : d.sub U) : ↥U → M) = (s : ↥U → M) := rfl

/-- **The inclusion of the sheaves attached to nested pointwise conditions.** -/
def DeningerAddCond.incl {X : TopCat.{u}} {M : Type u} [AddCommGroup M]
    (c d : DeningerAddCond X M) (h : ∀ (x : X) (a : M), c.cond x a → d.cond x a) :
    c.presheaf ⟶ d.presheaf where
  app U := AddCommGrpCat.ofHom (c.inclSub d h U.unop)
  naturality _ _ _ := rfl

theorem DeningerAddCond.incl_app_hom {X : TopCat.{u}} {M : Type u} [AddCommGroup M]
    (c d : DeningerAddCond X M) (h : ∀ (x : X) (a : M), c.cond x a → d.cond x a)
    (U : (Opens X)ᵒᵖ) :
    ConcreteCategory.hom ((c.incl d h).app U) = c.inclSub d h U.unop := rfl

end RHTower
