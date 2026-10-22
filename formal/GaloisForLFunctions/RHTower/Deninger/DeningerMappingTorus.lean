import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.OpenQuotient

/-!
# The mapping torus of a trivial monodromy is a product

Suspending a space by a period, with trivial monodromy, gives the product of the space with the
circle of that period: the quotient of `X × ℝ` by the deck translation `(x, t) ↦ (x, t + T)` is
homeomorphic to `X × ℝ/Tℤ`.

On a prime packet the Frobenius acts trivially, because multiplication by the prime has already
been divided out of the unit group; so the packet's mapping torus is the product of its profinite
factor with the circle of period `log p`.

* `DeningerMappingTorus` : the suspension by the deck translation.
* `deningerMappingTorusHomeomorph` : it is the product with the circle.
-/

namespace RHTower

open Set

section MappingTorus

variable (X : Type*) [TopologicalSpace X] (T : ℝ)

/-- The deck relation of the suspension with trivial monodromy. -/
def deningerTorusSetoid : Setoid (X × ℝ) where
  r p q := p.1 = q.1 ∧ ∃ n : ℤ, q.2 = p.2 + n * T
  iseqv :=
    { refl := fun p => ⟨rfl, 0, by simp⟩
      symm := by
        rintro p q ⟨h1, n, h2⟩
        exact ⟨h1.symm, -n, by rw [h2]; push_cast; ring⟩
      trans := by
        rintro p q r ⟨h1, n, h2⟩ ⟨h3, m, h4⟩
        refine ⟨h1.trans h3, n + m, ?_⟩
        rw [h4, h2]
        push_cast
        ring }

/-- The suspension of a space by the deck translation of period `T`. -/
def DeningerMappingTorus : Type _ := Quotient (deningerTorusSetoid X T)

instance : TopologicalSpace (DeningerMappingTorus X T) :=
  inferInstanceAs (TopologicalSpace (Quotient (deningerTorusSetoid X T)))

variable {X T}

/-- The projection to the suspension. -/
def deningerTorusMk (p : X × ℝ) : DeningerMappingTorus X T :=
  Quotient.mk (deningerTorusSetoid X T) p

omit [TopologicalSpace X] in
theorem deningerTorusMk_surjective : Function.Surjective (deningerTorusMk (X := X) (T := T)) :=
  Quotient.mk_surjective

omit [TopologicalSpace X] in
theorem deningerTorusMk_eq {p q : X × ℝ} (h1 : p.1 = q.1) {n : ℤ} (h2 : q.2 = p.2 + n * T) :
    deningerTorusMk p = (deningerTorusMk q : DeningerMappingTorus X T) :=
  Quotient.sound ⟨h1, n, h2⟩

theorem deningerTorusMk_continuous :
    Continuous (deningerTorusMk (X := X) (T := T)) := continuous_quotient_mk'

/-- The comparison map to the product with the circle. -/
def deningerTorusCompare (p : X × ℝ) : X × AddCircle T := (p.1, (p.2 : AddCircle T))

theorem deningerTorusCompare_continuous :
    Continuous (deningerTorusCompare (X := X) (T := T)) :=
  continuous_fst.prodMk (continuous_quotient_mk'.comp continuous_snd)

omit [TopologicalSpace X] in
theorem deningerTorusCompare_surjective :
    Function.Surjective (deningerTorusCompare (X := X) (T := T)) := by
  rintro ⟨x, a⟩
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective a
  exact ⟨(x, t), rfl⟩

theorem deningerTorusCompare_isOpenMap :
    IsOpenMap (deningerTorusCompare (X := X) (T := T)) :=
  IsOpenMap.prodMap IsOpenMap.id QuotientAddGroup.isOpenMap_coe

theorem deningerTorusCompare_isQuotientMap :
    Topology.IsQuotientMap (deningerTorusCompare (X := X) (T := T)) :=
  deningerTorusCompare_isOpenMap.isQuotientMap deningerTorusCompare_continuous
    deningerTorusCompare_surjective

omit [TopologicalSpace X] in
/-- The comparison map identifies exactly the deck-equivalent points. -/
theorem deningerTorusCompare_eq_iff (p q : X × ℝ) :
    deningerTorusCompare p = (deningerTorusCompare q : X × AddCircle T)
      ↔ (deningerTorusSetoid X T).r p q := by
  constructor
  · intro h
    have h1 : p.1 = q.1 := (Prod.ext_iff.mp h).1
    have h2 : ((p.2 : AddCircle T)) = (q.2 : AddCircle T) := (Prod.ext_iff.mp h).2
    rw [QuotientAddGroup.eq] at h2
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp h2
    refine ⟨h1, n, ?_⟩
    rw [zsmul_eq_mul] at hn
    linarith [hn]
  · rintro ⟨h1, n, h2⟩
    refine Prod.ext h1 ?_
    show ((p.2 : AddCircle T)) = (q.2 : AddCircle T)
    rw [QuotientAddGroup.eq]
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨n, ?_⟩
    rw [zsmul_eq_mul, h2]
    ring

/-- **The suspension with trivial monodromy is the product with the circle.** -/
noncomputable def deningerMappingTorusHomeomorph :
    DeningerMappingTorus X T ≃ₜ X × AddCircle T where
  toFun := Quotient.lift deningerTorusCompare fun p q h =>
    (deningerTorusCompare_eq_iff p q).mpr h
  invFun := fun z => deningerTorusMk
    (z.1, (QuotientAddGroup.mk_surjective z.2).choose)
  left_inv := by
    refine Quotient.ind fun p => ?_
    refine Quotient.sound ((deningerTorusCompare_eq_iff _ p).mp ?_)
    refine Prod.ext rfl ?_
    exact (QuotientAddGroup.mk_surjective (p.2 : AddCircle T)).choose_spec
  right_inv := by
    rintro ⟨x, a⟩
    refine Prod.ext rfl ?_
    exact (QuotientAddGroup.mk_surjective a).choose_spec
  continuous_toFun := Continuous.quotient_lift deningerTorusCompare_continuous _
  continuous_invFun := by
    refine deningerTorusCompare_isQuotientMap.continuous_iff.mpr ?_
    have hfun : (fun z : X × AddCircle T => deningerTorusMk (X := X) (T := T)
        (z.1, (QuotientAddGroup.mk_surjective z.2).choose)) ∘ deningerTorusCompare
        = deningerTorusMk (X := X) (T := T) := by
      funext p
      refine Quotient.sound ((deningerTorusCompare_eq_iff _ p).mp ?_)
      refine Prod.ext rfl ?_
      exact (QuotientAddGroup.mk_surjective (p.2 : AddCircle T)).choose_spec
    rw [hfun]
    exact deningerTorusMk_continuous

end MappingTorus

end RHTower
