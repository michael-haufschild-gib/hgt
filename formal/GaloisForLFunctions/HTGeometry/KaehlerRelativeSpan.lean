import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Localization.Basic

/-!
# Relative differentials as absolute differentials modulo the base

For a tower `R → A → B` the exact sequence `B ⊗[A] Ω[A⁄R] → Ω[B⁄R] → Ω[B⁄A] → 0` identifies the
relative differentials with a quotient of the absolute ones.  The image of the first map is the
`B`-span of the differentials of the elements of `A`:

```text
range_mapBaseChange_eq_span   range (mapBaseChange R A B) = span B {D (a) | a ∈ A}
kaehlerQuotientEquiv          Ω[B⁄R] ⧸ span B {D (a) | a ∈ A}  ≃ₗ[B]  Ω[B⁄A]
```

Two criteria cut that span down to a finite family: differentials of algebra generators of `A`
suffice (`D_mem_of_adjoin_eq_top`, because the elements with differential in a fixed submodule form
a subalgebra), and differentials of an ambient ring of which `A` is a localization suffice
(`D_mem_of_isLocalization`, because a denominator becomes a unit).
-/

namespace GaloisForLFunctions.HTGeometry

open KaehlerDifferential

section Range

variable (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- **The image of the base differentials is the span of the differentials of the base.** -/
theorem range_mapBaseChange_eq_span :
    LinearMap.range (KaehlerDifferential.mapBaseChange R A B)
      = Submodule.span B (Set.range fun a : A => KaehlerDifferential.D R B (algebraMap A B a)) := by
  set S : Submodule B Ω[B⁄R] :=
    Submodule.span B (Set.range fun a : A => KaehlerDifferential.D R B (algebraMap A B a)) with hS
  have key : ∀ y : Ω[A⁄R], KaehlerDifferential.map R R A B y ∈ S := by
    intro y
    have hy : y ∈ (⊤ : Submodule A Ω[A⁄R]) := trivial
    rw [← KaehlerDifferential.span_range_derivation R A] at hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨a, rfl⟩
      exact Submodule.subset_span ⟨a, (KaehlerDifferential.map_D R R A B a).symm⟩
    · simp
    · intro u v _ _ hu hv
      rw [map_add]; exact Submodule.add_mem _ hu hv
    · intro a u _ hu
      rw [map_smul]
      exact Submodule.smul_of_tower_mem _ a hu
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x with
    | zero => simp
    | tmul b y =>
        rw [KaehlerDifferential.mapBaseChange_tmul]
        exact Submodule.smul_mem _ _ (key y)
    | add u v hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  · rw [hS, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨1 ⊗ₜ KaehlerDifferential.D R A a, by
      rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]⟩

/-- **The relative differentials are the absolute differentials modulo the base differentials.** -/
noncomputable def kaehlerQuotientEquiv :
    (Ω[B⁄R] ⧸ Submodule.span B
        (Set.range fun a : A => KaehlerDifferential.D R B (algebraMap A B a))) ≃ₗ[B] Ω[B⁄A] :=
  (Submodule.quotEquivOfEq _ _ (by
      rw [← range_mapBaseChange_eq_span, KaehlerDifferential.range_mapBaseChange])).trans
    (LinearMap.quotKerEquivOfSurjective (KaehlerDifferential.map R A B B)
      (KaehlerDifferential.map_surjective R A B))

end Range

section Generation

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- Elements whose differential lands in a fixed submodule form an `R`-subalgebra. -/
def cotangentVanishingSubalgebra (S : Submodule B Ω[B⁄R]) : Subalgebra R A where
  carrier := {a : A | KaehlerDifferential.D R B (algebraMap A B a) ∈ S}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, map_mul, Derivation.leibniz] at *
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx)
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, map_add] at *
    exact Submodule.add_mem _ hx hy
  algebraMap_mem' := by
    intro r
    simp only [Set.mem_setOf_eq, ← IsScalarTower.algebraMap_apply R A B,
      Derivation.map_algebraMap]
    exact Submodule.zero_mem _

/-- **Differentials of algebra generators suffice.** -/
theorem D_mem_of_adjoin_eq_top (S : Submodule B Ω[B⁄R]) {G : Set A}
    (hG : Algebra.adjoin R G = ⊤)
    (hmem : ∀ a ∈ G, KaehlerDifferential.D R B (algebraMap A B a) ∈ S) (a : A) :
    KaehlerDifferential.D R B (algebraMap A B a) ∈ S := by
  have hle : Algebra.adjoin R G ≤ cotangentVanishingSubalgebra S := Algebra.adjoin_le hmem
  rw [hG] at hle
  exact hle (Algebra.mem_top)

/-- **Differentials of a ring of which the base is a localization suffice.**  A denominator is a
unit upstairs, so it can be divided out of the Leibniz rule. -/
theorem D_mem_of_isLocalization {A₀ : Type*} [CommRing A₀] [Algebra R A₀] [Algebra A₀ A]
    [IsScalarTower R A₀ A] (M : Submonoid A₀) [IsLocalization M A] (S : Submodule B Ω[B⁄R])
    (h : ∀ a₀ : A₀, KaehlerDifferential.D R B (algebraMap A B (algebraMap A₀ A a₀)) ∈ S)
    (a : A) : KaehlerDifferential.D R B (algebraMap A B a) ∈ S := by
  obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj (M := M) a
  set sB : B := algebraMap A B (algebraMap A₀ A (s : A₀)) with hsB
  have hunit : IsUnit sB := by
    rw [hsB]
    exact ((IsLocalization.map_units (M := M) A s).map (algebraMap A B))
  have hkey : sB • KaehlerDifferential.D R B (algebraMap A B a) ∈ S := by
    have hD : KaehlerDifferential.D R B
        (algebraMap A B (a * algebraMap A₀ A (s : A₀))) ∈ S := by
      rw [hx]; exact h x
    rw [map_mul, Derivation.leibniz] at hD
    have h2 : algebraMap A B a • KaehlerDifferential.D R B
        (algebraMap A B (algebraMap A₀ A (s : A₀))) ∈ S :=
      Submodule.smul_mem _ _ (by
        have := h (s : A₀)
        simpa using this)
    have := Submodule.sub_mem _ hD h2
    simpa [hsB] using this
  obtain ⟨b, hb⟩ := hunit.exists_left_inv
  have hfin := Submodule.smul_mem S b hkey
  rwa [smul_smul, hb, one_smul] at hfin

end Generation

end GaloisForLFunctions.HTGeometry
