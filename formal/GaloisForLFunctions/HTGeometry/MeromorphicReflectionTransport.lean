import GaloisForLFunctions.HTGeometry.MeromorphicReflection

/-!
# Translating a reflection is a reflection, and the transport identity in the field

Precomposition is contravariant, so the translation and reflection automorphisms of the meromorphic
field compose to another reflection:

```text
reflect_{c-a} ∘ translate_a = reflect_c,
```

because `(z + a) ↦ (c - a) - (z + a)` is `z ↦ c - z` read the other way.  That single law is what
makes the multiple-sine difference equation work: shifting by a period moves the reflected copy of
the Barnes source onto the reflection point of the frame with that period deleted.

With it, the reflected source `L = x - eps · reflect_c x` satisfies the exact transport identity

```text
(T_a - 1) L = (T_a - 1) x + eps · reflect_{c-a} ((T_a - 1) x)
```

inside the meromorphic field itself — the same field in which the Barnes ladder is proved.  This is
the field-level form of the pointwise transport, and it is what composes with the ladder.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

/-! ### Translating a reflection -/

/-- **Composition law on germs.**  Reflecting at `c - a` after translating by `a` is reflecting at
`c`. -/
theorem complexReflectionAnalyticEquiv_addTranslationAnalyticEquiv (a c : ℂ)
    (x : analyticSubring (Set.univ : Set ℂ)) :
    complexReflectionAnalyticEquiv (c - a) (addTranslationAnalyticEquiv a x) =
      complexReflectionAnalyticEquiv c x := by
  apply Subtype.ext
  show ((precompAnalytic (analyticOnNhd_complexReflection (c - a) _)
      (Set.mapsTo_univ _ _)
      (precompAnalytic (analyticOnNhd_addTranslation a _)
        (Set.mapsTo_univ _ _) x) : analyticSubring (Set.univ : Set ℂ)) :
      Germ (𝓟 (Set.univ : Set ℂ)) ℂ) =
    ((precompAnalytic (analyticOnNhd_complexReflection c _)
      (Set.mapsTo_univ _ _) x : analyticSubring (Set.univ : Set ℂ)) :
      Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
  rw [precompAnalytic_coe, precompAnalytic_coe, precompAnalytic_coe]
  induction (x : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) using Germ.inductionOn with
  | _ F =>
    rw [Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_compTendsto]
    refine Germ.coe_eq.mpr (eventually_principal.mpr fun z _ => ?_)
    simp only [Function.comp_apply, addTranslation, complexReflection]
    ring_nf

/-- **Composition law on the meromorphic field.** -/
theorem complexReflectionMeroEquiv_addTranslationMeroEquiv (a c : ℂ)
    (x : meroField (Set.univ : Set ℂ)) :
    complexReflectionMeroEquiv (c - a) (addTranslationMeroEquiv a x) =
      complexReflectionMeroEquiv c x := by
  letI := Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty
  have hext :
      (((complexReflectionMeroEquiv (c - a)).toRingHom).comp
          ((addTranslationMeroEquiv a).toRingHom)) =
        (complexReflectionMeroEquiv c).toRingHom := by
    refine IsLocalization.ringHom_ext
      (nonZeroDivisors (analyticSubring (Set.univ : Set ℂ))) ?_
    ext b
    show complexReflectionMeroEquiv (c - a)
        (addTranslationMeroEquiv a
          (algebraMap (analyticSubring Set.univ) (meroField Set.univ) b)) =
      complexReflectionMeroEquiv c
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ) b)
    rw [addTranslationMeroEquiv_algebraMap, complexReflectionMeroEquiv_algebraMap,
      complexReflectionMeroEquiv_algebraMap,
      complexReflectionAnalyticEquiv_addTranslationAnalyticEquiv]
  simpa using DFunLike.congr_fun hext x

/-- **Composition law on germs, other order.**  Translating a reflection at `c` gives the reflection
at `c - a`. -/
theorem addTranslationAnalyticEquiv_complexReflectionAnalyticEquiv (a c : ℂ)
    (x : analyticSubring (Set.univ : Set ℂ)) :
    addTranslationAnalyticEquiv a (complexReflectionAnalyticEquiv c x) =
      complexReflectionAnalyticEquiv (c - a) x := by
  apply Subtype.ext
  show ((precompAnalytic (analyticOnNhd_addTranslation a _)
      (Set.mapsTo_univ _ _)
      (precompAnalytic (analyticOnNhd_complexReflection c _)
        (Set.mapsTo_univ _ _) x) : analyticSubring (Set.univ : Set ℂ)) :
      Germ (𝓟 (Set.univ : Set ℂ)) ℂ) =
    ((precompAnalytic (analyticOnNhd_complexReflection (c - a) _)
      (Set.mapsTo_univ _ _) x : analyticSubring (Set.univ : Set ℂ)) :
      Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
  rw [precompAnalytic_coe, precompAnalytic_coe, precompAnalytic_coe]
  induction (x : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) using Germ.inductionOn with
  | _ F =>
    rw [Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_compTendsto]
    refine Germ.coe_eq.mpr (eventually_principal.mpr fun z _ => ?_)
    simp only [Function.comp_apply, addTranslation, complexReflection]
    ring_nf

/-- **Composition law on the meromorphic field, other order.** -/
theorem addTranslationMeroEquiv_complexReflectionMeroEquiv (a c : ℂ)
    (x : meroField (Set.univ : Set ℂ)) :
    addTranslationMeroEquiv a (complexReflectionMeroEquiv c x) =
      complexReflectionMeroEquiv (c - a) x := by
  letI := Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty
  have hext :
      (((addTranslationMeroEquiv a).toRingHom).comp
          ((complexReflectionMeroEquiv c).toRingHom)) =
        (complexReflectionMeroEquiv (c - a)).toRingHom := by
    refine IsLocalization.ringHom_ext
      (nonZeroDivisors (analyticSubring (Set.univ : Set ℂ))) ?_
    ext b
    show addTranslationMeroEquiv a
        (complexReflectionMeroEquiv c
          (algebraMap (analyticSubring Set.univ) (meroField Set.univ) b)) =
      complexReflectionMeroEquiv (c - a)
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ) b)
    rw [complexReflectionMeroEquiv_algebraMap, addTranslationMeroEquiv_algebraMap,
      complexReflectionMeroEquiv_algebraMap,
      addTranslationAnalyticEquiv_complexReflectionAnalyticEquiv]
  simpa using DFunLike.congr_fun hext x

/-! ### The transport identity in the field -/

/-- The reflected source `L = x - eps · reflect_c x` inside the meromorphic field. -/
def meroReflectedSource (ε : ℤ) (c : ℂ) (x : meroField (Set.univ : Set ℂ)) :
    meroField (Set.univ : Set ℂ) :=
  x - (ε : meroField (Set.univ : Set ℂ)) * complexReflectionMeroEquiv c x

/-- **The transport identity inside the meromorphic field.**  The shift difference of a reflected
source is the shift difference of the source plus `eps` times that same shift difference read
through the reflection of the *deleted* frame. -/
theorem meroShiftDiff_reflectedSource (ε : ℤ) (c a : ℂ)
    (x : meroField (Set.univ : Set ℂ)) :
    addTranslationMeroEquiv a (meroReflectedSource ε c x) - meroReflectedSource ε c x =
      (addTranslationMeroEquiv a x - x) +
        (ε : meroField (Set.univ : Set ℂ)) * complexReflectionMeroEquiv (c - a)
          (addTranslationMeroEquiv a x - x) := by
  unfold meroReflectedSource
  rw [map_sub, map_mul, map_intCast,
    addTranslationMeroEquiv_complexReflectionMeroEquiv a c x, map_sub,
    complexReflectionMeroEquiv_addTranslationMeroEquiv a c x]
  ring

/-- **The ladder transports inside the field.**  If `(T_a - 1) x = -y`, then the reflected source of
`x` at `c` has shift difference `-(reflected source of y at c - a with the flipped sign)`. -/
theorem meroShiftDiff_reflectedSource_of_ladder (ε : ℤ) (c a : ℂ)
    (x y : meroField (Set.univ : Set ℂ))
    (hladder : addTranslationMeroEquiv a x - x = -y) :
    addTranslationMeroEquiv a (meroReflectedSource ε c x) - meroReflectedSource ε c x =
      -(meroReflectedSource (-ε) (c - a) y) := by
  rw [meroShiftDiff_reflectedSource, hladder, map_neg]
  unfold meroReflectedSource
  push_cast
  ring

end

end GaloisForLFunctions
