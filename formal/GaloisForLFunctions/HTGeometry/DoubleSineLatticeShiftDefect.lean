import GaloisForLFunctions.HTGeometry.DoubleSineOrbitIndependence

/-!
# Shifts in the period lattice have base-field defects

The other half of the defect count.  Independence holds for shifts in distinct classes; for shifts
in the *same* class the two translates differ by an element of the two-cylinder base field, so they
are differentially dependent.

The reason is that the structural defects lie in the base field, translations act on the base field
by dilations, and defects compose additively:

```text
Δ_{a+b} M = T^a (Δ_b M) + Δ_a M,      Δ_{-a} M = -T^{-a}(Δ_a M).
```

So the set of shifts whose defect lies in the base field is a subgroup containing both periods,
hence contains the whole period lattice.
-/

open Filter Set Topology Complex Polynomial
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance dlsDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance dlsComplexAlgebra : Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance dlsMeroDifferential : Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

variable {l : Fin 2 → ℂ}

/-- The shifts whose defect lies in the embedded two-cylinder field. -/
def BaseDefectShift (hl : LinearIndependent ℚ l) (M : meroField (Set.univ : Set ℂ)) (h : ℂ) :
    Prop :=
  ∃ y : RatFunc (RatFunc ℂ),
    addTranslationMeroEquiv h M - M = twoCylinderEmbed hl y

theorem addTranslationMeroEquiv_zero_apply (M : meroField (Set.univ : Set ℂ)) :
    addTranslationMeroEquiv (0 : ℂ) M = M := by
  have hgerm : addTranslationAnalyticEquiv (0 : ℂ) = RingEquiv.refl _ := by
    refine RingEquiv.ext fun x => ?_
    apply Subtype.ext
    show ((addTranslationAnalyticEquiv (0 : ℂ) x : analyticSubring (Set.univ : Set ℂ)) :
        Germ (𝓟 (Set.univ : Set ℂ)) ℂ) = (x : Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
    rw [show ((addTranslationAnalyticEquiv (0 : ℂ) x : analyticSubring (Set.univ : Set ℂ)) :
        Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
        = (x : Germ (𝓟 (Set.univ : Set ℂ)) ℂ).compTendsto (addTranslation 0)
          (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)) from rfl]
    induction (x : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) using Germ.inductionOn with
    | _ F =>
      rw [Germ.coe_compTendsto]
      refine Germ.coe_eq.mpr (eventually_principal.mpr fun z _ => ?_)
      simp [addTranslation]
  have hext : ((addTranslationMeroEquiv (0 : ℂ)).toRingHom) = RingHom.id _ := by
    refine IsLocalization.ringHom_ext
      (nonZeroDivisors (analyticSubring (Set.univ : Set ℂ))) ?_
    ext c
    show addTranslationMeroEquiv (0 : ℂ)
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ) c)
      = algebraMap (analyticSubring Set.univ) (meroField Set.univ) c
    rw [addTranslationMeroEquiv_algebraMap, hgerm]
    rfl
  simpa using DFunLike.congr_fun hext M

theorem baseDefectShift_zero (hl : LinearIndependent ℚ l) (M : meroField (Set.univ : Set ℂ)) :
    BaseDefectShift hl M 0 := by
  refine ⟨0, ?_⟩
  rw [map_zero, addTranslationMeroEquiv_zero_apply, sub_self]

theorem baseDefectShift_add (hl : LinearIndependent ℚ l) (M : meroField (Set.univ : Set ℂ))
    {a b : ℂ} (ha : BaseDefectShift hl M a) (hb : BaseDefectShift hl M b) :
    BaseDefectShift hl M (a + b) := by
  obtain ⟨ya, hya⟩ := ha
  obtain ⟨yb, hyb⟩ := hb
  refine ⟨twoCylTranslate (q0 := Complex.exp (l 0 * a)) (q1 := Complex.exp (l 1 * a))
    (Complex.exp_ne_zero _) (Complex.exp_ne_zero _) yb + ya, ?_⟩
  have hsplit : addTranslationMeroEquiv (a + b) M
      = addTranslationMeroEquiv a (addTranslationMeroEquiv b M) := by
    rw [← addTranslationMeroEquiv_add]
  rw [hsplit, (twoCylinderEmbed hl).map_add,
    ← addTranslationMeroEquiv_twoCylinderEmbed_general hl a yb, ← hya]
  have hb' : addTranslationMeroEquiv b M = M + twoCylinderEmbed hl yb := by
    linear_combination hyb
  rw [hb', (addTranslationMeroEquiv a).map_add]
  ring

theorem baseDefectShift_neg (hl : LinearIndependent ℚ l) (M : meroField (Set.univ : Set ℂ))
    {a : ℂ} (ha : BaseDefectShift hl M a) : BaseDefectShift hl M (-a) := by
  obtain ⟨y, hy⟩ := ha
  refine ⟨-twoCylTranslate (q0 := Complex.exp (l 0 * (-a))) (q1 := Complex.exp (l 1 * (-a)))
    (Complex.exp_ne_zero _) (Complex.exp_ne_zero _) y, ?_⟩
  rw [(twoCylinderEmbed hl).map_neg,
    ← addTranslationMeroEquiv_twoCylinderEmbed_general hl (-a) y, ← hy,
    (addTranslationMeroEquiv (-a)).map_sub]
  have hcancel : addTranslationMeroEquiv (-a) (addTranslationMeroEquiv a M) = M := by
    rw [addTranslationMeroEquiv_add]
    have hz : -a + a = 0 := by ring
    rw [hz, addTranslationMeroEquiv_zero_apply]
  rw [hcancel]
  ring

theorem baseDefectShift_zsmul (hl : LinearIndependent ℚ l) (M : meroField (Set.univ : Set ℂ))
    {a : ℂ} (ha : BaseDefectShift hl M a) (m : ℤ) :
    BaseDefectShift hl M ((m : ℂ) * a) := by
  induction m using Int.induction_on with
  | zero => simpa using baseDefectShift_zero hl M
  | succ k ih =>
      have hadd := baseDefectShift_add hl M ih ha
      convert hadd using 2
      push_cast
      ring
  | pred k ih =>
      have hadd := baseDefectShift_add hl M ih (baseDefectShift_neg hl M ha)
      convert hadd using 2
      push_cast
      ring

/-- **Every shift in the period lattice has its defect in the base field.** -/
theorem baseDefectShift_lattice (hl : LinearIndependent ℚ l) (M : meroField (Set.univ : Set ℂ))
    {ω : Fin 2 → ℂ} (h0 : BaseDefectShift hl M (ω 0)) (h1 : BaseDefectShift hl M (ω 1))
    (m n : ℤ) : BaseDefectShift hl M ((m : ℂ) * ω 0 + (n : ℂ) * ω 1) :=
  baseDefectShift_add hl M (baseDefectShift_zsmul hl M h0 m) (baseDefectShift_zsmul hl M h1 n)

end

end GaloisForLFunctions.HTGeometry
