import GaloisForLFunctions.Bottcher.ProductCover
import GaloisForLFunctions.HTGeometry.ClosedSubgroupIdentityComponent

/-!
# Translations of several-variable meromorphic germs

The several-variable analytic germ ring `analyticSubringGen` and its meromorphic fraction field
`meroFieldGen` already exist for an arbitrary complex normed space, together with the
precomposition automorphisms of an analytic self-biholomorphism.  This file instantiates them at
the translations `z ↦ z + h` and builds the resulting period group.

* `addTranslationMeroEquivGen` — the translation automorphism of the several-variable meromorphic
  field, with `addTranslationMeroEquivGen_add` and `addTranslationMeroEquivGen_zero`;
* `meroPeriodSubgroupGen` — the period group;
* **`memPeriod_iff_gen`** — the cross-multiplied pointwise criterion;
* **`isClosed_meroPeriodSubgroupGen`** — the period group is closed.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

open Bottcher

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable section

/-! ## The translation biholomorphism -/

/-- Translation of a several-variable carrier. -/
def addTranslationGen (h : E) : E → E := fun z => z + h

theorem analyticOnNhd_addTranslationGen (h : E) (U : Set E) :
    AnalyticOnNhd ℂ (addTranslationGen h) U :=
  analyticOnNhd_id.add analyticOnNhd_const

omit [NormedSpace ℂ E] in
theorem addTranslationGen_comp_neg (h : E) (U : Set E) :
    Set.EqOn (addTranslationGen h ∘ addTranslationGen (-h)) id U := by
  intro z _
  simp [addTranslationGen]

theorem isPreconnected_univ_gen : IsPreconnected (Set.univ : Set E) :=
  (convex_univ (𝕜 := ℝ) (E := E)).isPreconnected

/-- The translation automorphism of the several-variable analytic germ ring. -/
def addTranslationAnalyticEquivGen (h : E) :
    analyticSubringGen (Set.univ : Set E) ≃+* analyticSubringGen (Set.univ : Set E) :=
  precompAnalyticEquivGen _
    (analyticOnNhd_addTranslationGen h _) (analyticOnNhd_addTranslationGen (-h) _)
    (Set.mapsTo_univ _ _) (Set.mapsTo_univ _ _)
    (addTranslationGen_comp_neg h _)
    (by simpa using addTranslationGen_comp_neg (-h) (Set.univ : Set E))

theorem addTranslationAnalyticEquivGen_coe (h : E) (a : analyticSubringGen (Set.univ : Set E)) :
    ((addTranslationAnalyticEquivGen h a : analyticSubringGen (Set.univ : Set E)) :
        Germ (𝓟 (Set.univ : Set E)) ℂ)
      = (a : Germ (𝓟 (Set.univ : Set E)) ℂ).compTendsto (addTranslationGen h)
          (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)) := rfl

/-- A translated analytic function represents the translated germ. -/
theorem addTranslationAnalyticEquivGen_rep (h : E)
    {a : analyticSubringGen (Set.univ : Set E)} {A : E → ℂ}
    (hA : Germ.coeRingHom (𝓟 (Set.univ : Set E)) A = (a : Germ (𝓟 Set.univ) ℂ)) :
    Germ.coeRingHom (𝓟 (Set.univ : Set E)) (fun z => A (z + h)) =
      ((addTranslationAnalyticEquivGen h a : analyticSubringGen (Set.univ : Set E)) :
        Germ (𝓟 (Set.univ : Set E)) ℂ) := by
  rw [addTranslationAnalyticEquivGen_coe, ← hA]
  change (↑(fun z => A (z + h)) : Germ (𝓟 (Set.univ : Set E)) ℂ) =
    (↑A : Germ (𝓟 (Set.univ : Set E)) ℂ).compTendsto (addTranslationGen h)
      (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _))
  rw [Germ.coe_compTendsto]
  rfl

theorem addTranslationAnalyticEquivGen_add (p q : E)
    (a : analyticSubringGen (Set.univ : Set E)) :
    addTranslationAnalyticEquivGen p (addTranslationAnalyticEquivGen q a)
      = addTranslationAnalyticEquivGen (p + q) a := by
  apply Subtype.ext
  rw [addTranslationAnalyticEquivGen_coe, addTranslationAnalyticEquivGen_coe,
    addTranslationAnalyticEquivGen_coe]
  induction (a : Germ (𝓟 (Set.univ : Set E)) ℂ) using Germ.inductionOn with
  | _ F =>
    rw [Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_compTendsto]
    refine Germ.coe_eq.mpr (eventually_principal.mpr fun z _ => ?_)
    simp only [Function.comp_apply, addTranslationGen]
    rw [add_assoc]

/-! ## The translation automorphism of the meromorphic field -/

local instance meroGenDomain :
    IsDomain (analyticSubringGen (Set.univ : Set E)) :=
  isDomain_analyticSubringGen Set.univ isOpen_univ isPreconnected_univ_gen Set.univ_nonempty

/-- The translation automorphism of the several-variable meromorphic field. -/
def addTranslationMeroEquivGen (h : E) :
    meroFieldGen (Set.univ : Set E) ≃+* meroFieldGen (Set.univ : Set E) :=
  precompMeroEquivGen _
    (analyticOnNhd_addTranslationGen h _) (analyticOnNhd_addTranslationGen (-h) _)
    (Set.mapsTo_univ _ _) (Set.mapsTo_univ _ _)
    (addTranslationGen_comp_neg h _)
    (by simpa using addTranslationGen_comp_neg (-h) (Set.univ : Set E))
    isOpen_univ isPreconnected_univ_gen Set.univ_nonempty

theorem addTranslationMeroEquivGen_algebraMap (h : E)
    (a : analyticSubringGen (Set.univ : Set E)) :
    addTranslationMeroEquivGen h
        (algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen Set.univ) a)
      = algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen Set.univ)
          (addTranslationAnalyticEquivGen h a) :=
  precompMeroEquivGen_algebraMap _ _ _ _ _ _ _ isOpen_univ isPreconnected_univ_gen
    Set.univ_nonempty a

theorem addTranslationMeroEquivGen_add (p q : E) (x : meroFieldGen (Set.univ : Set E)) :
    addTranslationMeroEquivGen p (addTranslationMeroEquivGen q x)
      = addTranslationMeroEquivGen (p + q) x := by
  have key : ∀ c : analyticSubringGen (Set.univ : Set E),
      addTranslationMeroEquivGen p (addTranslationMeroEquivGen q
          (algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen Set.univ) c))
        = addTranslationMeroEquivGen (p + q)
          (algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen Set.univ) c) := by
    intro c
    rw [addTranslationMeroEquivGen_algebraMap, addTranslationMeroEquivGen_algebraMap,
      addTranslationMeroEquivGen_algebraMap, addTranslationAnalyticEquivGen_add]
  obtain ⟨a, b, _hb, rfl⟩ :=
    IsFractionRing.div_surjective (A := analyticSubringGen (Set.univ : Set E)) x
  simp only [map_div₀]
  rw [key a, key b]

theorem addTranslationMeroEquivGen_zero (x : meroFieldGen (Set.univ : Set E)) :
    addTranslationMeroEquivGen (0 : E) x = x := by
  have h := addTranslationMeroEquivGen_add (0 : E) (0 : E) x
  rw [add_zero] at h
  exact (addTranslationMeroEquivGen (0 : E)).injective h

/-! ## The period group -/

/-- The period group of a several-variable global meromorphic germ. -/
def meroPeriodSubgroupGen (x : meroFieldGen (Set.univ : Set E)) : AddSubgroup E where
  carrier := {h : E | addTranslationMeroEquivGen h x = x}
  zero_mem' := addTranslationMeroEquivGen_zero x
  add_mem' := by
    intro a b ha hb
    show addTranslationMeroEquivGen (a + b) x = x
    rw [← addTranslationMeroEquivGen_add]
    rw [show addTranslationMeroEquivGen b x = x from hb]
    exact ha
  neg_mem' := by
    intro a ha
    show addTranslationMeroEquivGen (-a) x = x
    have hax : addTranslationMeroEquivGen a x = x := ha
    have hstep := congrArg (addTranslationMeroEquivGen (-a)) hax
    rw [addTranslationMeroEquivGen_add, neg_add_cancel,
      addTranslationMeroEquivGen_zero] at hstep
    exact hstep.symm

theorem mem_meroPeriodSubgroupGen {x : meroFieldGen (Set.univ : Set E)} {h : E} :
    h ∈ meroPeriodSubgroupGen (E := E) x ↔ addTranslationMeroEquivGen h x = x := Iff.rfl

/-- **Cross-multiplied period criterion in several variables.** -/
theorem mem_meroPeriodSubgroupGen_iff
    {a b : analyticSubringGen (Set.univ : Set E)} (hb : b ≠ 0)
    {A B : E → ℂ}
    (hAa : Germ.coeRingHom (𝓟 (Set.univ : Set E)) A = (a : Germ (𝓟 Set.univ) ℂ))
    (hBb : Germ.coeRingHom (𝓟 (Set.univ : Set E)) B = (b : Germ (𝓟 Set.univ) ℂ))
    (h : E) :
    h ∈ meroPeriodSubgroupGen (E := E)
        (algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen Set.univ) a /
          algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen Set.univ) b) ↔
      ∀ z : E, A (z + h) * B z = A z * B (z + h) := by
  have hinj : Function.Injective
      (algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen Set.univ)) :=
    IsFractionRing.injective (analyticSubringGen (Set.univ : Set E)) (meroFieldGen Set.univ)
  have hb0 : algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen Set.univ) b ≠ 0 := by
    simpa [map_eq_zero_iff _ hinj] using hb
  have hσb : addTranslationAnalyticEquivGen h b ≠ 0 := by
    intro hz
    apply hb
    have := congrArg (addTranslationAnalyticEquivGen h).symm hz
    rwa [RingEquiv.symm_apply_apply, map_zero] at this
  have hσb0 : algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen Set.univ)
      (addTranslationAnalyticEquivGen h b) ≠ 0 := by
    simpa [map_eq_zero_iff _ hinj] using hσb
  have hL : ((addTranslationAnalyticEquivGen h a * b : analyticSubringGen (Set.univ : Set E)) :
      Germ (𝓟 (Set.univ : Set E)) ℂ)
      = Germ.coeRingHom (𝓟 (Set.univ : Set E)) (fun z => A (z + h) * B z) := by
    rw [show ((addTranslationAnalyticEquivGen h a * b :
        analyticSubringGen (Set.univ : Set E)) : Germ (𝓟 (Set.univ : Set E)) ℂ)
        = ((addTranslationAnalyticEquivGen h a : analyticSubringGen (Set.univ : Set E)) :
            Germ (𝓟 (Set.univ : Set E)) ℂ) * (b : Germ (𝓟 (Set.univ : Set E)) ℂ) from rfl,
      ← addTranslationAnalyticEquivGen_rep h hAa, ← hBb, ← map_mul]
    rfl
  have hR : ((a * addTranslationAnalyticEquivGen h b : analyticSubringGen (Set.univ : Set E)) :
      Germ (𝓟 (Set.univ : Set E)) ℂ)
      = Germ.coeRingHom (𝓟 (Set.univ : Set E)) (fun z => A z * B (z + h)) := by
    rw [show ((a * addTranslationAnalyticEquivGen h b :
        analyticSubringGen (Set.univ : Set E)) : Germ (𝓟 (Set.univ : Set E)) ℂ)
        = (a : Germ (𝓟 (Set.univ : Set E)) ℂ) *
          ((addTranslationAnalyticEquivGen h b : analyticSubringGen (Set.univ : Set E)) :
            Germ (𝓟 (Set.univ : Set E)) ℂ) from rfl,
      ← addTranslationAnalyticEquivGen_rep h hBb, ← hAa, ← map_mul]
    rfl
  rw [mem_meroPeriodSubgroupGen, map_div₀, addTranslationMeroEquivGen_algebraMap,
    addTranslationMeroEquivGen_algebraMap, div_eq_div_iff hσb0 hb0, ← map_mul, ← map_mul,
    hinj.eq_iff, Subtype.ext_iff, hL, hR]
  change (↑(fun z => A (z + h) * B z) : Germ (𝓟 (Set.univ : Set E)) ℂ)
      = ↑(fun z => A z * B (z + h)) ↔ _
  rw [Germ.coe_eq, EventuallyEq, eventually_principal]
  exact ⟨fun hz z => hz z (Set.mem_univ z), fun hz z _ => hz z⟩

/-- **The period group of a several-variable meromorphic germ is closed.** -/
theorem isClosed_meroPeriodSubgroupGen (x : meroFieldGen (Set.univ : Set E)) :
    IsClosed ((meroPeriodSubgroupGen (E := E) x : Set E)) := by
  obtain ⟨a, b, hbmem, rfl⟩ :=
    IsFractionRing.div_surjective (A := analyticSubringGen (Set.univ : Set E)) x
  have hb : b ≠ 0 := nonZeroDivisors.ne_zero hbmem
  obtain ⟨A, hA, hAa⟩ := a.2
  obtain ⟨B, hB, hBb⟩ := b.2
  have hAcont : Continuous A := continuousOn_univ.mp hA.continuousOn
  have hBcont : Continuous B := continuousOn_univ.mp hB.continuousOn
  have hset : (meroPeriodSubgroupGen (E := E)
      (algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen Set.univ) a /
        algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen Set.univ) b) : Set E)
      = ⋂ z : E, {h : E | A (z + h) * B z = A z * B (z + h)} := by
    ext h
    simp only [SetLike.mem_coe, mem_meroPeriodSubgroupGen_iff hb hAa hBb, Set.mem_iInter,
      Set.mem_setOf_eq]
  rw [hset]
  refine isClosed_iInter fun z => ?_
  have hc1 : Continuous fun h : E => A (z + h) * B z :=
    (hAcont.comp (continuous_const.add continuous_id)).mul continuous_const
  have hc2 : Continuous fun h : E => A z * B (z + h) :=
    continuous_const.mul (hBcont.comp (continuous_const.add continuous_id))
  exact isClosed_eq hc1 hc2

end

end GaloisForLFunctions.HTGeometry
