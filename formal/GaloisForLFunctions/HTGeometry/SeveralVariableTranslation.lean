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
    (hA : Germ.coeRingHom (𝓟 (Set.univ : Set E)) A = (a : Germ (𝓟 (Set.univ : Set E)) ℂ)) :
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
        (algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E)) a)
      = algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E))
          (addTranslationAnalyticEquivGen h a) :=
  precompMeroEquivGen_algebraMap _ _ _ _ _ _ _ isOpen_univ isPreconnected_univ_gen
    Set.univ_nonempty a

theorem addTranslationMeroEquivGen_add (p q : E) (x : meroFieldGen (Set.univ : Set E)) :
    addTranslationMeroEquivGen p (addTranslationMeroEquivGen q x)
      = addTranslationMeroEquivGen (p + q) x := by
  have key : ∀ c : analyticSubringGen (Set.univ : Set E),
      addTranslationMeroEquivGen p (addTranslationMeroEquivGen q
          (algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E)) c))
        = addTranslationMeroEquivGen (p + q)
          (algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E)) c) := by
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
    (hAa : Germ.coeRingHom (𝓟 (Set.univ : Set E)) A = (a : Germ (𝓟 (Set.univ : Set E)) ℂ))
    (hBb : Germ.coeRingHom (𝓟 (Set.univ : Set E)) B = (b : Germ (𝓟 (Set.univ : Set E)) ℂ))
    (h : E) :
    h ∈ meroPeriodSubgroupGen (E := E)
        (algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E)) a /
          algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E)) b) ↔
      ∀ z : E, A (z + h) * B z = A z * B (z + h) := by
  have hinj : Function.Injective
      (algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E))) :=
    IsFractionRing.injective (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E))
  have hb0 : algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E)) b ≠ 0 := by
    simpa [map_eq_zero_iff _ hinj] using hb
  have hσb : addTranslationAnalyticEquivGen h b ≠ 0 := by
    intro hz
    apply hb
    have := congrArg (addTranslationAnalyticEquivGen h).symm hz
    rwa [RingEquiv.symm_apply_apply, map_zero] at this
  have hσb0 : algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E))
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
      (algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E)) a /
        algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E)) b) : Set E)
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

/-! ## Complex lines of periods -/

theorem realSmul_eq_complexSmul (r : ℝ) (u : E) : (r : ℝ) • u = ((r : ℂ)) • u := by
  rw [← IsScalarTower.algebraMap_smul ℂ r u, Complex.coe_algebraMap]

/-- The nonvanishing locus of a nonzero analytic function is dense. -/
theorem dense_ne_zero_of_analyticOnNhd {B : E → ℂ}
    (hB : AnalyticOnNhd ℂ B (Set.univ : Set E)) (hB0 : ∃ z, B z ≠ 0) :
    Dense {z : E | B z ≠ 0} := by
  refine dense_iff_inter_open.mpr fun U hU hUne => ?_
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  obtain ⟨z₀, hz₀⟩ := hUne
  have hzero : B =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hU.mem_nhds hz₀] with z hz
    by_contra hne
    exact Set.eq_empty_iff_forall_notMem.mp hcon z ⟨hz, hne⟩
  have hall := hB.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ_gen
    (Set.mem_univ z₀) hzero
  obtain ⟨w, hw⟩ := hB0
  exact hw (hall (Set.mem_univ w))

/-- **A real line of periods is a complex line of periods.**  Along the complex line through a
period direction the numerator minus the regular value times the denominator is analytic in one
variable and vanishes on the real axis, so it vanishes identically; the resulting identity extends
from the dense regular locus by continuity. -/
theorem complex_smul_mem_meroPeriodSubgroupGen
    {x : meroFieldGen (Set.univ : Set E)} {v : E}
    (hv : ∀ t : ℝ, (t : ℝ) • v ∈ meroPeriodSubgroupGen (E := E) x) (w : ℂ) :
    w • v ∈ meroPeriodSubgroupGen (E := E) x := by
  obtain ⟨a, b, hbmem, rfl⟩ :=
    IsFractionRing.div_surjective (A := analyticSubringGen (Set.univ : Set E)) x
  have hb : b ≠ 0 := nonZeroDivisors.ne_zero hbmem
  obtain ⟨A, hA, hAa⟩ := a.2
  obtain ⟨B, hB, hBb⟩ := b.2
  have hBne : ∃ z : E, B z ≠ 0 := by
    by_contra hcon
    apply hb
    have hBz : B = 0 := by
      funext z
      by_contra hz
      exact hcon ⟨z, hz⟩
    have hg : (b : Germ (𝓟 (Set.univ : Set E)) ℂ) = 0 := by
      rw [← hBb, hBz]
      exact map_zero _
    exact Subtype.ext hg
  have hdense := dense_ne_zero_of_analyticOnNhd hB hBne
  have hreal : ∀ (t : ℝ) (z : E), A (z + (t : ℝ) • v) * B z = A z * B (z + (t : ℝ) • v) :=
    fun t => (mem_meroPeriodSubgroupGen_iff hb hAa hBb ((t : ℝ) • v)).mp (hv t)
  have hreg : ∀ z : E, B z ≠ 0 → ∀ u : ℂ, A (z + u • v) * B z = A z * B (z + u • v) := by
    intro z hz u
    set c : ℂ := A z / B z with hc
    set G : ℂ → ℂ := fun s => A (z + s • v) - c * B (z + s • v) with hG
    have hlin : AnalyticOnNhd ℂ (fun s : ℂ => z + s • v) (Set.univ : Set ℂ) := by
      refine analyticOnNhd_const.add (fun s _ => ?_)
      exact (analyticAt_id).smul analyticAt_const
    have hGanal : AnalyticOnNhd ℂ G (Set.univ : Set ℂ) :=
      (hA.comp hlin (Set.mapsTo_univ _ _)).sub
        (analyticOnNhd_const.mul (hB.comp hlin (Set.mapsTo_univ _ _)))
    have hGreal : ∀ t : ℝ, G ((t : ℂ)) = 0 := by
      intro t
      have hpt := hreal t z
      show A (z + (t : ℂ) • v) - c * B (z + (t : ℂ) • v) = 0
      rw [← realSmul_eq_complexSmul t v, hc, sub_eq_zero, div_mul_eq_mul_div, eq_div_iff hz]
      exact hpt
    have hfreq : ∃ᶠ s in 𝓝[≠] (0 : ℂ), G s = 0 := by
      have hmap : Tendsto (fun t : ℝ => ((t : ℂ))) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have := (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left
            (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))
          simpa using this
        · filter_upwards [self_mem_nhdsWithin] with t ht
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
          exact fun hcon => ht (by exact_mod_cast hcon)
      exact hmap.frequently (Frequently.of_forall hGreal)
    have hzeroAll : Set.EqOn G 0 (Set.univ : Set ℂ) :=
      hGanal.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
        (Set.mem_univ (0 : ℂ)) hfreq
    have hGu : A (z + u • v) - c * B (z + u • v) = 0 := by
      have := hzeroAll (Set.mem_univ u)
      simpa [hG] using this
    rw [sub_eq_zero] at hGu
    rw [hGu, hc]
    field_simp
  refine (mem_meroPeriodSubgroupGen_iff hb hAa hBb (w • v)).mpr fun z => ?_
  have hc1 : Continuous fun z : E => A (z + w • v) * B z :=
    (((continuousOn_univ.mp hA.continuousOn)).comp (continuous_id.add continuous_const)).mul
      (continuousOn_univ.mp hB.continuousOn)
  have hc2 : Continuous fun z : E => A z * B (z + w • v) :=
    (continuousOn_univ.mp hA.continuousOn).mul
      (((continuousOn_univ.mp hB.continuousOn)).comp (continuous_id.add continuous_const))
  have hfun := Continuous.ext_on hdense hc1 hc2 (fun z hz => hreg z hz w)
  exact congrFun hfun z

/-- **The maximal real subspace of a several-variable period group is stable under `i`.** -/
theorem lineSubmodule_meroPeriodSubgroupGen_smul_I (x : meroFieldGen (Set.univ : Set E)) :
    ∀ v ∈ lineSubmodule (meroPeriodSubgroupGen (E := E) x),
      (Complex.I : ℂ) • v ∈ lineSubmodule (meroPeriodSubgroupGen (E := E) x) := by
  intro v hv
  refine mem_lineSubmodule.mpr fun t => ?_
  have hv' : ∀ s : ℝ, (s : ℝ) • v ∈ meroPeriodSubgroupGen (E := E) x := mem_lineSubmodule.mp hv
  have hrw : (t : ℝ) • ((Complex.I : ℂ) • v) = ((t : ℂ) * Complex.I) • v := by
    rw [realSmul_eq_complexSmul, smul_smul]
  rw [hrw]
  exact complex_smul_mem_meroPeriodSubgroupGen hv' _

/-- **In several variables the only remaining period-escape condition is noncompactness.**  The
period group of a global meromorphic germ is closed and its identity component is a complex
subspace. -/
theorem isEscapeSubgroup_meroPeriodSubgroupGen [FiniteDimensional ℂ E]
    (x : meroFieldGen (Set.univ : Set E))
    (hnc : ¬ CompactSpace (E ⧸ meroPeriodSubgroupGen (E := E) x)) :
    IsEscapeSubgroup (meroPeriodSubgroupGen (E := E) x) :=
  isEscapeSubgroup_of_isClosed (isClosed_meroPeriodSubgroupGen x)
    (lineSubmodule_meroPeriodSubgroupGen_smul_I x) hnc

end

end GaloisForLFunctions.HTGeometry
