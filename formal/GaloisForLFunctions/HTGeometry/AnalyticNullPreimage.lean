import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Topology.Compactness.Lindelof

/-!
# Null-preimage law for nonconstant real-analytic maps

A nonconstant real-analytic function has a countable critical set and is locally
analytically invertible off that set.  Consequently it pulls every
Lebesgue-null set back to a Lebesgue-null set.  This file proves that law
directly from isolated zeros, compact exhaustion, local analytic inverses, and
the differentiable null-image theorem.
-/

open Set Filter Metric Topology MeasureTheory
open scoped Topology ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The zero set of a nonzero globally real-analytic function is countable. -/
theorem analytic_zero_set_countable
    {f : ℝ → ℝ} (hf : AnalyticOnNhd ℝ f univ)
    (hne : ∃ x, f x ≠ 0) : {x | f x = 0}.Countable := by
  obtain ⟨x0, hx0⟩ := hne
  have hcod : f ⁻¹' ({0} : Set ℝ)ᶜ ∈ codiscrete ℝ :=
    hf.preimage_zero_mem_codiscrete hx0
  change f ⁻¹' ({0} : Set ℝ)ᶜ ∈ codiscreteWithin univ at hcod
  have hlocalRaw :=
    (codiscreteWithin_iff_locallyFiniteComplementWithin.mp hcod)
  have hlocal : ∀ z : ℝ, ∃ t ∈ 𝓝 z, (t ∩ {x | f x = 0}).Finite := by
    intro z
    have hset : univ \ (f ⁻¹' ({0} : Set ℝ)ᶜ) = {x | f x = 0} := by
      ext y
      simp
    simpa only [hset] using hlocalRaw z (mem_univ z)
  have hlocalOpen :
      ∀ z : ℝ, ∃ U : Set ℝ, IsOpen U ∧ z ∈ U ∧
        (U ∩ {x | f x = 0}).Finite := by
    intro z
    obtain ⟨t, ht, htFin⟩ := hlocal z
    obtain ⟨U, hUt, hUopen, hzU⟩ := _root_.mem_nhds_iff.mp ht
    exact ⟨U, hUopen, hzU, htFin.subset (inter_subset_inter hUt Subset.rfl)⟩
  choose U hUopen hUmem hUfinite using hlocalOpen
  have hfiniteBounded (n : ℕ) :
      ({x | f x = 0} ∩ closedBall 0 (n : ℝ)).Finite := by
    have hballCover : closedBall (0 : ℝ) n ⊆ ⋃ z ∈ (univ : Set ℝ), U z := by
      intro z hz
      simp only [mem_iUnion, mem_univ]
      exact ⟨z, ⟨trivial, hUmem z⟩⟩
    obtain ⟨b, _hbsub, hbfinite, hbcover⟩ :=
      (isCompact_closedBall (0 : ℝ) n).elim_finite_subcover_image
        (b := (univ : Set ℝ)) (c := U)
        (fun z _ => hUopen z) hballCover
    have hsub : {x | f x = 0} ∩ closedBall 0 (n : ℝ) ⊆
        ⋃ z ∈ b, U z ∩ {x | f x = 0} := by
      intro z hz
      have hzU := hbcover hz.2
      simp only [mem_iUnion] at hzU ⊢
      obtain ⟨i, hi⟩ := hzU
      obtain ⟨hib, hiU⟩ := hi
      exact ⟨i, ⟨hib, hiU, hz.1⟩⟩
    exact (hbfinite.biUnion fun z _ => hUfinite z).subset hsub
  have hcover : {x | f x = 0} =
      ⋃ n : ℕ, ({x | f x = 0} ∩ closedBall 0 (n : ℝ)) := by
    rw [← inter_iUnion, iUnion_closedBall_nat, inter_univ]
  rw [hcover]
  exact countable_iUnion fun n => (hfiniteBounded n).countable

/-- **Real-analytic null-preimage law.** A nonconstant globally real-analytic
map pulls every Lebesgue-null set back to a Lebesgue-null set. -/
theorem analytic_preimage_volume_eq_zero
    {f : ℝ → ℝ} (hf : AnalyticOnNhd ℝ f univ)
    (hnonconstant : ∃ x y, f x ≠ f y)
    {E : Set ℝ} (hE : volume E = 0) :
    volume (f ⁻¹' E) = 0 := by
  obtain ⟨x0, y0, hxy⟩ := hnonconstant
  have hderivExists : ∃ x, deriv f x ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hxy (is_const_of_deriv_eq_zero
      (differentiableOn_univ.mp hf.differentiableOn) h x0 y0)
  have hcriticalCountable : {x | deriv f x = 0}.Countable :=
    analytic_zero_set_countable hf.deriv hderivExists
  have hcriticalNull : volume {x | deriv f x = 0} = 0 :=
    hcriticalCountable.measure_zero volume
  have hlocalNull : ∀ x : ℝ, deriv f x ≠ 0 →
      ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ volume (f ⁻¹' E ∩ U) = 0 := by
    intro x hx
    let hax : AnalyticAt ℝ f x := hf x (mem_univ x)
    let hsx : HasStrictDerivAt f (deriv f x) x := hax.hasStrictDerivAt
    let g : ℝ → ℝ := hsx.localInverse f (deriv f x) x hx
    have hleftEv : ∀ᶠ y in 𝓝 x, g (f y) = y :=
      hsx.eventually_left_inverse hx
    have hgan : AnalyticAt ℝ g (f x) := hax.analyticAt_localInverse hx
    have hgdiffEv : ∀ᶠ y in 𝓝 (f x), DifferentiableAt ℝ g y :=
      hgan.eventually_analyticAt.mono fun _ hy => hy.differentiableAt
    obtain ⟨V, hVsub, hVopen, hfxV⟩ := _root_.mem_nhds_iff.mp hgdiffEv
    obtain ⟨U0, hU0sub, hU0open, hxU0⟩ := _root_.mem_nhds_iff.mp hleftEv
    let U := U0 ∩ f ⁻¹' V
    have hUopen : IsOpen U := hU0open.inter
      (hVopen.preimage (continuousOn_univ.mp hf.continuousOn))
    have hxU : x ∈ U := ⟨hxU0, hfxV⟩
    have hdiff : DifferentiableOn ℝ g (E ∩ V) := by
      intro y hy
      exact (hVsub hy.2).differentiableWithinAt
    have hEVnull : volume (E ∩ V) = 0 :=
      measure_mono_null inter_subset_left hE
    have himageNull : volume (g '' (E ∩ V)) = 0 :=
      addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
        volume hdiff hEVnull
    have hsubset : f ⁻¹' E ∩ U ⊆ g '' (E ∩ V) := by
      intro y hy
      refine ⟨f y, ⟨hy.1, hy.2.2⟩, ?_⟩
      exact hU0sub hy.2.1
    exact ⟨U, hUopen, hxU, measure_mono_null hsubset himageNull⟩
  let regular : Set ℝ := {x | deriv f x ≠ 0}
  choose U hUopen hUmem hUnull using hlocalNull
  have hcover : regular ⊆ ⋃ x : regular, U x x.prop := by
    intro x hx
    simp only [mem_iUnion]
    exact ⟨⟨x, hx⟩, hUmem x hx⟩
  have hregularLindelof : IsLindelof regular :=
    isLindelof_iff_lindelofSpace.mpr inferInstance
  obtain ⟨r, hrcount, hrcover⟩ :=
    hregularLindelof.elim_countable_subcover
      (fun x : regular => U x x.prop) (fun x => hUopen x x.prop) hcover
  letI : Encodable r := hrcount.toEncodable
  have hregularNull : volume (f ⁻¹' E ∩ regular) = 0 := by
    apply measure_mono_null ?_ (measure_iUnion_null fun x : r => hUnull x.1 x.1.prop)
    intro x hx
    have hxcover := hrcover hx.2
    simp only [mem_iUnion] at hxcover ⊢
    obtain ⟨i, hi⟩ := hxcover
    obtain ⟨hir, hxUi⟩ := hi
    exact ⟨⟨i, hir⟩, hx.1, hxUi⟩
  have hcriticalPartNull : volume (f ⁻¹' E ∩ {x | deriv f x = 0}) = 0 :=
    measure_mono_null inter_subset_right hcriticalNull
  apply measure_mono_null ?_ (measure_union_null hregularNull hcriticalPartNull)
  intro x hx
  by_cases hdx : deriv f x = 0
  · exact Or.inr ⟨hx, hdx⟩
  · exact Or.inl ⟨hx, hdx⟩

/-- Local-domain form of the real-analytic null-preimage law. It applies on an
open set whenever the derivative is nowhere identically zero on a
neighborhood. This is the form needed for meromorphic affine charts. -/
theorem analyticOnNhd_preimage_volume_eq_zero_of_deriv_not_eventually_zero
    {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℝ f U)
    (hnonflat : ∀ x ∈ U, ¬ ∀ᶠ y in 𝓝 x, deriv f y = 0)
    {E : Set ℝ} (hE : volume E = 0) :
    volume (f ⁻¹' E ∩ U) = 0 := by
  let critical : Set ℝ := {x | x ∈ U ∧ deriv f x = 0}
  have hlocalCritical : ∀ x ∈ U,
      ∃ V : Set ℝ, IsOpen V ∧ x ∈ V ∧ (V ∩ critical).Finite := by
    intro x hx
    have hpunct : ∀ᶠ y in 𝓝[≠] x, deriv f y ≠ 0 :=
      ((hf x hx).deriv.eventually_eq_zero_or_eventually_ne_zero).resolve_left
        (hnonflat x hx)
    have hev : ∀ᶠ y in 𝓝 x, y ∈ ({x} : Set ℝ)ᶜ → deriv f y ≠ 0 :=
      eventually_nhdsWithin_iff.mp hpunct
    obtain ⟨V, hVsub, hVopen, hxV⟩ := _root_.mem_nhds_iff.mp hev
    refine ⟨V, hVopen, hxV, (finite_singleton x).subset ?_⟩
    intro y hy
    by_contra hyx
    have hyne : y ∈ ({x} : Set ℝ)ᶜ := by simpa [mem_compl_iff] using hyx
    exact (hVsub hy.1 hyne) hy.2.2
  choose V hVopen hVmem hVfinite using hlocalCritical
  have hcriticalCover : U ⊆ ⋃ x : U, V x x.prop := by
    intro x hx
    simp only [mem_iUnion]
    exact ⟨⟨x, hx⟩, hVmem x hx⟩
  have hULindelof : IsLindelof U :=
    isLindelof_iff_lindelofSpace.mpr inferInstance
  obtain ⟨rCrit, hrCritCount, hrCritCover⟩ :=
    hULindelof.elim_countable_subcover
      (fun x : U => V x x.prop) (fun x => hVopen x x.prop) hcriticalCover
  letI : Encodable rCrit := hrCritCount.toEncodable
  have hcriticalCountable : critical.Countable := by
    apply (countable_iUnion fun x : rCrit => (hVfinite x.1 x.1.prop).countable).mono
    intro x hx
    have hxcover := hrCritCover hx.1
    simp only [mem_iUnion] at hxcover ⊢
    obtain ⟨i, hi⟩ := hxcover
    obtain ⟨hir, hxi⟩ := hi
    exact ⟨⟨i, hir⟩, hxi, hx⟩
  have hcriticalNull : volume critical = 0 :=
    hcriticalCountable.measure_zero volume
  have hlocalRegular : ∀ x ∈ U, deriv f x ≠ 0 →
      ∃ W : Set ℝ, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
        volume (f ⁻¹' E ∩ W) = 0 := by
    intro x hx hdx
    let hax : AnalyticAt ℝ f x := hf x hx
    let hsx : HasStrictDerivAt f (deriv f x) x := hax.hasStrictDerivAt
    let g : ℝ → ℝ := hsx.localInverse f (deriv f x) x hdx
    have hleftEv : ∀ᶠ y in 𝓝 x, g (f y) = y :=
      hsx.eventually_left_inverse hdx
    have hgan : AnalyticAt ℝ g (f x) := hax.analyticAt_localInverse hdx
    have hgdiffEv : ∀ᶠ y in 𝓝 (f x), DifferentiableAt ℝ g y :=
      hgan.eventually_analyticAt.mono fun _ hy => hy.differentiableAt
    obtain ⟨T, hTsub, hTopen, hfxT⟩ := _root_.mem_nhds_iff.mp hgdiffEv
    obtain ⟨W0, hW0sub, hW0open, hxW0⟩ := _root_.mem_nhds_iff.mp hleftEv
    let W := W0 ∩ (U ∩ f ⁻¹' T)
    have hWopen : IsOpen W := hW0open.inter
      (hf.continuousOn.isOpen_inter_preimage hU hTopen)
    have hxW : x ∈ W := ⟨hxW0, hx, hfxT⟩
    have hWsub : W ⊆ U := fun _ hy => hy.2.1
    have hdiff : DifferentiableOn ℝ g (E ∩ T) := by
      intro y hy
      exact (hTsub hy.2).differentiableWithinAt
    have hETnull : volume (E ∩ T) = 0 :=
      measure_mono_null inter_subset_left hE
    have himageNull : volume (g '' (E ∩ T)) = 0 :=
      addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
        volume hdiff hETnull
    have hsubset : f ⁻¹' E ∩ W ⊆ g '' (E ∩ T) := by
      intro y hy
      refine ⟨f y, ⟨hy.1, hy.2.2.2⟩, ?_⟩
      exact hW0sub hy.2.1
    exact ⟨W, hWopen, hxW, hWsub, measure_mono_null hsubset himageNull⟩
  let regular : Set ℝ := {x | x ∈ U ∧ deriv f x ≠ 0}
  choose W hWopen hWmem hWsub hWnull using hlocalRegular
  have hregularCover : regular ⊆ ⋃ x : regular, W x x.prop.1 x.prop.2 := by
    intro x hx
    simp only [mem_iUnion]
    exact ⟨⟨x, hx⟩, hWmem x hx.1 hx.2⟩
  have hregularLindelof : IsLindelof regular :=
    isLindelof_iff_lindelofSpace.mpr inferInstance
  obtain ⟨rReg, hrRegCount, hrRegCover⟩ :=
    hregularLindelof.elim_countable_subcover
      (fun x : regular => W x x.prop.1 x.prop.2)
      (fun x => hWopen x x.prop.1 x.prop.2) hregularCover
  letI : Encodable rReg := hrRegCount.toEncodable
  have hregularNull : volume (f ⁻¹' E ∩ regular) = 0 := by
    apply measure_mono_null ?_
      (measure_iUnion_null fun x : rReg => hWnull x.1 x.1.prop.1 x.1.prop.2)
    intro x hx
    have hxcover := hrRegCover hx.2
    simp only [mem_iUnion] at hxcover ⊢
    obtain ⟨i, hi⟩ := hxcover
    obtain ⟨hir, hxi⟩ := hi
    exact ⟨⟨i, hir⟩, hx.1, hxi⟩
  have hcriticalPartNull : volume (f ⁻¹' E ∩ critical) = 0 :=
    measure_mono_null inter_subset_right hcriticalNull
  apply measure_mono_null ?_ (measure_union_null hregularNull hcriticalPartNull)
  intro x hx
  by_cases hdx : deriv f x = 0
  · exact Or.inr ⟨hx.1, hx.2, hdx⟩
  · exact Or.inl ⟨hx.1, hx.2, hdx⟩

end

end GaloisForLFunctions.HTGeometry
