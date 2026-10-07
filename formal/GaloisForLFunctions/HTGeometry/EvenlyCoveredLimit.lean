import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Order.IntermediateValue

/-!
# Limits of continuous lifts at evenly covered points

A connected final ray cannot change its discrete sheet over an evenly covered
neighborhood. This is classical covering theory used by the toric no-escape route.
-/

namespace GaloisForLFunctions.HTGeometry.EvenlyCoveredLimit

open Filter Topology Set

theorem exists_lift_limit {E X I : Type*}
    [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace I]
    {f : E → X} {y : X} (hcov : IsEvenlyCovered f y I)
    {u : ℝ → E} (hu : Continuous u)
    (hfu : Tendsto (fun t ↦ f (u t)) atTop (𝓝 y)) :
    ∃ e, f e = y ∧ Tendsto u atTop (𝓝 e) := by
  classical
  obtain ⟨hI, U, hyU, hU, _, H, hH⟩ := hcov
  letI : DiscreteTopology I := hI
  obtain ⟨a, ha⟩ := eventually_atTop.mp (hfu (hU.mem_nhds hyU))
  letI : PreconnectedSpace (Ici a) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ici
  let v : Ici a → f ⁻¹' U := fun t ↦ ⟨u t, ha t t.2⟩
  have hv : Continuous v := (hu.comp continuous_subtype_val).subtype_mk _
  let k : Ici a → I := fun t ↦ (H (v t)).2
  have hk : Continuous k := continuous_snd.comp (H.continuous.comp hv)
  let i₀ : I := k ⟨a, le_refl a⟩
  have hk₀ (t : Ici a) : k t = i₀ :=
    TotallyDisconnectedSpace.eq_of_continuous k hk t ⟨a, le_refl a⟩
  let base : ℝ → U := fun t ↦ if ht : a ≤ t then ⟨f (u t), ha t ht⟩ else ⟨y, hyU⟩
  have hbase : Tendsto base atTop (𝓝 (⟨y, hyU⟩ : U)) := by
    apply tendsto_subtype_rng.mpr
    apply hfu.congr'
    filter_upwards [eventually_ge_atTop a] with t ht
    simp [base, ht]
  let e := H.symm (⟨y, hyU⟩, i₀)
  refine ⟨e, ?_, ?_⟩
  · have he := hH e
    simpa [e] using he.symm
  · have hprod : Tendsto (fun t ↦ (base t, i₀)) atTop (𝓝 (⟨y, hyU⟩, i₀)) :=
      hbase.prodMk_nhds tendsto_const_nhds
    have ht := (continuous_subtype_val.comp H.symm.continuous).continuousAt.tendsto.comp hprod
    apply ht.congr'
    filter_upwards [eventually_ge_atTop a] with t ht
    have hpair : H (v ⟨t, ht⟩) = (base t, i₀) := by
      apply Prod.ext
      · apply Subtype.ext
        simpa [base, ht, v] using hH (v ⟨t, ht⟩)
      · exact hk₀ ⟨t, ht⟩
    change (H.symm (base t, i₀) : E) = u t
    rw [← hpair, H.symm_apply_apply]

theorem exp_lift_limit {u : ℝ → ℂ} (hu : Continuous u) {y : ℂ} (hy : y ≠ 0)
    (h : Tendsto (fun t ↦ Complex.exp (u t)) atTop (𝓝 y)) :
    ∃ z, Complex.exp z = y ∧ Tendsto u atTop (𝓝 z) :=
  exists_lift_limit (Complex.isCoveringMapOn_exp y hy) hu h

theorem escape_of_exp_zero {A : Type*} {l : Filter A} {u : A → ℂ}
    (h : Tendsto (fun t ↦ Complex.exp (u t)) l (𝓝 0)) :
    Tendsto u l (cocompact ℂ) := by
  apply hasBasis_cocompact.tendsto_right_iff.mpr
  intro K hK
  have hn : (0 : ℂ) ∉ Complex.exp '' K := by
    rintro ⟨z, _, hz⟩
    exact Complex.exp_ne_zero z hz
  have he : ∀ᶠ t in l, Complex.exp (u t) ∉ Complex.exp '' K :=
    h ((hK.image Complex.continuous_exp).isClosed.isOpen_compl.mem_nhds hn)
  exact he.mono fun t ht hmem ↦ ht ⟨u t, hmem, rfl⟩

theorem inv_limit_of_exp_zero {A : Type*} {l : Filter A} {u : A → ℂ}
    (h : Tendsto (fun t ↦ Complex.exp (u t)) l (𝓝 0)) :
    Tendsto (fun t ↦ (u t)⁻¹) l (𝓝 0) := by
  have hi : Tendsto (Inv.inv : ℂ → ℂ) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  exact hi.comp (escape_of_exp_zero h)

end GaloisForLFunctions.HTGeometry.EvenlyCoveredLimit
