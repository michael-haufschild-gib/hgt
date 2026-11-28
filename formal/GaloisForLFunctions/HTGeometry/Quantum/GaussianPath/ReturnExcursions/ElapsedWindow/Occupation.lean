import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ElapsedWindow.InitialAscent

/-! # A finite-time occupation bound for the distinguished first wait -/

open Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
open PrescribedTimes
noncomputable section

private theorem closed_shift {X : Type*} [TopologicalSpace X] (f : X × ℝ → ℝ)
    (hf : Continuous f) (u r : ℝ) : IsClosed {p : X × ℝ | f (p.1,p.2+u) ≤ r} := by
  have hm : Continuous (fun p : X × ℝ => (p.1,p.2+u)) :=
    continuous_fst.prodMk (continuous_snd.add continuous_const)
  exact isClosed_le (hf.comp hm) (continuous_const (y:=r))

/-- If the first wait lies in a given band and the first ascent lasts at
least a, the reflected interval supplies 2a-h consecutive starting dates
for a whole affordable window of length h. Integrating over prefixes
charges one joint window event at each absolute date. -/
theorem first_wait_window_occupation (n P s : ℕ) (μ : Measure (PrefixIndex n → ℝ))
    [SFinite μ] (A B a h : ℝ) :
    ENNReal.ofReal (2*a-h) * μ {x | crossingWait n P s x ∈ Icc A B ∧
      a ≤ crossingOrigin n P (9/80) x} ≤
      ∫⁻ t in Icc A (B+2*a-h), μ {x | ∀ u ∈ Icc 0 h,
        pathGateDistance n (P+s) x (t+u) ≤ 17/80} := by
  classical
  let X := PrefixIndex n → ℝ
  let E : Set X := {x | crossingWait n P s x ∈ Icc A B ∧ a ≤ crossingOrigin n P (9/80) x}
  let J := Icc A (B+2*a-h)
  let F (t : ℝ) : Set X := {x | ∀ u ∈ Icc 0 h, pathGateDistance n (P+s) x (t+u) ≤ 17/80}
  let Z : Set (X × ℝ) := {p | p.2 ∈ J ∧ p.1 ∈ F p.2}
  have mJ : MeasurableSet J := measurableSet_Icc
  have mE : MeasurableSet E := ((measurable_crossingWait n P s) measurableSet_Icc).inter
    (measurableSet_le measurable_const (measurable_crossingOrigin n P (9/80)))
  have mZ : MeasurableSet Z := by
    have he : Z = (Prod.snd ⁻¹' J) ∩ ⋂ u : Icc (0:ℝ) h,
        {p : X × ℝ | pathGateDistance n (P+s) p.1 (p.2+u.val) ≤ 17/80} := by
      ext p
      simp only [Z,F,mem_setOf_eq,mem_inter_iff,mem_preimage,mem_iInter]
      exact and_congr_right (fun _ => ⟨fun f u => f u u.2,fun f u hu => f ⟨u,hu⟩⟩)
    rw [he]
    apply (measurable_snd mJ).inter
    apply IsClosed.measurableSet
    apply isClosed_iInter
    intro u
    exact closed_shift (fun p => pathGateDistance n (P+s) p.1 p.2)
      (continuous_distance n (P+s)) u.val (17/80)
  calc
    _ = ∫⁻ x, E.indicator (fun _ => ENNReal.ofReal (2*a-h)) x ∂μ := by
      rw [lintegral_indicator mE,setLIntegral_const]
    _ ≤ (μ.prod volume) Z := by
      rw [Measure.prod_apply mZ]
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ E
      · rw [indicator_of_mem hx]
        let Δ := crossingWait n P s x
        let σ := crossingOrigin n P (9/80) x
        have hΔ : Δ ∈ Icc A B := hx.1
        have hσ : a ≤ σ := hx.2
        have hsub : Ioo Δ (Δ+2*a-h) ⊆ Prod.mk x ⁻¹' Z := by
          intro t ht
          refine ⟨⟨hΔ.1.trans ht.1.le,by linarith only [ht.2,hΔ.2]⟩,?_⟩
          intro u hu
          exact reflected_initial_segment n P s x (t+u)
            ⟨by linarith only [ht.1,hu.1],by linarith only [ht.2,hu.2,hσ]⟩
        have hv := measure_mono (μ:=volume) hsub
        rwa [Real.volume_Ioo,show Δ+2*a-h-Δ=2*a-h by ring] at hv
      · rw [indicator_of_notMem hx]
        exact zero_le
    _ = _ := by
      rw [Measure.prod_apply_symm mZ,←lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro t
      by_cases ht : t ∈ J
      · rw [indicator_of_mem ht]
        congr 1
        exact Set.ext fun x => (and_iff_right ht)
      · rw [indicator_of_notMem ht]
        have hz : (fun x : X => (x,t)) ⁻¹' Z = ∅ := Set.eq_empty_iff_forall_notMem.mpr
          (fun _ hx => ht hx.1)
        rw [hz,measure_empty]

#print axioms first_wait_window_occupation
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
