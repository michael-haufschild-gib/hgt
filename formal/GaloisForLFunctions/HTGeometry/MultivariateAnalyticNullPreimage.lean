/-
# Nonconstant real-analytic maps of several variables pull null sets back to null sets

In one variable this is the countability of the critical set plus local analytic inversion.  In
several variables it follows by peeling off one coordinate: either the function does not depend on
that coordinate at all, in which case the statement descends to one variable fewer, or the analytic
difference between the function and its slice at zero is not identically zero, in which case almost
every transverse slice is a nonconstant one-variable analytic function and Fubini assembles the
one-variable law.

Consequently the pushforward of any measure dominated by Lebesgue measure under a nonconstant
real-analytic function is absolutely continuous.

Main results:
* `slicePair` — the measure-preserving coordinate split peeling off the first variable.
* `analytic_preimage_volume_eq_zero_fin` — **the null-preimage law in several variables**.
* `absolutelyContinuous_map_analytic` — the pushforward is absolutely continuous.
-/
import GaloisForLFunctions.HTGeometry.MultivariateAnalyticZeroNull

open Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The coordinate split peeling the first variable off a finite real product. -/
def slicePair (n : ℕ) : (Fin (n + 1) → ℝ) → ((Fin n → ℝ) × ℝ) :=
  fun w => (Fin.tail w, w 0)

theorem measurePreserving_slicePair (n : ℕ) :
    MeasurePreserving (slicePair n) volume (volume.prod volume) := by
  have h : MeasurePreserving (fun w : Fin (n + 1) → ℝ => (Fin.tail w, w 0)) volume
      (volume.prod volume) := by
    simpa [Function.comp_def] using
      (Measure.measurePreserving_swap.comp
        (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0))
  exact h

theorem slicePair_preimage_cons {n : ℕ} (Q : (Fin (n + 1) → ℝ) → Prop) :
    slicePair n ⁻¹' {z : (Fin n → ℝ) × ℝ | Q (Fin.cons z.2 z.1)} = {w | Q w} := by
  ext w
  simp only [mem_preimage, mem_setOf_eq, slicePair, Fin.cons_self_tail]

theorem slicePair_preimage_prod_univ {n : ℕ} (T : Set (Fin n → ℝ)) :
    slicePair n ⁻¹' (T ×ˢ (univ : Set ℝ)) = {w : Fin (n + 1) → ℝ | Fin.tail w ∈ T} := by
  ext w
  simp [slicePair]

/-- Peeling off the first coordinate is an analytic map. -/
theorem analyticAt_tail {n : ℕ} (w₀ : Fin (n + 1) → ℝ) :
    AnalyticAt ℝ (fun w : Fin (n + 1) → ℝ => (Fin.tail w : Fin n → ℝ)) w₀ := by
  refine AnalyticAt.pi fun j => ?_
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j.succ).analyticAt w₀

/-- **The null-preimage law in several variables.**  A nonconstant globally real-analytic function
of finitely many real variables pulls every Lebesgue-null set back to a Lebesgue-null set. -/
theorem analytic_preimage_volume_eq_zero_fin :
    ∀ n : ℕ, ∀ f : (Fin n → ℝ) → ℝ, AnalyticOnNhd ℝ f univ → (∃ a b, f a ≠ f b) →
      ∀ E : Set ℝ, volume E = 0 → volume (f ⁻¹' E) = 0 := by
  intro n
  induction n with
  | zero =>
      intro f _ hnc
      obtain ⟨a, b, hab⟩ := hnc
      exact absurd (congrArg f (Subsingleton.elim a b)) hab
  | succ n ih =>
      intro f hf hnc E hE
      obtain ⟨E', hEE', hE'meas, hE'null⟩ := exists_measurable_superset_of_null hE
      have hfcont : Continuous f := by
        have := hf.continuousOn
        rwa [continuousOn_univ] at this
      have hcons : Continuous
          (fun z : (Fin n → ℝ) × ℝ => (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ)) := by
        refine continuous_pi fun i => ?_
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          exact continuous_snd
        · simp only [Fin.cons_succ]
          exact (continuous_apply j).comp continuous_fst
      have hcons0 : Continuous
          (fun z : (Fin n → ℝ) × ℝ => (Fin.cons 0 z.1 : Fin (n + 1) → ℝ)) := by
        refine continuous_pi fun i => ?_
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          exact continuous_const
        · simp only [Fin.cons_succ]
          exact (continuous_apply j).comp continuous_fst
      refine measure_mono_null (preimage_mono hEE') ?_
      obtain ⟨a, b, hab⟩ := hnc
      have hgan : AnalyticOnNhd ℝ (fun x : Fin n → ℝ => f (Fin.cons 0 x)) univ :=
        analyticOnNhd_slice_left hf 0
      have hFan : AnalyticOnNhd ℝ
          (fun w : Fin (n + 1) → ℝ => f w - f (Fin.cons 0 (Fin.tail w))) univ := by
        intro w₀ _
        refine (hf _ (mem_univ _)).sub ?_
        exact AnalyticAt.comp
          (g := fun x : Fin n → ℝ => f (Fin.cons 0 x))
          (f := fun w : Fin (n + 1) → ℝ => (Fin.tail w : Fin n → ℝ)) (x := w₀)
          (hgan _ (mem_univ _)) (analyticAt_tail w₀)
      by_cases hFzero : ∀ w : Fin (n + 1) → ℝ, f w - f (Fin.cons 0 (Fin.tail w)) = 0
      · have hfeq : ∀ w : Fin (n + 1) → ℝ, f w = f (Fin.cons 0 (Fin.tail w)) := by
          intro w
          have := hFzero w
          linarith
        have hgnc : ∃ a' b' : Fin n → ℝ, f (Fin.cons 0 a') ≠ f (Fin.cons 0 b') := by
          refine ⟨Fin.tail a, Fin.tail b, ?_⟩
          rw [← hfeq a, ← hfeq b]
          exact hab
        have hgnull : volume ((fun x : Fin n → ℝ => f (Fin.cons 0 x)) ⁻¹' E') = 0 :=
          ih _ hgan hgnc E' hE'null
        have hgmeas : MeasurableSet ((fun x : Fin n → ℝ => f (Fin.cons 0 x)) ⁻¹' E') := by
          refine hE'meas.preimage ?_
          refine (hfcont.comp ?_).measurable
          refine continuous_pi fun i => ?_
          refine Fin.cases ?_ (fun j => ?_) i
          · simp only [Fin.cons_zero]
            exact continuous_const
          · simp only [Fin.cons_succ]
            exact continuous_apply j
        have hset : f ⁻¹' E' =
            slicePair n ⁻¹' (((fun x : Fin n → ℝ => f (Fin.cons 0 x)) ⁻¹' E') ×ˢ univ) := by
          rw [slicePair_preimage_prod_univ]
          ext w
          simp only [mem_preimage, mem_setOf_eq]
          rw [hfeq w]
        rw [hset, (measurePreserving_slicePair n).measure_preimage
          ((hgmeas.prod MeasurableSet.univ).nullMeasurableSet), Measure.prod_prod, hgnull,
          zero_mul]
      · rw [not_forall] at hFzero
        have hFnull : volume {w : Fin (n + 1) → ℝ | f w - f (Fin.cons 0 (Fin.tail w)) = 0} = 0 :=
          analytic_zero_set_volume_fin (n + 1) _ hFan hFzero
        set T : Set ((Fin n → ℝ) × ℝ) :=
          {z | f (Fin.cons z.2 z.1) - f (Fin.cons 0 z.1) = 0} with hT
        have hTmeas : MeasurableSet T := by
          refine (isClosed_singleton.preimage ?_).measurableSet
          exact (hfcont.comp hcons).sub (hfcont.comp hcons0)
        have hTpre : slicePair n ⁻¹' T =
            {w : Fin (n + 1) → ℝ | f w - f (Fin.cons 0 (Fin.tail w)) = 0} := by
          ext w
          simp only [hT, mem_preimage, mem_setOf_eq, slicePair, Fin.cons_self_tail]
        have hTnull : (volume.prod volume) T = 0 := by
          rw [← (measurePreserving_slicePair n).measure_preimage hTmeas.nullMeasurableSet, hTpre]
          exact hFnull
        have hslices := (Measure.measure_prod_null hTmeas).mp hTnull
        set S : Set ((Fin n → ℝ) × ℝ) := {z | f (Fin.cons z.2 z.1) ∈ E'} with hS
        have hSmeas : MeasurableSet S := hE'meas.preimage (hfcont.comp hcons).measurable
        have hSsections : (fun x : Fin n → ℝ => volume (Prod.mk x ⁻¹' S)) =ᵐ[volume] 0 := by
          filter_upwards [hslices] with x hx
          have hxsec : volume {y : ℝ | f (Fin.cons y x) - f (Fin.cons 0 x) = 0} = 0 := by
            have hrew : Prod.mk x ⁻¹' T = {y : ℝ | f (Fin.cons y x) - f (Fin.cons 0 x) = 0} := by
              ext y
              simp only [hT, mem_preimage, mem_setOf_eq]
            rw [hrew] at hx
            simpa using hx
          have hne : ∃ y : ℝ, f (Fin.cons y x) ≠ f (Fin.cons 0 x) := by
            by_contra hcon
            rw [not_exists] at hcon
            simp only [not_not] at hcon
            have huniv : {y : ℝ | f (Fin.cons y x) - f (Fin.cons 0 x) = 0} = univ := by
              ext y
              simp [hcon y]
            rw [huniv] at hxsec
            simp at hxsec
          obtain ⟨y₁, hy₁⟩ := hne
          have hsec : Prod.mk x ⁻¹' S = {y : ℝ | f (Fin.cons y x) ∈ E'} := by
            ext y
            simp only [hS, mem_preimage, mem_setOf_eq]
          rw [hsec]
          exact analytic_preimage_volume_eq_zero (analyticOnNhd_slice_right hf x)
            ⟨y₁, 0, hy₁⟩ hE'null
        have hSnull : (volume.prod volume) S = 0 :=
          Measure.measure_prod_null_of_ae_null hSmeas hSsections
        rw [show f ⁻¹' E' = slicePair n ⁻¹' S from (slicePair_preimage_cons _).symm,
          (measurePreserving_slicePair n).measure_preimage hSmeas.nullMeasurableSet]
        exact hSnull

/-- **The pushforward of a measure dominated by Lebesgue measure under a nonconstant real-analytic
function is absolutely continuous.** -/
theorem absolutelyContinuous_map_analytic {n : ℕ} {μ : Measure (Fin n → ℝ)}
    (hμ : μ ≪ volume) {f : (Fin n → ℝ) → ℝ} (hf : AnalyticOnNhd ℝ f univ)
    (hnc : ∃ a b, f a ≠ f b) (hmeas : Measurable f) :
    Measure.map f μ ≪ volume := by
  intro E hE
  obtain ⟨E', hEE', hE'meas, hE'null⟩ := exists_measurable_superset_of_null hE
  refine measure_mono_null hEE' ?_
  rw [Measure.map_apply hmeas hE'meas]
  exact hμ (analytic_preimage_volume_eq_zero_fin n f hf hnc E' hE'null)

end

end GaloisForLFunctions.HTGeometry
