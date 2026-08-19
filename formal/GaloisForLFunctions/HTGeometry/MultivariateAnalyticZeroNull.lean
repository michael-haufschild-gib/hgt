/-
# Real-analytic zero sets in several variables are Lebesgue-null

A real-analytic function of one variable that is nonzero somewhere has a countable zero set.  In
several variables the zero set is no longer countable, but it is still null: slicing off one
coordinate, the sections over the complement of a null set of transverse points are one-variable
zero sets, and Fubini assembles them.

Main results:
* `analyticAt_cons_left`, `analyticAt_cons_right` — the coordinate slices are analytic.
* `analytic_zero_set_volume_fin` — **a nonzero real-analytic function has a null zero set**.
-/
import GaloisForLFunctions.HTGeometry.AnalyticNullPreimage
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

open Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Fixing the first coordinate is an analytic map of the remaining ones. -/
theorem analyticAt_cons_left {n : ℕ} (y : ℝ) (x₀ : Fin n → ℝ) :
    AnalyticAt ℝ (fun x : Fin n → ℝ => (Fin.cons y x : Fin (n + 1) → ℝ)) x₀ := by
  refine AnalyticAt.pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using analyticAt_const (v := y) (x := x₀)
  · have : AnalyticAt ℝ (fun x : Fin n → ℝ => x j) x₀ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).analyticAt x₀
    simpa using this

/-- Fixing the remaining coordinates is an analytic map of the first one. -/
theorem analyticAt_cons_right {n : ℕ} (x : Fin n → ℝ) (y₀ : ℝ) :
    AnalyticAt ℝ (fun y : ℝ => (Fin.cons y x : Fin (n + 1) → ℝ)) y₀ := by
  refine AnalyticAt.pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact analyticAt_id
  · simpa using analyticAt_const (v := x j) (x := y₀)

/-- The left slice of a globally analytic function is globally analytic. -/
theorem analyticOnNhd_slice_left {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : AnalyticOnNhd ℝ f univ) (y : ℝ) :
    AnalyticOnNhd ℝ (fun x : Fin n → ℝ => f (Fin.cons y x)) univ := by
  intro x₀ _
  exact AnalyticAt.comp (g := f) (f := fun x : Fin n → ℝ => (Fin.cons y x : Fin (n + 1) → ℝ))
    (x := x₀) (hf _ (mem_univ _)) (analyticAt_cons_left y x₀)

/-- The right slice of a globally analytic function is globally analytic. -/
theorem analyticOnNhd_slice_right {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : AnalyticOnNhd ℝ f univ) (x : Fin n → ℝ) :
    AnalyticOnNhd ℝ (fun y : ℝ => f (Fin.cons y x)) univ := by
  intro y₀ _
  exact AnalyticAt.comp (g := f) (f := fun y : ℝ => (Fin.cons y x : Fin (n + 1) → ℝ))
    (x := y₀) (hf _ (mem_univ _)) (analyticAt_cons_right x y₀)

/-- **A nonzero real-analytic function of finitely many real variables has a Lebesgue-null zero
set.** -/
theorem analytic_zero_set_volume_fin :
    ∀ n : ℕ, ∀ f : (Fin n → ℝ) → ℝ, AnalyticOnNhd ℝ f univ → (∃ x, f x ≠ 0) →
      volume {x : Fin n → ℝ | f x = 0} = 0 := by
  intro n
  induction n with
  | zero =>
      intro f _ hne
      obtain ⟨x₀, hx₀⟩ := hne
      have hempty : {x : Fin 0 → ℝ | f x = 0} = ∅ := by
        ext x
        have hx : x = x₀ := Subsingleton.elim _ _
        simp [hx, hx₀]
      simp [hempty]
  | succ n ih =>
      intro f hf hne
      obtain ⟨p, hp⟩ := hne
      have hpcons : (Fin.cons (p 0) (Fin.tail p) : Fin (n + 1) → ℝ) = p := Fin.cons_self_tail p
      have hslice0 : (fun x : Fin n → ℝ => f (Fin.cons (p 0) x)) (Fin.tail p) ≠ 0 := by
        simpa [hpcons] using hp
      have hZnull : volume {x : Fin n → ℝ | f (Fin.cons (p 0) x) = 0} = 0 :=
        ih _ (analyticOnNhd_slice_left hf (p 0)) ⟨Fin.tail p, hslice0⟩
      set S : Set ((Fin n → ℝ) × ℝ) := {z | f (Fin.cons z.2 z.1) = 0} with hS
      have hcons : Continuous
          (fun z : (Fin n → ℝ) × ℝ => (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ)) := by
        refine continuous_pi fun i => ?_
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          exact continuous_snd
        · simp only [Fin.cons_succ]
          exact (continuous_apply j).comp continuous_fst
      have hfcont : Continuous f := by
        have := hf.continuousOn
        rwa [continuousOn_univ] at this
      have hSmeas : MeasurableSet S :=
        (isClosed_singleton.preimage (hfcont.comp hcons)).measurableSet
      have hsections : (fun x : Fin n → ℝ => volume (Prod.mk x ⁻¹' S)) =ᵐ[volume] 0 := by
        have hae : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), f (Fin.cons (p 0) x) ≠ 0 := by
          rw [ae_iff]
          simpa using hZnull
        filter_upwards [hae] with x hx
        have hsec : Prod.mk x ⁻¹' S = {y : ℝ | f (Fin.cons y x) = 0} := by
          ext y
          simp [hS]
        rw [hsec]
        exact ((analytic_zero_set_countable (analyticOnNhd_slice_right hf x)
          ⟨p 0, hx⟩).measure_zero volume)
      have hprod : (volume.prod volume) S = 0 :=
        Measure.measure_prod_null_of_ae_null hSmeas hsections
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      let g : (Fin (n + 1) → ℝ) → ((Fin n → ℝ) × ℝ) := fun z => (e z).swap
      have hg : MeasurePreserving g volume (volume.prod volume) := by
        simpa [g, e, Function.comp_def] using
          (Measure.measurePreserving_swap.comp
            (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0))
      have hpre : g ⁻¹' S = {x : Fin (n + 1) → ℝ | f x = 0} := by
        ext z
        simp [g, e, hS, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv]
      rw [← hpre, hg.measure_preimage hSmeas.nullMeasurableSet, hprod]

end

end GaloisForLFunctions.HTGeometry
