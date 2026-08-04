import GaloisForLFunctions.HTGeometry.ClockTubeSliceHolo

/-!
# The iterates of the clock equation with several coupled transverse coordinates

The characteristic clock equation on a tube,

`∂ξ∂η u = (∑ᵢ ∂ᵢ² u + V u)/4`,

is solved by the same iteration as in one transverse variable. This file defines the iterates and
proves the two structural facts that let the iteration continue: each iterate is holomorphic along
every coordinate slice of the tube, and the whole family is continuous jointly in the two null
coordinates and the transverse point.

Neither property loses any of the tube. The estimates that force a smaller radius are needed only for
the *bounds*; the regularity is preserved exactly, because the derivative of a holomorphic function
of one variable is holomorphic on the same open set and the contour of the cross case may be chosen
from the point alone.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-- A potential of the clock equation on a tube: jointly continuous, and holomorphic along every
coordinate slice. -/
structure TubePotential (V : ℝ → ℝ → (Fin k → ℂ) → ℂ) (ρ : ℝ) : Prop where
  cont : ContinuousOn (fun q : (ℝ × ℝ) × (Fin k → ℂ) => V q.1.1 q.1.2 q.2) (univ ×ˢ tube k ρ)
  holo : ∀ s t : ℝ, SliceHolo (V s t) ρ

/-- The iterates of the characteristic clock equation on a tube. -/
noncomputable def tubeIterate (V : ℝ → ℝ → (Fin k → ℂ) → ℂ) :
    ℕ → ℝ → ℝ → (Fin k → ℂ) → ℂ
  | 0, _, _, _ => 1
  | m + 1, ξ, η, z =>
      ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η, tubeStep (V s t) (tubeIterate V m s t) z

theorem tubeIterate_zero (V : ℝ → ℝ → (Fin k → ℂ) → ℂ) (ξ η : ℝ) :
    tubeIterate V 0 ξ η = fun _ => 1 := rfl

theorem tubeIterate_succ (V : ℝ → ℝ → (Fin k → ℂ) → ℂ) (m : ℕ) (ξ η : ℝ) (z : Fin k → ℂ) :
    tubeIterate V (m + 1) ξ η z
      = ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
        tubeStep (V s t) (tubeIterate V m s t) z := rfl

set_option maxHeartbeats 1000000 in
/-- **The iterates are slice holomorphic on the tube and jointly continuous there.** -/
theorem tubeIterate_regular {ρ : ℝ} (hρ : 0 < ρ) {V : ℝ → ℝ → (Fin k → ℂ) → ℂ}
    (hV : TubePotential V ρ) :
    ∀ m : ℕ,
      (∀ s t : ℝ, SliceHolo (tubeIterate V m s t) ρ) ∧
        ContinuousOn (fun r : (ℝ × ℝ) × (Fin k → ℂ) => tubeIterate V m r.1.1 r.1.2 r.2)
          (univ ×ˢ tube k ρ) := by
  classical
  have hopen : IsOpen ((univ : Set ((ℝ : Type) × ℝ)) ×ˢ tube k ρ) :=
    isOpen_univ.prod (isOpen_tube k ρ)
  intro m
  induction m with
  | zero =>
    refine ⟨fun s t => ?_, ?_⟩
    · intro z _ i
      exact differentiableOn_const 1
    · exact continuousOn_const
  | succ m ih =>
    obtain ⟨holo, cont⟩ := ih
    -- the slice continuity of an iterate, at a fixed point of the tube
    have hcontSlice : ∀ s t : ℝ, ContinuousOn (tubeIterate V m s t) (tube k ρ) := by
      intro s t y hy
      exact ((cont.continuousAt (hopen.mem_nhds ⟨mem_univ ((s, t) : ℝ × ℝ), hy⟩)).comp
        (x := y) (f := fun y' : (Fin k → ℂ) => (((s, t) : ℝ × ℝ), y'))
        (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
    -- the step operator, jointly continuous on the tube
    have hstepAt : ∀ q : (ℝ × ℝ) × (Fin k → ℂ), q.2 ∈ tube k ρ →
        ContinuousAt (fun r : (ℝ × ℝ) × (Fin k → ℂ) =>
          tubeStep (V r.1.1 r.1.2) (tubeIterate V m r.1.1 r.1.2) r.2) q := by
      intro q hq2
      obtain ⟨ρ₁, hρ₁0, hρ₁, hq₁⟩ := exists_inner_radius hρ hq2
      have hsecond : ∀ i : Fin k, ContinuousAt (fun r : (ℝ × ℝ) × (Fin k → ℂ) =>
          cpartial i (cpartial i (tubeIterate V m r.1.1 r.1.2)) r.2) q := fun i =>
        continuousAt_cpartial_cpartial_of_tube (P := ℝ × ℝ) hρ₁ hρ₁0
          (W := fun p : ℝ × ℝ => tubeIterate V m p.1 p.2) cont (fun p => holo p.1 p.2) i hq₁
      have hsum : ContinuousAt (fun r : (ℝ × ℝ) × (Fin k → ℂ) =>
          ∑ i, cpartial i (cpartial i (tubeIterate V m r.1.1 r.1.2)) r.2) q :=
        tendsto_finsetSum (f := fun (i : Fin k) (r : (ℝ × ℝ) × (Fin k → ℂ)) =>
          cpartial i (cpartial i (tubeIterate V m r.1.1 r.1.2)) r.2)
          (a := fun i => cpartial i (cpartial i (tubeIterate V m q.1.1 q.1.2)) q.2)
          Finset.univ fun i _ => hsecond i
      have hVat : ContinuousAt (fun r : (ℝ × ℝ) × (Fin k → ℂ) => V r.1.1 r.1.2 r.2) q :=
        hV.cont.continuousAt (hopen.mem_nhds ⟨mem_univ _, hq2⟩)
      have hWat : ContinuousAt
          (fun r : (ℝ × ℝ) × (Fin k → ℂ) => tubeIterate V m r.1.1 r.1.2 r.2) q :=
        cont.continuousAt (hopen.mem_nhds ⟨mem_univ _, hq2⟩)
      exact (hsum.add (hVat.mul hWat)).div_const 4
    have hstep : ContinuousOn (fun r : (ℝ × ℝ) × (Fin k → ℂ) =>
        tubeStep (V r.1.1 r.1.2) (tubeIterate V m r.1.1 r.1.2) r.2) (univ ×ˢ tube k ρ) :=
      fun q hq => (hstepAt q hq.2).continuousWithinAt
    -- the step operator is slice holomorphic
    have hstepHolo : ∀ s t : ℝ, SliceHolo (tubeStep (V s t) (tubeIterate V m s t)) ρ :=
      fun s t => sliceHolo_tubeStep (hV.holo s t) (hcontSlice s t) (holo s t)
    refine ⟨fun ξ η => ?_, fun q hq => ?_⟩
    · -- slice holomorphy of the next iterate
      refine sliceHolo_intervalIntegral (F := fun s z =>
        ∫ t in (0 : ℝ)..η, tubeStep (V s t) (tubeIterate V m s t) z) 0 ξ ?_ ?_
      · intro z hz i q hq
        obtain ⟨ρ₁, hρ₁0, hρ₁, hq₁⟩ := exists_inner_radius hρ
          (update_mem_tube hz i hq.2)
        have hbase := continuousAt_innerIntegral_of_tube (η := η)
          (H := fun s t z => tubeStep (V s t) (tubeIterate V m s t) z) hρ₁ hρ₁0 hstep
          (q := ((q.1, Function.update z i q.2) : ℝ × (Fin k → ℂ))) hq₁
        have hmap : ContinuousAt
            (fun q' : ℝ × ℂ => ((q'.1, Function.update z i q'.2) : ℝ × (Fin k → ℂ))) q :=
          (continuous_fst.prodMk ((differentiable_updateSlice z i).continuous.comp
            continuous_snd)).continuousAt
        exact (hbase.comp (x := q)
          (f := fun q' : ℝ × ℂ => ((q'.1, Function.update z i q'.2) : ℝ × (Fin k → ℂ)))
          hmap).continuousWithinAt
      · intro s
        refine sliceHolo_intervalIntegral
          (F := fun t z => tubeStep (V s t) (tubeIterate V m s t) z) 0 η ?_ ?_
        · intro z hz i q hq
          have hmem : ((s, q.1) : ℝ × ℝ) ∈ (univ : Set (ℝ × ℝ)) := mem_univ _
          have hbase := hstepAt (((s, q.1) : ℝ × ℝ), Function.update z i q.2)
            (update_mem_tube hz i hq.2)
          have hmap : ContinuousAt (fun q' : ℝ × ℂ =>
              ((((s, q'.1) : ℝ × ℝ), Function.update z i q'.2) : (ℝ × ℝ) × (Fin k → ℂ))) q :=
            ((continuous_const.prodMk continuous_fst).prodMk
              ((differentiable_updateSlice z i).continuous.comp continuous_snd)).continuousAt
          exact (hbase.comp (x := q)
            (f := fun q' : ℝ × ℂ =>
              ((((s, q'.1) : ℝ × ℝ), Function.update z i q'.2) : (ℝ × ℝ) × (Fin k → ℂ)))
            hmap).continuousWithinAt
        · exact fun t => hstepHolo s t
    · -- joint continuity of the next iterate
      obtain ⟨ρ₁, hρ₁0, hρ₁, hq₁⟩ := exists_inner_radius hρ hq.2
      exact (continuousAt_iteratedIntegral_of_tube
        (G := fun s t z => tubeStep (V s t) (tubeIterate V m s t) z)
        hρ₁ hρ₁0 hstep hq₁).continuousWithinAt

end GaloisForLFunctions.HTGeometry
