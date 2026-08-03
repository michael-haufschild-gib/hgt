import GaloisForLFunctions.HTGeometry.ClockStripStepOperator
import GaloisForLFunctions.HTGeometry.ClockStripIteratedContinuity

/-!
# The iterates of the clock equation

The characteristic clock equation `∂ξ∂η u = (u'' + V u)/4` on a transverse strip is solved by the
iteration

`W₀ = 1`,  `W_{m+1}(ξ, η) = ∫₀^ξ ∫₀^η (W_m(s,t)'' + V·W_m(s,t))/4 ds dt`.

This file defines the iterates and proves the two structural facts that let the iteration continue:
each iterate is holomorphic in the transverse variable on the strip, and the whole family is
continuous jointly in the two null coordinates and that variable.

Neither property loses any of the strip. The derivative estimates that force a smaller radius are
needed only for the *bounds*; here every appeal to them is made at an intermediate radius chosen
separately for each point, which recovers the full strip.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric MeasureTheory

/-- The iterates of the characteristic clock equation. -/
noncomputable def clockIterate (V : ℂ → ℂ) : ℕ → ℝ → ℝ → ℂ → ℂ
  | 0, _, _, _ => 1
  | m + 1, ξ, η, z =>
      ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η, clockStripStep V (clockIterate V m s t) z

theorem clockIterate_zero (V : ℂ → ℂ) (ξ η : ℝ) :
    clockIterate V 0 ξ η = fun _ => 1 := rfl

theorem clockIterate_succ (V : ℂ → ℂ) (m : ℕ) (ξ η : ℝ) (z : ℂ) :
    clockIterate V (m + 1) ξ η z
      = ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η, clockStripStep V (clockIterate V m s t) z := rfl

/-- **The iterates are holomorphic on the strip and jointly continuous there.** -/
set_option maxHeartbeats 1000000 in
theorem clockIterate_regular {ρ : ℝ} {V : ℂ → ℂ}
    (hVc : ContinuousOn V (imStrip ρ)) (hVd : DifferentiableOn ℂ V (imStrip ρ)) :
    ∀ m : ℕ,
      (∀ s t : ℝ, DifferentiableOn ℂ (clockIterate V m s t) (imStrip ρ)) ∧
        ContinuousOn (fun r : (ℝ × ℝ) × ℂ => clockIterate V m r.1.1 r.1.2 r.2)
          (univ ×ˢ imStrip ρ) := by
  have hopen : IsOpen ((univ : Set (ℝ × ℝ)) ×ˢ imStrip ρ) :=
    isOpen_univ.prod (isOpen_imStrip ρ)
  intro m
  induction m with
  | zero =>
    refine ⟨fun s t => ?_, ?_⟩
    · rw [clockIterate_zero]
      exact differentiableOn_const 1
    · exact continuousOn_const
  | succ m ih =>
    obtain ⟨holo, cont⟩ := ih
    have hstepAt : ∀ q : (ℝ × ℝ) × ℂ, q.2 ∈ imStrip ρ →
        ContinuousAt
          (fun r : (ℝ × ℝ) × ℂ => clockStripStep V (clockIterate V m r.1.1 r.1.2) r.2) q := by
      intro q hq2
      have him : |q.2.im| < ρ := mem_imStrip.mp hq2
      have h1 : |q.2.im| < (|q.2.im| + ρ) / 2 := by linarith
      have h2 : (|q.2.im| + ρ) / 2 < ρ := by linarith
      have h0 : (0 : ℝ) ≤ (|q.2.im| + ρ) / 2 := le_trans (abs_nonneg _) h1.le
      have hsecond : ContinuousAt
          (fun q' : (ℝ × ℝ) × ℂ => deriv (deriv (clockIterate V m q'.1.1 q'.1.2)) q'.2) q :=
        continuousAt_deriv_deriv_of_strip (P := ℝ × ℝ) h2 h0
          (W := fun p : ℝ × ℝ => clockIterate V m p.1 p.2) cont (fun p => holo p.1 p.2)
          (mem_imStrip.mpr h1)
      have hVat : ContinuousAt (fun q' : (ℝ × ℝ) × ℂ => V q'.2) q :=
        (hVc.continuousAt ((isOpen_imStrip ρ).mem_nhds hq2)).comp continuousAt_snd
      have hWat : ContinuousAt
          (fun q' : (ℝ × ℝ) × ℂ => clockIterate V m q'.1.1 q'.1.2 q'.2) q :=
        cont.continuousAt (hopen.mem_nhds ⟨mem_univ _, hq2⟩)
      exact (hsecond.add (hVat.mul hWat)).div_const 4
    have hstep : ContinuousOn
        (fun r : (ℝ × ℝ) × ℂ => clockStripStep V (clockIterate V m r.1.1 r.1.2) r.2)
        (univ ×ˢ imStrip ρ) := fun q hq => (hstepAt q hq.2).continuousWithinAt
    have hinner : ∀ s η : ℝ,
        DifferentiableOn ℂ
          (fun z => ∫ t in (0 : ℝ)..η, clockStripStep V (clockIterate V m s t) z)
          (imStrip ρ) := by
      intro s η
      refine differentiableOn_intervalIntegral_of_holomorphic_on
        (F := fun t z => clockStripStep V (clockIterate V m s t) z) ?_ ?_
      · intro q hq
        have hmap : ContinuousAt
            (fun q' : ℝ × ℂ => (((s, q'.1), q'.2) : (ℝ × ℝ) × ℂ)) q :=
          Continuous.continuousAt
            ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
        exact ((hstepAt ((s, q.1), q.2) hq.2).comp hmap).continuousWithinAt
      · exact fun t => differentiableOn_clockStripStep hVd (holo s t)
    have hinnerCont : ∀ η : ℝ, ContinuousOn
        (fun q : ℝ × ℂ => ∫ t in (0 : ℝ)..η, clockStripStep V (clockIterate V m q.1 t) q.2)
        (univ ×ˢ imStrip ρ) := by
      intro η q hq
      exact (continuousAt_innerIntegral_of_strip
        (H := fun s t z => clockStripStep V (clockIterate V m s t) z)
        hstep hq.2).continuousWithinAt
    refine ⟨fun ξ η => ?_, fun q hq => ?_⟩
    · exact differentiableOn_intervalIntegral_of_holomorphic_on
        (F := fun s z => ∫ t in (0 : ℝ)..η, clockStripStep V (clockIterate V m s t) z)
        (hinnerCont η) (fun s => hinner s η)
    · exact (continuousAt_iteratedIntegral_of_strip
        (G := fun s t z => clockStripStep V (clockIterate V m s t) z)
        hstep hq.2).continuousWithinAt

end GaloisForLFunctions.HTGeometry
