import GaloisForLFunctions.RHTower.TraceClassCyclicity
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Strong bounded convergence against a trace-class operator

A uniformly operator-bounded net that converges strongly may be multiplied on the left by a
fixed trace-class operator without losing convergence of ordinary traces.  The proof uses a
Hilbert--Schmidt factorization of the trace-class factor, cyclically places the varying operator
between the two Hilbert--Schmidt factors, and applies Tannery's theorem to the resulting diagonal.
-/

noncomputable section

open Complex ContinuousLinearMap Filter
open scoped InnerProductSpace Topology

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Uniformly bounded strong convergence is trace-continuous after right multiplication by a
fixed trace-class operator.** -/
theorem opTrace_comp_tendsto_of_strong_tendsto_of_uniform_bound
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {Aι : ι → H →L[ℂ] H} {A T : H →L[ℂ] H}
    (hT : T.IsTraceClass) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ n in l, ‖Aι n‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun n => Aι n x) l (𝓝 (A x))) :
    Tendsto (fun n => opTrace (Aι n ∘L T)) l
      (𝓝 (opTrace (A ∘L T))) := by
  obtain ⟨S, U, hS, hU, hfac⟩ := hT
  let b := hsBasis ℂ H
  let f := fun n i =>
    inner ℂ (adjoint U (b i)) (Aι n (S (b i)))
  let g := fun i =>
    inner ℂ (adjoint U (b i)) (A (S (b i)))
  let bound := fun i =>
    (C / 2) * (‖adjoint U (b i)‖ ^ 2 + ‖S (b i)‖ ^ 2)
  have hboundSummable : Summable bound := by
    have hsum := (hU.adjoint.summable b).add (hS.summable b)
    have hscaled := Summable.mul_left (C / 2) hsum
    simpa only [bound] using hscaled
  have hpoint : ∀ i, Tendsto (fun n => f n i) l (𝓝 (g i)) := by
    intro i
    exact ((innerSL ℂ (adjoint U (b i))).continuous.tendsto
      (A (S (b i)))).comp (hstrong (S (b i)))
  have hdom : ∀ᶠ n in l, ∀ i, ‖f n i‖ ≤ bound i := by
    filter_upwards [hbound] with n hn i
    have hinner := norm_inner_le_norm (𝕜 := ℂ)
      (adjoint U (b i)) (Aι n (S (b i)))
    have hop := (Aι n).le_opNorm (S (b i))
    have hAS : ‖Aι n (S (b i))‖ ≤ C * ‖S (b i)‖ :=
      hop.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    calc
      ‖f n i‖ ≤ ‖adjoint U (b i)‖ * ‖Aι n (S (b i))‖ := hinner
      _ ≤ ‖adjoint U (b i)‖ * (C * ‖S (b i)‖) := by
        gcongr
      _ ≤ bound i := by
        dsimp only [bound]
        have hu : 0 ≤ ‖adjoint U (b i)‖ := norm_nonneg _
        have hs : 0 ≤ ‖S (b i)‖ := norm_nonneg _
        nlinarith [sq_nonneg (‖adjoint U (b i)‖ - ‖S (b i)‖)]
  have htsum := tendsto_tsum_of_dominated_convergence
    hboundSummable hpoint hdom
  have hstage (n : ι) :
      opTrace (Aι n ∘L T) = ∑' i, f n i := by
    calc
      opTrace (Aι n ∘L T) = opTrace ((Aι n ∘L S) ∘L U) := by
        rw [hfac, comp_assoc]
      _ = opTrace (U ∘L (Aι n ∘L S)) :=
        opTrace_comp_comm (hS.comp_left (Aι n)) hU
      _ = ∑' i, inner ℂ (b i) ((U ∘L (Aι n ∘L S)) (b i)) :=
        opTrace_comp_eq_tsum_basis hU (hS.comp_left (Aι n)) b
      _ = ∑' i, f n i := by
        apply tsum_congr
        intro i
        rw [inner_comp_apply]
        rfl
  have hlimit : opTrace (A ∘L T) = ∑' i, g i := by
    calc
      opTrace (A ∘L T) = opTrace ((A ∘L S) ∘L U) := by
        rw [hfac, comp_assoc]
      _ = opTrace (U ∘L (A ∘L S)) :=
        opTrace_comp_comm (hS.comp_left A) hU
      _ = ∑' i, inner ℂ (b i) ((U ∘L (A ∘L S)) (b i)) :=
        opTrace_comp_eq_tsum_basis hU (hS.comp_left A) b
      _ = ∑' i, g i := by
        apply tsum_congr
        intro i
        rw [inner_comp_apply]
        rfl
  simpa only [hstage, hlimit] using htsum

end RHTower
