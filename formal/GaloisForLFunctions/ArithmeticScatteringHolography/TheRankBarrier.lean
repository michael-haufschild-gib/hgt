import GaloisForLFunctions.ArithmeticScatteringHolography.TheKreinFluxLaw
import GaloisForLFunctions.RHTower.CompactTestXiDivisibilityObstruction

/-!
# The rank barrier

A causal probe is a compactly supported input. Over a curve the ringdown has finite rank, and a probe of finite length
silences it: the probe `1 - t w + q w²` reduces the ringdown signal to zero after finitely many ticks
(`ringSignal_silenced`), and any finite set of modes can be silenced in the same way.

Over `ℤ` this cannot happen. The transform of a compactly supported probe has exponential type, so it has linearly many
zeros, while the zeros of `ξ` are superlinear. So **every nonzero compactly supported probe excites infinitely many
modes of the horizon** (`infinite_excited_modes`). So the difference between the graph model and the modular horizon has a
precise form: all of the statements that close at finite rank by a polynomial identity have no direct analogue, and the
missing ingredient over `ℤ` is exactly the control of infinitely many modes by a finite probe.
-/

open Complex
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography

open _root_.RHTower

/-- **A finite probe silences the ringdown of the graph.** -/
theorem ringSignal_silenced (q t : ℂ) (n : ℕ) :
    ringSignal q t (n + 2) - t * ringSignal q t (n + 1) + q * ringSignal q t n = 0 := by
  rw [ringSignal_add_two]
  ring

/-- **The rank barrier over `ℤ`.** A nonzero continuous compactly supported probe is nonzero at infinitely many simple
zeros on the critical line: its response has infinitely many modes. -/
theorem infinite_excited_modes {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hne : f ≠ 0) :
    {t : ℝ | 0 < t ∧ xi (linePt t) = 0 ∧ paperFT f t ≠ 0}.Infinite := by
  intro hfin
  have hfi : MeasureTheory.Integrable f := hf.integrable_of_hasCompactSupport hfc
  have hFne : paperFT f ≠ 0 := fun h0 =>
    hne (CompactTestXiDivisibility.eq_zero_of_paperFT_real_eq_zero hf hfi fun r => congrFun h0 r)
  obtain ⟨A, C, hA, hC, hgrow⟩ := CompactTestXiDivisibility.exists_paperFT_exponentialType hf hfc
  obtain ⟨t, htE, ht0, hxi, -, hnz⟩ := exists_simpleCritical_nonzero_of_exponentialType
    (WeilEF.differentiable_paperFT hf hfc) hFne hA hC hgrow hfin.toFinset
  exact htE (hfin.mem_toFinset.mpr ⟨ht0, hxi, hnz⟩)

end GaloisForLFunctions.ArithmeticScatteringHolography

end
