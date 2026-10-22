import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonTimeSymmetric

/-!
# For a symmetric driving, one direction of stability is enough

The capstone of statement 367 asks for stability in *both* directions of time before it pins the
spectral radius at one. For a background that is even in time the two demands are the same demand:
the reflected background is the background itself, so a bound on the solutions run forwards is
literally a bound on the solutions of the reflected problem run forwards.

**A time-symmetric periodic clock that keeps time forwards keeps it backwards, and its spectral radius
is exactly one.**

The static case is an instance: a constant background is even in time and periodic with every period,
so a stable clock in a static potential can only oscillate — the conclusion of statement 351, obtained
from a symmetry instead of from the conserved energy.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ENNReal

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Symmetric

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- **For a time-symmetric background, forward stability is backward stability.** -/
theorem stable_neg_of_time_symmetric (hsym : ∀ r : ℝ, W (-r) = W r)
    (hfwd : ∀ g h : Lp ℂ 2 (volume : Measure E), ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖kgFieldStateT W g h t‖ ≤ C) :
    ∀ g h : Lp ℂ 2 (volume : Measure E), ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖kgFieldStateT (fun r : ℝ => W (-r)) g h t‖ ≤ C := by
  have hfun : (fun r : ℝ => W (-r)) = W := funext hsym
  rw [hfun]
  exact hfwd

/-- **A time-symmetric periodic clock that keeps time forwards has spectral radius exactly one.** -/
theorem spectralRadius_eq_one_of_time_symmetric_stable (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hsym : ∀ r : ℝ, W (-r) = W r) (hT : 0 < T)
    (hfwd : ∀ g h : Lp ℂ 2 (volume : Measure E), ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖kgFieldStateT W g h t‖ ≤ C) :
    spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T) = 1 :=
  spectralRadius_eq_one_of_two_way_stable hb0 hWb hWs hper hT hfwd
    (stable_neg_of_time_symmetric hsym hfwd)

end Symmetric

/-! ## The static case -/

section Static

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b T : ℝ}

/-- A constant background is even in time. -/
theorem timeSymmetric_const (W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (r : ℝ) : (fun _ : ℝ => W₀) (-r) = (fun _ : ℝ => W₀) r := rfl

/-- **A stable clock in a static potential can only oscillate.** -/
theorem spectralRadius_eq_one_of_static_stable (hb0 : 0 ≤ b)
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => W₀) r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fun _ : ℝ => W₀) r x) (hT : 0 < T)
    (hfwd : ∀ g h : Lp ℂ 2 (volume : Measure E), ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖kgFieldStateT (fun _ : ℝ => W₀) g h t‖ ≤ C) :
    spectralRadius ℂ (kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs T) = 1 :=
  spectralRadius_eq_one_of_time_symmetric_stable hb0 hWb hWs (periodic_const W₀ T)
    (timeSymmetric_const W₀) hT hfwd

end Static

end GaloisForLFunctions.HTGeometry
