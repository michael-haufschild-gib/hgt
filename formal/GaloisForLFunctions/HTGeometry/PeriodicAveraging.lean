import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.RCLike.Basic

/-!
# Averaging over a period on a coordinate space

For a map on a finite coordinate space over `ℝ` or `ℂ` and a nonzero period in one coordinate
direction, the average over one period is again defined on the whole space, is differentiable with
the average of the derivative, preserves periodicity in every coordinate, and is invariant under the
whole translation flow in the averaged direction.  A map invariant under the flow in every direction
is constant.  This is the mechanism behind the computation of the cohomology of a torus, in the model
where a form on the torus is a periodic form on the covering space.

* `periodCurve` : the curve traversing one period in a coordinate direction.
* `averageOp` : the average of a map over one period.
* `const_of_flowInvariant` : invariance in every direction forces constancy.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

section PeriodCurve

variable {𝕜 : Type*} [RCLike 𝕜] {r : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The curve traversing one period in a coordinate direction. -/
noncomputable def periodCurve (p : 𝕜) (w : Fin r → 𝕜) (j : Fin r) (s : ℝ) : Fin r → 𝕜 :=
  w + ((s : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)

theorem periodCurve_zero (p : 𝕜) (w : Fin r → 𝕜) (j : Fin r) : periodCurve p w j 0 = w := by
  show w + (((0 : ℝ) : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) = w
  norm_num

theorem periodCurve_one (p : 𝕜) (w : Fin r → 𝕜) (j : Fin r) :
    periodCurve p w j 1 = w + p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) := by
  show w + (((1 : ℝ) : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) = _
  norm_num

theorem periodCurve_add (p : 𝕜) (w : Fin r → 𝕜) (j : Fin r) (c : Fin r → 𝕜) (s : ℝ) :
    periodCurve p (w + c) j s = periodCurve p w j s + c := by
  show w + c + ((s : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) =
    (w + ((s : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)) + c
  abel

theorem periodCurve_trans (p : 𝕜) (w : Fin r → 𝕜) (j : Fin r) (t s : ℝ) :
    periodCurve p (periodCurve p w j t) j s = periodCurve p w j (t + s) := by
  show w + ((t : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) +
      ((s : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) =
    w + (((t + s : ℝ) : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)
  rw [add_assoc, ← add_smul]
  congr 1
  push_cast
  ring_nf

theorem periodCurve_comm (p : 𝕜) (w : Fin r → 𝕜) (i j : Fin r) (t s : ℝ) :
    periodCurve p (periodCurve p w i t) j s = periodCurve p (periodCurve p w j s) i t := by
  show w + ((t : 𝕜) * p) • (Pi.single i (1 : 𝕜) : Fin r → 𝕜) +
      ((s : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) =
    w + ((s : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) +
      ((t : 𝕜) * p) • (Pi.single i (1 : 𝕜) : Fin r → 𝕜)
  abel

theorem periodCurve_succ (p : 𝕜) (w : Fin r → 𝕜) (j : Fin r) (t : ℝ) :
    periodCurve p w j (t + 1) = periodCurve p w j t + p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) := by
  show w + (((t + 1 : ℝ) : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) =
    w + ((t : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) +
      p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)
  rw [add_assoc, ← add_smul]
  congr 1
  push_cast
  ring_nf

theorem continuous_periodCurve (p : 𝕜) (w : Fin r → 𝕜) (j : Fin r) :
    Continuous (periodCurve p w j) := by
  show Continuous fun s : ℝ => w + ((s : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)
  have hcast : Continuous fun s : ℝ => ((s : 𝕜) * p) := by
    exact (RCLike.continuous_ofReal.mul continuous_const)
  exact continuous_const.add (hcast.smul continuous_const)

/-- **The period curve is differentiable** with constant derivative the period vector. -/
theorem periodCurve_hasDerivAt (p : 𝕜) (w : Fin r → 𝕜) (j : Fin r) (s : ℝ) :
    HasDerivAt (periodCurve p w j) (p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)) s := by
  have h1 : HasDerivAt (fun t : ℝ => ((t : 𝕜))) 1 s := by
    simpa using (RCLike.ofRealCLM (K := 𝕜)).hasDerivAt (x := s)
  have h2 : HasDerivAt (fun t : ℝ => ((t : 𝕜) * p)) p s := by
    have h := h1.mul_const p
    rwa [one_mul] at h
  have h3 := h2.smul_const (Pi.single j (1 : 𝕜) : Fin r → 𝕜)
  exact h3.const_add w

end PeriodCurve

end GaloisForLFunctions.HTGeometry
