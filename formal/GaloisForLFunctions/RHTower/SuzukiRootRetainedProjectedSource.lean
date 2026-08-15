import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Projecting the root-retained carrier equation

The carrier equation `(2L·I + R − T)F' + F = 0` is posed on the whole space, with the exterior
endpoint coordinates retained.  Applying a projection `P` that commutes with the jump multiplier `R`
and with differentiation — but *not* with the adjacency `T` — splits the adjacency term alone:

`T F' = T P F' + T Q F'`,   `Q = I − P`,

so the projected equation is the interior equation forced by an exterior source,

`(2L·I + R − P T P)(P F)' + P F = P T Q (Q F)'`.

Nothing is eliminated: the source keeps the exterior derivative, and its size is controlled by the
plain operator norm of `P T Q`, so an `L²` exterior derivative gives an `L²` source.  The classical
Schur complement remains available afterwards — it is recovered here from an inverse witness on the
exterior block — but it is a coordinate elimination performed after the fact, not a prerequisite for
solving the retained system.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-! ## The retained carrier equation -/

/-- The root-retained carrier equation `(2L·I + R − T)F'(L) + F(L) = 0`, with `R` an arbitrary
linear jump multiplier and `T` the full self-adjoint adjacency. -/
def RootRetainedCarrier (R : X →ₗ[ℂ] X) (T : X →L[ℂ] X) (F F' : ℝ → X) : Prop :=
  ∀ L : ℝ, ((2 * L : ℝ) : ℂ) • F' L + R (F' L) - T (F' L) + F L = 0

/-- **The projected carrier equation.**  Applying `P` splits only the adjacency term, leaving the
interior equation forced by the retained exterior derivative. -/
theorem projected_carrier_equation {R : X →ₗ[ℂ] X} {T P : X →L[ℂ] X} {F F' : ℝ → X}
    (hPR : ∀ x : X, P (R x) = R (P x))
    (hF : RootRetainedCarrier R T F F') (L : ℝ) :
    ((2 * L : ℝ) : ℂ) • P (F' L) + R (P (F' L)) - P (T (P (F' L))) + P (F L)
      = P (T ((ContinuousLinearMap.id ℂ X - P) (F' L))) := by
  have hsplit : F' L = P (F' L) + (ContinuousLinearMap.id ℂ X - P) (F' L) := by
    simp
  have happ : P (((2 * L : ℝ) : ℂ) • F' L + R (F' L) - T (F' L) + F L) = P 0 := by
    rw [hF L]
  rw [map_add, map_sub, map_add, map_smul, hPR, map_zero] at happ
  have hT : P (T (F' L))
      = P (T (P (F' L))) + P (T ((ContinuousLinearMap.id ℂ X - P) (F' L))) := by
    conv_lhs => rw [hsplit]
    rw [map_add, map_add]
  rw [hT] at happ
  have hfinal := happ
  linear_combination (norm := module) hfinal

/-! ## The exterior source is controlled by the exterior derivative -/

/-- The projected exterior source is bounded pointwise by the exterior derivative. -/
theorem norm_projectedSource_le (T P : X →L[ℂ] X) (y : X) :
    ‖P (T ((ContinuousLinearMap.id ℂ X - P) y))‖
      ≤ (‖P‖ * ‖T‖ * ‖ContinuousLinearMap.id ℂ X - P‖) * ‖y‖ := by
  calc ‖P (T ((ContinuousLinearMap.id ℂ X - P) y))‖
      ≤ ‖P‖ * ‖T ((ContinuousLinearMap.id ℂ X - P) y)‖ := P.le_opNorm _
    _ ≤ ‖P‖ * (‖T‖ * ‖(ContinuousLinearMap.id ℂ X - P) y‖) := by
        exact mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    _ ≤ ‖P‖ * (‖T‖ * (‖ContinuousLinearMap.id ℂ X - P‖ * ‖y‖)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
          (norm_nonneg _)
        exact (ContinuousLinearMap.id ℂ X - P).le_opNorm y
    _ = (‖P‖ * ‖T‖ * ‖ContinuousLinearMap.id ℂ X - P‖) * ‖y‖ := by ring

/-- **The projected exterior source is square integrable whenever the exterior derivative is.**
This is the unweighted boundary-log `L²` statement: no compression inverse and no weight are
involved, only the operator norm of `P T Q`. -/
theorem lintegral_sq_projectedSource_ne_top {T P : X →L[ℂ] X} {F' : ℝ → X} {L₀ : ℝ}
    (hQ : (∫⁻ L in Ioi L₀, ‖(ContinuousLinearMap.id ℂ X - P) (F' L)‖ₑ ^ 2) ≠ ⊤) :
    (∫⁻ L in Ioi L₀, ‖P (T ((ContinuousLinearMap.id ℂ X - P) (F' L)))‖ₑ ^ 2) ≠ ⊤ := by
  set C : ℝ := ‖P‖ * ‖T‖ with hC
  have hmono : ∀ L : ℝ, ‖P (T ((ContinuousLinearMap.id ℂ X - P) (F' L)))‖ₑ ^ 2
      ≤ ENNReal.ofReal (C ^ 2) * ‖(ContinuousLinearMap.id ℂ X - P) (F' L)‖ₑ ^ 2 := by
    intro L
    have hstep : ‖P (T ((ContinuousLinearMap.id ℂ X - P) (F' L)))‖
        ≤ C * ‖(ContinuousLinearMap.id ℂ X - P) (F' L)‖ := by
      calc ‖P (T ((ContinuousLinearMap.id ℂ X - P) (F' L)))‖
          ≤ ‖P‖ * ‖T ((ContinuousLinearMap.id ℂ X - P) (F' L))‖ := P.le_opNorm _
        _ ≤ ‖P‖ * (‖T‖ * ‖(ContinuousLinearMap.id ℂ X - P) (F' L)‖) :=
            mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
        _ = C * ‖(ContinuousLinearMap.id ℂ X - P) (F' L)‖ := by rw [hC]; ring
    have henorm : ‖P (T ((ContinuousLinearMap.id ℂ X - P) (F' L)))‖ₑ
        ≤ ENNReal.ofReal C * ‖(ContinuousLinearMap.id ℂ X - P) (F' L)‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hstep
    calc ‖P (T ((ContinuousLinearMap.id ℂ X - P) (F' L)))‖ₑ ^ 2
        ≤ (ENNReal.ofReal C * ‖(ContinuousLinearMap.id ℂ X - P) (F' L)‖ₑ) ^ 2 :=
          pow_le_pow_left' henorm 2
      _ = ENNReal.ofReal (C ^ 2) * ‖(ContinuousLinearMap.id ℂ X - P) (F' L)‖ₑ ^ 2 := by
          rw [mul_pow, ENNReal.ofReal_pow (by positivity)]
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hmono)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hQ

/-! ## The projection passes through differentiation -/

/-- A projection of a differentiable carrier is differentiable with the projected derivative: this
is what lets the projected equation be read as an equation for `(P F)'`. -/
theorem hasDerivAt_projected {P : X →L[ℂ] X} {F F' : ℝ → X} {L : ℝ}
    (hF : HasDerivAt F (F' L) L) :
    HasDerivAt (fun x => P (F x)) (P (F' L)) L :=
  (ContinuousLinearMap.hasFDerivAt (P.restrictScalars ℝ)).comp_hasDerivAt L hF

/-! ## The Schur complement recovered after the fact -/

/-- **The exact interior Schur complement.**  From an inverse witness on the exterior block, the
interior component of `(α I + T)c = f` satisfies the classical self-energy equation.  This is a
coordinate elimination performed on the already-solved retained system, not an input to it. -/
theorem schur_complement_of_inverse {T P S : X →L[ℂ] X} {α : ℂ} {c f : X}
    (hS : ∀ x : X, S (α • (ContinuousLinearMap.id ℂ X - P) x
      + (ContinuousLinearMap.id ℂ X - P) (T ((ContinuousLinearMap.id ℂ X - P) x)))
      = (ContinuousLinearMap.id ℂ X - P) x)
    (hc : α • c + T c = f) :
    α • P c + P (T (P c))
        - P (T (S ((ContinuousLinearMap.id ℂ X - P) (T (P c)))))
      = P f - P (T (S ((ContinuousLinearMap.id ℂ X - P) f))) := by
  set Q : X →L[ℂ] X := ContinuousLinearMap.id ℂ X - P with hQ
  have hsplit : ∀ x : X, P x + Q x = x := by
    intro x
    rw [hQ]
    simp
  -- exterior row
  have hQrow : α • Q c + Q (T (Q c)) = Q f - Q (T (P c)) := by
    have := congrArg (fun x => Q x) hc
    simp only [map_add, map_smul] at this
    have hTc : Q (T c) = Q (T (P c)) + Q (T (Q c)) := by
      conv_lhs => rw [← hsplit c]
      rw [map_add, map_add]
    rw [hTc] at this
    linear_combination (norm := module) this
  have hQc : Q c = S (Q f) - S (Q (T (P c))) := by
    have hkey := hS c
    rw [hQrow] at hkey
    rw [← hkey, map_sub]
  -- interior row
  have hProw : α • P c + P (T c) = P f := by
    have := congrArg (fun x => P x) hc
    simpa only [map_add, map_smul] using this
  have hTc : P (T c) = P (T (P c)) + P (T (Q c)) := by
    conv_lhs => rw [← hsplit c]
    rw [map_add, map_add]
  rw [hTc, hQc, map_sub, map_sub] at hProw
  linear_combination (norm := module) hProw

end GaloisForLFunctions.RHTower
