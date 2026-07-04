/-
# q62 — discharging the Brolin support input from GAP-A

The both-connected q62 bridge (`Q62BackwardOrbitBrolin`) consumes the support
datum `LimitingBrolinMeasureAtSupportsJulia c a` (= `frontier (filledJulia c) ⊆
supp (limitingBrolinMeasureAt c a)`) and the equivalent `BackwardOrbitDense`.
This module discharges that datum from the GAP-A Riesz→support chain
(`Brolin/RieszSupport`), reducing the whole support-form route to the two named
analytic inputs:

* `volume (filledJulia c) = 0` — hyperbolic-Julia Lebesgue-nullity;
* `WeylOnBall (greenFunctionDyn c)` — Weyl's lemma (distributional ⟹ pointwise
  harmonicity).

Both are measure-theoretic/elliptic-regularity facts, not new dynamics.  Once they
land, `q62_phiMero_bothconnected_*` no longer needs a support hypothesis.
-/
import GaloisForLFunctions.Bottcher.Q62BackwardOrbitBrolin
import GaloisForLFunctions.Bottcher.Brolin.RieszSupport

open MeasureTheory Complex

namespace Bottcher

noncomputable section

/-- **The q62 Brolin support input, discharged from GAP-A.**  For every target `a`,
the arbitrary-target Brolin measure charges every Julia-frontier ball — conditional
only on Julia-null and Weyl's lemma.  This is literally
`LimitingBrolinMeasureAtSupportsJulia c a`. -/
theorem limitingBrolinMeasureAtSupportsJulia_of_filledJulia_null_of_weyl
    (c a : ℂ) (hnull : volume (filledJulia c) = 0)
    (hWeyl : WeylOnBall (greenFunctionDyn c)) :
    LimitingBrolinMeasureAtSupportsJulia c a :=
  frontier_filledJulia_subset_support_limitingBrolinMeasureAt c a hnull hWeyl

/-- The `∀ fixed-point target` form consumed by the q62 both-connected capstones
(`hsupp` hypothesis).  Discharges the support datum for the fixed point the bridge
selects internally. -/
theorem forall_fixedPoint_limitingBrolinMeasureAtSupportsJulia_of_filledJulia_null_of_weyl
    (c : ℂ) (hnull : volume (filledJulia c) = 0)
    (hWeyl : WeylOnBall (greenFunctionDyn c)) :
    ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a :=
  fun a _ => limitingBrolinMeasureAtSupportsJulia_of_filledJulia_null_of_weyl c a hnull hWeyl

/-- **Backward-orbit density from GAP-A.**  At a fixed point with critical-orbit
avoidance, `BackwardOrbitDense` follows from Julia-null + Weyl.  This is the
dynamical input the one-sided pullback density needs. -/
theorem backwardOrbitDense_of_filledJulia_null_of_weyl
    (c a : ℂ) (hnull : volume (filledJulia c) = 0)
    (hWeyl : WeylOnBall (greenFunctionDyn c))
    (hcrit : CriticalOrbitAvoidingTarget c a) :
    BackwardOrbitDense c a :=
  backwardOrbitDense_of_limitingBrolinMeasureAtSupportsJulia
    (limitingBrolinMeasureAtSupportsJulia_of_filledJulia_null_of_weyl c a hnull hWeyl) hcrit

/-- **Fixed-point backward-orbit density from GAP-A**, targets chosen internally.
Given `c ≠ 1/4`, produces a fixed point with dense non-critical backward orbit,
conditional only on Julia-null + Weyl — collapsing the support-form route to those
two inputs. -/
theorem exists_fixedPoint_backwardOrbitDense_of_filledJulia_null_of_weyl
    {c : ℂ} (hc : c ≠ 1 / 4) (hnull : volume (filledJulia c) = 0)
    (hWeyl : WeylOnBall (greenFunctionDyn c)) :
    ∃ a : ℂ, quadratic c a = a ∧ BackwardOrbitDense c a :=
  exists_fixedPoint_backwardOrbitDense_of_limitingBrolinMeasureAtSupportsJulia hc
    (forall_fixedPoint_limitingBrolinMeasureAtSupportsJulia_of_filledJulia_null_of_weyl
      c hnull hWeyl)

end

end Bottcher
