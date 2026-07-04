/-
# q62 — the Brolin support route, with Weyl's lemma discharged

`weylOnBall_greenFunctionDyn` (Brolin/WeylLemma) proves `WeylOnBall (greenFunctionDyn c)`
unconditionally, so the `hWeyl` hypothesis threaded through the GAP-A support theorem and
its q62 consumers is now automatic.  This module supplies the `hWeyl`-free forms: the entire
support-form route to `BackwardOrbitDense` / `LimitingBrolinMeasureAtSupportsJulia` now
reduces to the single measure-theoretic input `volume (filledJulia c) = 0`.
-/
import GaloisForLFunctions.Bottcher.Brolin.WeylLemma
import GaloisForLFunctions.Bottcher.Q62BrolinSupportDischarge

open MeasureTheory Complex

namespace Bottcher

noncomputable section

/-- **The q62 Brolin support input from Julia-nullity alone.**  For every target `a`, the
Brolin measure charges every Julia-frontier ball — conditional only on `volume(filledJulia c)=0`
(Weyl's lemma is discharged internally). -/
theorem limitingBrolinMeasureAtSupportsJulia_of_filledJulia_null (c a : ℂ)
    (hnull : volume (filledJulia c) = 0) :
    LimitingBrolinMeasureAtSupportsJulia c a :=
  limitingBrolinMeasureAtSupportsJulia_of_filledJulia_null_of_weyl c a hnull
    (weylOnBall_greenFunctionDyn c)

/-- `∀`-fixed-point form consumed by the q62 both-connected capstones. -/
theorem forall_fixedPoint_limitingBrolinMeasureAtSupportsJulia_of_filledJulia_null
    (c : ℂ) (hnull : volume (filledJulia c) = 0) :
    ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a :=
  fun a _ => limitingBrolinMeasureAtSupportsJulia_of_filledJulia_null c a hnull

/-- **Backward-orbit density from Julia-nullity alone**, targets chosen internally. -/
theorem exists_fixedPoint_backwardOrbitDense_of_filledJulia_null
    {c : ℂ} (hc : c ≠ 1 / 4) (hnull : volume (filledJulia c) = 0) :
    ∃ a : ℂ, quadratic c a = a ∧ BackwardOrbitDense c a :=
  exists_fixedPoint_backwardOrbitDense_of_filledJulia_null_of_weyl hc hnull
    (weylOnBall_greenFunctionDyn c)

end

end Bottcher
