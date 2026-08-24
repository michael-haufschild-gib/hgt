import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary
import GaloisForLFunctions.HTGeometry.LocalInverseHypertranscendence
import GaloisForLFunctions.HTGeometry.AnalyticMeroPolynomialEval
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Cancellation for differentially algebraic entire functions

If `f * g = h`, both `f` and `h` are differentially algebraic, and `f` is not identically zero,
then `g` is differentially algebraic.  Zeros of `f` prevent pointwise division, so the proof takes
place in the global meromorphic differential field and descends through the analytic-jet bridge.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open Bottcher
open scoped UnivMeroFieldInstances

noncomputable section

theorem differentiallyAlgebraic_right_of_mul_eq
    {f g h : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ)
    (hh : AnalyticOnNhd ℂ h Set.univ)
    (hfne : ∃ z, f z ≠ 0)
    (hrel : ∀ z, f z * g z = h z)
    (hfDA : DifferentiallyAlgebraic f)
    (hhDA : DifferentiallyAlgebraic h) :
    DifferentiallyAlgebraic g := by
  let fm := analyticMeroElement f hf
  let gm := analyticMeroElement g hg
  let hm := analyticMeroElement h hh
  obtain ⟨z₀, hz₀⟩ := hfne
  have hfmne : fm ≠ 0 := analyticMeroElement_ne_zero isOpen_univ isPreconnected_univ
    Set.univ_nonempty hf (Set.mem_univ z₀) hz₀
  have hfmDA : DifferentialAlgebraicOver (RatFunc ℂ) fm :=
    differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic hf hfDA
  have hhmDA : DifferentialAlgebraicOver (RatFunc ℂ) hm :=
    differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic hh hhDA
  have hquotDA : DifferentialAlgebraicOver (RatFunc ℂ) (hm / fm) :=
    differentialAlgebraicOver_div hhmDA hfmDA
  have hfieldrel : fm * gm = hm := by
    rw [← analyticMeroElement_mul hf hg]
    exact analyticMeroElement_congr _ _ (funext hrel)
  have hgm : gm = hm / fm := by
    apply (eq_div_iff hfmne).2
    rw [mul_comm]
    exact hfieldrel
  apply differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement hg
  change DifferentialAlgebraicOver (RatFunc ℂ) gm
  rw [hgm]
  exact hquotDA

end

end GaloisForLFunctions.HTGeometry
