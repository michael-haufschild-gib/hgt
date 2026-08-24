import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicBaseChange
import GaloisForLFunctions.HTGeometry.HypertranscendentalPow
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances
import GaloisForLFunctions.HTGeometry.AnalyticMeroPolynomialEval

/-!
# Quadratic algebraic closure of entire differentially algebraic functions

An entire root of a monic quadratic whose two entire coefficients are differentially algebraic is
differentially algebraic.  The proof works in the global meromorphic differential field, adjoins the
two coefficients, applies ordinary algebraicity of the root, and descends across a DA base change.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open Bottcher
open scoped UnivMeroFieldInstances

noncomputable section

/-- An entire root of `X² - qX + s` is differentially algebraic when `q` and `s` are. -/
theorem differentiallyAlgebraic_of_quadratic_relation
    {h q s : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h Set.univ)
    (hq : AnalyticOnNhd ℂ q Set.univ)
    (hs : AnalyticOnNhd ℂ s Set.univ)
    (hrel : ∀ z, h z ^ 2 - q z * h z + s z = 0)
    (hqDA : DifferentiallyAlgebraic q)
    (hsDA : DifferentiallyAlgebraic s) :
    DifferentiallyAlgebraic h := by
  let hm := analyticMeroElement h hh
  let qm := analyticMeroElement q hq
  let sm := analyticMeroElement s hs
  let G : Set (meroField (Set.univ : Set ℂ)) := {qm, sm}
  have hG : ∀ g ∈ G, DifferentialAlgebraicOver (RatFunc ℂ) g := by
    intro g hg
    rcases hg with (rfl | rfl)
    · exact differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic hq hqDA
    · exact differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic hs hsDA
  have hqmem : qm ∈ differentialAdjoin (RatFunc ℂ) G :=
    subset_differentialAdjoin (RatFunc ℂ) G (by simp [G])
  have hsmem : sm ∈ differentialAdjoin (RatFunc ℂ) G :=
    subset_differentialAdjoin (RatFunc ℂ) G (by simp [G])
  let qF : differentialAdjoin (RatFunc ℂ) G := ⟨qm, hqmem⟩
  let sF : differentialAdjoin (RatFunc ℂ) G := ⟨sm, hsmem⟩
  let p : Polynomial (differentialAdjoin (RatFunc ℂ) G) :=
    Polynomial.X ^ 2 + (-Polynomial.C qF * Polynomial.X + Polynomial.C sF)
  have hpdeg :
      (-Polynomial.C qF * Polynomial.X + Polynomial.C sF).degree < (2 : WithBot ℕ) := by
    have hqdeg : (-Polynomial.C qF * Polynomial.X).degree ≤ 1 := by
      calc
        (-Polynomial.C qF * Polynomial.X).degree
            ≤ (-Polynomial.C qF).degree + Polynomial.X.degree := Polynomial.degree_mul_le _ _
        _ ≤ 0 + 1 := add_le_add (by simpa only [Polynomial.degree_neg] using
          (Polynomial.degree_C_le : (Polynomial.C qF).degree ≤ 0)) (by simp)
        _ = 1 := by norm_num
    have hsdeg : (Polynomial.C sF).degree ≤ 1 :=
      (Polynomial.degree_C_le).trans (by norm_num)
    calc
      (-Polynomial.C qF * Polynomial.X + Polynomial.C sF).degree
          ≤ max (-Polynomial.C qF * Polynomial.X).degree (Polynomial.C sF).degree :=
            Polynomial.degree_add_le _ _
      _ ≤ 1 := max_le hqdeg hsdeg
      _ < 2 := by norm_num
  have hpmonic : p.Monic := Polynomial.monic_X_pow_add hpdeg
  have hfieldrel : hm ^ 2 - qm * hm + sm = 0 := by
    have hpw := analyticMeroElement_pow hh 2
    have hmul := analyticMeroElement_mul hq hh
    have hsub :
        analyticMeroElement (fun z => h z ^ 2 - q z * h z) ((hh.pow 2).sub (hq.mul hh)) =
          analyticMeroElement (fun z => h z ^ 2) (hh.pow 2) -
            analyticMeroElement (fun z => q z * h z) (hq.mul hh) :=
      analyticMeroElement_sub (hh.pow 2) (hq.mul hh)
    have hadd :
        analyticMeroElement (fun z => (h z ^ 2 - q z * h z) + s z)
            (((hh.pow 2).sub (hq.mul hh)).add hs) =
          analyticMeroElement (fun z => h z ^ 2 - q z * h z)
              ((hh.pow 2).sub (hq.mul hh)) + analyticMeroElement s hs :=
      analyticMeroElement_add ((hh.pow 2).sub (hq.mul hh)) hs
    rw [← hpw, ← hmul, ← hsub, ← hadd]
    have hzero : (fun z => h z ^ 2 - q z * h z + s z) = 0 := funext hrel
    calc
      analyticMeroElement (fun z => h z ^ 2 - q z * h z + s z)
          (((hh.pow 2).sub (hq.mul hh)).add hs) =
          analyticMeroElement (fun _ : ℂ => 0) analyticOnNhd_const :=
        analyticMeroElement_congr _ _ hzero
      _ = 0 := analyticMeroElement_zero Set.univ
  have hmint : IsIntegral (differentialAdjoin (RatFunc ℂ) G) hm := by
    refine ⟨p, hpmonic, ?_⟩
    simp [p]
    dsimp [qF, sF]
    linear_combination hfieldrel
  have hmDAF : DifferentialAlgebraicOver (differentialAdjoin (RatFunc ℂ) G) hm :=
    differentialAlgebraicOver_of_isAlgebraic (isAlgebraic_iff_isIntegral.mpr hmint)
  have hmDA : DifferentialAlgebraicOver (RatFunc ℂ) hm :=
    (differentialAlgebraicOver_differentialAdjoin_iff hG).mp hmDAF
  exact differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement hh hmDA

end

end GaloisForLFunctions.HTGeometry
