import GaloisForLFunctions.HTGeometry.AnharmonicMeromorphicSubstitution
import GaloisForLFunctions.RHTower.XiHypertranscendenceUnconditional
import GaloisForLFunctions.RHTower.MobiusLogarithmicJetLiGenerator

/-!
# The Keiper--Li generator is hypertranscendental

The Keiper--Li generating function is the Möbius logarithmic jet of the completed xi function for
the chart `r z = 1/(1-z)`.  That chart is the order-three anharmonic substitution, so it acts as a
rescaled differential automorphism of the meromorphic function field of the twice-punctured plane
over the rational coordinate field.

Since the rescaled substitution preserves differential algebraicity exactly, and the completed xi
function satisfies no algebraic differential equation, the Li generator satisfies none either.
-/

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry Bottcher
open scoped Differential

noncomputable section

attribute [local instance] anharmonicIsDomain anharmonicIntAlgebraAnalytic
  anharmonicIntAlgebraMero anharmonicMeroDifferential anharmonicRatFuncAlgebra
  anharmonicRatFuncDifferential anharmonicDifferentialAlgebra anharmonicMeroCharZero

theorem analyticOnNhd_xi_anharmonic : AnalyticOnNhd ℂ xi anharmonicDomain :=
  xi_analyticOnNhd_univ.mono (Set.subset_univ _)

theorem analyticOnNhd_xi_comp_anharmonic :
    AnalyticOnNhd ℂ (fun z => xi (anharmonicMap z)) anharmonicDomain := fun z hz =>
  (xi_analyticOnNhd_univ _ (Set.mem_univ _)).comp (analyticOnNhd_anharmonicMap z hz)

/-- The completed xi function as an element of the meromorphic field of the twice-punctured
plane. -/
def xiAnharmonic : meroField anharmonicDomain :=
  analyticMeroElement xi analyticOnNhd_xi_anharmonic

/-- Xi is hypertranscendental over `ℂ(z)` in the anharmonic meromorphic field. -/
theorem hypertranscendentalOver_xiAnharmonic :
    HypertranscendentalOver (RatFunc ℂ) xiAnharmonic :=
  hypertranscendentalOver_analyticMeroElement_of_hypertranscendental
    xi_differentiable analyticOnNhd_xi_anharmonic xi_hypertranscendental

/-- The Keiper--Li generating function as an element of the meromorphic field. -/
def liGeneratorMero : meroField anharmonicDomain :=
  anharmonicRescaledEquiv.mobiusJet xiAnharmonic

/-- **The Keiper--Li generator satisfies no algebraic differential equation over `ℂ(z)`.**
Unconditional: the anharmonic substitution transfers differential algebraicity exactly, and the
completed xi function is hypertranscendental. -/
theorem hypertranscendentalOver_liGeneratorMero :
    HypertranscendentalOver (RatFunc ℂ) liGeneratorMero :=
  (anharmonicRescaledEquiv.hypertranscendentalOver_mobiusJet_iff xiAnharmonic).mpr
    hypertranscendentalOver_xiAnharmonic

/-! ## Identification with the analytic Li generator -/

theorem liChart_eq_anharmonicMap : liChart = anharmonicMap := by
  funext z
  simp [liChart, anharmonicMap, one_div]

/-- The Li generator is the logarithmic derivative of `xi` composed with the anharmonic chart. -/
theorem liGenerator_eq_div (z : ℂ) :
    liGenerator z = deriv (fun w => xi (anharmonicMap w)) z / xi (anharmonicMap z) := by
  rw [liGenerator, liChart_eq_anharmonicMap]
  rfl

theorem anharmonicMeroEquiv_xiAnharmonic :
    anharmonicMeroEquiv xiAnharmonic
      = analyticMeroElement (fun z => xi (anharmonicMap z))
          analyticOnNhd_xi_comp_anharmonic := by
  rw [xiAnharmonic, analyticMeroElement, anharmonicMeroEquiv_algebraMap]
  rfl

theorem xiAnharmonic_ne_zero : xiAnharmonic ≠ 0 := by
  intro h
  refine hypertranscendentalOver_xiAnharmonic ?_
  rw [h, differentialAlgebraicOver_iff_exists_finPoly]
  refine ⟨0, MvPolynomial.X 0, MvPolynomial.X_ne_zero 0, ?_⟩
  have hjet : ∀ j : ℕ, differentialJet j (0 : meroField anharmonicDomain) = 0 := by
    intro j
    induction j with
    | zero => simp [differentialJet]
    | succ j ih => rw [differentialJet_succ, ih, map_zero]
  simp [hjet]

/-- **The meromorphic Li generator is the quotient of the two analytic germs.**  Multiplying by
the germ of `xi ∘ r` returns the germ of `(xi ∘ r)'`, so the field element is exactly the
logarithmic derivative whose pointwise value is the analytic Li generator. -/
theorem liGeneratorMero_mul_xiComp :
    liGeneratorMero * analyticMeroElement (fun z => xi (anharmonicMap z))
        analyticOnNhd_xi_comp_anharmonic
      = (analyticMeroElement (fun z => xi (anharmonicMap z))
          analyticOnNhd_xi_comp_anharmonic)′ := by
  have hne : analyticMeroElement (fun z => xi (anharmonicMap z))
      analyticOnNhd_xi_comp_anharmonic ≠ 0 := by
    rw [← anharmonicMeroEquiv_xiAnharmonic]
    intro h
    exact xiAnharmonic_ne_zero (by simpa using congrArg anharmonicMeroEquiv.symm h)
  rw [liGeneratorMero, DifferentialRescaledEquiv.mobiusJet_eq_logDeriv]
  simp only [anharmonicRescaledEquiv_ambientEquiv, anharmonicMeroEquiv_xiAnharmonic]
  field_simp

end

end RHTower
