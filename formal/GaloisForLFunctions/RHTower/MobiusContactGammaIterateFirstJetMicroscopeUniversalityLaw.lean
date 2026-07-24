import GaloisForLFunctions.HTGeometry.GammaIterationFirstJetAlgebraicIndependence
import GaloisForLFunctions.RHTower.MobiusGammaContactTransgression

/-!
# Möbius-contact Gamma-iterate first-jet microscope universality

Half the displacement of the finite Möbius--Gamma contact charge from its terminal charge `-2`
is exactly Gamma's signed reciprocal-factorial microscope scale. Replacing the anonymous scale by
this arithmetic charge simultaneously in the pole translation and derivative normalization makes
every coordinate of every finite Gamma-iterate first jet converge to its Riccati boundary.

The compatible finite-depth boundary mechanism underlies algebraic independence of the complete
countable tower containing the independent variable, values, and first derivatives of all positive
Gamma iterates.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Arithmetic factorial microscope scale read from the raw finite Möbius contact charge. -/
def mobiusContactGammaFactorialMicroscopeScale (n : ℕ) : ℂ :=
  (-2 - mobiusGammaContactPartialCharge n) / 2

/-- Contact-charge and Gamma reciprocal-factorial microscope scales coincide exactly. -/
theorem mobiusContactGammaFactorialMicroscopeScale_eq (n : ℕ) :
    mobiusContactGammaFactorialMicroscopeScale n =
      GaloisForLFunctions.reciprocalGammaFactorialScale n := by
  rw [mobiusContactGammaFactorialMicroscopeScale, mobiusGammaContactPartialCharge_eq]
  simp only [GaloisForLFunctions.reciprocalGammaFactorialScale]
  ring

/-- Complete Gamma-iterate first jet transported and rescaled by the arithmetic contact defect. -/
def mobiusContactGammaIterateScaledFirstJetTail
    (k n : ℕ) (x : ℂ) (i : Fin k × Fin 2) : ℂ :=
  GaloisForLFunctions.gammaIterateScaledFirstJetTail k
    (mobiusContactGammaFactorialMicroscopeScale n)
    (-(n : ℂ) + mobiusContactGammaFactorialMicroscopeScale n * x) i

/-- Every coordinate at every finite depth converges to the intrinsic Riccati first-jet boundary
under the Möbius-contact microscope. -/
theorem tendsto_mobiusContactGammaIterateScaledFirstJetTail
    {k : ℕ} {x : ℂ}
    (hk : 1 ≤ k)
    (hx : x ∈ GaloisForLFunctions.localGammaMicroscopeDomain
      (GaloisForLFunctions.gammaIterateRegularSet k))
    (hxLeft : x ∈ GaloisForLFunctions.gammaFactorialMicroscopeDomain)
    (i : Fin (k + 1) × Fin 2) :
    Tendsto (fun n =>
        mobiusContactGammaIterateScaledFirstJetTail (k + 1) n x i)
      atTop (𝓝 (GaloisForLFunctions.gammaFirstJetBoundaryTail
        k ((-x)⁻¹) i)) := by
  simpa only [mobiusContactGammaIterateScaledFirstJetTail,
    mobiusContactGammaFactorialMicroscopeScale_eq] using
    (GaloisForLFunctions.tendsto_gammaIterateScaledFirstJetTail_factorialBlowUp
      hk hx hxLeft i)

/-- **Möbius-contact Gamma-iterate first-jet microscope universality law.** The raw arithmetic
contact defect exposes every finite Riccati boundary coordinate, while the compatible complete
infinite first-jet family remains algebraically independent. -/
theorem mobiusContactGammaIteration_completeFirstJetMicroscopeUniversality :
    (∀ (k : ℕ) (x : ℂ),
      1 ≤ k →
      x ∈ GaloisForLFunctions.localGammaMicroscopeDomain
        (GaloisForLFunctions.gammaIterateRegularSet k) →
      x ∈ GaloisForLFunctions.gammaFactorialMicroscopeDomain →
      ∀ i : Fin (k + 1) × Fin 2,
        Tendsto (fun n =>
            mobiusContactGammaIterateScaledFirstJetTail (k + 1) n x i)
          atTop (𝓝 (GaloisForLFunctions.gammaFirstJetBoundaryTail
            k ((-x)⁻¹) i))) ∧
      AlgebraicIndependent ℂ
        GaloisForLFunctions.gammaIterateInfiniteFirstJetFamily := by
  refine ⟨?_, GaloisForLFunctions.algebraicIndependent_gammaIterateInfiniteFirstJetFamily⟩
  intro k x hk hx hxLeft i
  exact tendsto_mobiusContactGammaIterateScaledFirstJetTail hk hx hxLeft i

end

end GaloisForLFunctions.RHTower
