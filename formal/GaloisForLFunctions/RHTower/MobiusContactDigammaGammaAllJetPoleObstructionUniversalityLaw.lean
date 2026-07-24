import GaloisForLFunctions.HTGeometry.AccumulatingPoleAlgebraicity
import GaloisForLFunctions.HTGeometry.DigammaGammaFirstOrder
import GaloisForLFunctions.HTGeometry.DigammaGammaLocalHypertranscendence
import GaloisForLFunctions.RHTower.MobiusGammaContactTransgression

/-!
# Möbius-contact digamma–Gamma all-jet pole-obstruction universality

The finite Möbius contact defect is the all-order factorial microscope for `digamma ∘ Gamma`.
This arithmetic normalization exposes its reciprocal boundary and organizes its global
hypertranscendence, local differential obstruction, and polewise meromorphic-germ obstruction.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Contact presentation of the digamma–Gamma factorial microscope scale. -/
def mobiusContactDigammaGammaScale (n : ℕ) : ℂ :=
  (-2 - mobiusGammaContactPartialCharge n) / 2

theorem mobiusContactDigammaGammaScale_eq (n : ℕ) :
    mobiusContactDigammaGammaScale n =
      GaloisForLFunctions.reciprocalGammaFactorialScale n := by
  rw [mobiusContactDigammaGammaScale, mobiusGammaContactPartialCharge_eq]
  simp only [GaloisForLFunctions.reciprocalGammaFactorialScale]
  ring

/-- Factorial zoom of a function written directly in the contact coordinate. -/
def mobiusContactDigammaGammaZoom (h : ℂ → ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  h (-(n : ℂ) + mobiusContactDigammaGammaScale n * x)

theorem mobiusContactDigammaGammaZoom_eq (h : ℂ → ℂ) (n : ℕ) :
    mobiusContactDigammaGammaZoom h n =
      GaloisForLFunctions.factorialBlowUpZoom h n := by
  funext x
  rw [mobiusContactDigammaGammaZoom, GaloisForLFunctions.factorialBlowUpZoom,
    mobiusContactDigammaGammaScale_eq]

/-- Every contact-normalized derivative order converges to the reciprocal digamma boundary. -/
theorem tendsto_mobiusContactDigammaGamma_allJetBoundary
    {x : ℂ} (hx : x ∈ GaloisForLFunctions.reciprocalGammaBlowUpDisk) (j : ℕ) :
    Tendsto
      (fun n => iteratedDeriv j
        (mobiusContactDigammaGammaZoom
          (fun z => Complex.digamma (Complex.Gamma z)) n) x)
      atTop
      (𝓝 (iteratedDeriv j GaloisForLFunctions.digammaReciprocalLimit x)) := by
  simpa only [mobiusContactDigammaGammaZoom_eq] using
    (GaloisForLFunctions.iteratedDeriv_digammaGamma_factorialBlowUp_tendsto hx j)

/-- `digamma ∘ Gamma` is not algebraic over meromorphic germs at any negative integer. -/
theorem mobiusContactDigammaGamma_not_locallyMeromorphicallyAlgebraicAt_negNat
    (n : ℕ) :
    ¬GaloisForLFunctions.LocallyMeromorphicallyAlgebraicAt
      (fun z : ℂ => Complex.digamma (Complex.Gamma z)) (-(n : ℂ)) := by
  exact GaloisForLFunctions.ReciprocalGammaPoleBranch.digamma_comp_Gamma_not_locallyMeromorphicallyAlgebraic
      (GaloisForLFunctions.HTGeometry.chosenReciprocalGammaPoleBranch n)

/-- **Möbius-contact digamma–Gamma all-jet pole-obstruction universality law.** One contact
microscope controls every jet boundary and the complete global/local algebraic obstruction
hierarchy. -/
theorem mobiusContactDigammaGamma_completeAllJetPoleObstructionUniversality :
    (∀ (x : ℂ), x ∈ GaloisForLFunctions.reciprocalGammaBlowUpDisk →
      ∀ j : ℕ,
        Tendsto
          (fun n => iteratedDeriv j
            (mobiusContactDigammaGammaZoom
              (fun z => Complex.digamma (Complex.Gamma z)) n) x)
          atTop
          (𝓝 (iteratedDeriv j GaloisForLFunctions.digammaReciprocalLimit x))) ∧
    GaloisForLFunctions.Hypertranscendental
      (fun z => Complex.digamma (Complex.Gamma z)) ∧
    (∀ V : Set ℂ, IsOpen V → V.Nonempty →
      V ⊆ GaloisForLFunctions.digammaGammaRegularSet →
      ¬GaloisForLFunctions.DifferentiallyAlgebraicOn
        (fun z => Complex.digamma (Complex.Gamma z)) V) ∧
    (∀ n : ℕ,
      ¬GaloisForLFunctions.LocallyMeromorphicallyAlgebraicAt
        (fun z : ℂ => Complex.digamma (Complex.Gamma z)) (-(n : ℂ))) := by
  refine ⟨?_, GaloisForLFunctions.hypertranscendental_digamma_comp_Gamma, ?_, ?_⟩
  · intro x hx j
    exact tendsto_mobiusContactDigammaGamma_allJetBoundary hx j
  · intro V hVopen hVne hVreg
    exact GaloisForLFunctions.no_local_differential_relation_digamma_comp_Gamma
      hVopen hVne hVreg
  · exact mobiusContactDigammaGamma_not_locallyMeromorphicallyAlgebraicAt_negNat

end

end GaloisForLFunctions.RHTower
