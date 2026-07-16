import GaloisForLFunctions.HTGeometry.ThermodynamicAffinityFisherBound
import GaloisForLFunctions.RHTower.MobiusIncidenceClockGiniFisherFourUnit

/-!
# Quadratic-current lower layer of the Mobius incidence Gini clock

The finite incidence KMS construction realizes its total entropy production as the exact Gini
clock energy.  The general thermodynamic Fisher bound therefore supplies a second, algebraic
layer: the sum of the symmetric quadratic population currents is bounded by that Gini energy.

This removes logarithms from the lower certificate while retaining a quantitative observable
current.  At response level, the Gini/entropy-production resolvent has at least the absorptive
strength of the quadratic-current resolvent at every upper-half-plane observation point.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Total pseudo-entropy/Fisher current cost of the finite incidence KMS realization. -/
def finiteIncidencePseudoEntropyEnergy
    {α : Type*} [Fintype α]
    (sigma epsilon : ℝ) (d : α → ℕ) : ℝ :=
  ∑ a, ∑ b,
    finiteKMSPseudoEntropyProductionTransitionIntensity
      (finiteIncidenceInverseTemperature sigma epsilon)
      (finiteIncidenceEnergy epsilon d)
      (finiteIncidenceKMSAmplitude sigma epsilon d) a b

/-- The finite incidence quadratic-current energy is nonnegative without an injectivity
hypothesis on the labels. -/
theorem finiteIncidencePseudoEntropyEnergy_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (sigma epsilon : ℝ) (d : α → ℕ) :
    0 ≤ finiteIncidencePseudoEntropyEnergy sigma epsilon d := by
  unfold finiteIncidencePseudoEntropyEnergy
  apply Finset.sum_nonneg
  intro a ha
  apply Finset.sum_nonneg
  intro b hb
  exact finiteKMSPseudoEntropyProductionTransitionIntensity_nonneg _ _ _ a b

/-- **Incidence Gini--Fisher bound.**  The exact finite Gini clock energy controls the complete
quadratic population-current cost. -/
theorem finiteIncidencePseudoEntropyEnergy_le_gini
    {α : Type*} [Fintype α] [Nonempty α]
    {sigma epsilon : ℝ} (hsigma : 0 < sigma) (hepsilon : 0 < epsilon)
    {d : α → ℕ} (hd : ∀ i, 0 < d i) (hinj : Function.Injective d) :
    finiteIncidencePseudoEntropyEnergy sigma epsilon d ≤
      finiteIncidenceGiniEnergy sigma epsilon d := by
  rw [← sum_finiteKMSEntropyProductionTransitionIntensity_incidence
    hsigma hepsilon hd hinj]
  exact
    sum_finiteKMSPseudoEntropyProductionTransitionIntensity_le_entropyProduction
      (finiteIncidenceInverseTemperature sigma epsilon)
      (finiteIncidenceEnergy epsilon d)
      (finiteIncidenceKMSAmplitude sigma epsilon d)
      (finiteIncidenceKMSAmplitude_hermitian sigma epsilon d)

/-- The same quadratic current cost is controlled by the layer-cake relative clock energy, using
the existing exact Gini identity. -/
theorem finiteIncidencePseudoEntropyEnergy_le_relativeClockEnergy
    {α : Type*} [Fintype α] [Nonempty α]
    {sigma epsilon : ℝ} (hsigma : 0 < sigma) (hepsilon : 0 < epsilon)
    {d : α → ℕ} (hd : ∀ i, 0 < d i) (hinj : Function.Injective d) :
    finiteIncidencePseudoEntropyEnergy sigma epsilon d ≤
      finiteIncidenceRelativeClockEnergy sigma epsilon d := by
  rw [finiteIncidenceRelativeClockEnergy_eq_gini hd]
  exact finiteIncidencePseudoEntropyEnergy_le_gini hsigma hepsilon hd hinj

/-- Passive response built from the algebraic quadratic-current intensities of the finite
incidence system. -/
def finiteIncidencePseudoEntropyResponse
    {α : Type*} [Fintype α]
    (sigma epsilon : ℝ) (d : α → ℕ) (z : ℂ) : ℂ :=
  _root_.HTGeometry.finiteTransitionPassiveResponse
    (finiteKMSPseudoEntropyProductionTransitionIntensity
      (finiteIncidenceInverseTemperature sigma epsilon)
      (finiteIncidenceEnergy epsilon d)
      (finiteIncidenceKMSAmplitude sigma epsilon d))
    (finiteIncidenceEnergy epsilon d) z

/-- The exact Gini/entropy-production response has at least the absorptive strength of the
quadratic-current response. -/
theorem finiteIncidenceKMSResponse_im_le_pseudoEntropyResponse
    {α : Type*} [Fintype α] [Nonempty α]
    (sigma epsilon : ℝ) (d : α → ℕ)
    {z : ℂ} (hz : 0 < z.im) :
    (finiteIncidenceKMSResponse sigma epsilon d z).im ≤
      (finiteIncidencePseudoEntropyResponse sigma epsilon d z).im := by
  unfold finiteIncidenceKMSResponse finiteIncidencePseudoEntropyResponse
  exact finiteKMSEntropyProductionResponse_im_le_pseudo
    (finiteIncidenceInverseTemperature sigma epsilon)
    (finiteIncidenceEnergy epsilon d)
    (finiteIncidenceKMSAmplitude sigma epsilon d)
    (finiteIncidenceKMSAmplitude_hermitian sigma epsilon d) hz

end

end RHTower
