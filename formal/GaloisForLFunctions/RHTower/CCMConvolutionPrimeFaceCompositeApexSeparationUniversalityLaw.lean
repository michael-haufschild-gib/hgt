import GaloisForLFunctions.RHTower.CCMConvolutionTiltOddsRigidityUniversalityLaw
import GaloisForLFunctions.RHTower.CCMFirstClockApexSuperlevelMajorization

/-!
# CCM convolution prime-face/composite-apex separation universality

Infinite Dirichlet-convolution functionals restricted to the first-clock irreducible-prime face
see only the unit coordinate and those prime coordinates.  Hence an arbitrary source spike at
composite `4` is invisible to every aligned/counter prime-face observation.  The full
prime-power apex measure behaves oppositely: coordinate `4` is its positive unit-amplitude
obstruction.  This is an exact information-loss explanation for why prime-face rigidity cannot
lift to full apex majorization.
-/

open ArithmeticFunction Finset Set

namespace RHTower

noncomputable section

/-- Aligned/counter first-clock observations of an arbitrary arithmetic source after an arbitrary
coefficientwise infinite Dirichlet-convolution functional. -/
def ccmConvolutionIrreduciblePrimeFaceObservation
    (c : ℕ → ℝ) (f : ArithmeticFunction ℝ) (L : ℝ) : ℝ × ℝ :=
  (∑ p ∈ ccmFirstClockIrreduciblePrimeSupport L,
      (p : ℝ) ^ (-1 / 2 : ℝ) *
        dirichletConvolutionSeries c f p *
        max (Real.sin ((2 * Real.pi / L) * Real.log p)) 0,
    ∑ p ∈ ccmFirstClockIrreduciblePrimeSupport L,
      (p : ℝ) ^ (-1 / 2 : ℝ) *
        dirichletConvolutionSeries c f p *
        max (-Real.sin ((2 * Real.pi / L) * Real.log p)) 0)

/-- Prime-face convolution observations are extensional in precisely the unit coordinate and the
prime coordinates selected by the first-clock aperture. -/
theorem ccmConvolutionIrreduciblePrimeFaceObservation_ext
    (c : ℕ → ℝ) (f g : ArithmeticFunction ℝ) (L : ℝ)
    (hone : f 1 = g 1)
    (hprime :
      ∀ p ∈ ccmFirstClockIrreduciblePrimeSupport L, f p = g p) :
    ccmConvolutionIrreduciblePrimeFaceObservation c f L =
      ccmConvolutionIrreduciblePrimeFaceObservation c g L := by
  apply Prod.ext
  · simp only [ccmConvolutionIrreduciblePrimeFaceObservation]
    apply Finset.sum_congr rfl
    intro p hp
    have hpPrime : p.Prime :=
      (Finset.mem_filter.mp hp).2
    rw [dirichletConvolutionSeries_apply_prime c f hpPrime,
      dirichletConvolutionSeries_apply_prime c g hpPrime,
      hone, hprime p hp]
  · simp only [ccmConvolutionIrreduciblePrimeFaceObservation]
    apply Finset.sum_congr rfl
    intro p hp
    have hpPrime : p.Prime :=
      (Finset.mem_filter.mp hp).2
    rw [dirichletConvolutionSeries_apply_prime c f hpPrime,
      dirichletConvolutionSeries_apply_prime c g hpPrime,
      hone, hprime p hp]

/-- Arithmetic source supported at the single composite coordinate `4`. -/
def ccmCompositeFourSpike (u : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 4 then u else 0, by simp⟩

@[simp] theorem ccmCompositeFourSpike_apply (u : ℝ) (n : ℕ) :
    ccmCompositeFourSpike u n = if n = 4 then u else 0 :=
  rfl

@[simp] theorem ccmCompositeFourSpike_apply_one (u : ℝ) :
    ccmCompositeFourSpike u 1 = 0 := by
  simp

theorem ccmCompositeFourSpike_apply_prime
    (u : ℝ) {p : ℕ} (hp : p.Prime) :
    ccmCompositeFourSpike u p = 0 := by
  rw [ccmCompositeFourSpike_apply, if_neg]
  intro hp4
  subst p
  norm_num at hp

/-- Every infinite convolution prime-face observation is blind to an arbitrary perturbation at
composite coordinate `4`. -/
theorem ccmConvolutionIrreduciblePrimeFaceObservation_fourSpike_invariant
    (c : ℕ → ℝ) (f : ArithmeticFunction ℝ) (u L : ℝ) :
    ccmConvolutionIrreduciblePrimeFaceObservation
        c (f + ccmCompositeFourSpike u) L =
      ccmConvolutionIrreduciblePrimeFaceObservation c f L := by
  apply ccmConvolutionIrreduciblePrimeFaceObservation_ext
  · simp
  · intro p hp
    simp [ccmCompositeFourSpike_apply_prime _
      (Finset.mem_filter.mp hp).2]

/-- Coordinate `4` never belongs to an irreducible-prime observation aperture. -/
theorem four_not_mem_ccmFirstClockIrreduciblePrimeSupport (L : ℝ) :
    4 ∉ ccmFirstClockIrreduciblePrimeSupport L := by
  intro hfour
  have : Nat.Prime 4 :=
    (Finset.mem_filter.mp hfour).2
  norm_num at this

/-- Exact separation certificate: every convolution prime-face observer erases arbitrary
composite-four data, although coordinate `4` is a positive unit-amplitude atom of the full source
and is exactly what destroys apex majorization. -/
def CCMConvolutionPrimeFaceCompositeApexSeparation : Prop :=
  (∀ (c : ℕ → ℝ) (f : ArithmeticFunction ℝ) (u L : ℝ),
      ccmConvolutionIrreduciblePrimeFaceObservation
          c (f + ccmCompositeFourSpike u) L =
        ccmConvolutionIrreduciblePrimeFaceObservation c f L) ∧
    (∀ L : ℝ, 4 ∉ ccmFirstClockIrreduciblePrimeSupport L) ∧
    4 ∈ Finset.Icc 2
      ⌊Real.exp ccmFirstClockNegativeApexLength⌋₊ ∧
    0 < criticalMellinAtomWeight 4 ∧
    ccmFirstClockCounterAmplitude ccmFirstClockNegativeApexLength 4 = 1 ∧
    0 <
      ccmFirstClockBadApexMeasure ccmFirstClockNegativeApexLength
        ccmFirstClockClosedApexSet ∧
    ccmFirstClockGoodApexMeasure ccmFirstClockNegativeApexLength
        ccmFirstClockClosedApexSet = 0 ∧
    ¬CCMFirstClockApexSuperlevelMajorization

/-- **CCM convolution prime-face/composite-apex separation universality law.** -/
theorem ccmConvolutionPrimeFace_compositeApexSeparationUniversality :
    CCMConvolutionPrimeFaceCompositeApexSeparation := by
  exact
    ⟨ccmConvolutionIrreduciblePrimeFaceObservation_fourSpike_invariant,
      four_not_mem_ccmFirstClockIrreduciblePrimeSupport,
      four_mem_ccmFirstClockNegativeApex_cutoff,
      criticalMellinAtomWeight_four_pos,
      ccmFirstClockCounterAmplitude_four_negativeApex,
      ccmFirstClockBadApexMeasure_closedApex_pos,
      ccmFirstClockGoodApexMeasure_closedApex_eq_zero,
      not_ccmFirstClockApexSuperlevelMajorization⟩

end

end RHTower
