import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeBands

/-!
# Complete energy of disjoint prime-scale charge distributions

Exactly charged differences of prefixes realize any finite collection of
disjoint logarithmic prime bands. Their complete limiting form is diagonal:
each band pays the average cofactor logarithm divided by its width.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory SelectiveMultiscaleArithmeticPositivity
  RenormalizedArithmeticPotentialTheory

/-- The polarized complete-energy kernel of two prime bands. -/
def primeChargeBandKernel (a b c e d : ℕ) (t u : ℝ) : ℝ :=
  ∑ i ∈ ({0, 1} : Finset ℕ), ∑ j ∈ ({0, 1} : Finset ℕ),
    primeChargeBandWeights a b t i * primeChargeBandWeights c e u j *
      primePrefixReceivingKernel (primeChargeBandExponents a b i)
        (primeChargeBandExponents c e j) d

theorem primeChargeBandKernel_symm (a b c e d : ℕ) (t u : ℝ) :
    primeChargeBandKernel a b c e d t u = primeChargeBandKernel c e a b d u t := by
  unfold primeChargeBandKernel
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  simp only [primePrefixReceivingKernel, max_comm, min_comm]
  ring

/-- Nonoverlapping bands have exactly zero off-diagonal limiting energy. -/
theorem primeChargeBandKernel_eq_zero {a b c e : ℕ}
    (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hce : c < e)
    (hsep : b ≤ c ∨ e ≤ a) (d : ℕ) (t u : ℝ) :
    primeChargeBandKernel a b c e d t u = 0 := by
  rcases hsep with hbc | hea
  · exact primeChargeBand_mixed_kernel_zero ha hab hbc hce t u
  · rw [primeChargeBandKernel_symm]
    exact primeChargeBand_mixed_kernel_zero hc hce hea hab u t

/-- Coefficients of a finite distribution of exact prime-band charges. -/
def primeChargeBandDistributionCoefficients {ι : Type*} (S : Finset ι)
    (a b : ι → ℕ) (t : ι → ℝ) (d X : ℕ) : ℕ → ℝ :=
  primeChargeCombinationCoefficients (S ×ˢ ({0, 1} : Finset ℕ))
    (fun i => primeChargeBandExponents (a i.1) (b i.1) i.2)
    (fun i => primeChargeBandWeights (a i.1) (b i.1) (t i.1) i.2) d X

private theorem band_distribution_exponents {ι : Type*} (S : Finset ι)
    (a b : ι → ℕ) {d : ℕ} (ha : ∀ i ∈ S, 0 < a i)
    (hab : ∀ i ∈ S, a i < b i) (hbd : ∀ i ∈ S, b i ≤ d) :
    (∀ i ∈ S ×ˢ ({0, 1} : Finset ℕ), 0 < primeChargeBandExponents (a i.1) (b i.1) i.2) ∧
    (∀ i ∈ S ×ˢ ({0, 1} : Finset ℕ), primeChargeBandExponents (a i.1) (b i.1) i.2 ≤ d) := by
  constructor
  · intro i hi
    have hiS := (mem_product.mp hi).1
    have h1 := ha i.1 hiS
    have h2 := hab i.1 hiS
    unfold primeChargeBandExponents
    split_ifs <;> omega
  · intro i hi
    have hiS := (mem_product.mp hi).1
    have h1 := hab i.1 hiS
    have h2 := hbd i.1 hiS
    unfold primeChargeBandExponents
    split_ifs <;> omega

/-- Every band contributes its prescribed charge exactly at each finite polynomial scale. -/
theorem primeChargeBandDistribution_receiving_charge {ι : Type*} (S : Finset ι)
    (a b : ι → ℕ) (t : ι → ℝ) {d X : ℕ} (hX : 2 ≤ X)
    (ha : ∀ i ∈ S, 0 < a i) (hab : ∀ i ∈ S, a i < b i) (hbd : ∀ i ∈ S, b i ≤ d) :
    packetMean (X ^ d) (arithmeticPrimeGenerator (X ^ d)
      (primeChargeBandDistributionCoefficients S a b t d X)) = ∑ i ∈ S, t i := by
  have he := band_distribution_exponents S a b ha hab hbd
  rw [primeChargeBandDistributionCoefficients, primeChargeCombination_receiving_charge
    _ _ _ hX he.1 he.2, sum_product]
  exact sum_congr rfl fun i hi => primeChargeBand_weights_sum (hab i hi) (t i)

/-- Every finite band distribution is exactly harmonic-pole neutral. -/
theorem primeChargeBandDistribution_neutral {ι : Type*} (S : Finset ι)
    (a b : ι → ℕ) (t : ι → ℝ) (d : ℕ) {X : ℕ} (hX : 1 ≤ X) :
    harmonicSum (X ^ d) (conductorHorizonProfile (X ^ d)
      (primeChargeBandDistributionCoefficients S a b t d X)) = 0 :=
  primeChargeCombination_neutral _ _ _ d hX

/-- Every finite band distribution has vanishing raw input norm and adjunction energy. -/
theorem primeChargeBandDistribution_small_inputs {ι : Type*} (S : Finset ι)
    (a b : ι → ℕ) (t : ι → ℝ) {d : ℕ} (ha : ∀ i ∈ S, 0 < a i)
    (hab : ∀ i ∈ S, a i < b i) (hbd : ∀ i ∈ S, b i ≤ d) :
    Tendsto (fun X : ℕ =>
      ‖packetVector (normalizedConductorPacket (X ^ d)
        (primeChargeBandDistributionCoefficients S a b t d X)) (X ^ d)‖) atTop (𝓝 0) ∧
    Tendsto (fun X : ℕ => primeAdjunctionMass (X ^ d)
      (primeChargeBandDistributionCoefficients S a b t d X)) atTop (𝓝 0) := by
  have he := band_distribution_exponents S a b ha hab hbd
  exact ⟨tendsto_primeChargeCombination_input_norm _ _ _ he.1 he.2,
    tendsto_primeChargeCombination_adjunction _ _ _ he.1 he.2⟩

/-- Disjoint prime bands diagonalize the limiting complete form, with every finite-horizon term retained. -/
theorem tendsto_primeChargeBandDistribution_complete_energy {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {ι : Type*} (S : Finset ι)
    (a b : ι → ℕ) (t : ι → ℝ) {d : ℕ}
    (ha : ∀ i ∈ S, 0 < a i) (hab : ∀ i ∈ S, a i < b i) (hbd : ∀ i ∈ S, b i ≤ d)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → b i ≤ a j ∨ b j ≤ a i) :
    Tendsto (fun X : ℕ => completeWeilEnergy φ
      (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
      (packetVector (normalizedConductorPacket (X ^ d)
        (primeChargeBandDistributionCoefficients S a b t d X)) (X ^ d)))
      atTop (𝓝 (∑ i ∈ S, t i ^ 2 *
        ((d : ℝ) - ((a i : ℝ) + b i) / 2) / ((b i : ℝ) - a i))) := by
  have he := band_distribution_exponents S a b ha hab hbd
  have h := tendsto_primeChargeCombination_complete_energy hφ hφ0 hsupp hM hK
    (S ×ˢ ({0, 1} : Finset ℕ))
    (fun i => primeChargeBandExponents (a i.1) (b i.1) i.2)
    (fun i => primeChargeBandWeights (a i.1) (b i.1) (t i.1) i.2) he.1 he.2
  have hkernel :
      (∑ i ∈ S ×ˢ ({0, 1} : Finset ℕ), ∑ j ∈ S ×ˢ ({0, 1} : Finset ℕ),
        primeChargeBandWeights (a i.1) (b i.1) (t i.1) i.2 *
          primeChargeBandWeights (a j.1) (b j.1) (t j.1) j.2 *
          primePrefixReceivingKernel (primeChargeBandExponents (a i.1) (b i.1) i.2)
            (primeChargeBandExponents (a j.1) (b j.1) j.2) d) =
        ∑ i ∈ S, t i ^ 2 * ((d : ℝ) - ((a i : ℝ) + b i) / 2) /
          ((b i : ℝ) - a i) := by
    simp only [sum_product]
    apply sum_congr rfl
    intro i hi
    rw [sum_comm (s := ({0, 1} : Finset ℕ)) (t := S)]
    change (∑ j ∈ S, primeChargeBandKernel (a i) (b i) (a j) (b j) d (t i) (t j)) = _
    rw [sum_eq_single i]
    · exact primeChargeBand_kernel_sum (ha i hi) (hab i hi) (t i)
    · intro j hj hji
      exact primeChargeBandKernel_eq_zero (ha i hi) (hab i hi) (ha j hj) (hab j hj)
        (hsep i hi j hj hji.symm) d (t i) (t j)
    · exact fun hni => (hni hi).elim
  rw [hkernel] at h
  exact h

#print axioms primeChargeBandDistribution_receiving_charge
#print axioms primeChargeBandDistribution_small_inputs
#print axioms tendsto_primeChargeBandDistribution_complete_energy

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
