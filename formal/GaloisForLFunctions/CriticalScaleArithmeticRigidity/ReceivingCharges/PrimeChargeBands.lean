import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeCombinations

/-!
# Receiving charge on a logarithmic prime band

A difference of two exactly charged prefixes isolates a prime-scale band
in the limit. Its total charge stays exact at every cutoff, while the full
critical energy is the cofactor weight averaged over that band.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory

/-- The two prefix exponents defining a prime band. -/
def primeChargeBandExponents (a b i : ℕ) : ℕ := if i = 0 then b else a

/-- The two exact prefix charges whose total is the prescribed band charge. -/
def primeChargeBandWeights (a b : ℕ) (t : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then t * (b : ℝ) / ((b : ℝ) - a) else -t * (a : ℝ) / ((b : ℝ) - a)

/-- An exactly charged neutral packet with limiting prime support between two polynomial cutoffs. -/
def primeChargeBandCoefficients (a b d X : ℕ) (t : ℝ) : ℕ → ℝ :=
  primeChargeCombinationCoefficients {0, 1} (primeChargeBandExponents a b)
    (primeChargeBandWeights a b t) d X

theorem primeChargeBand_weights_sum {a b : ℕ} (hab : a < b) (t : ℝ) :
    (∑ i ∈ ({0, 1} : Finset ℕ), primeChargeBandWeights a b t i) = t := by
  have hD : (b : ℝ) - a ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab.ne')
  norm_num only [sum_insert, mem_singleton, zero_ne_one, not_false_eq_true, sum_singleton,
    primeChargeBandWeights, if_pos rfl, one_ne_zero, if_false, ite_true]
  field_simp [hD]
  ring

/-- A prime-band packet retains its prescribed receiving charge exactly. -/
theorem primeChargeBand_receiving_charge {a b d X : ℕ}
    (ha : 0 < a) (hab : a < b) (hbd : b ≤ d) (hX : 2 ≤ X) (t : ℝ) :
    packetMean (X ^ d) (arithmeticPrimeGenerator (X ^ d)
      (primeChargeBandCoefficients a b d X t)) = t := by
  rw [primeChargeBandCoefficients, primeChargeCombination_receiving_charge]
  · exact primeChargeBand_weights_sum hab t
  · exact hX
  · intro i hi
    unfold primeChargeBandExponents
    split_ifs <;> omega
  · intro i hi
    unfold primeChargeBandExponents
    split_ifs <;> omega

theorem primeChargeBand_kernel_sum {a b d : ℕ} (ha : 0 < a) (hab : a < b) (t : ℝ) :
    (∑ i ∈ ({0, 1} : Finset ℕ), ∑ j ∈ ({0, 1} : Finset ℕ),
      primeChargeBandWeights a b t i * primeChargeBandWeights a b t j *
        primePrefixReceivingKernel (primeChargeBandExponents a b i) (primeChargeBandExponents a b j) d) =
      t ^ 2 * ((d : ℝ) - ((a : ℝ) + b) / 2) / ((b : ℝ) - a) := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (ha.trans hab).ne'
  have hD : (b : ℝ) - a ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab.ne')
  norm_num only [sum_insert, mem_singleton, zero_ne_one, not_false_eq_true, sum_singleton,
    primeChargeBandWeights, primeChargeBandExponents, if_pos rfl, one_ne_zero, if_false, ite_true,
    primePrefixReceivingKernel, max_self, min_self, max_eq_left hab.le, max_eq_right hab.le,
    min_eq_left hab.le, min_eq_right hab.le]
  field_simp [haR, hbR, hD]
  ring

/-- The full critical energy of an exactly charged prime band has its explicit cofactor cost. -/
theorem tendsto_primeChargeBand_complete_energy {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {a b d : ℕ}
    (ha : 0 < a) (hab : a < b) (hbd : b ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      completeWeilEnergy φ (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
        (packetVector (normalizedConductorPacket (X ^ d)
          (primeChargeBandCoefficients a b d X t)) (X ^ d)))
      atTop (𝓝 (t ^ 2 * ((d : ℝ) - ((a : ℝ) + b) / 2) / ((b : ℝ) - a))) := by
  have hpos : ∀ i ∈ ({0, 1} : Finset ℕ), 0 < primeChargeBandExponents a b i := by
    intro i _
    unfold primeChargeBandExponents
    split_ifs <;> omega
  have hle : ∀ i ∈ ({0, 1} : Finset ℕ), primeChargeBandExponents a b i ≤ d := by
    intro i _
    unfold primeChargeBandExponents
    split_ifs <;> omega
  have h := tendsto_primeChargeCombination_complete_energy hφ hφ0 hsupp hM hK
    {0, 1} (primeChargeBandExponents a b) (primeChargeBandWeights a b t) hpos hle
  rw [primeChargeBand_kernel_sum ha hab t] at h
  exact h

/-- Disjoint prime-scale bands have zero mixed complete-energy kernel. -/
theorem primeChargeBand_mixed_kernel_zero {a b c e d : ℕ}
    (ha : 0 < a) (hab : a < b) (hbc : b ≤ c) (hce : c < e) (t u : ℝ) :
    (∑ i ∈ ({0, 1} : Finset ℕ), ∑ j ∈ ({0, 1} : Finset ℕ),
      primeChargeBandWeights a b t i * primeChargeBandWeights c e u j *
        primePrefixReceivingKernel (primeChargeBandExponents a b i)
          (primeChargeBandExponents c e j) d) = 0 := by
  have hc : 0 < c := (ha.trans hab).trans_le hbc
  have he : 0 < e := hc.trans hce
  have hbe : b ≤ e := hbc.trans hce.le
  have hac : a ≤ c := hab.le.trans hbc
  have hae : a ≤ e := hac.trans hce.le
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have heR : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hba : (b : ℝ) - a ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab.ne')
  have hec : (e : ℝ) - c ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hce.ne')
  norm_num only [sum_insert, mem_singleton, zero_ne_one, not_false_eq_true, sum_singleton,
    primeChargeBandWeights, primeChargeBandExponents, if_pos rfl, one_ne_zero, if_false, ite_true,
    primePrefixReceivingKernel, max_eq_right hbe, min_eq_left hbe,
    max_eq_right hbc, min_eq_left hbc, max_eq_right hae, min_eq_left hae,
    max_eq_right hac, min_eq_left hac]
  field_simp [hcR, heR, hba, hec]
  ring

#print axioms primeChargeBand_receiving_charge
#print axioms tendsto_primeChargeBand_complete_energy
#print axioms primeChargeBand_mixed_kernel_zero

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
