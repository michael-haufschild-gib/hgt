import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureSevenTenthsShallowSector
import GaloisForLFunctions.RHTower.XiWardSourceWindowMultiplicity

/-!
# Seven-tenths shallow-band reflected HCF charge

This file propagates the `23/25` shallow-strip sector coercivity through a finite multiplicity-exact
Xi packet, its disjoint critical-line reflection, and the existing shallow/deep three-quarters
receiver.  The resulting source target is the corrected HCF lattice budget divided by the exact
reflected shallow charge, plus the strict-right deep-band count.

No zero-density-to-packet comparison or source asymptotic upper bound is asserted here.
-/

open Complex

namespace RHTower

noncomputable section

/-- Direct five-center charge of one Xi copy in the seven-tenths shallow band. -/
def criticalFeatureShallowDirectFiveCenterCharge : ℝ :=
  (23 / 25 : ℝ) * (23232 / 4225 + 32 / 221 : ℝ)

/-- Reflected-pair five-center charge in the seven-tenths shallow band. -/
def criticalFeatureShallowReflectedFiveCenterCharge : ℝ :=
  2 * criticalFeatureShallowDirectFiveCenterCharge

theorem criticalFeatureShallowDirectFiveCenterCharge_pos :
    0 < criticalFeatureShallowDirectFiveCenterCharge := by
  norm_num [criticalFeatureShallowDirectFiveCenterCharge]

theorem criticalFeatureShallowReflectedFiveCenterCharge_pos :
    0 < criticalFeatureShallowReflectedFiveCenterCharge := by
  norm_num [criticalFeatureShallowReflectedFiveCenterCharge,
    criticalFeatureShallowDirectFiveCenterCharge]

/-- Generic finite five-center summation: a pointwise local holomorphic charge propagates to the
all-copy corrected HCF lattice budget. -/
private theorem finite_offLine_card_mul_fiveCenterLocalCharge_le_offLineLatticeBudget
    (c : ℝ) (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hoff : ∀ q ∈ S, (q.1 : ℂ).re ≠ 1 / 2)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 2 ∈ K ∧
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K ∧
      round (xiSpectralPoint q).re + 2 ∈ K)
    (hlocal : ∀ q ∈ S, c ≤
      ((criticalFeatureCauchyKernelTest
        (((round (xiSpectralPoint q).re : ℤ) : ℝ) - 2) (xiSpectralPoint q)) ^ (2 : ℕ)).re +
      ((criticalFeatureCauchyKernelTest
        (((round (xiSpectralPoint q).re : ℤ) : ℝ) - 1) (xiSpectralPoint q)) ^ (2 : ℕ)).re +
      ((criticalFeatureCauchyKernelTest
        ((round (xiSpectralPoint q).re : ℤ) : ℝ) (xiSpectralPoint q)) ^ (2 : ℕ)).re +
      ((criticalFeatureCauchyKernelTest
        (((round (xiSpectralPoint q).re : ℤ) : ℝ) + 1) (xiSpectralPoint q)) ^ (2 : ℕ)).re +
      ((criticalFeatureCauchyKernelTest
        (((round (xiSpectralPoint q).re : ℤ) : ℝ) + 2) (xiSpectralPoint q)) ^ (2 : ℕ)).re) :
    (S.card : ℝ) * c ≤ criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  calc
    (S.card : ℝ) * c = ∑ _q ∈ S, c := by simp
    _ ≤ ∑ q ∈ S, ∑ k ∈ K,
        offLineCriticalFeatureHolomorphicEnergy (k : ℝ) q := by
      gcongr with q hq
      let kq : ℤ := round (xiSpectralPoint q).re
      have hmem := hcenters q hq
      have hqoff := hoff q hq
      have hfive := hlocal q hq
      have hoffeq (j : ℤ) :
          ((criticalFeatureCauchyKernelTest (j : ℝ)
            (xiSpectralPoint q)) ^ (2 : ℕ)).re =
            offLineCriticalFeatureHolomorphicEnergy (j : ℝ) q := by
        rw [offLineCriticalFeatureHolomorphicEnergy, if_neg hqoff]
      have hcastm2 : (kq : ℝ) - 2 = ((kq - 2 : ℤ) : ℝ) := by
        exact_mod_cast (rfl : kq - 2 = kq - 2)
      have hcastm1 : (kq : ℝ) - 1 = ((kq - 1 : ℤ) : ℝ) := by
        exact_mod_cast (rfl : kq - 1 = kq - 1)
      have hcastp1 : (kq : ℝ) + 1 = ((kq + 1 : ℤ) : ℝ) := by
        exact_mod_cast (rfl : kq + 1 = kq + 1)
      have hcastp2 : (kq : ℝ) + 2 = ((kq + 2 : ℤ) : ℝ) := by
        exact_mod_cast (rfl : kq + 2 = kq + 2)
      change c ≤
        ((criticalFeatureCauchyKernelTest ((kq : ℝ) - 2)
          (xiSpectralPoint q)) ^ (2 : ℕ)).re +
        ((criticalFeatureCauchyKernelTest ((kq : ℝ) - 1)
          (xiSpectralPoint q)) ^ (2 : ℕ)).re +
        ((criticalFeatureCauchyKernelTest (kq : ℝ)
          (xiSpectralPoint q)) ^ (2 : ℕ)).re +
        ((criticalFeatureCauchyKernelTest ((kq : ℝ) + 1)
          (xiSpectralPoint q)) ^ (2 : ℕ)).re +
        ((criticalFeatureCauchyKernelTest ((kq : ℝ) + 2)
          (xiSpectralPoint q)) ^ (2 : ℕ)).re at hfive
      rw [hcastm2, hcastm1, hcastp1, hcastp2,
        hoffeq, hoffeq, hoffeq, hoffeq, hoffeq] at hfive
      let Tq : Finset ℤ := {kq - 2, kq - 1, kq, kq + 1, kq + 2}
      have hTq : Tq ⊆ K := by
        intro j hj
        simp only [Tq, Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with hj | hj | hj | hj | hj
        · simpa [hj] using hmem.1
        · simpa [hj] using hmem.2.1
        · simpa [hj] using hmem.2.2.1
        · simpa [hj] using hmem.2.2.2.1
        · simpa [hj] using hmem.2.2.2.2
      have hsumTq :
          (∑ j ∈ Tq, offLineCriticalFeatureHolomorphicEnergy (j : ℝ) q) =
            offLineCriticalFeatureHolomorphicEnergy ((kq - 2 : ℤ) : ℝ) q +
              offLineCriticalFeatureHolomorphicEnergy ((kq - 1 : ℤ) : ℝ) q +
              offLineCriticalFeatureHolomorphicEnergy (kq : ℝ) q +
              offLineCriticalFeatureHolomorphicEnergy ((kq + 1 : ℤ) : ℝ) q +
              offLineCriticalFeatureHolomorphicEnergy ((kq + 2 : ℤ) : ℝ) q := by
        have hab : kq - 2 ≠ kq - 1 := by omega
        have hac : kq - 2 ≠ kq := by omega
        have had : kq - 2 ≠ kq + 1 := by omega
        have hae : kq - 2 ≠ kq + 2 := by omega
        have hbc : kq - 1 ≠ kq := by omega
        have hbd : kq - 1 ≠ kq + 1 := by omega
        have hbe : kq - 1 ≠ kq + 2 := by omega
        have hcd : kq ≠ kq + 1 := by omega
        have hce : kq ≠ kq + 2 := by omega
        have hde : kq + 1 ≠ kq + 2 := by omega
        simp [Tq, hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde]
        ring
      calc
        c ≤ ∑ j ∈ Tq,
            offLineCriticalFeatureHolomorphicEnergy (j : ℝ) q := by
          rw [hsumTq]
          simpa [Int.cast_sub, Int.cast_add] using hfive
        _ ≤ ∑ j ∈ K, offLineCriticalFeatureHolomorphicEnergy (j : ℝ) q := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hTq
          intro j hjK hjTq
          exact offLineCriticalFeatureHolomorphicEnergy_nonneg (j : ℝ) q
    _ = ∑ k ∈ K, ∑ q ∈ S,
        offLineCriticalFeatureHolomorphicEnergy (k : ℝ) q := by
      rw [Finset.sum_comm]
    _ ≤ ∑ k ∈ K, ∑' q : XiZeroCopy,
        offLineCriticalFeatureHolomorphicEnergy (k : ℝ) q := by
      gcongr with k hk
      exact (offLineCriticalFeatureHolomorphicEnergy_summable (k : ℝ)).sum_le_tsum S
        (fun q _ => offLineCriticalFeatureHolomorphicEnergy_nonneg (k : ℝ) q)
    _ = criticalFeaturePrimeGammaOffLineLatticeBudget K := by
      rw [criticalFeaturePrimeGammaOffLineLatticeBudget]
      apply Finset.sum_congr rfl
      intro k hk
      rw [criticalFeaturePrimeGammaOffLineExcess_eq_tsum_offLineHolomorphicEnergy]

/-- Every finite shallow off-line packet deposits the direct five-center shallow charge. -/
theorem finite_shallowOffLine_card_mul_directFiveCenterCharge_le_offLineLatticeBudget
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hoff : ∀ q ∈ S, (q.1 : ℂ).re ≠ 1 / 2)
    (hshallow : ∀ q ∈ S, |(xiSpectralPoint q).im| ≤ 1 / 5)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 2 ∈ K ∧
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K ∧
      round (xiSpectralPoint q).re + 2 ∈ K) :
    (S.card : ℝ) * criticalFeatureShallowDirectFiveCenterCharge ≤
      criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  apply finite_offLine_card_mul_fiveCenterLocalCharge_le_offLineLatticeBudget
    criticalFeatureShallowDirectFiveCenterCharge K S hoff hcenters
  intro q hq
  exact shallowDirectFiveCenterCriticalFeatureHolomorphicCharge_lower
    (hshallow q hq) (abs_sub_round _)

private theorem I_mul_xiSpectralPoint_lineConj_re_shallowFiveCenter
    (q : XiZeroCopy) :
    (I * xiSpectralPoint (xiZeroCopyLineConjEquiv q)).re =
      -(I * xiSpectralPoint q).re := by
  rw [xiSpectralPoint_lineConj]
  simp [Complex.mul_re]

private theorem xiZeroCopy_re_ne_half_of_transverse_re_ne_zero_shallowFiveCenter
    (q : XiZeroCopy) (hq : (I * xiSpectralPoint q).re ≠ 0) :
    (q.1 : ℂ).re ≠ 1 / 2 := by
  intro hline
  apply hq
  rw [I_mul_xiSpectralPoint, Complex.sub_re, hline]
  norm_num

/-- A strict-right shallow packet and its reflected packet deposit twice the direct shallow charge
in the all-copy corrected budget. -/
theorem finite_strictRight_shallow_card_mul_reflectedFiveCenterCharge_le_offLineLatticeBudget
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hshallow : ∀ q ∈ S, |(xiSpectralPoint q).im| ≤ 1 / 5)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 2 ∈ K ∧
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K ∧
      round (xiSpectralPoint q).re + 2 ∈ K) :
    (S.card : ℝ) * criticalFeatureShallowReflectedFiveCenterCharge ≤
      criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  let R : Finset XiZeroCopy := S.image xiZeroCopyLineConjEquiv
  let U : Finset XiZeroCopy := S ∪ R
  have hdisjoint : Disjoint S R := by
    rw [Finset.disjoint_left]
    intro q hqS hqR
    change q ∈ S.image xiZeroCopyLineConjEquiv at hqR
    rw [Finset.mem_image] at hqR
    obtain ⟨p, hpS, hpq⟩ := hqR
    subst q
    have hp := hright p hpS
    have hreflected := hright (xiZeroCopyLineConjEquiv p) hqS
    rw [I_mul_xiSpectralPoint_lineConj_re_shallowFiveCenter] at hreflected
    linarith
  have hcardR : R.card = S.card := by
    exact Finset.card_image_of_injective S xiZeroCopyLineConjEquiv.injective
  have hcardU : U.card = 2 * S.card := by
    change (S ∪ R).card = 2 * S.card
    rw [Finset.card_union_of_disjoint hdisjoint, hcardR]
    omega
  have hoffU : ∀ q ∈ U, (q.1 : ℂ).re ≠ 1 / 2 := by
    intro q hqU
    change q ∈ S ∪ R at hqU
    rw [Finset.mem_union] at hqU
    rcases hqU with hqS | hqR
    · exact xiZeroCopy_re_ne_half_of_transverse_re_ne_zero_shallowFiveCenter q
        (ne_of_gt (hright q hqS))
    · change q ∈ S.image xiZeroCopyLineConjEquiv at hqR
      rw [Finset.mem_image] at hqR
      obtain ⟨p, hpS, rfl⟩ := hqR
      apply xiZeroCopy_re_ne_half_of_transverse_re_ne_zero_shallowFiveCenter
      rw [I_mul_xiSpectralPoint_lineConj_re_shallowFiveCenter]
      exact neg_ne_zero.mpr (ne_of_gt (hright p hpS))
  have hshallowU : ∀ q ∈ U, |(xiSpectralPoint q).im| ≤ 1 / 5 := by
    intro q hqU
    change q ∈ S ∪ R at hqU
    rw [Finset.mem_union] at hqU
    rcases hqU with hqS | hqR
    · exact hshallow q hqS
    · change q ∈ S.image xiZeroCopyLineConjEquiv at hqR
      rw [Finset.mem_image] at hqR
      obtain ⟨p, hpS, rfl⟩ := hqR
      rw [xiSpectralPoint_lineConj]
      simpa using hshallow p hpS
  have hcentersU : ∀ q ∈ U,
      round (xiSpectralPoint q).re - 2 ∈ K ∧
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K ∧
      round (xiSpectralPoint q).re + 2 ∈ K := by
    intro q hqU
    change q ∈ S ∪ R at hqU
    rw [Finset.mem_union] at hqU
    rcases hqU with hqS | hqR
    · exact hcenters q hqS
    · change q ∈ S.image xiZeroCopyLineConjEquiv at hqR
      rw [Finset.mem_image] at hqR
      obtain ⟨p, hpS, rfl⟩ := hqR
      have hre : (xiSpectralPoint (xiZeroCopyLineConjEquiv p)).re =
          (xiSpectralPoint p).re := by
        rw [xiSpectralPoint_lineConj]
        simp
      rw [hre]
      exact hcenters p hpS
  have hcharge :=
    finite_shallowOffLine_card_mul_directFiveCenterCharge_le_offLineLatticeBudget
      K U hoffU hshallowU hcentersU
  calc
    (S.card : ℝ) * criticalFeatureShallowReflectedFiveCenterCharge =
        (U.card : ℝ) * criticalFeatureShallowDirectFiveCenterCharge := by
      rw [hcardU]
      push_cast
      rw [criticalFeatureShallowReflectedFiveCenterCharge]
      ring
    _ ≤ criticalFeaturePrimeGammaOffLineLatticeBudget K := hcharge

/-- Exact shallow/deep 75% receiver at the improved HCF charge.  Deep strict-right multiplicity is
left as a separate census term, ready for Route T's density-zero theorem. -/
theorem three_quarters_line_of_shallowReflectedFiveCenterCharge_and_deepCount
    {N N₀ Rdeep : ℝ} (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hN : 0 ≤ N)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hshallow : ∀ q ∈ S, |(xiSpectralPoint q).im| ≤ 1 / 5)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 2 ∈ K ∧
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K ∧
      round (xiSpectralPoint q).re + 2 ∈ K)
    (hsplit : N = N₀ + 2 * ((S.card : ℝ) + Rdeep))
    (hbudget :
      (1 / criticalFeatureShallowReflectedFiveCenterCharge) *
          criticalFeaturePrimeGammaOffLineLatticeBudget K + Rdeep ≤ N / 8) :
    3 * N / 4 ≤ N₀ := by
  have hcharge :=
    finite_strictRight_shallow_card_mul_reflectedFiveCenterCharge_le_offLineLatticeBudget
      K S hright hshallow hcenters
  have hQ := criticalFeatureShallowReflectedFiveCenterCharge_pos
  have hshallowEnergy : (S.card : ℝ) ≤
      (1 / criticalFeatureShallowReflectedFiveCenterCharge) *
        criticalFeaturePrimeGammaOffLineLatticeBudget K := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hQ]
    simpa [mul_comm] using hcharge
  exact three_quarters_line_of_shallowEnergy_and_deepCount
    hN hsplit hshallowEnergy hbudget

end


end RHTower
