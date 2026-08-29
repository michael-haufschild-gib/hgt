import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureDirectThreeCenterCanonicalTransfer

/-!
# Reflected-pair doubling of direct three-center HCF charge

The corrected HCF lattice budget sums all multiplicity-exact Xi zero copies.  A strict-right
packet therefore comes with a disjoint critical-line-reflected packet on the left.  Both packets
occupy the same height cells, so the direct three-center holomorphic charge can be collected on
their union.  This removes a previously unused factor two in the HCF receiver.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Critical-line reflection reverses the centered transverse coordinate. -/
private theorem I_mul_xiSpectralPoint_lineConj_re
    (q : XiZeroCopy) :
    (I * xiSpectralPoint (xiZeroCopyLineConjEquiv q)).re =
      -(I * xiSpectralPoint q).re := by
  rw [xiSpectralPoint_lineConj]
  simp [Complex.mul_re]

/-- Nonzero centered transverse coordinate is exactly enough to remove critical-line subtraction
for one multiplicity copy. -/
private theorem xiZeroCopy_re_ne_half_of_I_mul_xiSpectralPoint_re_ne_zero
    (q : XiZeroCopy) (hq : (I * xiSpectralPoint q).re ≠ 0) :
    (q.1 : ℂ).re ≠ 1 / 2 := by
  intro hline
  apply hq
  rw [I_mul_xiSpectralPoint, Complex.sub_re, hline]
  norm_num

/-- The direct three-center argument only requires copies to be off the critical line; orientation
was used in the earlier finite-packet theorem solely to establish this fact. -/
theorem finite_offLine_card_mul_directThreeCenterCharge_le_offLineLatticeBudget
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hoff : ∀ q ∈ S, (q.1 : ℂ).re ≠ 1 / 2)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K) :
    (S.card : ℝ) * (63488 / 21125 : ℝ) ≤
      criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  calc
    (S.card : ℝ) * (63488 / 21125 : ℝ) =
        ∑ _q ∈ S, (63488 / 21125 : ℝ) := by simp
    _ ≤ ∑ q ∈ S, ∑ k ∈ K,
        offLineCriticalFeatureHolomorphicEnergy (k : ℝ) q := by
      gcongr with q hq
      let kq : ℤ := round (xiSpectralPoint q).re
      have hmem := hcenters q hq
      have hqoff := hoff q hq
      have hthree :=
        directThreeCenterCriticalFeatureHolomorphicCharge_lower
          (z := xiSpectralPoint q) (t := (kq : ℝ))
          (abs_xiSpectralPoint_im_lt_half q) (abs_sub_round _)
      have hoffeq (j : ℤ) :
          ((criticalFeatureCauchyKernelTest (j : ℝ)
            (xiSpectralPoint q)) ^ 2).re =
            offLineCriticalFeatureHolomorphicEnergy (j : ℝ) q := by
        rw [offLineCriticalFeatureHolomorphicEnergy, if_neg hqoff]
      have hcastm : (kq : ℝ) - 1 = ((kq - 1 : ℤ) : ℝ) := by
        exact_mod_cast (rfl : kq - 1 = kq - 1)
      have hcastp : (kq : ℝ) + 1 = ((kq + 1 : ℤ) : ℝ) := by
        exact_mod_cast (rfl : kq + 1 = kq + 1)
      rw [hcastm, hcastp, hoffeq, hoffeq, hoffeq] at hthree
      let Tq : Finset ℤ := {kq - 1, kq, kq + 1}
      have hTq : Tq ⊆ K := by
        intro j hj
        simp only [Tq, Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with hj | hj | hj
        · simpa [hj] using hmem.1
        · simpa [hj] using hmem.2.1
        · simpa [hj] using hmem.2.2
      have hsumTq :
          (∑ j ∈ Tq, offLineCriticalFeatureHolomorphicEnergy (j : ℝ) q) =
            offLineCriticalFeatureHolomorphicEnergy ((kq - 1 : ℤ) : ℝ) q +
              offLineCriticalFeatureHolomorphicEnergy (kq : ℝ) q +
              offLineCriticalFeatureHolomorphicEnergy ((kq + 1 : ℤ) : ℝ) q := by
        have hm0 : kq - 1 ≠ kq := by omega
        have hmp : kq - 1 ≠ kq + 1 := by omega
        have h0p : kq ≠ kq + 1 := by omega
        simp [Tq, hm0, hmp, h0p]
        ring
      calc
        (63488 / 21125 : ℝ) ≤ ∑ j ∈ Tq,
            offLineCriticalFeatureHolomorphicEnergy (j : ℝ) q := by
          rw [hsumTq]
          simpa [Int.cast_sub, Int.cast_add] using hthree
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

/-- A strict-right packet and its disjoint critical-line-reflected packet deposit twice the direct
three-center charge in the same all-copy corrected budget. -/
theorem finite_strictRight_card_mul_reflectedDirectThreeCenterCharge_le_offLineLatticeBudget
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K) :
    (S.card : ℝ) * (126976 / 21125 : ℝ) ≤
      criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  let R : Finset XiZeroCopy := S.image xiZeroCopyLineConjEquiv
  let U : Finset XiZeroCopy := S ∪ R
  have hdisjoint : Disjoint S R := by
    rw [Finset.disjoint_left]
    intro q hqS hqR
    rw [R, Finset.mem_image] at hqR
    obtain ⟨p, hpS, hpq⟩ := hqR
    subst q
    have hp := hright p hpS
    have hreflected := hright (xiZeroCopyLineConjEquiv p) hqS
    rw [I_mul_xiSpectralPoint_lineConj_re] at hreflected
    linarith
  have hcardR : R.card = S.card := by
    exact Finset.card_image_of_injective S xiZeroCopyLineConjEquiv.injective
  have hcardU : U.card = 2 * S.card := by
    rw [U, Finset.card_union_of_disjoint hdisjoint, hcardR]
    omega
  have hoffU : ∀ q ∈ U, (q.1 : ℂ).re ≠ 1 / 2 := by
    intro q hqU
    rw [U, Finset.mem_union] at hqU
    rcases hqU with hqS | hqR
    · exact xiZeroCopy_re_ne_half_of_I_mul_xiSpectralPoint_re_ne_zero q
        (ne_of_gt (hright q hqS))
    · rw [R, Finset.mem_image] at hqR
      obtain ⟨p, hpS, rfl⟩ := hqR
      apply xiZeroCopy_re_ne_half_of_I_mul_xiSpectralPoint_re_ne_zero
      rw [I_mul_xiSpectralPoint_lineConj_re]
      exact neg_ne_zero.mpr (ne_of_gt (hright p hpS))
  have hcentersU : ∀ q ∈ U,
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K := by
    intro q hqU
    rw [U, Finset.mem_union] at hqU
    rcases hqU with hqS | hqR
    · exact hcenters q hqS
    · rw [R, Finset.mem_image] at hqR
      obtain ⟨p, hpS, rfl⟩ := hqR
      have hre : (xiSpectralPoint (xiZeroCopyLineConjEquiv p)).re =
          (xiSpectralPoint p).re := by
        rw [xiSpectralPoint_lineConj]
        simp
      rw [hre]
      exact hcenters p hpS
  have hcharge :=
    finite_offLine_card_mul_directThreeCenterCharge_le_offLineLatticeBudget
      K U hoffU hcentersU
  calc
    (S.card : ℝ) * (126976 / 21125 : ℝ) =
        (U.card : ℝ) * (63488 / 21125 : ℝ) := by
      rw [hcardU]
      push_cast
      ring
    _ ≤ criticalFeaturePrimeGammaOffLineLatticeBudget K := hcharge

/-- Reflected-pair direct three-center 75% receiver.  The sufficient corrected-source ceiling is
`15872/21125`, twice the previous `7936/21125`. -/
theorem three_quarters_line_of_reflectedDirectThreeCenter_primeGammaOffLineLatticeBudget
    {N N₀ : ℝ} (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenters : ∀ q ∈ S,
      round (xiSpectralPoint q).re - 1 ∈ K ∧
      round (xiSpectralPoint q).re ∈ K ∧
      round (xiSpectralPoint q).re + 1 ∈ K)
    (hsplit : N = N₀ + 2 * S.card)
    (hbudget : criticalFeaturePrimeGammaOffLineLatticeBudget K ≤
      (15872 / 21125 : ℝ) * N) :
    3 * N / 4 ≤ N₀ := by
  have hcharge :=
    finite_strictRight_card_mul_reflectedDirectThreeCenterCharge_le_offLineLatticeBudget
      K S hright hcenters
  have hcount : (S.card : ℝ) ≤ N / 8 := by
    nlinarith
  nlinarith

/-- At the reflected-pair constant, corrected HCF budget ceiling is equivalent to the literal
source-only pole--Gamma Plemelj covariance ceiling. -/
theorem canonical_correctedBudget_ceiling_iff_plemeljCovariance_ceiling_reflectedDirectThreeCenter :
    CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePrimeGammaOffLineLatticeBudget
          (criticalFeatureCanonicalLatticeWindow n))
        (15872 / 21125) ↔
      CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePoleGammaPlemeljCovariance
          (criticalFeatureCanonicalLatticeWindow n))
        (15872 / 21125) := by
  have hdiff := tendsto_canonical_correctedBudget_sub_plemeljCovariance_div
  have htransfer (X Y : ℕ → ℝ)
      (hXY : Tendsto
        (fun n => (X n - Y n) / criticalFeatureCanonicalZeroCount n)
        atTop (𝓝 0))
      (hY : CriticalFeatureCanonicalAsymptoticUpper Y (15872 / 21125)) :
      CriticalFeatureCanonicalAsymptoticUpper X (15872 / 21125) := by
    intro ε hε
    have hY' := hY (ε / 2) (by linarith)
    have herr : ∀ᶠ n : ℕ in atTop,
        (X n - Y n) / criticalFeatureCanonicalZeroCount n < ε / 2 :=
      (tendsto_order.1 hXY).2 _ (by linarith)
    filter_upwards [hY', herr, eventually_criticalFeatureCanonicalZeroCount_pos]
      with n hYn heren hN
    have hdiffn : X n - Y n <
        (ε / 2) * criticalFeatureCanonicalZeroCount n :=
      (div_lt_iff₀ hN).mp heren
    nlinarith
  constructor
  · intro hcorrected
    apply htransfer _ _ ?_ hcorrected
    have hneg := hdiff.neg
    simp only [neg_zero] at hneg
    convert hneg using 1
    funext n
    ring
  · exact htransfer _ _ hdiff

end

end RHTower
