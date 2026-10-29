import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheRobinFinitePartIsStableUnderLipschitzPerturbations
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheCriticalExponent

/-!
# Smooth dilation has a small Lipschitz difference

A fixed compact `C²` profile supplies a Lipschitz bound proportional to
`c-1` for `phi(./c)-phi`, throughout `1<=c<=2`. Its absolute mass has the
same modulus. These are produced bounds for the actual dilated profiles.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory

/-- The derivative of the actual dilation difference is uniformly small,
so its global Lipschitz constant tends to zero with the ratio. -/
theorem exists_atomDilate_lipschitz_difference_budget {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 1 ≤ c → c ≤ 2 → ∀ u v : ℝ,
      |(atomDilate φ c u - φ u) - (atomDilate φ c v - φ v)| ≤
        C * (c - 1) * |u - v| := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hsupp
  have hφd : ContDiff ℝ 1 (deriv φ) := hφ.iterate_deriv' 1 1
  obtain ⟨B, hB⟩ := hφd.continuous.bounded_above_of_compact_support hφc.deriv
  have hB0 : 0 ≤ B := (norm_nonneg (deriv φ 0)).trans (hB 0)
  have hBabs : ∀ u, |deriv φ u| ≤ B := by
    intro u
    simpa only [Real.norm_eq_abs] using hB u
  obtain ⟨L, hL, hLipD⟩ := ArithmeticCriticalityTheory.exists_lipschitz_bound_of_compactSupport
    hφd hφc.deriv
  have hvan : VanishesOff φ := by
    intro u hu
    apply hsupp u
    intro h
    rw [abs_of_nonneg h.1] at hu
    exact (not_lt_of_ge h.2) hu
  have hvanD := vanishesOff_deriv hvan
  let C : ℝ := 1 + B + 2 * L
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro c hc1 hc2 u v
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hδ : 0 ≤ c - 1 := sub_nonneg.mpr hc1
  have hinv : 1 / c ≤ 1 := by
    simpa only [one_div_one] using one_div_le_one_div_of_le zero_lt_one hc1
  have hratio : |1 / c - 1| ≤ c - 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hinv), neg_sub,
      show 1 - 1 / c = (c - 1) / c by field_simp [hc0.ne']; ring]
    exact div_le_self hδ hc1
  have hd (z : ℝ) : HasDerivAt (fun z => atomDilate φ c z - φ z)
      (deriv φ (z / c) / c - deriv φ z) z := by
    simpa only [atomDilate, mul_one_div] using
      (((hφ.differentiable (by norm_num) (z / c)).hasDerivAt.comp z
        ((hasDerivAt_id z).div_const c)).sub
        (hφ.differentiable (by norm_num) z).hasDerivAt)
  have hbound : ∀ z, |deriv φ (z / c) / c - deriv φ z| ≤ C * (c - 1) := by
    intro z
    by_cases hz : |z| ≤ 2
    · have hzratio : |z / c - z| ≤ 2 * (c - 1) := by
        rw [show z / c - z = z * (1 / c - 1) by ring, abs_mul]
        exact mul_le_mul hz hratio (abs_nonneg _) (by norm_num)
      have hdiff : |deriv φ (z / c) - deriv φ z| ≤ L * (2 * (c - 1)) :=
        (hLipD z (z / c)).trans (mul_le_mul_of_nonneg_left hzratio hL)
      calc
        _ = |(deriv φ (z / c) - deriv φ z) / c + (1 / c - 1) * deriv φ z| := by
          congr 1
          ring
        _ ≤ |(deriv φ (z / c) - deriv φ z) / c| + |(1 / c - 1) * deriv φ z| :=
          abs_add_le _ _
        _ ≤ L * (2 * (c - 1)) + (c - 1) * B := by
          rw [abs_div, abs_of_pos hc0, abs_mul]
          exact add_le_add ((div_le_self (abs_nonneg _) hc1).trans hdiff)
            (mul_le_mul hratio (hBabs z) (abs_nonneg _) hδ)
        _ ≤ _ := by dsimp only [C]; nlinarith only [hδ]
    · have hz' : 2 < |z| := not_le.mp hz
      have hzc : 1 < |z / c| := by
        rw [abs_div, abs_of_pos hc0, one_lt_div hc0]
        exact hc2.trans_lt hz'
      rw [hvanD _ hzc, hvanD z (by linarith only [hz']), zero_div, sub_zero, abs_zero]
      exact mul_nonneg hC.le hδ
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (hd z).hasDerivWithinAt)
    (fun z _ => by simpa only [Real.norm_eq_abs] using hbound z)
    convex_univ (mem_univ v) (mem_univ u)
  simpa only [Real.norm_eq_abs] using h

/-- The same produced Lipschitz constant controls the absolute mass of the
actual profile change, with no separate regularity estimate assumed. -/
theorem exists_atomDilate_lipschitz_and_mass_budgets {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 1 ≤ c → c ≤ 2 →
      (∀ u v : ℝ, |(atomDilate φ c u - φ u) - (atomDilate φ c v - φ v)| ≤
        C * (c - 1) * |u - v|) ∧
      (∫ u, |atomDilate φ c u - φ u|) ≤ 6 * C * (c - 1) := by
  obtain ⟨C, hC, hb⟩ := exists_atomDilate_lipschitz_difference_budget hφ hsupp
  refine ⟨C, hC, ?_⟩
  intro c hc1 hc2
  refine ⟨hb c hc1 hc2, ?_⟩
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hδ : 0 ≤ c - 1 := sub_nonneg.mpr hc1
  obtain ⟨hψ, hψsupp, hψc⟩ := atomDilate_facts hφ hsupp hc0
  let d : ℝ → ℝ := fun u => atomDilate φ c u - φ u
  have hd : Continuous d := hψ.continuous.sub hφ.continuous
  have hdsupp : ∀ u, u ∉ Icc 0 2 → d u = 0 := by
    intro u hu
    have huψ : u ∉ Icc 0 c := fun h => hu ⟨h.1, h.2.trans hc2⟩
    have huφ : u ∉ Icc 0 1 := fun h => hu ⟨h.1, h.2.trans (by norm_num)⟩
    simp only [d, hψsupp u huψ, hsupp u huφ, sub_self]
  have hm : d (-1) = 0 := hdsupp (-1) (by norm_num)
  have hpoint : ∀ u ∈ Icc 0 2, |d u| ≤ 3 * C * (c - 1) := by
    intro u hu
    have h := hb c hc1 hc2 u (-1)
    change |d u - d (-1)| ≤ C * (c - 1) * |u - (-1)| at h
    rw [hm, sub_zero, sub_neg_eq_add, abs_of_nonneg (by linarith only [hu.1])] at h
    have hmul := mul_le_mul_of_nonneg_left (show u + 1 ≤ 3 by linarith only [hu.2])
      (mul_nonneg hC.le hδ)
    exact h.trans (hmul.trans_eq (by ring))
  have heq : (∫ u, |d u|) = ∫ u in Icc 0 2, |d u| := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
    intro u hu
    rw [hdsupp u hu, abs_zero]
  change (∫ u, |d u|) ≤ _
  rw [heq]
  calc
    _ ≤ ∫ _ in Icc (0 : ℝ) 2, 3 * C * (c - 1) :=
      setIntegral_mono_on hd.abs.integrableOn_Icc continuous_const.integrableOn_Icc
        measurableSet_Icc hpoint
    _ = _ := by
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by norm_num), sub_zero]
      ring

/-- Actual smooth profile dilations have a small mixed Robin change uniformly
in the displacement and the finite-part window. -/
theorem exists_atomDilate_mixedRobin_difference_budget {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ c : ℝ, 1 ≤ c → c ≤ 2 → ∀ W : ℝ, 0 ≤ W → ∀ a : ℝ,
      |mixedBumpRobin (atomDilate φ c) (fun u => atomDilate φ c (u - a)) W -
        mixedBumpRobin φ (fun u => φ (u - a)) W| ≤ K * W * (c - 1) := by
  obtain ⟨C, hC, hLip⟩ := exists_atomDilate_lipschitz_difference_budget hφ hsupp
  let A : ℝ := ∫ u, |φ u|
  have hA : 0 ≤ A := integral_nonneg fun u => abs_nonneg _
  let K : ℝ := 1 + 6 * C * A
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro c hc1 hc2 W hW a
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hδ : 0 ≤ c - 1 := sub_nonneg.mpr hc1
  obtain ⟨hψ, _hs, hψc⟩ := atomDilate_facts hφ hsupp hc0
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hsupp
  have h := abs_mixedBumpRobin_shift_sub_le hψ hψc hφ hφc hW
    (mul_nonneg hC.le hδ) (hLip c hc1 hc2) a
  rw [integral_abs_atomDilate hc0] at h
  have hmass : c * A + A ≤ 3 * A := by nlinarith only [mul_le_mul_of_nonneg_right hc2 hA]
  calc
    _ ≤ 2 * W * (C * (c - 1)) * (c * A + A) := h
    _ ≤ 2 * W * (C * (c - 1)) * (3 * A) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ _ := by
      dsimp only [K]
      nlinarith only [mul_nonneg hW hδ]

private theorem mixedBumpRobin_zero (W : ℝ) :
    mixedBumpRobin (fun _ => 0) (fun _ => 0) W = 0 := by
  simp only [mixedBumpRobin, neg_zero, zero_add, sub_self, zero_div]

/-- Atom-mass normalization preserves the small finite-part change, with one
constant for all shifts and all finite-part windows. -/
theorem exists_normalized_atomDilate_mixedRobin_difference_budget {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ c : ℝ, 1 ≤ c → c ≤ 2 → ∀ W : ℝ, 0 ≤ W → ∀ a : ℝ,
      |mixedBumpRobin (atomDilate φ c) (fun u => atomDilate φ c (u - a)) W / c -
        mixedBumpRobin φ (fun u => φ (u - a)) W| ≤ K * W * (c - 1) := by
  obtain ⟨C, hC, hb⟩ := exists_atomDilate_mixedRobin_difference_budget hφ hsupp
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hsupp
  obtain ⟨L, hL, hLip⟩ := ArithmeticCriticalityTheory.exists_lipschitz_bound_of_compactSupport
    (hφ.of_le (by norm_num)) hφc
  let A : ℝ := ∫ u, |φ u|
  have hA : 0 ≤ A := integral_nonneg fun u => abs_nonneg _
  let K : ℝ := 1 + C + 2 * L * A
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro c hc1 hc2 W hW a
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hδ : 0 ≤ c - 1 := sub_nonneg.mpr hc1
  have hinv : 1 / c ≤ 1 := by
    simpa only [one_div_one] using one_div_le_one_div_of_le zero_lt_one hc1
  have hratio : |1 / c - 1| ≤ c - 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hinv), neg_sub,
      show 1 - 1 / c = (c - 1) / c by field_simp [hc0.ne']; ring]
    exact div_le_self hδ hc1
  have hbase : |mixedBumpRobin φ (fun u => φ (u - a)) W| ≤ 2 * W * L * A := by
    have h := abs_mixedBumpRobin_shift_sub_le hφ hφc
      (f := φ) (g := fun _ : ℝ => 0) contDiff_const HasCompactSupport.zero hW hL
      (fun u v => by simpa only [sub_zero] using hLip v u) a
    simpa only [mixedBumpRobin_zero, sub_zero, abs_zero, integral_zero, add_zero] using h
  have hdiff := hb c hc1 hc2 W hW a
  calc
    _ = |(mixedBumpRobin (atomDilate φ c) (fun u => atomDilate φ c (u - a)) W -
          mixedBumpRobin φ (fun u => φ (u - a)) W) / c +
        (1 / c - 1) * mixedBumpRobin φ (fun u => φ (u - a)) W| := by
      congr 1
      ring
    _ ≤ |(mixedBumpRobin (atomDilate φ c) (fun u => atomDilate φ c (u - a)) W -
          mixedBumpRobin φ (fun u => φ (u - a)) W) / c| +
        |(1 / c - 1) * mixedBumpRobin φ (fun u => φ (u - a)) W| := abs_add_le _ _
    _ ≤ C * W * (c - 1) + (c - 1) * (2 * W * L * A) := by
      rw [abs_div, abs_of_pos hc0, abs_mul]
      exact add_le_add ((div_le_self (abs_nonneg _) hc1).trans hdiff)
        (mul_le_mul hratio hbase (abs_nonneg _) hδ)
    _ ≤ _ := by
      dsimp only [K]
      nlinarith only [mul_nonneg hW hδ]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_atomDilate_lipschitz_and_mass_budgets
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_atomDilate_mixedRobin_difference_budget
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_normalized_atomDilate_mixedRobin_difference_budget
