import GaloisForLFunctions.ArithmeticElectrostatics.ThePolynomialHeatDivisorObeysLogarithmicThresholds
import GaloisForLFunctions.ArithmeticElectrostatics.TheHeatDivisorPaysElapsedDepth
import GaloisForLFunctions.RHTower.DeBruijnNewmanEnergyUnitTime

/-!
# Initial depth layers pay for heat survival

The Riemann heat divisor inherits every polynomial logarithmic threshold
budget. A continuous minorant passes each finite nonreal target packet
through locally uniform polynomial heat convergence. Initial shallow roots
contribute exactly zero, while extended nonnegative sums retain arbitrarily
large initial budgets. Every surviving pair pays the explicit logarithmic
elapsed-time credit.
-/

open Polynomial Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.ArithmeticElectrostatics
noncomputable section

/-- Full nonreal logarithmic threshold moment at positive heat time. -/
def heatLogarithmicThresholdMoment (a t : ℝ) : ℝ :=
  heatWeightedZeroSum (fun z => if z.im = 0 then 0 else
    logarithmicDepthThreshold a (z.im ^ 2 + 2 * t)) t

/-- Upper-half logarithmic threshold moment, counting algebraic multiplicity. -/
def heatUpperLogarithmicThresholdMoment (a t : ℝ) : ℝ :=
  heatWeightedZeroSum (fun z => if 0 < z.im then
    logarithmicDepthThreshold a (z.im ^ 2 + 2 * t) else 0) t

theorem heatLogarithmicThresholdMoment_eq_sum (a : ℝ) {t : ℝ} (ht : 0 < t) :
    heatLogarithmicThresholdMoment a t =
      ∑ z ∈ (riemannHeat_nonreal_zeros_finite ht).toFinset,
        (zeroMult (riemannHeat t) z : ℝ) * logarithmicDepthThreshold a (z.im ^ 2 + 2 * t) := by
  classical
  unfold heatLogarithmicThresholdMoment heatWeightedZeroSum
  have hsupport : (∑' z : ℂ, (zeroMult (riemannHeat t) z : ℝ) *
      (if z.im = 0 then 0 else logarithmicDepthThreshold a (z.im ^ 2 + 2 * t))) =
      ∑ z ∈ (riemannHeat_nonreal_zeros_finite ht).toFinset,
        (zeroMult (riemannHeat t) z : ℝ) *
          (if z.im = 0 then 0 else logarithmicDepthThreshold a (z.im ^ 2 + 2 * t)) := by
    apply tsum_eq_sum
    intro z hz
    by_cases hf : riemannHeat t z = 0
    · have hi : z.im = 0 := by
        by_contra hi
        exact hz ((Set.Finite.mem_toFinset _).mpr ⟨hf, hi⟩)
      simp only [hi, if_true, mul_zero]
    · rw [zeroMult_riemannHeat_eq_zero ht.le hf, Nat.cast_zero, zero_mul]
  rw [hsupport]
  apply Finset.sum_congr rfl
  intro z hz
  rw [if_neg ((Set.Finite.mem_toFinset _).mp hz).2]

theorem heatUpperLogarithmicThresholdMoment_eq_sum (a : ℝ) {t : ℝ} (ht : 0 < t) :
    heatUpperLogarithmicThresholdMoment a t =
      ∑ z ∈ (riemannHeat_nonreal_zeros_finite ht).toFinset.filter (fun z => 0 < z.im),
        (zeroMult (riemannHeat t) z : ℝ) * logarithmicDepthThreshold a (z.im ^ 2 + 2 * t) := by
  classical
  unfold heatUpperLogarithmicThresholdMoment heatWeightedZeroSum
  have hsupport : (∑' z : ℂ, (zeroMult (riemannHeat t) z : ℝ) *
      (if 0 < z.im then logarithmicDepthThreshold a (z.im ^ 2 + 2 * t) else 0)) =
      ∑ z ∈ (riemannHeat_nonreal_zeros_finite ht).toFinset,
        (zeroMult (riemannHeat t) z : ℝ) *
          (if 0 < z.im then logarithmicDepthThreshold a (z.im ^ 2 + 2 * t) else 0) := by
    apply tsum_eq_sum
    intro z hz
    by_cases hf : riemannHeat t z = 0
    · have hi : z.im = 0 := by
        by_contra hi
        exact hz ((Set.Finite.mem_toFinset _).mpr ⟨hf, hi⟩)
      simp only [hi, lt_self_iff_false, if_false, mul_zero]
    · rw [zeroMult_riemannHeat_eq_zero ht.le hf, Nat.cast_zero, zero_mul]
  rw [hsupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> simp only [mul_zero]

theorem heatLogarithmicThresholdMoment_eq_twice_upper (a : ℝ) {t : ℝ} (ht : 0 < t) :
    heatLogarithmicThresholdMoment a t = 2 * heatUpperLogarithmicThresholdMoment a t := by
  classical
  let S := (riemannHeat_nonreal_zeros_finite ht).toFinset
  let f : ℂ → ℝ := fun z =>
    (zeroMult (riemannHeat t) z : ℝ) * logarithmicDepthThreshold a (z.im ^ 2 + 2 * t)
  have hS (z : ℂ) (hz : z ∈ S) := (Set.Finite.mem_toFinset _).mp hz
  have hconj (z : ℂ) (hz : z ∈ S) : starRingEnd ℂ z ∈ S := by
    apply (Set.Finite.mem_toFinset _).mpr
    constructor
    · rw [riemannHeat_conj ht.le, (hS z hz).1, map_zero]
    · simpa only [Complex.conj_im, neg_ne_zero] using (hS z hz).2
  have hpair := congrArg Complex.re (sum_conjugate_packet S
    (fun z hz => (hS z hz).2) hconj (fun z => (f z : ℂ)))
  have heven (z : ℂ) : f (starRingEnd ℂ z) = f z := by
    simp only [f, zeroMult_riemannHeat_conj ht.le, Complex.conj_im, neg_sq]
  simp only [Complex.re_sum, Complex.add_re, Complex.ofReal_re, heven] at hpair
  rw [heatLogarithmicThresholdMoment_eq_sum a ht, heatUpperLogarithmicThresholdMoment_eq_sum a ht]
  change (∑ z ∈ S, f z) = 2 * ∑ z ∈ S.filter (fun z => 0 < z.im), f z
  rw [hpair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem sum_root_depth_profile_xiRealApprox (n : ℕ) (F : ℝ → ℝ) :
    (((xiRealApprox n).map ofRealHom).roots.map (fun z => F (z.im ^ 2))).sum =
      ∑ ρ ∈ xiPairedCopyFinset (xiConjClosedFinset n), F ((xiSpectralPoint ρ).im ^ 2) := by
  rw [map_xiRealApprox, roots_C_mul _ XiC_zero_ne_zero, roots_xiZeroPoly,
    Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

/-- A uniform bound on finite initial packets controls the entire heat divisor. -/
theorem heat_logarithmicThreshold_le_initial_bound {a t K : ℝ}
    (ha : 0 < a) (ht : 0 < t)
    (hK : ∀ T : Finset XiZeroCopy,
      ∑ ρ ∈ T, logarithmicDepthThreshold a ((xiSpectralPoint ρ).im ^ 2) ≤ K) :
    heatLogarithmicThresholdMoment a t ≤ K := by
  classical
  have hK0 : 0 ≤ K := by simpa only [Finset.sum_empty] using hK ∅
  by_cases ht1 : t ≤ 1
  · let S := (riemannHeat_nonreal_zeros_finite ht).toFinset
    have hS (z : ℂ) (hz : z ∈ S) : z.im ≠ 0 := ((Set.Finite.mem_toFinset _).mp hz).2
    have hbase : Continuous (fun z : ℂ => z.im ^ 2 + 2 * t) :=
      (Complex.continuous_im.pow 2).add continuous_const
    obtain ⟨Ψ, hΨ, hΨ0, hΨreal, hΨle, hΨeq⟩ := exists_real_axis_vanishing_minorant S hS
      (fun z => logarithmicDepthThreshold a (z.im ^ 2 + 2 * t))
      ((continuous_logarithmicDepthThreshold a).comp hbase)
      (fun z => logarithmicDepthThreshold_nonneg a _)
    have hpoly (n : ℕ) :
        ((((polyHeat t (xiRealApprox n)).map ofRealHom).roots).map Ψ).sum ≤ K := by
      have h := (sum_weight_le_nonreal_profile
        (((polyHeat t (xiRealApprox n)).map ofRealHom).roots) Ψ
        (fun z => logarithmicDepthThreshold a (z.im ^ 2 + 2 * t)) hΨreal hΨle).trans
          (polynomial_logarithmicThreshold_le_initial (xiRealApprox_ne_zero n) ht.le ha)
      rw [sum_root_depth_profile_xiRealApprox] at h
      exact h.trans (hK _)
    have hsmall : 8 * xiApproxGrowth * t < 1 := by
      calc
        8 * xiApproxGrowth * t ≤ 8 * xiApproxGrowth * 1 :=
          mul_le_mul_of_nonneg_left ht1 (mul_nonneg (by norm_num) xiApproxGrowth_nonneg)
        _ < 1 := by nlinarith only [xiApproxGrowth_lt]
    have h := sum_zeroMult_mul_le_of_tendstoLocallyUniformly
      (differentiable_riemannHeat ht.le) ⟨0, RHTower.DeBruijn.riemannHeat_zero_ne ht.le⟩ S
      (tendstoLocallyUniformly_polyHeat_xiRealApprox ht hsmall)
      hΨ hΨ0 (Filter.Eventually.of_forall hpoly)
    have heq : (∑ z ∈ S, (zeroMult (riemannHeat t) z : ℝ) * Ψ z) =
        heatLogarithmicThresholdMoment a t := by
      rw [heatLogarithmicThresholdMoment_eq_sum a ht]
      apply Finset.sum_congr rfl
      intro z hz
      rw [hΨeq z hz]
    rwa [heq] at h
  · have hempty : (riemannHeat_nonreal_zeros_finite ht).toFinset = ∅ := by
      ext z
      constructor
      · intro hz
        exfalso
        have hz' := (Set.Finite.mem_toFinset _).mp hz
        exact hz'.2 (riemannHeat_zeros_real (show 1 / 8 ≤ t by linarith only [ht1]) hz'.1)
      · simp
    rw [heatLogarithmicThresholdMoment_eq_sum a ht, hempty, Finset.sum_empty]
    exact hK0

/-- Extended initial budget; depths at or below `a` cost zero. -/
def initialLogarithmicDepthBudget (a : ℝ) : ENNReal :=
  ∑' ρ : XiZeroCopy, ENNReal.ofReal (logarithmicDepthThreshold a ((xiSpectralPoint ρ).im ^ 2))

/-- Initial upper-half budget, with zero copies retaining multiplicity. -/
def initialUpperLogarithmicDepthBudget (a : ℝ) : ENNReal :=
  ∑' ρ : XiZeroCopy,
    ENNReal.ofReal (logarithmicDepthThreshold a ((max (xiSpectralPoint ρ).im 0) ^ 2))

theorem initialLogarithmicDepthBudget_eq_twice_upper (a : ℝ) :
    initialLogarithmicDepthBudget a = 2 * initialUpperLogarithmicDepthBudget a := by
  have hp (y : ℝ) : ENNReal.ofReal (logarithmicDepthThreshold a (y ^ 2)) =
      ENNReal.ofReal (logarithmicDepthThreshold a ((max y 0) ^ 2)) +
        ENNReal.ofReal (logarithmicDepthThreshold a ((max (-y) 0) ^ 2)) := by
    rcases le_total 0 y with hy | hy
    · simp only [max_eq_left hy, max_eq_right (neg_nonpos.mpr hy), zero_pow two_ne_zero,
        logarithmicDepthThreshold_zero, ENNReal.ofReal_zero, add_zero]
    · simp only [max_eq_right hy, max_eq_left (neg_nonneg.mpr hy), neg_sq, zero_pow two_ne_zero,
        logarithmicDepthThreshold_zero, ENNReal.ofReal_zero, zero_add]
  have hreindex : (∑' ρ : XiZeroCopy,
      ENNReal.ofReal (logarithmicDepthThreshold a ((max (-(xiSpectralPoint ρ).im) 0) ^ 2))) =
      ∑' ρ : XiZeroCopy,
        ENNReal.ofReal (logarithmicDepthThreshold a ((max (xiSpectralPoint ρ).im 0) ^ 2)) := by
    simpa only [xiSpectralPoint_reflect, Complex.neg_im] using
      xiZeroCopyReflectEquiv.tsum_eq
        (fun ρ => ENNReal.ofReal (logarithmicDepthThreshold a ((max (xiSpectralPoint ρ).im 0) ^ 2)))
  rw [show initialLogarithmicDepthBudget a = ∑' ρ : XiZeroCopy,
      (ENNReal.ofReal (logarithmicDepthThreshold a ((max (xiSpectralPoint ρ).im 0) ^ 2)) +
        ENNReal.ofReal (logarithmicDepthThreshold a ((max (-(xiSpectralPoint ρ).im) 0) ^ 2))) from
      tsum_congr (fun ρ => hp (xiSpectralPoint ρ).im)]
  rw [ENNReal.tsum_add, hreindex, ← two_mul]
  rfl

theorem heat_logarithmicThreshold_le_initial {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    ENNReal.ofReal (heatLogarithmicThresholdMoment a t) ≤ initialLogarithmicDepthBudget a := by
  by_cases htop : initialLogarithmicDepthBudget a = ⊤
  · rw [htop]
    exact le_top
  have hK (T : Finset XiZeroCopy) :
      (∑ ρ ∈ T, logarithmicDepthThreshold a ((xiSpectralPoint ρ).im ^ 2)) ≤
        (initialLogarithmicDepthBudget a).toReal := by
    have hnonneg (ρ : XiZeroCopy) := logarithmicDepthThreshold_nonneg a ((xiSpectralPoint ρ).im ^ 2)
    have hsum : ENNReal.ofReal
        (∑ ρ ∈ T, logarithmicDepthThreshold a ((xiSpectralPoint ρ).im ^ 2)) ≤
        initialLogarithmicDepthBudget a := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun ρ _ => hnonneg ρ)]
      exact ENNReal.sum_le_tsum T
    have h := ENNReal.toReal_mono htop hsum
    rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun ρ _ => hnonneg ρ))] at h
  exact (ENNReal.ofReal_le_ofReal (heat_logarithmicThreshold_le_initial_bound ha ht hK)).trans_eq
    (ENNReal.ofReal_toReal htop)

/-- Every positive heat fibre obeys its initial upper logarithmic threshold budget. -/
theorem heat_upper_logarithmicThreshold_le_initial {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    ENNReal.ofReal (heatUpperLogarithmicThresholdMoment a t) ≤ initialUpperLogarithmicDepthBudget a := by
  have h := heat_logarithmicThreshold_le_initial ha ht
  rw [heatLogarithmicThresholdMoment_eq_twice_upper a ht,
    initialLogarithmicDepthBudget_eq_twice_upper a,
    ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num), ENNReal.ofReal_ofNat,
    mul_comm 2 (ENNReal.ofReal _), mul_comm 2 (initialUpperLogarithmicDepthBudget a)] at h
  exact (ENNReal.mul_le_mul_iff_left (by norm_num : (2 : ENNReal) ≠ 0) (by simp)).mp h

/-- Each nonreal root pays `log(2t/a)` from the initial upper-depth budget. -/
theorem nonrealCount_logarithmic_credit_le_initial {a t : ℝ}
    (ha : 0 < a) (ht : 0 < t) (hat : a < 2 * t) :
    ENNReal.ofReal ((nonrealZeroCount t : ℝ) * Real.log (2 * t / a)) ≤
      2 * initialUpperLogarithmicDepthBudget a := by
  have hbase : logarithmicDepthThreshold a (2 * t) * (nonrealZeroCount t : ℝ) ≤
      heatLogarithmicThresholdMoment a t := by
    rw [heatLogarithmicThresholdMoment_eq_sum a ht, nonrealZeroCount_eq ht,
      Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z _
    rw [mul_comm (logarithmicDepthThreshold a (2 * t))]
    exact mul_le_mul_of_nonneg_left
      (monotone_logarithmicDepthThreshold ha (le_add_of_nonneg_left (sq_nonneg _)))
      (Nat.cast_nonneg _)
  have hcredit : logarithmicDepthThreshold a (2 * t) = Real.log (2 * t / a) := by
    unfold logarithmicDepthThreshold
    rw [max_eq_right ((le_div_iff₀ ha).mpr (by simpa only [one_mul] using hat.le))]
  rw [hcredit, mul_comm] at hbase
  rw [← initialLogarithmicDepthBudget_eq_twice_upper a]
  exact (ENNReal.ofReal_le_ofReal hbase).trans (heat_logarithmicThreshold_le_initial ha ht)

#print axioms heat_logarithmicThreshold_le_initial_bound
#print axioms heat_upper_logarithmicThreshold_le_initial
#print axioms nonrealCount_logarithmic_credit_le_initial

end
end GaloisForLFunctions.ArithmeticElectrostatics
