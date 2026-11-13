import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.SoftLogarithmicCompactProfiles
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.SoftLogarithmicNegativePartContinuity

/-!
# Strong limits of soft logarithmic trial profiles

Uniform first moments make the negative Fourier energy continuous.
Joint Fatou preserves the physical and positive Fourier energies, giving
finite-energy unit limits at or below the trial variational floor.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open HTGeometry CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri

/-- Joint Fatou controls the positive terms; uniform Fourier tails pass the
negative term continuously. Reality and support pass through an a.e. subsequence. -/
theorem closedSoftLogarithmic_limit_of_trials
    {F : ℕ → ℝ → ℝ} (hF : ∀ n, SoftLogarithmicHalfLineDomain (F n))
    (hm : ∀ n, (∫ u, F n u ^ 2) = 1)
    {V : ℕ → SoninL2} {v : SoninL2}
    (hV : ∀ n, (V n : ℝ → ℂ) =ᵐ[volume] cx (F n))
    (hconv : Tendsto V atTop (𝓝 v))
    {E B : ℝ} (hbound : ∀ n, softLogarithmicHalfLineEnergy (F n) ≤ E)
    (henergy : Tendsto (fun n => softLogarithmicHalfLineEnergy (F n)) atTop (𝓝 B)) :
    ClosedSoftLogarithmicHalfLineDomain v ∧ closedSoftLogarithmicHalfLineEnergy v ≤ B := by
  have hD (n : ℕ) := (hF n).toClosed (hV n)
  have hM (n : ℕ) : criticalHalfLineFirstMoment (F n) ≤ (E + 16) / 4 := by
    have h := ((hF n).sublevel_bounds (hm n) (hbound n)).1
    linarith only [h]
  have hneg := negativeLog_integral_tendsto_of_softLogarithmic_trials hF hm hV hconv hM
  have hphysical (n : ℕ) :=
    ((hF n).sublevel_bounds_of_L2_representative (hm n) (hbound n) (V n) (hV n)).2.1
  have hvphysical := weighted_norm_sq_of_L2_limit hconv measurable_abs abs_nonneg
    (fun n => (hphysical n).1) tendsto_const_nhds (fun n => (hphysical n).2)
  have hposm : Measurable (fun ξ : ℝ => max (Real.log |ξ|) 0) := by fun_prop
  have hseqi (n : ℕ) : Integrable (fun u : ℝ =>
      (8 * |u|) * ‖V n u‖ ^ 2 + max (Real.log |u|) 0 * ‖fourierUnitary (V n) u‖ ^ 2) := by
    apply (((hD n).moment.const_mul 8).add (hD n).integrable_positiveLogarithm).congr
    exact Eventually.of_forall fun u => by dsimp only [Pi.add_apply]; ring
  have hseqe (n : ℕ) : (∫ u : ℝ,
      (8 * |u|) * ‖V n u‖ ^ 2 + max (Real.log |u|) 0 * ‖fourierUnitary (V n) u‖ ^ 2) =
      softLogarithmicHalfLineEnergy (F n) +
        ∫ ξ : ℝ, max (-Real.log |ξ|) 0 * ‖fourierUnitary (V n) ξ‖ ^ 2 := by
    have hi : (fun u : ℝ => (8 * |u|) * ‖V n u‖ ^ 2 +
        max (Real.log |u|) 0 * ‖fourierUnitary (V n) u‖ ^ 2) =
        fun u => 8 * (|u| * ‖V n u‖ ^ 2) +
          max (Real.log |u|) 0 * ‖fourierUnitary (V n) u‖ ^ 2 := by funext u; ring
    rw [hi, integral_add ((hD n).moment.const_mul 8) (hD n).integrable_positiveLogarithm,
      integral_const_mul]
    have he := (hD n).energy_eq_parts
    rw [(hF n).closedEnergy_eq (hV n)] at he
    linarith only [he]
  have hsum := weighted_norm_sq_add_of_L2_limits hconv
    ((fourierUnitary.continuous.tendsto v).comp hconv)
    (measurable_const.mul measurable_abs) hposm
    (fun u => mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (abs_nonneg u))
    (fun _ => le_max_right _ _) hseqi (henergy.add hneg.2)
    (fun n => (hseqe n).le)
  have hpos : Integrable (fun ξ : ℝ =>
      max (Real.log |ξ|) 0 * ‖fourierUnitary v ξ‖ ^ 2) := by
    apply hsum.1.mono'
      (hposm.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable (fourierUnitary v)).norm.pow 2))
    exact Eventually.of_forall fun u => by
      dsimp only [Pi.mul_apply, Pi.pow_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (sq_nonneg _))]
      have hn : 0 ≤ (8 * |u|) * ‖v u‖ ^ 2 :=
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (abs_nonneg u)) (sq_nonneg _)
      linarith only [hn]
  obtain ⟨s, _, hae⟩ := exists_subseq_ae_tendsto hconv
  have hrep : ∀ᵐ u, ∀ n, V (s n) u = cx (F (s n)) u := by
    rw [ae_all_iff]
    exact fun n => hV (s n)
  have hd : ClosedSoftLogarithmicHalfLineDomain v := by
    refine ⟨?_, ?_, hvphysical.1, ?_⟩
    · filter_upwards [hae, hrep] with u hu hr
      have ht := Complex.continuous_im.continuousAt.tendsto.comp hu
      have hz : Tendsto (fun n => (V (s n) u).im) atTop (𝓝 (0 : ℝ)) := by
        have he : (fun n => (V (s n) u).im) = fun _ : ℕ => (0 : ℝ) := by
          funext n
          rw [hr n]
          exact Complex.ofReal_im (F (s n) u)
        rw [he]
        exact tendsto_const_nhds
      exact tendsto_nhds_unique ht hz
    · filter_upwards [hae, hrep] with u hu hr
      intro hnonneg
      have hz : Tendsto (fun n => V (s n) u) atTop (𝓝 (0 : ℂ)) := by
        have he : (fun n => V (s n) u) = fun _ : ℕ => (0 : ℂ) := by
          funext n
          rw [hr n]
          change (F (s n) u : ℂ) = 0
          rw [(hF (s n)).support u hnonneg, Complex.ofReal_zero]
        rw [he]
        exact tendsto_const_nhds
      exact tendsto_nhds_unique hu hz
    · apply (hpos.add hneg.1).congr
      exact Eventually.of_forall fun ξ => by
        dsimp only [Pi.add_apply]
        by_cases hξ : 0 ≤ Real.log |ξ|
        · rw [max_eq_left hξ, max_eq_right (neg_nonpos.mpr hξ),
            abs_of_nonneg hξ, zero_mul, add_zero]
        · rw [max_eq_right (lt_of_not_ge hξ).le,
            max_eq_left (neg_nonneg.mpr (lt_of_not_ge hξ).le),
            abs_of_neg (lt_of_not_ge hξ), zero_mul, zero_add]
  refine ⟨hd, ?_⟩
  have hi : (∫ u : ℝ, (8 * |u|) * ‖v u‖ ^ 2 +
      max (Real.log |u|) 0 * ‖fourierUnitary v u‖ ^ 2) =
      8 * (∫ u : ℝ, |u| * ‖v u‖ ^ 2) +
        ∫ ξ : ℝ, max (Real.log |ξ|) 0 * ‖fourierUnitary v ξ‖ ^ 2 := by
    have he : (fun u : ℝ => (8 * |u|) * ‖v u‖ ^ 2 +
        max (Real.log |u|) 0 * ‖fourierUnitary v u‖ ^ 2) =
        fun u => 8 * (|u| * ‖v u‖ ^ 2) +
          max (Real.log |u|) 0 * ‖fourierUnitary v u‖ ^ 2 := by funext u; ring
    rw [he, integral_add (hd.moment.const_mul 8) hpos, integral_const_mul]
  have hb := hsum.2
  rw [hi] at hb
  rw [hd.energy_eq_parts]
  linarith only [hb]

/-- A compact minimizing sequence has a unit finite-energy limit below the trial floor. -/
theorem exists_closedSoftLogarithmic_unit_below_floor :
    ∃ v : SoninL2, ClosedSoftLogarithmicHalfLineDomain v ∧ ‖v‖ = 1 ∧
      closedSoftLogarithmicHalfLineEnergy v ≤ softLogarithmicHalfLineGroundEnergy := by
  obtain ⟨F, hF, v, hm, hb, hn, he, hv⟩ := exists_softLogarithmic_strong_minimizingSequence
  have h := closedSoftLogarithmic_limit_of_trials hF hm
    (fun n => (hF n).memLp_complex.coeFn_toLp) hv hb he
  exact ⟨v, h.1, hn, h.2⟩

#print axioms closedSoftLogarithmic_limit_of_trials
#print axioms exists_closedSoftLogarithmic_unit_below_floor
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

