import GaloisForLFunctions.InfiniteRankWeilTheory.AlmostEveryIsolatedTopSampling
import GaloisForLFunctions.InfiniteRankWeilTheory.TheTowersOfZeta
import GaloisForLFunctions.ZeroConfigurationGeometry.AsymptoticAbscissaSpectralGapAndTopAnnihilator

/-!
# Metric detection of an exceptional zeta top

Failure of the zeta abscissa law forces every sufficiently large sampled Weil lag above every
sub-top exponential threshold at almost every positive base. Consequently a positive-measure
set of bases with infinitely many subexponential readings forces AAL. Together with zeros
approaching the line, this gives an equivalent formulation of RH.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- Failure of actual zeta AAL forces eventual detection of the finite top at almost every base.
The lag weights supply both absolute summability and nonzero merged coefficients. -/
theorem not_asymptoticAbscissaLaw_implies_metric_top_detection :
    ¬ RHTower.AsymptoticAbscissaLaw → 1 / 2 < RHTower.zetaZeroAbscissa ∧
      ∀ᵐ ℓ ∂volume, 0 < ℓ → ∀ a : ℝ, a < RHTower.zetaZeroAbscissa - 1 / 2 → ∀ C : ℝ,
        ∀ᶠ n : ℕ in atTop,
          C * Real.exp (a * (n : ℝ) * ℓ) < ‖RHTower.weilLagFunction ((n : ℝ) * ℓ)‖ := by
  classical
  intro hnot
  rw [asymptoticAbscissaLaw_zetaConfig_iff,
    not_asymptoticAbscissaLaw_iff_hasIsolatedTop] at hnot
  obtain ⟨F, Θ, Θ₂, hFne, hΘ, hgap, hF, hrest⟩ := hnot
  have hΘeq : Θ = RHTower.zetaZeroAbscissa := by
    apply le_antisymm
    · obtain ⟨j, hj⟩ := hFne
      rw [← hF j hj]
      exact RHTower.re_le_zetaZeroAbscissa (RHTower.riemannZeta_eq_zero_of_xiZeroCopy j)
    · apply ZeroConfigurationGeometry.zetaZeroAbscissa_le_of_forall_xiZeroCopy_re_le hΘ.le
      intro j
      by_cases hj : j ∈ F
      · exact (hF j hj).le
      · exact (hrest j hj).trans hgap.le
  have hvis : ∃ j ∈ F,
      (∑ i ∈ F with (zetaConfig i).im = (zetaConfig j).im, lagWeight i) ≠ 0 := by
    obtain ⟨j, hj⟩ := hFne
    refine ⟨j, hj, fun h => ?_⟩
    have hre := congrArg Complex.re h
    rw [Complex.re_sum, Complex.zero_re] at hre
    have hpos : 0 < ∑ i ∈ F with (zetaConfig i).im = (zetaConfig j).im,
        (lagWeight i).re := Finset.sum_pos (fun i _ => re_lagWeight_pos i)
          ⟨j, Finset.mem_filter.mpr ⟨hj, rfl⟩⟩
    linarith only [hre, hpos]
  rw [← hΘeq]
  refine ⟨hΘ, ?_⟩
  simpa only [weilLagFunction_mul_eq_levelSum] using
    ae_eventually_isolatedTop_exp_lower zetaConfig lagWeight summable_norm_lagWeight
      F hgap hF hrest hvis

/-- Positive bases admitting infinitely many subexponential lag readings at every positive
exponent. The constants and the subsequences may depend on both the base and the exponent. -/
def subexponentialLagBases : Set ℝ :=
  {ℓ : ℝ | 0 < ℓ ∧ ∀ a : ℝ, 0 < a → ∃ C : ℝ, ∃ᶠ n : ℕ in atTop,
    ‖RHTower.weilLagFunction ((n : ℝ) * ℓ)‖ ≤ C * Real.exp (a * (n : ℝ) * ℓ)}

/-- A positive-measure family of bases with infinitely many small readings rules out every
finite exceptional top of the actual zeta divisor. -/
theorem asymptoticAbscissaLaw_of_pos_volume_subexponentialLagBases
    (hpos : 0 < volume subexponentialLagBases) : RHTower.AsymptoticAbscissaLaw := by
  by_contra hnot
  obtain ⟨hΘ, hmetric⟩ := not_asymptoticAbscissaLaw_implies_metric_top_detection hnot
  have hnull : volume subexponentialLagBases = 0 := by
    have hae : ∀ᵐ ℓ ∂volume, ℓ ∉ subexponentialLagBases := by
      filter_upwards [hmetric] with ℓ hℓ
      rintro ⟨hℓpos, hgood⟩
      have ha : 0 < (RHTower.zetaZeroAbscissa - 1 / 2) / 2 := by linarith only [hΘ]
      obtain ⟨C, hC⟩ := hgood ((RHTower.zetaZeroAbscissa - 1 / 2) / 2) ha
      obtain ⟨n, hnle, hnlt⟩ := (hC.and_eventually
        (hℓ hℓpos ((RHTower.zetaZeroAbscissa - 1 / 2) / 2)
          (by linarith only [hΘ]) C)).exists
      exact (not_lt_of_ge hnle) hnlt
    have hset : {ℓ : ℝ | ¬ ℓ ∉ subexponentialLagBases} = subexponentialLagBases := by
      ext ℓ
      exact not_not
    have hz := ae_iff.mp hae
    rw [hset] at hz
    exact hz
  rw [hnull] at hpos
  exact lt_irrefl _ hpos

/-- RH is zeros approaching the line plus a positive-measure family of bases with infinitely
many subexponential readings. No thickness or density assumption on the reading levels occurs. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_metric_lag_bound :
    RiemannHypothesis ↔ RHTower.BacklundConverse.ZerosApproachLine ∧
      0 < volume subexponentialLagBases := by
  constructor
  · intro hRH
    refine ⟨(RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mp hRH).1, ?_⟩
    have hsub : Icc (1 : ℝ) 2 ⊆ subexponentialLagBases := by
      intro ℓ hℓ
      have hℓpos : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ.1
      refine ⟨hℓpos, fun a ha => ⟨max RHTower.poleSharpConstant 0, ?_⟩⟩
      apply Filter.Eventually.frequently
      apply Filter.Eventually.of_forall
      intro n
      calc ‖RHTower.weilLagFunction ((n : ℝ) * ℓ)‖ ≤ RHTower.poleSharpConstant :=
            RHTower.norm_weilLagFunction_le_of_riemannHypothesis hRH _
        _ ≤ max RHTower.poleSharpConstant 0 := le_max_left _ _
        _ ≤ max RHTower.poleSharpConstant 0 * Real.exp (a * (n : ℝ) * ℓ) :=
            le_mul_of_one_le_right (le_max_right _ _) (Real.one_le_exp (by positivity))
    have hv : 0 < volume (Icc (1 : ℝ) 2) := by rw [Real.volume_Icc]; norm_num
    exact hv.trans_le (measure_mono hsub)
  · rintro ⟨hZ, hmetric⟩
    exact RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr
      ⟨hZ, asymptoticAbscissaLaw_of_pos_volume_subexponentialLagBases hmetric⟩

#print axioms not_asymptoticAbscissaLaw_implies_metric_top_detection
#print axioms riemannHypothesis_iff_zerosApproachLine_and_metric_lag_bound

end GaloisForLFunctions.InfiniteRankWeilTheory
