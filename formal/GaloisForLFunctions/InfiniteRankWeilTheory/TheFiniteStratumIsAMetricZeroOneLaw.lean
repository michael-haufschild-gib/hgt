import GaloisForLFunctions.InfiniteRankWeilTheory.ZetaMetricTopDetection
import GaloisForLFunctions.InfiniteRankWeilTheory.TheCrudeStepAndTheCount

/-!
# The finite stratum is a metric zero–one law

If only finitely many zeros of `ζ` lie off the critical line, the set of bases `ℓ > 0` at which
the Weil lag `Φ(nℓ)` has infinitely many subexponential readings is either every positive base
(RH: the lag is bounded) or a null set (a finite top layer is seen at almost every base). B13 —
finitely many off-line zeros force none — is the statement that in the finite stratum this set is
not null.

* `subexponentialLagBases_eq_Ioi_of_riemannHypothesis`: under RH every positive base qualifies.
* `volume_subexponentialLagBases_eq_zero_of_finiteOffLine`: a finite layer gives ZAL, so a failure
  of RH there is a failure of the abscissa law, which the metric detection theorem sees at almost
  every base.
* `subexponentialLagBases_zero_one_of_finiteOffLine`: the dichotomy.
* `b13_iff_pos_volume_subexponentialLagBases`, `b13_iff_pos_volume_lagRecurrenceBases`: B13 in
  metric form. As a crude step this is weaker than the thick-set form `b13_iff_thick_lag_bounded`:
  no thick set of levels and no density are required, and the readings may depend on the base.
-/

open Set MeasureTheory Filter

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- **Under RH every positive base has subexponential readings**: the lag is bounded. -/
theorem subexponentialLagBases_eq_Ioi_of_riemannHypothesis (hRH : RiemannHypothesis) :
    subexponentialLagBases = Ioi 0 := by
  ext ℓ
  refine ⟨fun h => h.1, fun hℓ => ⟨hℓ, fun a ha => ⟨max RHTower.poleSharpConstant 0, ?_⟩⟩⟩
  have hℓ' : (0 : ℝ) < ℓ := hℓ
  refine Filter.Eventually.frequently (Filter.Eventually.of_forall fun n => ?_)
  calc ‖RHTower.weilLagFunction ((n : ℝ) * ℓ)‖ ≤ RHTower.poleSharpConstant :=
        RHTower.norm_weilLagFunction_le_of_riemannHypothesis hRH _
    _ ≤ max RHTower.poleSharpConstant 0 := le_max_left _ _
    _ ≤ max RHTower.poleSharpConstant 0 * Real.exp (a * (n : ℝ) * ℓ) :=
        le_mul_of_one_le_right (le_max_right _ _) (Real.one_le_exp (by positivity))

/-- **A finite nonempty off-line layer is seen at almost every base.** The layer gives ZAL, so off
RH the abscissa law fails and the bases with subexponential readings form a null set. -/
theorem volume_subexponentialLagBases_eq_zero_of_finiteOffLine (hF : FiniteOffLine)
    (hRH : ¬ RiemannHypothesis) : volume subexponentialLagBases = 0 := by
  by_contra h
  exact hRH (riemannHypothesis_iff_zerosApproachLine_and_metric_lag_bound.mpr
    ⟨zerosApproachLine_of_finiteOffLine hF, pos_iff_ne_zero.mpr h⟩)

/-- **Metric zero–one law of the finite stratum**: the bases with subexponential lag readings are
all positive bases or a null set. -/
theorem subexponentialLagBases_zero_one_of_finiteOffLine (hF : FiniteOffLine) :
    subexponentialLagBases = Ioi 0 ∨ volume subexponentialLagBases = 0 := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl (subexponentialLagBases_eq_Ioi_of_riemannHypothesis hRH)
  · exact Or.inr (volume_subexponentialLagBases_eq_zero_of_finiteOffLine hF hRH)

/-- **B13 in metric form.** Finitely many off-line zeros force none iff, in the finite stratum, a
positive-measure set of bases has infinitely many subexponential lag readings. -/
theorem b13_iff_pos_volume_subexponentialLagBases :
    (FiniteOffLine → RiemannHypothesis) ↔ (FiniteOffLine → 0 < volume subexponentialLagBases) := by
  constructor
  · intro h hF
    exact (riemannHypothesis_iff_zerosApproachLine_and_metric_lag_bound.mp (h hF)).2
  · intro h hF
    exact riemannHypothesis_iff_zerosApproachLine_and_metric_lag_bound.mpr
      ⟨zerosApproachLine_of_finiteOffLine hF, h hF⟩

/-- **B13 in metric recurrence form.** Finitely many off-line zeros force none iff, in the finite
stratum, for every rate `a > 0` a positive-measure set of bases has infinitely many readings below
a multiple of `e^{a n ℓ}`; the sets may depend on the rate. -/
theorem b13_iff_pos_volume_lagRecurrenceBases :
    (FiniteOffLine → RiemannHypothesis) ↔
      (FiniteOffLine → ∀ a : ℝ, 0 < a → 0 < volume (lagRecurrenceBases a)) := by
  constructor
  · intro h hF
    exact (riemannHypothesis_iff_zerosApproachLine_and_metric_recurrence_at_each_rate.mp (h hF)).2
  · intro h hF
    exact riemannHypothesis_iff_zerosApproachLine_and_metric_recurrence_at_each_rate.mpr
      ⟨zerosApproachLine_of_finiteOffLine hF, h hF⟩

end GaloisForLFunctions.InfiniteRankWeilTheory
