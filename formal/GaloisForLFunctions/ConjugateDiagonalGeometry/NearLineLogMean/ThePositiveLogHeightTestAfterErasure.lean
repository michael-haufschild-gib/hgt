import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.ThePureMoebiusEnergyOnASlowlyExpandingWindow
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.AFixedPositiveWindowOfLargeMoebiusReadings

/-!
# The log-height Möbius test survives bounded loss of observation time

Cofinal small readings may use different cutoffs and exclude different
measurable sets of times for each exponent. A uniform bound on the total
deleted length already forces the true zero width. All readings above
use the original positive interval [1,H].
-/
noncomputable section
open Complex Filter MeasureTheory Set Topology
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
open MultiscaleMollifiedZetaField
open SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg zetaZeroWidth_le_iff_xiZeroHalfPlaneBound)

private theorem retained_le_symmetric (N : ℕ) {H : ℝ} (hH : 1≤H) (D : Set ℝ) :
    retainedMoebiusEnergy N H D ≤ symmetricMoebiusEnergy N H := by
  have hc : Continuous fun t => ‖moebiusPoly N (linePoint t)‖^2 :=
    ((differentiable_moebiusPoly N).continuous.comp (by unfold linePoint; fun_prop)).norm.pow 2
  apply setIntegral_mono_set (μ := volume) (s := Icc 1 H \ D) (t := Icc (-H) H)
    hc.integrableOn_Icc (.of_forall fun _ => sq_nonneg _)
  exact Eventually.of_forall fun u hu =>
    ⟨(by linarith only [hH] : -H≤1).trans hu.1.1,hu.1.2⟩

/-- For a subpower expanding positive-height schedule, adaptive losses
of any fixed amount of observing time preserve the exact width
criterion. The bound on the removed length is allowed to depend on
the claimed width and is fixed before choosing the accuracy. -/
theorem width_iff_sparse_retained_moebius_energy {H : ℕ → ℝ}
    (hH : Tendsto H atTop atTop)
    (hs : ∀ a : ℝ, 0<a → ∀ᶠ N : ℕ in atTop, 1+H N≤(N:ℝ)^a) {β : ℝ} (hb : 0≤β) :
    zetaZeroWidth ≤ β ↔ ∃ d : ℝ, 0≤d ∧ ∀ e : ℝ, 0<e → ∃ᶠ N : ℕ in atTop,
      ∃ D : Set ℝ, MeasurableSet D ∧ volume D≤ENNReal.ofReal d ∧
        retainedMoebiusEnergy N (H N) D ≤ (N:ℝ)^(2*(β+e)) := by
  constructor
  · intro hw
    refine ⟨0,le_rfl,fun e he => ?_⟩
    apply Eventually.frequently
    filter_upwards [expanding_window_upper hH hs hw he,hH.eventually_ge_atTop 1] with N hu hpos
    exact ⟨∅,MeasurableSet.empty,by simp,(retained_le_symmetric N hpos ∅).trans hu⟩
  · rintro ⟨d,hd,hm⟩
    by_contra! hw
    obtain ⟨b,hl,hh⟩ := exists_between hw
    obtain ⟨γ,_,hbar⟩ := positive_moebius_energy_after_erasure (hb.trans hl.le) hh hd
    let e := (b-β)/2
    have he : 0<e := half_pos (sub_pos.mpr hl)
    obtain ⟨N,⟨D,hmD,hD,hread⟩,hpaid,ht,hn⟩ :=
      ((hm e he).and_eventually (hbar.and ((hH.eventually_ge_atTop (γ+(d+2))).and
        (eventually_ge_atTop 2)))).exists
    have hcross := (hpaid _ ht D hmD hD).trans hread
    have hx : 1<(N:ℝ) := by exact_mod_cast (by omega : 1<N)
    have hlt := Real.rpow_lt_rpow_of_exponent_lt hx (show 2*(β+e)<2*b by dsimp only [e]; linarith only [hl])
    exact hlt.not_ge hcross

/-- At the single prescribed height log N, even the existence of
bounded-measure deletions producing cofinally subpower pure moments is
equivalent to RH. -/
theorem rh_iff_erased_positive_log_height :
    RiemannHypothesis ↔ ∃ d : ℝ, 0≤d ∧ ∀ e : ℝ, 0<e → ∃ᶠ N : ℕ in atTop,
      ∃ D : Set ℝ, MeasurableSet D ∧ volume D≤ENNReal.ofReal d ∧
        retainedMoebiusEnergy N (Real.log (N:ℝ)) D ≤ (N:ℝ)^(2*e) := by
  rw [_root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero,
    ←zetaZeroWidth_le_iff_xiZeroHalfPlaneBound le_rfl]
  simpa only [zero_add, Function.comp_apply] using (width_iff_sparse_retained_moebius_energy
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
    (fun _ ha => log_height_subpower ha) (β:=0) le_rfl)

#print axioms rh_iff_erased_positive_log_height
#print axioms width_iff_sparse_retained_moebius_energy
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
