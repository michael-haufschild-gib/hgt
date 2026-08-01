import GaloisForLFunctions.RHTower.SoninCouplingEnergyGrowth
import GaloisForLFunctions.RHTower.SoninBurnolApertureCancellation

/-!
# The scalar Burnol counterterm cannot restore the floor

The Burnol aperture counterterm is the logarithm of the aperture ratio: one fixed real number,
independent of the prime and of the dilation scale.  Contributed once per scale of a source packet
it is a bounded completion, and the coupling energy is unbounded, so the completed channel is still
unbounded below — at every strict aperture flag, not only on short ones.

More generally a completion that restores the floor must itself tend to infinity along the scales:
it has to track an energy that grows without bound.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology

/-- **A completion with a floor must diverge.**  If the coupling energy grows without bound, any
per-scale contribution restoring the floor tends to infinity along the scales. -/
theorem tendsto_atTop_of_bddBelow_soninCompletedPacketValueVar
    {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (p : ℕ → ℝ) (hp : ∀ i, 1 < p i) (hcp : ∀ i, c < p i * a) (κ : ℕ → ℝ)
    (henergy : Tendsto (fun i => hsNormSq
      (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i))) atTop atTop)
    (hfloor : ∃ M : ℝ, ∀ s : Finset ℕ, M ≤ soninCompletedPacketValueVar s a b c p hp κ) :
    Tendsto κ atTop atTop := by
  have hzero := tendsto_min_sub_hsNormSq_of_bddBelow ha hab hbc p hp hcp κ hfloor
  refine tendsto_atTop.mpr fun M => ?_
  have h1 : ∀ᶠ i in atTop, (-1 : ℝ) < min (κ i - hsNormSq
      (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i))) 0 :=
    hzero.eventually_const_lt (by norm_num)
  have h2 : ∀ᶠ i in atTop, M + 1 ≤ hsNormSq
      (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i)) :=
    henergy.eventually_ge_atTop (M + 1)
  filter_upwards [h1, h2] with i hi1 hi2
  have hmin := min_le_left (κ i - hsNormSq
    (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i))) 0
  linarith

/-- **The Burnol counterterm leaves the channel unbounded below.**  Contributing the aperture
logarithm once per scale is a bounded completion, so it cannot restore the floor at any strict
flag. -/
theorem not_bddBelow_soninCompletedPacketValueVar_burnolCounterterm
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) :
    ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ soninCompletedPacketValueVar s a b c (soninCrossingClock a c)
          (one_lt_soninCrossingClock a c) (fun _ => Real.log (b / a)) :=
  not_bddBelow_soninCompletedPacketValueVar_of_bddAbove a b c ha hb hab hbc q haq hqb
    (fun _ => Real.log (b / a)) (Real.log (b / a)) (fun _ => le_rfl)

/-- The scalar Burnol counterterm is the real part of the corpus counterterm. -/
theorem re_soninBurnolApertureCounterterm (a b : ℝ) :
    (soninBurnolApertureCounterterm a b).re = Real.log (b / a) := rfl

/-- **No prime-independent scalar completion works.**  Any completion contributing one fixed real
number per scale leaves the channel unbounded below. -/
theorem not_bddBelow_soninCompletedPacketValueVar_const
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) (κ₀ : ℝ) :
    ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ soninCompletedPacketValueVar s a b c (soninCrossingClock a c)
          (one_lt_soninCrossingClock a c) (fun _ => κ₀) :=
  not_bddBelow_soninCompletedPacketValueVar_of_bddAbove a b c ha hb hab hbc q haq hqb
    (fun _ => κ₀) κ₀ (fun _ => le_rfl)

end RHTower
