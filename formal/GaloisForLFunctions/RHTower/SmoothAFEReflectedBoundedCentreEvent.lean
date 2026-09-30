import GaloisForLFunctions.RHTower.SmoothAFEReflectedSmoothFirstMean

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace RHTower
open SteinhausModel

/-- The actual finite-node smooth backgrounds all have norm at most one. -/
def reflectedPrimalBoundedCentreEvent {J : ℕ} (d b : Fin J → ℝ)
    (tau r : ℝ) (N Y : ℕ) : Set Omega :=
  {ω | ∀ j, ‖steinhausSmoothCarrier
    (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N) N Y ω‖ ≤ 1}

theorem measurableSet_reflectedPrimalBoundedCentreEvent {J : ℕ} (d b : Fin J → ℝ)
    (tau r : ℝ) (N Y : ℕ) :
    MeasurableSet (reflectedPrimalBoundedCentreEvent d b tau r N Y) := by
  simp only [reflectedPrimalBoundedCentreEvent, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  apply measurableSet_le _ measurable_const
  exact (Finset.measurable_sum _ (fun n _ => measurable_const.mul (measurable_X n))).norm

/-- Centre selection reads only the same small-prime coordinates as the actual conditional covariance. -/
theorem reflectedPrimalBoundedCentreEvent_congr_smallPrimes {J : ℕ} (d b : Fin J → ℝ)
    (tau r : ℝ) (N Y : ℕ) {ω η : Omega}
    (h : ∀ p ∈ Nat.primesLE Y, ω p = η p) :
    ω ∈ reflectedPrimalBoundedCentreEvent d b tau r N Y ↔
      η ∈ reflectedPrimalBoundedCentreEvent d b tau r N Y := by
  have heq (j : Fin J) := steinhausSmoothCarrier_congr_of_eqOn_smallPrimes
    (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N) N Y h
  simp only [reflectedPrimalBoundedCentreEvent, Set.mem_setOf_eq, heq]

/-- The original probability cost of removing unbounded centres is controlled by the actual summed first mean. -/
theorem measureReal_reflectedPrimalBoundedCentreEvent_compl_le {J : ℕ} (d b : Fin J → ℝ)
    (tau r : ℝ) (N Y : ℕ) :
    steinhausMeasure.real (reflectedPrimalBoundedCentreEvent d b tau r N Y)ᶜ ≤
      ∫ ω, ∑ j, ‖steinhausSmoothCarrier
        (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N)
          N Y ω‖ ∂steinhausMeasure := by
  let f : Omega → ℝ := fun ω => ∑ j, ‖steinhausSmoothCarrier
    (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N) N Y ω‖
  have hf (ω : Omega) : 0 ≤ f ω := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hi : Integrable f steinhausMeasure :=
    integrable_finsetSum _ (fun j _ => integrable_norm_steinhausFiniteSum _ _)
  have hsub : (reflectedPrimalBoundedCentreEvent d b tau r N Y)ᶜ ⊆ {ω | 1 ≤ f ω} := by
    intro ω hω
    obtain ⟨j, hj⟩ : ∃ j, 1 < ‖steinhausSmoothCarrier
        (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N) N Y ω‖ := by
      simpa only [Set.mem_compl_iff, reflectedPrimalBoundedCentreEvent, Set.mem_setOf_eq,
        not_forall, not_le] using hω
    have hterm : ‖steinhausSmoothCarrier
        (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N) N Y ω‖ ≤ f ω := by
      exact Finset.single_le_sum
        (f := fun k : Fin J => ‖steinhausSmoothCarrier
          (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d k) (tau + b k) r N) N Y ω‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    exact hj.le.trans hterm
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hf) hi (1 : ℝ)
  exact (measureReal_mono hsub).trans (by simpa only [one_mul] using hmarkov)

/-- Every event of fixed positive original mass retains half that mass with all actual centres bounded. -/
theorem eventually_reflectedPrimalBoundedCentreEvent_inter_mass
    {J : ℕ} (d b : Fin J → ℝ) (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2)
    {m : ℝ} (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, (∀ j, (N : ℝ) ≤ tau + b j) →
      ∀ r : ℝ, 0 < r → ∀ Y : ℕ, ∀ E : Set Omega, m ≤ steinhausMeasure.real E →
        m / 2 ≤ steinhausMeasure.real
          (E ∩ reflectedPrimalBoundedCentreEvent d b tau r N Y) := by
  filter_upwards [eventually_integral_sum_norm_reflectedPrimalSmoothCarrier_le
    d b hd hdhalf (half_pos hm)] with N hN
  intro tau htau r hr Y E hE
  have hbad := (measureReal_reflectedPrimalBoundedCentreEvent_compl_le d b tau r N Y).trans
    (hN tau htau r hr Y)
  have hdiff := le_measureReal_sdiff (μ := steinhausMeasure) (s₁ := E)
    (s₂ := (reflectedPrimalBoundedCentreEvent d b tau r N Y)ᶜ)
  rw [Set.sdiff_compl] at hdiff
  linarith

end RHTower
