import GaloisForLFunctions.RHTower.SmoothAFEReflectedWindowFirstMean

open MeasureTheory Filter Finset
open scoped Topology
noncomputable section
namespace RHTower
open SteinhausModel

/-- The literal retained-prime background with independent smoothing and polynomial scales. -/
def reflectedPrimalRetainedBackground (d tau : ℝ) (N L : ℕ) (S : Finset ℕ) (ω : Omega) : ℂ :=
  ∑ n ∈ Sieve.smoothUpTo S L,
    smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau 1 N n * X n ω

/-- Every finite-node retained background has norm at most one. -/
def reflectedPrimalWindowBoundedCentreEvent {J : ℕ} (d b : Fin J → ℝ)
    (tau : ℝ) (N L : ℕ) (S : Finset ℕ) : Set Omega :=
  {ω | ∀ j, ‖reflectedPrimalRetainedBackground (d j) (tau + b j) N L S ω‖ ≤ 1}

theorem measurableSet_reflectedPrimalWindowBoundedCentreEvent {J : ℕ} (d b : Fin J → ℝ)
    (tau : ℝ) (N L : ℕ) (S : Finset ℕ) :
    MeasurableSet (reflectedPrimalWindowBoundedCentreEvent d b tau N L S) := by
  simp only [reflectedPrimalWindowBoundedCentreEvent, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  apply measurableSet_le _ measurable_const
  exact (Finset.measurable_sum _ (fun n _ => measurable_const.mul (measurable_X n))).norm

/-- Retained-centre selection depends only on the retained coordinates, even above smoothing N. -/
theorem reflectedPrimalWindowBoundedCentreEvent_congr_retained {J : ℕ} (d b : Fin J → ℝ)
    (tau : ℝ) (N L : ℕ) (S : Finset ℕ) {ω η : Omega}
    (h : ∀ p ∈ S, ω p = η p) :
    ω ∈ reflectedPrimalWindowBoundedCentreEvent d b tau N L S ↔
      η ∈ reflectedPrimalWindowBoundedCentreEvent d b tau N L S := by
  have heq (j : Fin J) : reflectedPrimalRetainedBackground (d j) (tau + b j) N L S ω =
      reflectedPrimalRetainedBackground (d j) (tau + b j) N L S η := by
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    apply X_congr_of_eqOn_primeFactors
    intro p hp
    exact h p ((Sieve.mem_smoothUpTo.mp hn).2 hp)
  simp only [reflectedPrimalWindowBoundedCentreEvent, Set.mem_setOf_eq, heq]

/-- Removing unbounded retained centres costs at most their summed first mean. -/
theorem measureReal_reflectedPrimalWindowBoundedCentreEvent_compl_le {J : ℕ} (d b : Fin J → ℝ)
    (tau : ℝ) (N L : ℕ) (S : Finset ℕ) :
    steinhausMeasure.real (reflectedPrimalWindowBoundedCentreEvent d b tau N L S)ᶜ ≤
      ∫ ω, ∑ j, ‖reflectedPrimalRetainedBackground (d j) (tau + b j) N L S ω‖ ∂steinhausMeasure := by
  let f : Omega → ℝ := fun ω => ∑ j, ‖reflectedPrimalRetainedBackground (d j) (tau + b j) N L S ω‖
  have hf (ω : Omega) : 0 ≤ f ω := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hi : Integrable f steinhausMeasure :=
    integrable_finsetSum _ (fun j _ => integrable_norm_steinhausFiniteSum _ _)
  have hsub : (reflectedPrimalWindowBoundedCentreEvent d b tau N L S)ᶜ ⊆ {ω | 1 ≤ f ω} := by
    intro ω hω
    obtain ⟨j, hj⟩ : ∃ j, 1 < ‖reflectedPrimalRetainedBackground (d j) (tau + b j) N L S ω‖ := by
      simpa only [Set.mem_compl_iff, reflectedPrimalWindowBoundedCentreEvent, Set.mem_setOf_eq,
        not_forall, not_le] using hω
    have hterm : ‖reflectedPrimalRetainedBackground (d j) (tau + b j) N L S ω‖ ≤ f ω :=
      Finset.single_le_sum
        (f := fun k : Fin J => ‖reflectedPrimalRetainedBackground (d k) (tau + b k) N L S ω‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    exact hj.le.trans hterm
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hf) hi (1 : ℝ)
  exact (measureReal_mono hsub).trans (by simpa only [one_mul] using hmarkov)

/-- Finite-node retained backgrounds vanish in summed first mean uniformly in both choices
of polynomial length and retained prime set. -/
theorem eventually_integral_sum_norm_reflectedPrimalRetainedBackground_le
    {J : ℕ} (d b : Fin J → ℝ) (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, ∀ S : Finset ℕ, ∀ tau : ℝ,
      (∀ j, (N : ℝ) ≤ tau + b j) →
      (∫ ω, ∑ j, ‖reflectedPrimalRetainedBackground (d j) (tau + b j) N L S ω‖ ∂steinhausMeasure) ≤ ε := by
  have hε' : 0 < ε / (J + 1 : ℝ) := div_pos hε (by positivity)
  have hall : ∀ᶠ N : ℕ in atTop, ∀ j : Fin J, ∀ L : ℕ, ∀ S : Finset ℕ,
      ∀ tau : ℝ, (N : ℝ) ≤ tau →
      (∫ ω, ‖reflectedPrimalRetainedBackground (d j) tau N L S ω‖ ∂steinhausMeasure) ≤
        ε / (J + 1 : ℝ) :=
    Filter.eventually_all.mpr (fun j =>
      eventually_integral_norm_reflectedPrimalWindowSmooth_le (hd j) (hdhalf j) hε')
  filter_upwards [hall] with N hN
  intro L S tau htau
  have hint (j : Fin J) : Integrable
      (fun ω => ‖reflectedPrimalRetainedBackground (d j) (tau + b j) N L S ω‖) steinhausMeasure :=
    integrable_norm_steinhausFiniteSum _ _
  rw [integral_finsetSum _ (fun j _ => hint j)]
  calc
    _ ≤ ∑ _j : Fin J, ε / (J + 1 : ℝ) := Finset.sum_le_sum (fun j _ => hN j L S _ (htau j))
    _ = (J : ℝ) * (ε / (J + 1 : ℝ)) := by simp
    _ ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < J + 1)]
      nlinarith [Nat.cast_nonneg (α := ℝ) J]

/-- Every fixed-mass event retains half its original mass with all actual retained centres bounded. -/
theorem eventually_reflectedPrimalWindowBoundedCentreEvent_inter_mass
    {J : ℕ} (d b : Fin J → ℝ) (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2)
    {m : ℝ} (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, ∀ S : Finset ℕ, ∀ tau : ℝ,
      (∀ j, (N : ℝ) ≤ tau + b j) → ∀ E : Set Omega, m ≤ steinhausMeasure.real E →
        m / 2 ≤ steinhausMeasure.real
          (E ∩ reflectedPrimalWindowBoundedCentreEvent d b tau N L S) := by
  filter_upwards [eventually_integral_sum_norm_reflectedPrimalRetainedBackground_le
    d b hd hdhalf (half_pos hm)] with N hN
  intro L S tau htau E hE
  have hbad := (measureReal_reflectedPrimalWindowBoundedCentreEvent_compl_le d b tau N L S).trans
    (hN L S tau htau)
  have hdiff := le_measureReal_sdiff (μ := steinhausMeasure) (s₁ := E)
    (s₂ := (reflectedPrimalWindowBoundedCentreEvent d b tau N L S)ᶜ)
  rw [Set.sdiff_compl] at hdiff
  linarith

end RHTower
