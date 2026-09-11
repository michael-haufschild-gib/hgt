import GaloisForLFunctions.HTGeometry.SelfConsistentExtremalSpectralMixing
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Time-varying self-consistent transfer and vanishing refresh

The asymmetric contraction mechanism emphasized in arXiv:2609.10119 propagates
through arbitrary coupling schedules by a product bound in the finite-group
model. The explicit harmonic schedule has refresh fraction 1/(n+2), giving
convergence at rate 1/(n+1) without a uniform contraction factor below one.
Entropy and all Lotz-type spectral-tail statistics retain their monotonicity.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators NNReal
open Filter
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- A prescribed coupling schedule drives the state-dependent convolution at each step. -/
def selfConsistentScheduledOrbit (r : ℕ → ℝ) (p : FiniteProbabilityLaw G) : ℕ → FiniteProbabilityLaw G
  | 0 => p
  | n+1 => selfConsistentRefreshAt (r n) (selfConsistentScheduledOrbit r p n)

/-- The asymmetric core estimate propagates by a product, with no uniform coupling bound. -/
theorem selfConsistentScheduledOrbit_bound (r : ℕ → ℝ) (p : FiniteProbabilityLaw G) (n : ℕ) :
    refreshDistance (selfConsistentScheduledOrbit r p n) (uniformNoiseLaw (ι := G)) ≤
      (∏ k ∈ Finset.range n, refreshRate (r k))*refreshDistance p (uniformNoiseLaw (ι := G)) := by
  induction n with
  | zero => simp [selfConsistentScheduledOrbit]
  | succ n ih =>
    change refreshDistance (selfConsistentRefreshAt (r n) _) _ ≤ _
    apply (selfConsistentRefreshAt_core_bound (r n) _).trans
    rw [Finset.prod_range_succ]
    calc
      refreshRate (r n)*refreshDistance (selfConsistentScheduledOrbit r p n) (uniformNoiseLaw (ι := G)) ≤
          refreshRate (r n)*((∏ k ∈ Finset.range n, refreshRate (r k))*
            refreshDistance p (uniformNoiseLaw (ι := G))) :=
        mul_le_mul_of_nonneg_left ih (refreshRate_pos _).le
      _ = _ := by ring

theorem selfConsistentScheduledOrbit_entropy (r : ℕ → ℝ) (p : FiniteProbabilityLaw G) :
    Monotone (fun n => entropy (selfConsistentScheduledOrbit r p n).prob) := by
  apply monotone_nat_of_le_succ
  intro n
  exact selfConsistentRefreshAt_entropy (r n) _

/-- All spectral-tail tests remain monotone for arbitrary time-varying coupling. -/
theorem selfConsistentScheduledOrbit_spectral (r : ℕ → ℝ) (p : FiniteProbabilityLaw G)
    (a : ℝ) (c : Fin (Fintype.card G+1) → ℝ≥0) :
    Antitone (fun n => lotzSpectralStatistic a c (indexedGroupLaw (selfConsistentScheduledOrbit r p n))) := by
  apply antitone_nat_of_succ_le
  intro n
  exact selfConsistentRefreshAt_spectral (r n) _ a c

/-- Coupling tending to one, with a vanishing but nonsummable refresh fraction. -/
def harmonicRefreshSchedule (n : ℕ) : ℝ := -Real.log (n+1)

theorem harmonicRefreshSchedule_rate (n : ℕ) :
    refreshRate (harmonicRefreshSchedule n) = (n+1 : ℝ)/(n+2) := by
  have hp : (0 : ℝ) < n+1 := by positivity
  simp only [refreshRate, harmonicRefreshSchedule, Real.exp_neg, Real.exp_log hp]
  field_simp
  ring

theorem harmonicRefreshSchedule_product (n : ℕ) :
    (∏ k ∈ Finset.range n, refreshRate (harmonicRefreshSchedule k)) = 1/(n+1 : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, harmonicRefreshSchedule_rate]
    push_cast
    have h1 : (n+1 : ℝ) ≠ 0 := by positivity
    have h2 : (n+2 : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- This nonlinear, nonuniformly contracting schedule still has an explicit harmonic rate. -/
theorem harmonicRefreshSchedule_orbit_bound (p : FiniteProbabilityLaw G) (n : ℕ) :
    refreshDistance (selfConsistentScheduledOrbit harmonicRefreshSchedule p n) (uniformNoiseLaw (ι := G)) ≤
      refreshDistance p (uniformNoiseLaw (ι := G))/(n+1 : ℝ) := by
  have h := selfConsistentScheduledOrbit_bound harmonicRefreshSchedule p n
  rw [harmonicRefreshSchedule_product] at h
  simpa [div_eq_mul_inv, mul_comm] using h

theorem harmonicRefreshSchedule_orbit_tendsto (p : FiniteProbabilityLaw G) :
    Tendsto (fun n => refreshDistance (selfConsistentScheduledOrbit harmonicRefreshSchedule p n)
      (uniformNoiseLaw (ι := G))) atTop (nhds 0) := by
  have hlim : Tendsto (fun n : ℕ => refreshDistance p (uniformNoiseLaw (ι := G))/(n+1 : ℝ))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (refreshDistance p (uniformNoiseLaw (ι := G)))
  exact squeeze_zero (fun n => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (harmonicRefreshSchedule_orbit_bound p) hlim

end GaloisForLFunctions.HTGeometry
