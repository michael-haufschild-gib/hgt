import GaloisForLFunctions.HTGeometry.BohrParseval
import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewRecurrence

/-!
# Bohr almost periodicity of summable-spectrum screw series

Every screw series with nonnegative summable weights is Bohr almost periodic.  The proof is
independent of relations among the frequencies: finite truncations are finite sums of periodic
functions, while the reciprocal-weight tail is uniformly small on the whole real line.

This is the uniform-dynamical companion to the exact relation-hull recurrence theorem in
`SummableSpectrumScrewRecurrence`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

noncomputable section

variable {I : Type*} {a omega : I → ℝ}

/-- The defining family of a nonnegative summable screw series is summable pointwise. -/
theorem summable_screwSeries_term
    (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a) (t : ℝ) :
    Summable (fun i => a i * (1 - Real.cos (omega i * t))) := by
  apply Summable.of_nonneg_of_le
  · intro i
    exact mul_nonneg (hpos i) (sub_nonneg.mpr (Real.cos_le_one _))
  · intro i
    calc
      a i * (1 - Real.cos (omega i * t)) ≤ a i * 2 :=
        mul_le_mul_of_nonneg_left
          (by linarith [Real.neg_one_le_cos (omega i * t)]) (hpos i)
      _ = 2 * a i := by ring
  · exact hsum.mul_left 2

private theorem screwSeriesTerm_isBohrAlmostPeriodic (i : I) :
    IsBohrAlmostPeriodic (fun t : ℝ => a i * (1 - Real.cos (omega i * t))) := by
  rcases lt_trichotomy (omega i) 0 with hw | hw | hw
  · have hwne : omega i ≠ 0 := ne_of_lt hw
    have hterm : Function.Periodic
        (fun t : ℝ => a i * (1 - Real.cos (omega i * t)))
        (-(2 * Real.pi / omega i)) := by
      intro t
      dsimp only
      have harg : omega i * (t + -(2 * Real.pi / omega i)) =
          omega i * t - 2 * Real.pi := by
        field_simp [hwne] <;> ring
      rw [harg, Real.cos_periodic.sub_eq]
    have hpneg : 2 * Real.pi / omega i < 0 :=
      div_neg_of_pos_of_neg (mul_pos (by norm_num) Real.pi_pos) hw
    exact isBohrAlmostPeriodic_of_periodic (by linarith) hterm
  · rw [hw]
    simpa using isBohrAlmostPeriodic_const (0 : ℝ)
  · have hwne : omega i ≠ 0 := ne_of_gt hw
    have hterm : Function.Periodic
        (fun t : ℝ => a i * (1 - Real.cos (omega i * t)))
        (2 * Real.pi / omega i) := by
      intro t
      dsimp only
      have harg : omega i * (t + 2 * Real.pi / omega i) =
          omega i * t + 2 * Real.pi := by
        field_simp [hwne]
      rw [harg, Real.cos_periodic]
    exact isBohrAlmostPeriodic_of_periodic (by positivity) hterm

private theorem finiteScrewSeries_isBohrAlmostPeriodic (S : Finset I) :
    IsBohrAlmostPeriodic
      (fun t : ℝ => ∑ i ∈ S, a i * (1 - Real.cos (omega i * t))) := by
  classical
  induction S using Finset.induction with
  | empty => simpa using isBohrAlmostPeriodic_const (0 : ℝ)
  | @insert i S hi ih =>
      have h := isBohrAlmostPeriodic_add
        (f := fun t : ℝ => a i * (1 - Real.cos (omega i * t)))
        (g := fun t : ℝ => ∑ j ∈ S, a j * (1 - Real.cos (omega j * t)))
        (by fun_prop) (screwSeriesTerm_isBohrAlmostPeriodic i)
        (continuous_finsetSum S (fun _ _ => by fun_prop)) ih
      simpa only [Finset.sum_insert hi] using h

/-- A screw series with nonnegative summable weights is Bohr almost periodic.  No countability,
frequency-independence, or nonzero-frequency hypothesis is required. -/
theorem isBohrAlmostPeriodic_screwSeries
    (hpos : ∀ i, 0 ≤ a i) (hsum : Summable a) :
    IsBohrAlmostPeriodic (screwSeries a omega) := by
  classical
  apply isBohrAlmostPeriodic_of_uniform_approx
  intro ε hε
  let term : I → ℝ → ℝ := fun i t => a i * (1 - Real.cos (omega i * t))
  have hterm : ∀ i t, ‖term i t‖ ≤ 2 * a i := by
    intro i t
    have hnonneg : 0 ≤ term i t :=
      mul_nonneg (hpos i) (sub_nonneg.mpr (Real.cos_le_one _))
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    dsimp only [term]
    calc
      a i * (1 - Real.cos (omega i * t)) ≤ a i * 2 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.neg_one_le_cos (omega i * t)]) (hpos i)
      _ = 2 * a i := by ring
  have huniform : TendstoUniformly
      (fun S : Finset I => fun t : ℝ => ∑ i ∈ S, term i t)
      (screwSeries a omega) atTop := by
    change TendstoUniformly
      (fun S : Finset I => fun t : ℝ => ∑ i ∈ S, term i t)
      (fun t : ℝ => ∑' i, term i t) atTop
    exact tendstoUniformly_tsum (hsum.mul_left 2) hterm
  have hevent := (Metric.tendstoUniformly_iff.mp huniform) ε hε
  rw [eventually_atTop] at hevent
  obtain ⟨S, hS⟩ := hevent
  refine ⟨(fun t : ℝ => ∑ i ∈ S, term i t), ?_, ?_⟩
  · simpa only [term] using finiteScrewSeries_isBohrAlmostPeriodic (a := a) (omega := omega) S
  · intro t
    have ht := hS S (le_refl S) t
    simpa only [Real.dist_eq, Real.norm_eq_abs, term] using ht.le

end

end GaloisForLFunctions.HTGeometry
