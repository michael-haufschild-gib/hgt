import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints.SectorPressure

/-! # The differentiability boundary of fixed-count prime pressure -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints

open Filter Topology Set

/-- The limiting pressure is the larger of the two endpoint exponents. -/
theorem pressure_eq_max {c d : ℝ} (hcd : c ≤ d) (k : ℕ) (s : ℝ) :
    pressure c d k s = max ((1-s)*(k*c)) ((1-s)*(k*d)) := by
  have h := mul_le_mul_of_nonneg_left hcd (Nat.cast_nonneg k : (0:ℝ) ≤ k)
  by_cases hs : s ≤ 1
  · rw [pressure,if_pos hs,max_eq_right (mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hs))]
  · rw [pressure,if_neg hs,max_eq_left (mul_le_mul_of_nonpos_left h (sub_nonpos.mpr (le_of_not_ge hs)))]

private theorem pressure_right {s : ℝ} (hs : 1 ≤ s) (c d : ℝ) (k : ℕ) :
    pressure c d k s = (1-s)*(k*c) := by
  rcases eq_or_lt_of_le hs with h | h
  · subst s
    simp [pressure]
  · exact if_neg h.not_ge

private theorem pressure_line (s a : ℝ) : HasDerivAt (fun x : ℝ => (1-x)*a) (-a) s := by
  apply (((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).mul_const a).congr_deriv
  ring

/-- At the transition, the one-sided pressure slopes equal the negatives of the two endpoint total energies. -/
theorem pressure_slopes (c d : ℝ) (k : ℕ) :
    HasDerivWithinAt (pressure c d k) (-(k*d)) (Iic 1) 1 ∧ HasDerivWithinAt (pressure c d k) (-(k*c)) (Ici 1) 1 := by
  constructor
  · exact (pressure_line 1 (k*d)).hasDerivWithinAt.congr (fun z hz => if_pos (show z ≤ 1 from hz)) (if_pos le_rfl)
  · exact (pressure_line 1 (k*c)).hasDerivWithinAt.congr (fun _ hz => pressure_right hz c d k) (pressure_right le_rfl c d k)

/-- The derivative jump counts the selected modes in units of the band's energy width. -/
theorem pressure_derivative_jump (c d : ℝ) (k : ℕ) :
    derivWithin (pressure c d k) (Ici 1) 1 - derivWithin (pressure c d k) (Iic 1) 1 = k*(d-c) := by
  rw [(pressure_slopes c d k).2.derivWithin (uniqueDiffWithinAt_Ici 1),
    (pressure_slopes c d k).1.derivWithin (uniqueDiffWithinAt_Iic 1)]
  ring

theorem pressure_corner_iff {c d : ℝ} (hcd : c < d) {k : ℕ} (hk : 0 < k) (s : ℝ) :
    ¬ DifferentiableAt ℝ (pressure c d k) s ↔ s = 1 := by
  constructor
  · intro hn
    rcases lt_trichotomy s 1 with h | h | h
    · apply False.elim ∘ hn
      have H : HasDerivAt (pressure c d k) (-(k*d)) s := (pressure_line s (k*d)).congr_of_eventuallyEq (by
        filter_upwards [Iio_mem_nhds h] with z hz
        exact if_pos (show z < 1 from hz).le)
      exact H.differentiableAt
    · exact h
    · apply False.elim ∘ hn
      have H : HasDerivAt (pressure c d k) (-(k*c)) s := (pressure_line s (k*c)).congr_of_eventuallyEq (by
        filter_upwards [Ioi_mem_nhds h] with z hz
        exact pressure_right (show 1 < z from hz).le c d k)
      exact H.differentiableAt
  · rintro rfl H
    have hl := (pressure_slopes c d k).1.derivWithin (uniqueDiffWithinAt_Iic 1)
    have hr := (pressure_slopes c d k).2.derivWithin (uniqueDiffWithinAt_Ici 1)
    have hgl := H.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic 1)
    have hgr := H.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 1)
    have hgap := mul_lt_mul_of_pos_left hcd (Nat.cast_pos.mpr hk : 0 < (k:ℝ))
    linarith only [hl,hr,hgl,hgr,hgap]

/-- The fixed-count pressure fails to be differentiable exactly at isometric composition. -/
theorem split_isometric_iff_pressure_corner {c d : ℝ} (hc : 0 < c) (hcd : c < d) {k : ℕ} (hk : 0 < k) (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      ∃ P : ℝ → ℝ, (∀ β, Tendsto (fun h : Ioi (0:ℝ) => h.val * Real.log (coefficient (added c d h) β k))
        criticalApproach (𝓝 (P β))) ∧ ¬ DifferentiableAt ℝ P (2*s.re) := by
  letI : NeBot criticalApproach := criticalApproach_neBot
  rw [split_isometric_iff]
  constructor
  · intro hs
    refine ⟨pressure c d k,fun β => pressure_limit hc hcd β hk,(pressure_corner_iff hcd hk _).mpr ?_⟩
    rw [hs]
    ring
  · rintro ⟨P,hP,hnd⟩
    have he : P = pressure c d k := funext fun β => tendsto_nhds_unique (hP β) (pressure_limit hc hcd β hk)
    rw [he,pressure_corner_iff hcd hk] at hnd
    linarith only [hnd]

#print axioms pressure_eq_max
#print axioms pressure_derivative_jump
#print axioms pressure_slopes
#print axioms pressure_corner_iff
#print axioms split_isometric_iff_pressure_corner

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints
