import GaloisForLFunctions.RHTower.Sieve.TwistedCellMeanSquare

/-!
# The second reciprocal energy

The Cauchy-weighted energy of a prime-supported Dirichlet polynomial against a bounded envelope is
bounded by a constant multiple of the envelope's bound times the Brun–Titchmarsh mean square, with
no dependence on the length of the range.  The reciprocal Cauchy weights at the centres of a tiling
by cells of half-width `ρ` sum to at most `2π/ρ` uniformly in the number of cells — each centre is
charged to the integral of the weight over its own cell — and the mean square is the same on every
cell, so the range cancels out entirely.
-/

namespace RHTower.Sieve

open MeasureTheory

noncomputable section

/-- Each cell centre is charged to the Cauchy integral over its own cell. -/
theorem inv_one_add_sq_centre_le_integral {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2) (c : ℝ) :
    (ρ / 2) / (1 + c ^ 2) ≤ ∫ t in (c - ρ)..(c + ρ), 1 / (1 + t ^ 2) := by
  have hc0 : (0 : ℝ) < 1 + c ^ 2 := by positivity
  have hle : c - ρ ≤ c + ρ := by linarith
  have hpt : ∀ t ∈ Set.Icc (c - ρ) (c + ρ),
      (1 / 4) * (1 / (1 + c ^ 2)) ≤ 1 / (1 + t ^ 2) := by
    intro t ht
    have habs : |c - t| ≤ 1 / 2 := by
      rw [abs_le]
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h := inv_one_add_sq_le_cell habs
    have ht0 : (0 : ℝ) < 1 + t ^ 2 := by positivity
    have hid : (4 : ℝ) / (1 + t ^ 2) = 4 * (1 / (1 + t ^ 2)) := by ring
    rw [hid] at h
    linarith
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hle
    (intervalIntegrable_const)
    ((continuous_const.div (by continuity) fun t => by positivity).intervalIntegrable _ _) hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  refine le_trans (le_of_eq ?_) hmono
  field_simp
  ring

/-- **The Cauchy weight summed over the cell centres.**  The bound does not depend on the number
of cells. -/
theorem sum_inv_one_add_sq_scaledCentre_le {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2) (N : ℕ) :
    ∑ k ∈ Finset.range (2 * N), 1 / (1 + (scaledCentre ρ N k) ^ 2)
      ≤ 2 * Real.pi / ρ := by
  classical
  set a : ℕ → ℝ := fun k => -2 * ρ * (N : ℝ) + 2 * ρ * (k : ℝ) with ha
  have hcell : ∀ k : ℕ, a k = scaledCentre ρ N k - ρ ∧ a (k + 1) = scaledCentre ρ N k + ρ := by
    intro k
    constructor
    · rw [ha, scaledCentre]; ring
    · rw [ha, scaledCentre]; push_cast; ring
  have hterm : ∀ k ∈ Finset.range (2 * N),
      1 / (1 + (scaledCentre ρ N k) ^ 2)
        ≤ (2 / ρ) * ∫ t in (a k)..(a (k + 1)), 1 / (1 + t ^ 2) := by
    intro k _
    obtain ⟨h1, h2⟩ := hcell k
    rw [h1, h2]
    have hbase := inv_one_add_sq_centre_le_integral hρ hρ2 (scaledCentre ρ N k)
    have hmul := mul_le_mul_of_nonneg_left hbase (show (0:ℝ) ≤ 2 / ρ by positivity)
    refine le_trans (le_of_eq ?_) hmul
    field_simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun t : ℝ => 1 / (1 + t ^ 2)) (μ := volume) (a := a) (n := 2 * N)
    (fun k _ => ((continuous_const.div (by continuity) fun t => by positivity)).intervalIntegrable
      (a k) (a (k + 1)))
  rw [hsum]
  have ha0 : a 0 = -2 * ρ * (N : ℝ) := by rw [ha]; norm_num
  have haN : a (2 * N) = 2 * ρ * (N : ℝ) := by rw [ha]; push_cast; ring
  rw [ha0, haN, integral_one_div_one_add_sq]
  have h1 := Real.arctan_lt_pi_div_two (2 * ρ * (N : ℝ))
  have h2 := Real.neg_pi_div_two_lt_arctan (-2 * ρ * (N : ℝ))
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hbound : Real.arctan (2 * ρ * (N : ℝ)) - Real.arctan (-2 * ρ * (N : ℝ)) ≤ Real.pi := by
    linarith
  have hcoef : (0 : ℝ) < 2 / ρ := by positivity
  calc (2 / ρ) * (Real.arctan (2 * ρ * (N : ℝ)) - Real.arctan (-2 * ρ * (N : ℝ)))
      ≤ (2 / ρ) * Real.pi := mul_le_mul_of_nonneg_left hbound hcoef.le
    _ = 2 * Real.pi / ρ := by ring

theorem pi_inv_le_half : 1 / Real.pi ≤ 1 / 2 := by
  have h := Real.pi_gt_three
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- **Lemma F, equation (F2).**  The second reciprocal energy: a Cauchy-weighted mean square of a
prime-supported Dirichlet polynomial against a bounded envelope, uniformly in the height. -/
theorem cauchy_energy_bt_le {T : ℝ} (hT : 0 ≤ T) (N : ℕ) (hN : T ≤ 2 * (1 / Real.pi) * (N : ℝ))
    {S : Finset ℕ} (hs : ∀ m ∈ S, Nat.Prime m) {a : ℕ → ℂ} (hbdd : ∀ n : ℕ, ‖a n‖ ≤ 1)
    {F : ℝ → ℝ} (hFc : Continuous F) (hFnn : ∀ t, 0 ≤ F t) {L : ℝ} (hL : ∀ t, F t ≤ L) :
    (∫ w in (-T)..T,
        ‖logPoly (fun p : ℕ => a p * ((Real.log (p : ℝ) : ℝ) : ℂ) / (p : ℂ)) S w‖ ^ 2
          * F w / (1 + w ^ 2))
      ≤ 8 * Real.pi ^ 2 * L
          * (4500 * ∑ p ∈ S, ‖a p‖ ^ 2 * Real.log p / (p : ℝ) + 16 / Real.pi) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set ρ : ℝ := 1 / Real.pi with hρdef
  have hρ : (0 : ℝ) < ρ := by rw [hρdef]; positivity
  have hρ2 : ρ ≤ 1 / 2 := pi_inv_le_half
  set b : ℕ → ℂ := fun p : ℕ => a p * ((Real.log (p : ℝ) : ℝ) : ℂ) / (p : ℂ) with hb
  set Eval : ℝ := 4500 * ∑ p ∈ S, ‖a p‖ ^ 2 * Real.log p / (p : ℝ) + 16 / Real.pi with hEval
  have hL0 : 0 ≤ L := le_trans (hFnn 0) (hL 0)
  have hE0 : 0 ≤ Eval := by
    rw [hEval]
    have hsum : 0 ≤ ∑ p ∈ S, ‖a p‖ ^ 2 * Real.log p / (p : ℝ) := by
      refine Finset.sum_nonneg fun p hp => ?_
      have hp2 : 2 ≤ p := (hs p hp).two_le
      have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
      positivity
    have : (0 : ℝ) ≤ 16 / Real.pi := by positivity
    linarith
  have hBc : Continuous fun w : ℝ => ‖logPoly b S w‖ ^ 2 := continuous_normSq_logPoly b S
  have hBnn : ∀ w : ℝ, 0 ≤ ‖logPoly b S w‖ ^ 2 := fun w => by positivity
  have hmain := cell_energy_scaled_le (T := T) (ρ := ρ) hT hρ hρ2 N hN hBc hFc hBnn hFnn
    (fun _ => L) (fun _ => Eval)
    (fun k t _ => hL t)
    (fun k => by
      rw [hb]
      exact integral_cell_normSq_logPoly_bt_le hs hbdd (scaledCentre ρ N k))
  refine hmain.trans ?_
  have hterm : ∀ k ∈ Finset.range (2 * N),
      4 * L * Eval / (1 + (scaledCentre ρ N k) ^ 2)
        = (4 * L * Eval) * (1 / (1 + (scaledCentre ρ N k) ^ 2)) := by
    intro k _
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hcentres := sum_inv_one_add_sq_scaledCentre_le hρ hρ2 N
  have hcoef : (0 : ℝ) ≤ 4 * L * Eval := by positivity
  refine (mul_le_mul_of_nonneg_left hcentres hcoef).trans (le_of_eq ?_)
  rw [hρdef]
  field_simp
  ring

end

end RHTower.Sieve
