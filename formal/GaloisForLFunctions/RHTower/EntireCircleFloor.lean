import GaloisForLFunctions.RHTower.EntireMinimumModulusAt

/-!
# A circle floor for a nonzero entire function

The minimum-modulus theorem produces a circle carrying a positive floor once the free scale parameter
beats the number of zeros in the surrounding disc.  That number is itself bounded a priori by the
Jensen count, so the parameter can be chosen in advance and the floor obtained on some circle inside
*any* prescribed nondegenerate annulus.

This is the minimum modulus in the form a separation argument consumes: a radius and a positive lower
bound, with no zero-counting left to the caller.
-/

open Metric

namespace RHTower

/-- **A nonzero entire function has a positive floor on some circle of any annulus.** -/
theorem exists_circle_floor_of_ne_zero {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) {c : ℂ} (hfc : f c ≠ 0)
    {A B : ℝ} (hA : 0 ≤ A) (hAB : A < B) :
    ∃ s ∈ Set.Icc A B, ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, ‖z - c‖ = s → ε ≤ ‖f z‖ := by
  have hB0 : 0 ≤ B := le_trans hA hAB.le
  set R : ℝ := B + 1 with hR
  set R' : ℝ := 2 * R + 1 with hR'
  have hR0 : 0 < R := by
    rw [hR]; linarith
  have h2R : 2 * R < R' := by
    rw [hR']; linarith
  have hBR : B < R := by
    rw [hR]; linarith
  -- a bound on the large closed ball
  obtain ⟨Mf, hMfb⟩ := (isCompact_closedBall c R').exists_bound_of_continuousOn
    (fun z _ => (hf z (Set.mem_univ z)).continuousAt.continuousWithinAt)
  have hcmem : c ∈ closedBall c R' := by
    simp only [mem_closedBall, dist_self]
    rw [hR']; linarith
  have hfcnorm : 0 < ‖f c‖ := norm_pos_iff.mpr hfc
  have hMf0 : 0 < Mf := lt_of_lt_of_le hfcnorm (hMfb c hcmem)
  have hMfsphere : ∀ z : ℂ, ‖z - c‖ = R' → ‖f z‖ ≤ Mf := by
    intro z hz
    refine hMfb z ?_
    simp only [mem_closedBall, Complex.dist_eq]
    exact le_of_eq hz
  -- nowhere locally zero
  have hnz : ∀ a ∈ (Set.univ : Set ℂ), ¬ ∀ᶠ z in nhds a, f z = 0 := by
    intro a _ hcon
    have hev : f =ᶠ[nhds a] 0 := by
      filter_upwards [hcon] with z hz
      exact hz
    have heq := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ a) hev
    exact hfc (heq (Set.mem_univ c))
  -- the a priori zero count
  have hlogpos : 0 < Real.log ((R' - R) / R) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hR0]
    rw [hR']
    linarith
  set N₀ : ℝ := Real.log (Mf / ‖f c‖) / Real.log ((R' - R) / R) with hN₀
  have hN₀0 : 0 ≤ N₀ := by
    rw [hN₀]
    refine div_nonneg ?_ hlogpos.le
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hfcnorm, one_mul]
    exact hMfb c hcmem
  set H : ℝ := (B - A) / (2 * (N₀ + 1)) with hH
  have hH0 : 0 < H := by
    rw [hH]
    refine div_pos (by linarith) (by linarith)
  obtain ⟨T, m, L, hL, hcount, hcircle⟩ :=
    exists_radius_norm_ge_of_analytic_at (f := f) (U := Set.univ) (c := c)
      (R := R) (R' := R') (Mf := Mf) (H := H) (A := A) (B := B)
      isOpen_univ hR0 h2R (Set.subset_univ _) hf hnz hMfsphere hH0 hB0 hBR
  have hNle : ((∑ a ∈ T, m a : ℕ) : ℝ) ≤ N₀ := by
    have hc := hcount hMf0 hfc
    rw [hN₀, le_div_iff₀ hlogpos]
    exact hc
  have hgap : 2 * ((∑ a ∈ T, m a : ℕ) : ℝ) * H < B - A := by
    have hstep : 2 * ((∑ a ∈ T, m a : ℕ) : ℝ) * H ≤ 2 * N₀ * H :=
      mul_le_mul_of_nonneg_right (by linarith) hH0.le
    have hval : 2 * N₀ * H = N₀ * (B - A) / (N₀ + 1) := by
      rw [hH]
      field_simp
    have hlt : N₀ * (B - A) / (N₀ + 1) < B - A := by
      rw [div_lt_iff₀ (by linarith)]
      nlinarith [hAB, hN₀0]
    linarith [hstep, hval, hlt]
  obtain ⟨s, hs, hfloor⟩ := hcircle hgap
  refine ⟨s, hs, H ^ (∑ a ∈ T, m a) * L, ?_, hfloor⟩
  positivity

end RHTower
