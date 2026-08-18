import GaloisForLFunctions.RHTower.Sieve.AnnulusRelBound

/-!
# The annulus bound, uniformly over the ladder and the frequency range

On the annulus `w₀ ≤ |w| ≤ T₀` the Route-T width and the height cost are monotone in the frequency,
so their values at the top of the annulus serve for every frequency in it; and the block data enter
only through uniform bounds on the endpoints.  The result is a single relative constant `ρ`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The annulus bound, uniform in the step and the frequency.** -/
theorem exists_annulus_bound_uniform :
    ∃ A delta Ctot τ₀ : ℝ, 0 < delta ∧ 0 < Ctot ∧ 2 ≤ τ₀ ∧
      ∀ (z₀ z L B₀ : ℕ) (Q η D w₀ T₀ Lx q μ xmin Hmaj : ℝ),
        1 ≤ z₀ → Q = (z₀ : ℝ) → 0 ≤ η → z = ⌊Q * (1 + η) ^ L⌋₊ → 1 ≤ D →
        max τ₀ (16 * Real.pi / 3) ≤ 2 * Real.pi * w₀ → w₀ ≤ T₀ →
        (∀ j ∈ Finset.range L,
          Real.log (max ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1) ≤ Lx) →
        0 ≤ q →
        (∀ j ∈ Finset.range L,
          q ≤ Real.log (max ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1)) →
        0 ≤ μ → μ ≤ min delta (routeTWidthPolylogLower A (2 * Real.pi * T₀)) / 2 →
        0 < xmin →
        (∀ j ∈ Finset.range L, xmin ≤ max ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1) →
        1 / (2 * Real.pi * w₀)
            + Real.log (3 * (2 * Real.pi * T₀) / 2)
              / routeTWidthPolylogLower A (2 * Real.pi * T₀) ≤ Hmaj →
        ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-T₀) T₀ \ Set.Icc (-w₀) w₀,
          ‖primeBlockPoly (geomBlock (primesRange z₀ z) Q (1 + η) j) w‖
            ≤ (4 / Real.log 2)
                * ((1 + η) * relScaledMajorant Ctot D Lx Hmaj μ q (2 * Real.pi * w₀) xmin
                  + 7 * Real.exp 9 / Q) * (Q * (1 + η) ^ j) := by
  obtain ⟨A, delta, Ctot, τ₀, hdelta, hCtot, hτ₀, hbound⟩ :=
    exists_norm_primeBlockPoly_geomBlock_rho_le
  refine ⟨A, delta, Ctot, τ₀, hdelta, hCtot, hτ₀, ?_⟩
  intro z₀ z L B₀ Q η D w₀ T₀ Lx q μ xmin Hmaj hz₀ hQ hη hz hD hw₀ hwT hLx hq0 hq hμ0 hμ
    hxmin hxminj hHmaj j hj w hw
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hw₀τ : τ₀ ≤ 2 * Real.pi * w₀ := le_trans (le_max_left _ _) hw₀
  have hw₀16 : 16 * Real.pi / 3 ≤ 2 * Real.pi * w₀ := le_trans (le_max_right _ _) hw₀
  have hw₀0 : (0 : ℝ) < 2 * Real.pi * w₀ := by linarith
  have hw₀pos : (0 : ℝ) < w₀ := by nlinarith [hw₀0, hpi]
  -- the frequency lies in the annulus
  have hwT₀ : |w| ≤ T₀ := by
    have h1 : w ∈ Set.Icc (-T₀) T₀ := hw.1
    rw [Set.mem_Icc] at h1
    exact abs_le.2 ⟨h1.1, h1.2⟩
  have hwlo : w₀ ≤ |w| := by
    by_contra hcon
    have hlt : |w| < w₀ := by linarith [not_le.1 hcon]
    exact hw.2 (Set.mem_Icc.2 ⟨by linarith [neg_abs_le w], by linarith [le_abs_self w]⟩)
  have habs : |(-(2 * Real.pi * w))| = 2 * Real.pi * |w| := by
    rw [abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hlo : 2 * Real.pi * w₀ ≤ |(-(2 * Real.pi * w))| := by
    rw [habs]
    nlinarith [hwlo, hpi]
  have hσ : |(2 * Real.pi * T₀)| = 2 * Real.pi * T₀ := by
    have : (0 : ℝ) ≤ T₀ := le_trans hw₀pos.le hwT
    rw [abs_of_nonneg (by positivity)]
  have hhi : |(-(2 * Real.pi * w))| ≤ |(2 * Real.pi * T₀)| := by
    rw [habs, hσ]
    nlinarith [hwT₀, hpi]
  have hτ : τ₀ ≤ |(-(2 * Real.pi * w))| := le_trans hw₀τ hlo
  have h16 : 16 * Real.pi / 3 ≤ |(-(2 * Real.pi * w))| := le_trans hw₀16 hlo
  have hμw : μ ≤ min delta (routeTWidthPolylogLower A (-(2 * Real.pi * w))) / 2 := by
    have hanti := routeTWidthPolylogLower_antitone (A := A) (τ := -(2 * Real.pi * w))
      (σ := 2 * Real.pi * T₀) hhi
    have : min delta (routeTWidthPolylogLower A (2 * Real.pi * T₀))
        ≤ min delta (routeTWidthPolylogLower A (-(2 * Real.pi * w))) :=
      le_min (min_le_left _ _) (le_trans (min_le_right _ _) hanti)
    linarith [hμ]
  have hHm : 1 / (2 * Real.pi * w₀)
      + Real.log (3 * |(2 * Real.pi * T₀)| / 2)
        / routeTWidthPolylogLower A (2 * Real.pi * T₀) ≤ Hmaj := by
    rw [hσ]
    exact hHmaj
  exact hbound z₀ z L j Q η D w (2 * Real.pi * w₀) (2 * Real.pi * T₀) Lx q μ xmin Hmaj
    hz₀ hQ hη (Finset.mem_range.1 hj) hz hD hτ h16 hw₀0 hlo hhi (hLx j hj) hq0 (hq j hj) hμ0 hμw hxmin
    (hxminj j hj) hHm

end

end RHTower.Sieve
