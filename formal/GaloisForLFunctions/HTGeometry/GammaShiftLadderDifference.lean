import GaloisForLFunctions.HTGeometry.GammaShiftLadder
import GaloisForLFunctions.HTGeometry.ArchimedeanPowerIndependence

/-!
# The forward difference of the shifted ladder coefficients

The functional equation `ψ(s+μ+1) = ψ(s+μ) + 1/(s+μ)` expands, in descending powers of `s`, into a
plain geometric series.  Comparing it with the ladder of `GammaShiftLadder` and using the
independence of descending powers gives, with no analytic input beyond the ladder itself,

```text
d_m(μ+1) - d_m(μ) = -(-μ)^m      for every m and every μ.
```

This is the recursion that pins the ladder coefficients down: `d_0(μ) = 1/2 - μ`, and each `d_m` is
determined up to an additive constant by the one below it.  Together with the (separately proved)
degree bound it forces `d_m` to be a polynomial of degree exactly `m+1` with leading coefficient
`(-1)^{m+1}/(m+1)`, which is what the power-sum reading of
`finite-archimedean-gamma-product-boundary-law` §5 consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

/-- The geometric expansion of `1/(z+μ)` in descending powers of `z`, with its exact remainder. -/
theorem inv_add_eq_geom_add_rem (mu : ℂ) : ∀ (M : ℕ) {z : ℂ}, z ≠ 0 → z + mu ≠ 0 →
    1 / (z + mu) = (∑ j ∈ Finset.range M, (-mu) ^ j / z ^ (j + 1))
      + (-mu) ^ M / (z ^ M * (z + mu)) := by
  intro M
  induction M with
  | zero =>
      intro z _ hzmu
      simp
  | succ M ih =>
      intro z hz hzmu
      rw [ih hz hzmu, Finset.sum_range_succ]
      have hzp : z ^ M ≠ 0 := pow_ne_zero _ hz
      have hzp1 : z ^ (M + 1) ≠ 0 := pow_ne_zero _ hz
      field_simp
      ring

/-- The sequence whose vanishing is the difference relation. -/
def shiftLadderDiffSeq (mu : ℂ) : ℕ → ℂ
  | 0 => 0
  | (k + 1) => (-mu) ^ k + (shiftLadderCoeff (mu + 1) k - shiftLadderCoeff mu k)

/-- **The forward difference of the ladder coefficients.** -/
theorem shiftLadderCoeff_succ_sub (mu : ℂ) (m : ℕ) :
    shiftLadderCoeff (mu + 1) m - shiftLadderCoeff mu m = -((-mu) ^ m) := by
  obtain ⟨K1, R1, hK1, hR1, hb1⟩ := exists_norm_shiftLadderDefect_le (mu + 1) (m + 1)
  obtain ⟨K2, R2, hK2, hR2, hb2⟩ := exists_norm_shiftLadderDefect_le mu (m + 1)
  set M : ℕ := m + 1 with hMdef
  set K : ℝ := K1 + K2 + ‖mu‖ ^ M * 2 with hKdef
  set R : ℝ := max (max R1 R2) (2 * ‖mu‖ + 2) with hRdef
  have hK0 : 0 ≤ K := by
    have : (0 : ℝ) ≤ ‖mu‖ ^ M * 2 := by positivity
    simp only [hKdef]; linarith
  have hmain : ∀ t : ℝ, R ≤ t → 1 ≤ t →
      ‖∑ j ∈ Finset.range (M + 1), shiftLadderDiffSeq mu j / (((t : ℝ) : ℂ)) ^ j‖
        ≤ K / t ^ (M + 1) := by
    intro t hRt ht1
    have hR1t : R1 ≤ t := le_trans (le_trans (le_max_left R1 R2) (le_max_left _ _)) hRt
    have hR2t : R2 ≤ t := le_trans (le_trans (le_max_right R1 R2) (le_max_left _ _)) hRt
    have hmut : 2 * ‖mu‖ + 2 ≤ t := le_trans (le_max_right _ _) hRt
    have ht0 : (0 : ℝ) < t := by linarith
    set z : ℂ := ((t : ℝ) : ℂ) with hzdef
    have hznorm : ‖z‖ = t := by
      rw [hzdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have hzre : (0 : ℝ) < z.re := by
      rw [hzdef, Complex.ofReal_re]; exact ht0
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hznorm; linarith
    have hmunorm : 2 * ‖mu‖ < ‖z‖ := by rw [hznorm]; linarith
    have hzmu : z + mu ≠ 0 := by
      have := shift_ne_neg_natCast hzre hmunorm 0
      simpa using this
    have hdig : Complex.digamma (z + (mu + 1)) = Complex.digamma (z + mu) + (z + mu)⁻¹ := by
      have hc : z + (mu + 1) = (z + mu) + 1 := by ring
      rw [hc]
      exact Complex.digamma_apply_add_one (z + mu) (fun k => shift_ne_neg_natCast hzre hmunorm k)
    -- the algebraic identity
    have hsplit : ∑ j ∈ Finset.range (M + 1), shiftLadderDiffSeq mu j / z ^ j
        = (shiftLadderDefect (mu + 1) M z - shiftLadderDefect mu M z)
          - (-mu) ^ M / (z ^ M * (z + mu)) := by
      have hpeel : ∑ j ∈ Finset.range (M + 1), shiftLadderDiffSeq mu j / z ^ j
          = ∑ k ∈ Finset.range M, shiftLadderDiffSeq mu (k + 1) / z ^ (k + 1) := by
        rw [Finset.sum_range_succ']
        simp [shiftLadderDiffSeq]
      have hgeom := inv_add_eq_geom_add_rem mu M hz0 hzmu
      have hexp : ∀ k : ℕ, shiftLadderDiffSeq mu (k + 1) / z ^ (k + 1)
          = (-mu) ^ k / z ^ (k + 1)
            + (shiftLadderCoeff (mu + 1) k / z ^ (k + 1)
              - shiftLadderCoeff mu k / z ^ (k + 1)) := by
        intro k
        rw [shiftLadderDiffSeq]
        ring
      rw [hpeel, Finset.sum_congr rfl (fun k _ => hexp k), Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      rw [shiftLadderDefect, shiftLadderDefect, hdig]
      have hinv : (z + mu)⁻¹ = 1 / (z + mu) := by rw [one_div]
      rw [hinv, hgeom]
      ring
    rw [hsplit]
    refine le_trans (norm_sub_le _ _) ?_
    have hb1' := hb1 z hzre (by rw [hznorm]; exact hR1t)
    have hb2' := hb2 z hzre (by rw [hznorm]; exact hR2t)
    have hd : ‖shiftLadderDefect (mu + 1) M z - shiftLadderDefect mu M z‖
        ≤ (K1 + K2) / t ^ (M + 1) := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [hznorm] at hb1' hb2'
      have : K1 / t ^ (M + 1) + K2 / t ^ (M + 1) = (K1 + K2) / t ^ (M + 1) := by ring
      linarith [hb1', hb2', this.le, this.symm.le]
    have hrem : ‖(-mu) ^ M / (z ^ M * (z + mu))‖ ≤ (‖mu‖ ^ M * 2) / t ^ (M + 1) := by
      have hlow : t - ‖mu‖ ≤ ‖z + mu‖ := by
        have h := norm_sub_le (z + mu) mu
        rw [add_sub_cancel_right] at h
        rw [hznorm] at h
        linarith
      have hhalf : t / 2 ≤ ‖z + mu‖ := by
        have : ‖mu‖ ≤ t / 2 := by linarith
        linarith
      have hzpos : (0 : ℝ) < ‖z + mu‖ := by linarith
      rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, hznorm]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hexp : t ^ (M + 1) = t ^ M * t := by ring
      rw [hexp]
      have h1 : ‖mu‖ ^ M * (t ^ M * t) ≤ ‖mu‖ ^ M * (t ^ M * (2 * ‖z + mu‖)) := by
        have : t ≤ 2 * ‖z + mu‖ := by linarith
        have hnn : (0 : ℝ) ≤ ‖mu‖ ^ M * t ^ M := by positivity
        nlinarith [hnn]
      calc ‖mu‖ ^ M * (t ^ M * t) ≤ ‖mu‖ ^ M * (t ^ M * (2 * ‖z + mu‖)) := h1
        _ = ‖mu‖ ^ M * 2 * (t ^ M * ‖z + mu‖) := by ring
    have hsum : (K1 + K2) / t ^ (M + 1) + (‖mu‖ ^ M * 2) / t ^ (M + 1) = K / t ^ (M + 1) := by
      rw [hKdef]; ring
    linarith [hd, hrem, hsum.le, hsum.symm.le]
  have hzero := power_expansion_eq_zero M (shiftLadderDiffSeq mu) K R hmain
  have hm := hzero (m + 1) (by simp [hMdef])
  rw [shiftLadderDiffSeq] at hm
  linear_combination hm

end

end GaloisForLFunctions.HTGeometry
