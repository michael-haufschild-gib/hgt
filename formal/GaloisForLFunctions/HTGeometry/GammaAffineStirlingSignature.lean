import GaloisForLFunctions.HTGeometry.GammaDigammaStirlingBound

/-!
# The Stirling signature of an affine Gamma argument

Applying `ψ(w) = log w − 1/(2w) + O(|w|⁻²)` at `w = λ s + μ` with `λ > 0` real and moving the
scale out of the logarithm gives the three-term signature

```text
ψ(λ s + μ) = log λ + log s + (μ − ½)/(λ s) + O(|s|⁻²).
```

The three data `log λ` (constant), `1` (coefficient of `log s`) and `μ − ½` (the `1/s` residue) are
exactly what separates the monomials of `e^{αs} s^β ∏_j Γ(λ_j s + μ_j)^{n_j}` in the archimedean
residue field: no flat cancellation is possible because the expansion is uniform with an explicit
constant.

Only mathlib's `Complex.log_ofReal_mul` (a positive real scale leaves the branch alone) and the
quadratic log bound are needed on top of the Stirling estimate.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

set_option maxHeartbeats 1000000 in
/-- **The affine Stirling signature.**  For a positive real scale `λ` and any shift `μ`,
`ψ(λ s + μ) − (log λ + log s + (μ − ½)/(λ s))` is `O(|s|⁻²)` with an explicit constant. -/
theorem exists_norm_digamma_affine_expansion_le {lam : ℝ} (hlam : 0 < lam) (mu : ℂ) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ s : ℂ, 0 < s.re → 0 < ((lam : ℂ) * s + mu).re → R ≤ ‖s‖ →
      ‖Complex.digamma ((lam : ℂ) * s + mu) -
        (((Real.log lam : ℝ) : ℂ) + Complex.log s + (mu - 1 / 2) / ((lam : ℂ) * s))‖
        ≤ C / ‖s‖ ^ (2 : ℕ) := by
  have hgen : ∀ a b : ℂ, a ≠ 0 → b ≠ 0 → 1 / (2 * a) - 1 / (2 * b) = (b - a) / (2 * a * b) := by
    intro a b ha hb
    field_simp
  refine ⟨(24 + ‖mu‖ ^ (2 : ℕ) + ‖mu‖) / lam ^ (2 : ℕ), max (2 * ‖mu‖ / lam) (4 / lam), by positivity,
    le_max_of_le_right (by positivity), fun s hs hw hR => ?_⟩
  have hnorm0 : (0 : ℝ) < ‖s‖ := by
    have h1 : (0 : ℝ) < 4 / lam := by positivity
    have h2 : 4 / lam ≤ ‖s‖ := le_trans (le_max_right _ _) hR
    linarith
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hnorm0
    simp at hnorm0
  have hmuR : 2 * ‖mu‖ / lam ≤ ‖s‖ := le_trans (le_max_left _ _) hR
  have hfourR : 4 / lam ≤ ‖s‖ := le_trans (le_max_right _ _) hR
  have hmu2 : 2 * ‖mu‖ ≤ lam * ‖s‖ := by
    rw [div_le_iff₀ hlam] at hmuR
    linarith
  have hfour : 4 ≤ lam * ‖s‖ := by
    rw [div_le_iff₀ hlam] at hfourR
    linarith
  set w : ℂ := (lam : ℂ) * s + mu with hwdef
  have hlams : ‖(lam : ℂ) * s‖ = lam * ‖s‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]
  have hwlow : lam * ‖s‖ / 2 ≤ ‖w‖ := by
    have h := norm_sub_le ((lam : ℂ) * s + mu) mu
    rw [add_sub_cancel_right, hlams] at h
    rw [hwdef]
    linarith
  have hwpos : (0 : ℝ) < ‖w‖ := by
    have : (0 : ℝ) < lam * ‖s‖ / 2 := by positivity
    linarith
  have hw2 : (2 : ℝ) ≤ ‖w‖ := by linarith
  -- (1) the Stirling estimate at `w`
  have hE1 : ‖Complex.digamma w - Complex.log w + 1 / (2 * w)‖ ≤ 24 / (lam ^ (2 : ℕ) * ‖s‖ ^ (2 : ℕ)) := by
    refine le_trans (norm_digammaStirlingDefect_le hw hw2) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hwlow, hwpos, hlam, hnorm0, sq_nonneg (lam * ‖s‖)]
  -- (2) moving the scale out of the logarithm
  have hlamspos : 0 < ((lam : ℂ) * s).re := by
    rw [Complex.re_ofReal_mul]
    positivity
  have hlamsne : ((lam : ℂ) * s) ≠ 0 := by
    intro h
    have : ‖(lam : ℂ) * s‖ = 0 := by rw [h]; simp
    rw [hlams] at this
    nlinarith [hlam, hnorm0]
  set u : ℂ := mu / ((lam : ℂ) * s) with hudef
  have hunorm : ‖u‖ = ‖mu‖ / (lam * ‖s‖) := by rw [hudef, norm_div, hlams]
  have huhalf : ‖u‖ ≤ 1 / 2 := by
    rw [hunorm, div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
    linarith
  have hquot : w / ((lam : ℂ) * s) = 1 + u := by
    rw [hwdef, hudef, add_div, div_self hlamsne]
  have hlogsplit : Complex.log w - Complex.log ((lam : ℂ) * s) = Complex.log (1 + u) := by
    rw [log_sub_log_of_re_pos hw hlamspos, hquot]
  have hE2 : ‖Complex.log (1 + u) - u‖ ≤ ‖mu‖ ^ (2 : ℕ) / (lam ^ (2 : ℕ) * ‖s‖ ^ (2 : ℕ)) := by
    have hlt : ‖u‖ < 1 := lt_of_le_of_lt huhalf (by norm_num)
    have hsq : ‖u‖ ^ (2 : ℕ) = ‖mu‖ ^ (2 : ℕ) / (lam ^ (2 : ℕ) * ‖s‖ ^ (2 : ℕ)) := by
      rw [hunorm, div_pow, mul_pow]
    have hchain : ‖u‖ ^ (2 : ℕ) * (1 - ‖u‖)⁻¹ / 2 ≤ ‖u‖ ^ (2 : ℕ) := by
      have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith [huhalf]) (by norm_num)]
        linarith [huhalf]
      nlinarith [sq_nonneg ‖u‖, hinv]
    calc ‖Complex.log (1 + u) - u‖ ≤ ‖u‖ ^ (2 : ℕ) * (1 - ‖u‖)⁻¹ / 2 :=
          Complex.norm_log_one_add_sub_self_le hlt
      _ ≤ ‖u‖ ^ (2 : ℕ) := hchain
      _ = ‖mu‖ ^ (2 : ℕ) / (lam ^ (2 : ℕ) * ‖s‖ ^ (2 : ℕ)) := hsq
  -- (3) moving the scale out of the reciprocal
  have hE3 : ‖1 / (2 * w) - 1 / (2 * ((lam : ℂ) * s))‖ ≤ ‖mu‖ / (lam ^ (2 : ℕ) * ‖s‖ ^ (2 : ℕ)) := by
    have hwne : w ≠ 0 := by
      intro h
      rw [h] at hwpos
      simp at hwpos
    have hnum : ((lam : ℂ) * s) - w = -mu := by rw [hwdef]; ring
    rw [hgen w ((lam : ℂ) * s) hwne hlamsne, hnum, norm_div, norm_neg, norm_mul, norm_mul,
      hlams]
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2n]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hwlow, hwpos, hlam, hnorm0, norm_nonneg mu,
      mul_nonneg (norm_nonneg mu) (mul_nonneg hlam.le hnorm0.le)]
  -- assemble
  have hlogscale : Complex.log ((lam : ℂ) * s) = ((Real.log lam : ℝ) : ℂ) + Complex.log s :=
    Complex.log_ofReal_mul hlam hs0
  have hsplit : Complex.digamma w -
      (((Real.log lam : ℝ) : ℂ) + Complex.log s + (mu - 1 / 2) / ((lam : ℂ) * s))
      = (Complex.digamma w - Complex.log w + 1 / (2 * w))
        + (Complex.log (1 + u) - u)
        - (1 / (2 * w) - 1 / (2 * ((lam : ℂ) * s))) := by
    rw [← hlogsplit, hlogscale, hudef]
    field_simp
    ring
  rw [hsplit]
  have htotal : ‖(Complex.digamma w - Complex.log w + 1 / (2 * w))
        + (Complex.log (1 + u) - u)
        - (1 / (2 * w) - 1 / (2 * ((lam : ℂ) * s)))‖
      ≤ 24 / (lam ^ (2 : ℕ) * ‖s‖ ^ (2 : ℕ)) + ‖mu‖ ^ (2 : ℕ) / (lam ^ (2 : ℕ) * ‖s‖ ^ (2 : ℕ))
        + ‖mu‖ / (lam ^ (2 : ℕ) * ‖s‖ ^ (2 : ℕ)) := by
    refine le_trans (norm_sub_le _ _) ?_
    refine add_le_add (le_trans (norm_add_le _ _) (add_le_add hE1 hE2)) hE3
  refine le_trans htotal (le_of_eq ?_)
  field_simp

end

end GaloisForLFunctions.HTGeometry
