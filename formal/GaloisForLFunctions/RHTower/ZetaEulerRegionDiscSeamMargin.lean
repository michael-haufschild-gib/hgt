import GaloisForLFunctions.RHTower.CircleZeroFreeDatumSeamMargin
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDeepCoefficientIdentification
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound

/-!
# Height-uniform seam margin of the `ζ` phase in the Euler region

For `σ₁ > 1` and every closed disc contained in `Re s ≥ σ₁`, the adjoint Hankel seam of the boundary
phase of `ζ` satisfies

`1 − ‖(1 − P) U† P‖² ≥ ((σ₁ − 1)/σ₁)²`   (`zetaEulerDisc_one_sub_seam_sq_ge`),

uniformly in the height and the radius.  Both `|ζ(s)|` and `|1/ζ(s)| = |Σ μ(n) n^{−s}|` are bounded
by `Σ n^{−σ₁} ≤ σ₁/(σ₁ − 1)` there.  The margin law `DiscArgumentDatum.one_sub_seam_sq_ge` then
applies with `m = (σ₁ − 1)/σ₁` and `M = σ₁/(σ₁ − 1)`.  The margin degenerates only as the disc
approaches the pole line `Re s = 1`, quadratically in the distance.
-/

noncomputable section

open Complex Metric

namespace RHTower

theorem norm_moebius_lSeries_term_le_rpow {σ₁ : ℝ} {s : ℂ} (hs : σ₁ ≤ s.re) (n : ℕ) :
    ‖LSeries.term (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) s n‖ ≤
      (n : ℝ) ^ (-σ₁) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero, norm_zero, Nat.cast_zero]
    exact Real.rpow_nonneg le_rfl _
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hn0 : (0 : ℝ) < n := by positivity
    have hcoeff : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := norm_moebius_le_one n
    rw [LSeries.term_of_ne_zero hn, norm_div, norm_natCast_cpow_zetaVerticalLineBound hn1]
    have hpowPos : (0 : ℝ) < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos hn0 _
    rw [Real.rpow_neg hn0.le]
    apply (div_le_iff₀ hpowPos).2
    calc ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := hcoeff
      _ ≤ ((n : ℝ) ^ σ₁)⁻¹ * (n : ℝ) ^ s.re := by
        rw [inv_mul_eq_div, le_div_iff₀ (Real.rpow_pos_of_pos hn0 _)]
        simpa only [one_mul] using Real.rpow_le_rpow_of_exponent_le hnR hs

/-- `|1/ζ(s)| ≤ σ₁/(σ₁ − 1)` on `Re s ≥ σ₁ > 1`. -/
theorem norm_inv_riemannZeta_le_of_le_re {σ₁ : ℝ} (hσ₁ : 1 < σ₁) {s : ℂ} (hs : σ₁ ≤ s.re) :
    ‖(riemannZeta s)⁻¹‖ ≤ 1 + 1 / (σ₁ - 1) := by
  have hs1 : 1 < s.re := by linarith
  rw [← LSeries_moebius_eq_inv_riemannZeta hs1]
  refine le_trans (norm_lSeries_le_of_term_bound (Real.summable_nat_rpow.mpr (by linarith))
    (norm_moebius_lSeries_term_le_rpow hs)) ?_
  exact Sieve.tsum_nat_rpow_neg_le hσ₁

theorem norm_riemannZeta_le_of_le_re {σ₁ : ℝ} (hσ₁ : 1 < σ₁) {s : ℂ} (hs : σ₁ ≤ s.re) :
    ‖riemannZeta s‖ ≤ 1 + 1 / (σ₁ - 1) := by
  have hs1 : 1 < s.re := by linarith
  refine le_trans (Sieve.norm_riemannZeta_le hs1) ?_
  have h1 : 0 < σ₁ - 1 := by linarith
  have h2 : σ₁ - 1 ≤ s.re - 1 := by linarith
  have : 1 / (s.re - 1) ≤ 1 / (σ₁ - 1) := one_div_le_one_div_of_le h1 h2
  linarith

/-- The disc datum of `ζ` on a disc contained in `Re s ≥ σ₁ > 1`. -/
def zetaEulerDiscDatum {σ₁ : ℝ} (hσ₁ : 1 < σ₁) (c : ℂ) (t : ℝ) (ht : 0 < t)
    (hc : σ₁ + t ≤ c.re) : DiscArgumentDatum where
  c := c
  t := t
  R := t + (σ₁ - 1) / 4
  U := {s : ℂ | (1 + σ₁) / 2 < s.re}
  F := riemannZeta
  t_pos := ht
  t_lt_R := by linarith
  isOpen := isOpen_lt continuous_const Complex.continuous_re
  closedBall_subset := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re] at h1
    have h2 := neg_abs_le (z.re - c.re)
    show (1 + σ₁) / 2 < z.re
    linarith
  differentiableOn := fun s hs => by
    have hs1 : s ≠ 1 := by
      intro h; rw [h] at hs; simp at hs; linarith
    exact (differentiableAt_riemannZeta hs1).differentiableWithinAt
  ne_zero := fun ζ hζ => by
    apply riemannZeta_ne_zero_of_one_lt_re
    rw [mem_sphere, dist_eq_norm] at hζ
    have h1 : |(ζ - c).re| ≤ ‖ζ - c‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re] at h1
    have h2 := neg_abs_le (ζ.re - c.re)
    linarith

/-- **Height-uniform margin in the Euler region.** -/
theorem zetaEulerDisc_one_sub_seam_sq_ge {σ₁ : ℝ} (hσ₁ : 1 < σ₁) (c : ℂ) (t : ℝ) (ht : 0 < t)
    (hc : σ₁ + t ≤ c.re) :
    ((σ₁ - 1) / σ₁) ^ 2 ≤
      1 - ‖(zetaEulerDiscDatum hσ₁ c t ht hc).circlePhase.datum.adjointHankelSeam‖ ^ 2 := by
  have hre : ∀ z ∈ closedBall c t, σ₁ ≤ z.re := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re] at h1
    have h2 := neg_abs_le (z.re - c.re)
    linarith
  have h0 : 0 < σ₁ - 1 := by linarith
  set K : ℝ := 1 + 1 / (σ₁ - 1) with hK
  have hKpos : 0 < K := by positivity
  have hKeq : K = σ₁ / (σ₁ - 1) := by rw [hK]; field_simp; ring
  have hbounds : ∀ ζ ∈ sphere c t, 1 / K ≤ ‖riemannZeta ζ‖ ∧ ‖riemannZeta ζ‖ ≤ K := by
    intro ζ hζ
    have hζre := hre ζ (sphere_subset_closedBall hζ)
    have hne : riemannZeta ζ ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by linarith)
    refine ⟨?_, norm_riemannZeta_le_of_le_re hσ₁ hζre⟩
    have hinv := norm_inv_riemannZeta_le_of_le_re hσ₁ hζre
    rw [norm_inv] at hinv
    have hpos : 0 < ‖riemannZeta ζ‖ := norm_pos_iff.mpr hne
    rw [div_le_iff₀ hKpos]
    have := (inv_le_iff_one_le_mul₀ hpos).mp hinv
    linarith
  have h := (zetaEulerDiscDatum hσ₁ c t ht hc).one_sub_seam_sq_ge
    (fun z hz => riemannZeta_ne_zero_of_one_lt_re (by linarith [hre z hz]))
    (m := 1 / K) (M := K) (by positivity) hbounds
  have hval : 1 / K / K = ((σ₁ - 1) / σ₁) ^ 2 := by
    rw [hKeq]; field_simp
  rw [hval] at h
  exact h

end RHTower
