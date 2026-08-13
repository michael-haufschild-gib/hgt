import Mathlib
import GaloisForLFunctions.RHTower.DeningerCriticalFloquetVonMangoldtWall
import GaloisForLFunctions.RHTower.PolePurchaseCollisionGap
import GaloisForLFunctions.RHTower.VonMangoldtLineSeriesSwap

/-!
# The coupled-purchase log-derivative identity

The middle of de la Vallée Poussin's coupled positivity: on `Re s > 1`,

`3(−ζ'/ζ)(σ) + 4 Re(−ζ'/ζ)(σ+it) + Re(−ζ'/ζ)(σ+2it)
  = ∑ Λ(n) n^{−σ} (3 + 4cos(t log n) + cos(2t log n))`,

whose right side is nonnegative termwise because `3 + 4cos θ + cos 2θ = 2(1+cos θ)² ≥ 0` and
`Λ ≥ 0`.  The Dirichlet-series input is mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`;
the bookkeeping is the real part of each line term and the interchange of `Re` with the sum.
-/

open ArithmeticFunction Complex

namespace RHTower

/-- The real part of one von Mangoldt line term: `Λ(n) n^{−σ} cos(t log n)`. -/
theorem re_vonMangoldt_line_term (σ t : ℝ) (n : ℕ) :
    (LSeries.term (fun m => (vonMangoldt m : ℂ)) ((σ : ℂ) + (t : ℂ) * I) n).re
      = (vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn]
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hdiv : (vonMangoldt n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)
        = (vonMangoldt n : ℂ) * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) := by
      rw [Complex.cpow_neg, div_eq_mul_inv]
    rw [hdiv, natCast_cpow_neg_line_eq n hn σ t]
    have hlog : Complex.log (n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log hnpos.le]
    have hre : (Complex.log (n : ℂ) * (-((σ : ℂ) + (t : ℂ) * I))).re
        = Real.log (n : ℝ) * (-σ) := by
      rw [hlog, Complex.re_ofReal_mul]
      congr 1
      simp
    have him : (Complex.log (n : ℂ) * (-((σ : ℂ) + (t : ℂ) * I))).im
        = Real.log (n : ℝ) * (-t) := by
      rw [hlog, Complex.im_ofReal_mul]
      congr 1
      simp
    rw [Complex.re_ofReal_mul, Complex.exp_re, hre, him]
    rw [Real.rpow_def_of_pos hnpos]
    have hcos : Real.cos (Real.log (n : ℝ) * (-t)) = Real.cos (t * Real.log (n : ℝ)) := by
      rw [show Real.log (n : ℝ) * (-t) = -(t * Real.log (n : ℝ)) by ring, Real.cos_neg]
    rw [hcos]
    ring

/-- The von Mangoldt series with a cosine weight is summable at `σ > 1`. -/
theorem summable_vonMangoldt_cos_weight {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    Summable fun n : ℕ =>
      (vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  refine Summable.of_norm_bounded (summable_vonMangoldt_mul_rpow hσ) ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |(vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)| = (vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) :=
    abs_of_nonneg (mul_nonneg (vonMangoldt_nonneg (n := n))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  rw [h1]
  have h2 : |Real.cos (t * Real.log n)| ≤ 1 := Real.abs_cos_le_one _
  have h3 : (0 : ℝ) ≤ (vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) :=
    mul_nonneg (vonMangoldt_nonneg (n := n)) (Real.rpow_nonneg (Nat.cast_nonneg n) (-σ))
  nlinarith [h3]

/-- The real part of the von Mangoldt L-series on a vertical line is the cosine-weighted
prime-power series. -/
theorem re_LSeries_vonMangoldt {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    (LSeries (fun m => (vonMangoldt m : ℂ)) ((σ : ℂ) + (t : ℂ) * I)).re
      = ∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  have hs : LSeriesSummable (fun m => (vonMangoldt m : ℂ)) ((σ : ℂ) + (t : ℂ) * I) :=
    LSeriesSummable_vonMangoldt (by simp [hσ])
  have hre := ((hs.hasSum.mapL Complex.reCLM).tsum_eq).symm
  rw [LSeries]
  refine hre.trans ?_
  exact tsum_congr fun n => re_vonMangoldt_line_term σ t n

/-- **The (INV3.2) log-derivative identity.**  On `Re s > 1`, the 3–4–1 combination of
`−ζ'/ζ` at heights `0, t, 2t` equals the nonnegatively-weighted von Mangoldt series. -/
theorem vallee_poussin_log_deriv_identity {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      + 4 * (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)
          / riemannZeta ((σ : ℂ) + (t : ℂ) * I)).re
      + (-deriv riemannZeta ((σ : ℂ) + (2 * t : ℝ) * I)
          / riemannZeta ((σ : ℂ) + (2 * t : ℝ) * I)).re
      = ∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
          * (3 + 4 * Real.cos (t * Real.log n) + Real.cos (2 * t * Real.log n)) := by
  have hL : ∀ u : ℝ, LSeries (fun m => (vonMangoldt m : ℂ)) ((σ : ℂ) + (u : ℂ) * I)
      = -deriv riemannZeta ((σ : ℂ) + (u : ℂ) * I)
        / riemannZeta ((σ : ℂ) + (u : ℂ) * I) := by
    intro u
    exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simp [hσ])
  have h0 : (σ : ℂ) = (σ : ℂ) + ((0 : ℝ) : ℂ) * I := by simp
  have e0 := re_LSeries_vonMangoldt hσ 0
  have et := re_LSeries_vonMangoldt hσ t
  have e2t := re_LSeries_vonMangoldt hσ (2 * t)
  rw [hL 0] at e0
  rw [hL t] at et
  rw [hL (2 * t)] at e2t
  rw [et, e2t, h0, e0]
  have s0 := summable_vonMangoldt_cos_weight hσ 0
  have st := summable_vonMangoldt_cos_weight hσ t
  have s2t := summable_vonMangoldt_cos_weight hσ (2 * t)
  rw [← tsum_mul_left, ← tsum_mul_left]
  rw [← Summable.tsum_add (s0.mul_left 3) (st.mul_left 4)]
  rw [← Summable.tsum_add ((s0.mul_left 3).add (st.mul_left 4)) s2t]
  refine tsum_congr fun n => ?_
  simp only [zero_mul, Real.cos_zero]
  ring

/-- The right side of the identity is nonnegative: the source cone `Λ ≥ 0` against the
de la Vallée Poussin pattern. -/
theorem vallee_poussin_log_deriv_nonneg {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      + 4 * (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)
          / riemannZeta ((σ : ℂ) + (t : ℂ) * I)).re
      + (-deriv riemannZeta ((σ : ℂ) + (2 * t : ℝ) * I)
          / riemannZeta ((σ : ℂ) + (2 * t : ℝ) * I)).re := by
  rw [vallee_poussin_log_deriv_identity hσ t]
  refine tsum_nonneg fun n => ?_
  have hpat : 0 ≤ 3 + 4 * Real.cos (t * Real.log n) + Real.cos (2 * (t * Real.log n)) :=
    vallee_poussin_nonneg (t * Real.log n)
  have hpat' : 0 ≤ 3 + 4 * Real.cos (t * Real.log n) + Real.cos (2 * t * Real.log n) := by
    rw [show 2 * t * Real.log n = 2 * (t * Real.log n) by ring]
    exact hpat
  exact mul_nonneg
    (mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hpat'

end RHTower
