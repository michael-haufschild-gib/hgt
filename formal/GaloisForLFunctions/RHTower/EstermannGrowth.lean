import GaloisForLFunctions.RHTower.EstermannZeta

/-!
# Growth of Estermann's zeta function

Right of the abscissa the double series is dominated termwise, so `D(s, a/q)` is at most the square
of the shifted `p`-series at `Re s`.  Reflecting with `estermannZeta_one_sub` transports that bound
to the left half plane, with the archimedean factor
`2 q^{2σ-1} (2π)^{-2σ} ‖Γ(s)‖² (1 + ‖cos πs‖)`.

These are the two edges a contour shift for the twisted second moment consumes.
-/

open Complex HurwitzZeta

namespace RHTower

noncomputable section

variable {q : ℕ} [NeZero q]

theorem summable_shiftedPSeries {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) ^ σ) :=
  (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_rpow (p := σ)).mpr hσ)

theorem shiftedPSeries_nonneg (σ : ℝ) :
    0 ≤ ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ)) ^ σ := by
  refine tsum_nonneg fun n => ?_
  positivity

/-- **The right edge.**  For `1 < Re s` the Estermann value is at most the square of the shifted
`p`-series at `Re s`. -/
theorem norm_estermannZeta_le (a : ZMod q) {s : ℂ} (hs : 1 < s.re) :
    ‖estermannZeta q a s‖
      ≤ (∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ)) ^ s.re)
        * (∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ)) ^ s.re) := by
  have hg := summable_shiftedPSeries hs
  have hprodsum : Summable (fun p : ℕ × ℕ =>
      (1 / (((p.1 + 1 : ℕ) : ℝ)) ^ s.re) * (1 / (((p.2 + 1 : ℕ) : ℝ)) ^ s.re)) :=
    hg.mul_of_nonneg hg (fun n => by positivity) (fun n => by positivity)
  have hprod := hg.hasSum.mul hg.hasSum hprodsum
  refine (hasSum_estermannZeta (q := q) a hs).norm_le_of_bounded hprod ?_
  intro p
  rw [norm_div, ZMod.stdAddChar_apply, Circle.norm_coe, norm_mul,
    norm_natCast_cpow_of_pos (by omega : 0 < p.1 + 1),
    norm_natCast_cpow_of_pos (by omega : 0 < p.2 + 1)]
  simp only [one_div, mul_inv]
  exact le_refl _

/-- **The left edge.**  Reflecting the right edge through the functional equation. -/
theorem norm_estermannZeta_one_sub_le (a : (ZMod q)ˣ) {s : ℂ} (hs : 1 < s.re)
    (hpole : ∀ n : ℕ, s ≠ 1 - (n : ℂ)) :
    ‖estermannZeta q ((a : ZMod q)) (1 - s)‖
      ≤ 2 * (q : ℝ) ^ (2 * s.re - 1) * (2 * Real.pi) ^ (-(2 * s.re))
          * ‖Complex.Gamma s‖ ^ (2 : ℕ) * (1 + ‖Complex.cos ((Real.pi : ℂ) * s)‖)
          * ((∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ)) ^ s.re)
              * (∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ)) ^ s.re)) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have := NeZero.pos q
    exact_mod_cast this
  have hpi0 : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [estermannZeta_one_sub a hpole]
  have hcastq : ((q : ℕ) : ℂ) = (((q : ℕ) : ℝ) : ℂ) := by push_cast; ring
  have hcastpi : (2 * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ)) : ℂ) := by push_cast; ring
  have hnq : ‖((q : ℕ) : ℂ) ^ (2 * s - 1)‖ = (q : ℝ) ^ (2 * s.re - 1) := by
    rw [hcastq, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
    congr 1
    simp [Complex.sub_re, Complex.mul_re]
  have hnpi : ‖(2 * (Real.pi : ℂ)) ^ (-(2 * s))‖ = (2 * Real.pi) ^ (-(2 * s.re)) := by
    rw [hcastpi, Complex.norm_cpow_eq_rpow_re_of_pos hpi0]
    congr 1
    simp [Complex.neg_re, Complex.mul_re]
  have hA := norm_estermannZeta_le (q := q) ((a⁻¹ : (ZMod q)ˣ) : ZMod q) hs
  have hB := norm_estermannZeta_le (q := q) (-((a⁻¹ : (ZMod q)ˣ) : ZMod q)) hs
  have hSnn : 0 ≤ ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ)) ^ s.re := shiftedPSeries_nonneg s.re
  have hinner : ‖estermannZeta q ((a⁻¹ : (ZMod q)ˣ) : ZMod q) s
      + Complex.cos ((Real.pi : ℂ) * s) * estermannZeta q (-((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s‖
      ≤ (1 + ‖Complex.cos ((Real.pi : ℂ) * s)‖)
        * ((∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ)) ^ s.re)
            * (∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ)) ^ s.re)) := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul]
    have hc : 0 ≤ ‖Complex.cos ((Real.pi : ℂ) * s)‖ := norm_nonneg _
    nlinarith [hA, hB, hc, hSnn]
  have hfac : (0 : ℝ) ≤ 2 * (q : ℝ) ^ (2 * s.re - 1) * (2 * Real.pi) ^ (-(2 * s.re))
      * ‖Complex.Gamma s‖ ^ (2 : ℕ) := by positivity
  have hsplit : ‖2 * ((q : ℕ) : ℂ) ^ (2 * s - 1) * (2 * (Real.pi : ℂ)) ^ (-(2 * s))
        * Complex.Gamma s ^ 2 *
        (estermannZeta q ((a⁻¹ : (ZMod q)ˣ) : ZMod q) s
          + Complex.cos ((Real.pi : ℂ) * s) * estermannZeta q (-((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s)‖
      = 2 * (q : ℝ) ^ (2 * s.re - 1) * (2 * Real.pi) ^ (-(2 * s.re)) * ‖Complex.Gamma s‖ ^ (2 : ℕ)
          * ‖estermannZeta q ((a⁻¹ : (ZMod q)ˣ) : ZMod q) s
            + Complex.cos ((Real.pi : ℂ) * s)
              * estermannZeta q (-((a⁻¹ : (ZMod q)ˣ) : ZMod q)) s‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, hnq, hnpi, norm_pow]
    norm_num
  rw [hsplit]
  nlinarith [hinner, hfac]

end

end RHTower
