import GaloisForLFunctions.RHTower.PolePlaneIndexBlindnessNoGo

/-!
# The quartet twist is not a Dirichlet series

The quartet twist `ζ_Q(s) = ζ(s) Q(s)/Q(0)` shares the functional equation, the Gamma factor and the
polar part of `ζ`, and carries an off-line quartet.  It is not an absolutely convergent Dirichlet
series `Σ c_n (n+1)^{-s}` on the line `Re s = 2`: such a series is bounded there by
`Σ ‖c_n‖ (n+1)^{-2}`, whereas `‖ζ_Q(2 + it)‖ ≥ (2 - π²/6) (t - |γ|)^4 / ‖Q(0)‖` is unbounded.

So the boundary-preserving twist leaves the exact-occurrence class: the only datum separating `ζ`
from the twist is that `ζ` is a Dirichlet series over the integers, and that datum acts on the
primitive part of the form, not through the boundary.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The twisted zeta `ζ(s) Q(s)/Q(0)`. -/
def zetaQuartetTwist (a0 gam : ℝ) (s : ℂ) : ℂ :=
  riemannZeta s * (offLineQuartet a0 gam s / offLineQuartet a0 gam 0)

/-- On `Re s = 2`, `‖(n+1)^s‖ = (n+1)²`. -/
theorem norm_natCast_add_one_cpow_re_two {s : ℂ} (hs : s.re = 2) (n : ℕ) :
    ‖((n : ℂ) + 1) ^ s‖ = ((n : ℝ) + 1) ^ 2 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hpos, hs]
  exact Real.rpow_two _

/-- `Σ_{n ≥ 0} 1/(n+2)² = π²/6 - 1`. -/
theorem hasSum_one_div_add_two_sq :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
  have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
  simpa [Finset.sum_range_succ] using h

/-- On the line `Re s = 2`, `‖ζ(s)‖ ≥ 2 - π²/6`. -/
theorem norm_riemannZeta_ge_of_re_eq_two {s : ℂ} (hs : s.re = 2) :
    2 - Real.pi ^ 2 / 6 ≤ ‖riemannZeta s‖ := by
  have hs1 : 1 < s.re := by rw [hs]; norm_num
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs1]
  set f : ℕ → ℂ := fun n => (1 : ℂ) / ((n : ℂ) + 1) ^ s with hf
  have hnorm : ∀ n, ‖f n‖ = 1 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    simp only [hf]
    rw [norm_div, norm_one, norm_natCast_add_one_cpow_re_two hs]
  have hnorm_succ : ∀ n, ‖f (n + 1)‖ = 1 / ((n : ℝ) + 2) ^ 2 := by
    intro n
    rw [hnorm]
    push_cast
    ring_nf
  have hsummable_norm_succ : Summable (fun n => ‖f (n + 1)‖) := by
    simp_rw [hnorm_succ]
    exact hasSum_one_div_add_two_sq.summable
  have hsummable_succ : Summable (fun n => f (n + 1)) := Summable.of_norm hsummable_norm_succ
  have hsummable : Summable f := (summable_nat_add_iff 1).mp hsummable_succ
  rw [hsummable.tsum_eq_zero_add]
  have hf0 : f 0 = 1 := by simp [hf]
  rw [hf0]
  have htail : ‖∑' n, f (n + 1)‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    calc ‖∑' n, f (n + 1)‖ ≤ ∑' n, ‖f (n + 1)‖ := norm_tsum_le_tsum_norm hsummable_norm_succ
      _ = Real.pi ^ 2 / 6 - 1 := by
          simp_rw [hnorm_succ]
          exact hasSum_one_div_add_two_sq.tsum_eq
  have hns := norm_sub_norm_le (1 : ℂ) (-(∑' n, f (n + 1)))
  rw [norm_neg, norm_one, sub_neg_eq_add] at hns
  linarith

/-- Each linear factor of the quartet on the line `Re s = 2` is at least `t - |γ|`. -/
theorem norm_line_sub_root_ge {t g x : ℝ} (ht : 0 ≤ t) :
    t - |g| ≤ ‖(2 + (t : ℂ) * I) - ((x : ℂ) + (g : ℂ) * I)‖ := by
  have him : ((2 + (t : ℂ) * I) - ((x : ℂ) + (g : ℂ) * I)).im = t - g := by
    simp [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have h1 := Complex.abs_im_le_norm ((2 + (t : ℂ) * I) - ((x : ℂ) + (g : ℂ) * I))
  rw [him] at h1
  have h2 : |t| - |g| ≤ |t - g| := abs_sub_abs_le_abs_sub t g
  rw [abs_of_nonneg ht] at h2
  linarith

theorem norm_line_sub_root_ge' {t g x : ℝ} (ht : 0 ≤ t) :
    t - |g| ≤ ‖(2 + (t : ℂ) * I) - ((x : ℂ) - (g : ℂ) * I)‖ := by
  have h := norm_line_sub_root_ge (g := -g) (x := x) (t := t) ht
  rw [abs_neg] at h
  have hcast : ((x : ℂ) + ((-g : ℝ) : ℂ) * I) = ((x : ℂ) - (g : ℂ) * I) := by
    push_cast
    ring
  rwa [hcast] at h

/-- On the line `Re s = 2`, `‖Q(2 + it)‖ ≥ (t - |γ|)^4` for `t ≥ |γ|`. -/
theorem norm_offLineQuartet_ge (a0 gam : ℝ) {t : ℝ} (ht : |gam| ≤ t) :
    (t - |gam|) ^ 4 ≤ ‖offLineQuartet a0 gam (2 + (t : ℂ) * I)‖ := by
  have ht0 : 0 ≤ t := le_trans (abs_nonneg _) ht
  have h0 : 0 ≤ t - |gam| := by linarith
  unfold offLineQuartet
  rw [norm_mul, norm_mul, norm_mul]
  have h1 := norm_line_sub_root_ge (g := gam) (x := 1 / 2 + a0) ht0
  have h2 := norm_line_sub_root_ge' (g := gam) (x := 1 / 2 + a0) ht0
  have h3 := norm_line_sub_root_ge (g := gam) (x := 1 / 2 - a0) ht0
  have h4 := norm_line_sub_root_ge' (g := gam) (x := 1 / 2 - a0) ht0
  calc (t - |gam|) ^ 4
      = (t - |gam|) * (t - |gam|) * (t - |gam|) * (t - |gam|) := by ring
    _ ≤ ‖(2 + (t : ℂ) * I) - (((1 / 2 + a0 : ℝ) : ℂ) + (gam : ℂ) * I)‖
        * ‖(2 + (t : ℂ) * I) - (((1 / 2 + a0 : ℝ) : ℂ) - (gam : ℂ) * I)‖
        * ‖(2 + (t : ℂ) * I) - (((1 / 2 - a0 : ℝ) : ℂ) + (gam : ℂ) * I)‖
        * ‖(2 + (t : ℂ) * I) - (((1 / 2 - a0 : ℝ) : ℂ) - (gam : ℂ) * I)‖ := by
        apply mul_le_mul _ h4 h0 (by positivity)
        apply mul_le_mul _ h3 h0 (by positivity)
        exact mul_le_mul h1 h2 h0 (norm_nonneg _)

/-- The twisted zeta is unbounded on the line `Re s = 2`. -/
theorem exists_norm_zetaQuartetTwist_gt {a0 : ℝ} (ha0 : 0 < a0) (ha1 : a0 < 1 / 2) (gam : ℝ)
    (B : ℝ) :
    ∃ t : ℝ, B < ‖zetaQuartetTwist a0 gam (2 + (t : ℂ) * I)‖ := by
  set m : ℝ := 2 - Real.pi ^ 2 / 6 with hm
  have hmpos : 0 < m := by
    have hpi := Real.pi_lt_d2
    have hpi0 := Real.pi_pos
    have hsq : Real.pi ^ 2 < (3.15 : ℝ) ^ 2 := by nlinarith
    rw [hm]
    norm_num at hsq ⊢
    linarith
  set Q0 : ℝ := ‖offLineQuartet a0 gam 0‖ with hQ0
  have hQ0pos : 0 < Q0 := norm_pos_iff.mpr (offLineQuartet_zero_ne_zero ha0 ha1 gam)
  set K : ℝ := max 1 (B * Q0 / m + 1) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKB : B * Q0 / m + 1 ≤ K := le_max_right _ _
  refine ⟨|gam| + K, ?_⟩
  have ht : |gam| ≤ |gam| + K := by linarith
  have hre : (2 + ((|gam| + K : ℝ) : ℂ) * I).re = 2 := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
  have hζ := norm_riemannZeta_ge_of_re_eq_two hre
  have hQ := norm_offLineQuartet_ge a0 gam ht
  have hK4 : K ≤ (|gam| + K - |gam|) ^ 4 := by
    have hsimp : (|gam| + K - |gam|) = K := by ring
    rw [hsimp]
    have hK3 : 1 ≤ K ^ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hK1) (by nlinarith [hK1] : (0 : ℝ) ≤ K ^ 2 + K + 1)]
    calc K = K * 1 := (mul_one K).symm
      _ ≤ K * K ^ 3 := mul_le_mul_of_nonneg_left hK3 (by linarith)
      _ = K ^ 4 := by ring
  unfold zetaQuartetTwist
  rw [norm_mul, norm_div]
  have h1 : m * (K / Q0) ≤
      ‖riemannZeta (2 + ((|gam| + K : ℝ) : ℂ) * I)‖ *
        (‖offLineQuartet a0 gam (2 + ((|gam| + K : ℝ) : ℂ) * I)‖ / Q0) :=
    mul_le_mul hζ (div_le_div_of_nonneg_right (le_trans hK4 hQ) hQ0pos.le)
      (by positivity) (norm_nonneg _)
  have h2 : B < m * (K / Q0) := by
    have hlt : B * Q0 / m < K := by linarith
    rw [div_lt_iff₀ hmpos] at hlt
    rw [← mul_div_assoc, lt_div_iff₀ hQ0pos]
    linarith
  linarith

/-- **The twisted zeta is not an absolutely convergent Dirichlet series on `Re s = 2`.**  No
coefficients `c` with `Σ ‖c_n‖ (n+1)^{-2} < ∞` represent `ζ_Q(2 + it) = Σ c_n (n+1)^{-(2+it)}` for all
real `t`: every such series is bounded on the line, and `ζ_Q` is not. -/
theorem zetaQuartetTwist_not_dirichletSeries {a0 : ℝ} (ha0 : 0 < a0) (ha1 : a0 < 1 / 2)
    (gam : ℝ) :
    ¬ ∃ c : ℕ → ℂ, Summable (fun n : ℕ => ‖c n‖ / ((n : ℝ) + 1) ^ 2) ∧
        ∀ t : ℝ, zetaQuartetTwist a0 gam (2 + (t : ℂ) * I)
          = ∑' n : ℕ, c n / ((n : ℂ) + 1) ^ (2 + (t : ℂ) * I) := by
  rintro ⟨c, hc, hrep⟩
  obtain ⟨t, ht⟩ := exists_norm_zetaQuartetTwist_gt ha0 ha1 gam
    (∑' n : ℕ, ‖c n‖ / ((n : ℝ) + 1) ^ 2)
  have hre : (2 + (t : ℂ) * I).re = 2 := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
  have hnorm : ∀ n : ℕ, ‖c n / ((n : ℂ) + 1) ^ (2 + (t : ℂ) * I)‖ = ‖c n‖ / ((n : ℝ) + 1) ^ 2 := by
    intro n
    rw [norm_div, norm_natCast_add_one_cpow_re_two hre]
  have hbound : ‖zetaQuartetTwist a0 gam (2 + (t : ℂ) * I)‖
      ≤ ∑' n : ℕ, ‖c n‖ / ((n : ℝ) + 1) ^ 2 := by
    rw [hrep t]
    calc ‖∑' n : ℕ, c n / ((n : ℂ) + 1) ^ (2 + (t : ℂ) * I)‖
        ≤ ∑' n : ℕ, ‖c n / ((n : ℂ) + 1) ^ (2 + (t : ℂ) * I)‖ :=
          norm_tsum_le_tsum_norm (by simp_rw [hnorm]; exact hc)
      _ = ∑' n : ℕ, ‖c n‖ / ((n : ℝ) + 1) ^ 2 := by simp_rw [hnorm]
  linarith

end

end RHTower
