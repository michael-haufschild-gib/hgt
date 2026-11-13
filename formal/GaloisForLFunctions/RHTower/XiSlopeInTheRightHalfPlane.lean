import GaloisForLFunctions.RHTower.XiHorizontalStripComparison
import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic
import GaloisForLFunctions.HTGeometry.LogLinearGronwallModel

/-!
# The slope of `ξ` in the right half-plane

On `Re s ≥ 5` the logarithmic derivative of `ξ` is the slope `xiSlope s = ½ log(s/2π)` up to
`4/‖s‖ + 2^{5 − Re s}/12` (`norm_logDeriv_xi_sub_xiSlope_le`): the four-factor formula, Stirling's
formula for the digamma function, and `Λ(n) n^{−σ} ≤ n^{−4} 2^{5−σ}` for the prime part.

Consequences, all for points of real part at least `5`:

* **two-point comparison** (`norm_xi_sub_mul_exp_le`): if `‖ξ'/ξ − a‖ ≤ η` on the segment from `p`
  to `q`, then `ξ(q) = ξ(p) e^{(q−p)a}` up to the relative error `e^{η‖q−p‖} − 1`;
* **growth to the right** (`norm_xi_add_le_mul_exp`) and **to the left** (`norm_xi_sub_le_mul_exp`,
  from `Re ξ'/ξ ≥ −4`);
* the slope varies by at most `‖s − s'‖/(2m)` on a segment of points of modulus at least `m`.

In the strip `−Y ≤ Re s ≤ 5` the modulus of `ξ` is at most a power of the height times its
modulus at real part `5` (`exists_norm_xi_le_strip`).
-/

open Complex Set

namespace RHTower

noncomputable section

/-- The model slope of `ξ`: `½ log(s/2π)`. -/
def xiSlope (s : ℂ) : ℂ := (Complex.log s - (Real.log (2 * Real.pi) : ℂ)) / 2

theorem xiSlope_re (s : ℂ) : (xiSlope s).re = (Real.log ‖s‖ - Real.log (2 * Real.pi)) / 2 := by
  simp [xiSlope, Complex.log_re]

theorem xiSlope_im (s : ℂ) : (xiSlope s).im = Complex.arg s / 2 := by
  simp [xiSlope, Complex.log_im]

theorem abs_xiSlope_im_lt {s : ℂ} (hs : 0 < s.re) : |(xiSlope s).im| < Real.pi / 4 := by
  rw [xiSlope_im, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hs)
  linarith

theorem xiSlope_sub (s s' : ℂ) :
    xiSlope s - xiSlope s' = (Complex.log s - Complex.log s') / 2 := by
  simp only [xiSlope]; ring

/-- The slope varies by at most `‖s − s'‖/(2m)` along a segment in the right half-plane whose
points have modulus at least `m`. -/
theorem norm_xiSlope_sub_le {s s' : ℂ} {m : ℝ} (hm : 0 < m)
    (hseg : ∀ w ∈ segment ℝ s' s, 0 < w.re ∧ m ≤ ‖w‖) :
    ‖xiSlope s - xiSlope s'‖ ≤ ‖s - s'‖ / (2 * m) := by
  have hd : ∀ w ∈ segment ℝ s' s, HasDerivWithinAt Complex.log w⁻¹ (segment ℝ s' s) w :=
    fun w hw => (Complex.hasStrictDerivAt_log
      (Complex.mem_slitPlane_iff.2 (Or.inl (hseg w hw).1))).hasDerivAt.hasDerivWithinAt
  have hb : ∀ w ∈ segment ℝ s' s, ‖w⁻¹‖ ≤ 1 / m := fun w hw => by
    rw [norm_inv, ← one_div]
    exact one_div_le_one_div_of_le hm (hseg w hw).2
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_segment s' s)
    (left_mem_segment ℝ s' s) (right_mem_segment ℝ s' s)
  rw [xiSlope_sub, norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
  calc ‖Complex.log s - Complex.log s'‖ / 2 ≤ 1 / m * ‖s - s'‖ / 2 := by gcongr
    _ = ‖s - s'‖ / (2 * m) := by field_simp

/-- A bound for the variation of the slope between any two points of the right half-plane. -/
theorem norm_xiSlope_sub_le_log {s s' : ℂ} (hs : 0 < s.re) (hs' : 0 < s'.re) :
    ‖xiSlope s - xiSlope s'‖ ≤ (|Real.log ‖s‖ - Real.log ‖s'‖| + Real.pi) / 2 := by
  rw [xiSlope_sub, norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
  gcongr
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im, Complex.log_re, Complex.log_re, Complex.log_im,
    Complex.log_im]
  have h1 := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hs))
  have h2 := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hs'))
  have : |Complex.arg s - Complex.arg s'| ≤ Real.pi := by
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  linarith

/-! ## The prime part decays -/

/-- `‖ζ'/ζ(s)‖ ≤ 2^{5 − Re s}/12` on `Re s ≥ 5`. -/
theorem norm_logDeriv_riemannZeta_le_two_rpow {s : ℂ} (hs : 5 ≤ s.re) :
    ‖logDeriv riemannZeta s‖ ≤ (2 : ℝ) ^ (5 - s.re) / 12 := by
  have hre : 1 < s.re := by linarith
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
  have hlog : logDeriv riemannZeta s =
      -LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s := by
    rw [hL, logDeriv_apply]; ring
  rw [hlog, norm_neg, LSeries]
  set c : ℝ := (2 : ℝ) ^ (5 - s.re) with hc
  have hc0 : 0 < c := by positivity
  set f : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ s.re with hf
  set g : ℕ → ℝ := fun n => c * (1 / (n : ℝ) ^ 4 - if n = 1 then 1 else 0) with hg
  have hterm : ∀ n : ℕ,
      ‖LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s n‖ = f n := by
    intro n
    rw [LSeries.norm_term_eq]
    split_ifs with h0
    · subst h0; simp [hf]
    · rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hfg : ∀ n, f n ≤ g n := by
    intro n
    simp only [hf, hg]
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp
    · have hn1 : n ≠ 1 := by omega
      rw [if_neg hn1, sub_zero]
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < n := by linarith
      have hΛ : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) :=
        ArithmeticFunction.vonMangoldt_le_log.trans
          ((Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith))
      have hsplit : (n : ℝ) ^ s.re = (n : ℝ) ^ 4 * (n : ℝ) * (n : ℝ) ^ (s.re - 5) := by
        have h5 : (n : ℝ) ^ 4 * (n : ℝ) = (n : ℝ) ^ (5 : ℝ) := by norm_cast
        rw [h5, ← Real.rpow_add hn0]
        congr 1; ring
      have hpow : (2 : ℝ) ^ (s.re - 5) ≤ (n : ℝ) ^ (s.re - 5) :=
        Real.rpow_le_rpow (by norm_num) hn2 (by linarith)
      have hcinv : c * (2 : ℝ) ^ (s.re - 5) = 1 := by
        rw [hc, ← Real.rpow_add (by norm_num)]; simp
      have h4 : (n : ℝ) ^ 4 ≠ 0 := by positivity
      rw [hsplit, div_le_iff₀ (by positivity)]
      calc ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) := hΛ
        _ = c * (2 : ℝ) ^ (s.re - 5) * n := by rw [hcinv, one_mul]
        _ ≤ c * (n : ℝ) ^ (s.re - 5) * n := by gcongr
        _ = c * (1 / (n : ℝ) ^ 4) * ((n : ℝ) ^ 4 * (n : ℝ) * (n : ℝ) ^ (s.re - 5)) := by
            field_simp
  have hg_sum : HasSum g (c * (Real.pi ^ 4 / 90 - 1)) :=
    (hasSum_zeta_four.sub (hasSum_ite_eq 1 (1 : ℝ))).mul_left c
  have hf0 : ∀ n, 0 ≤ f n := fun n =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hf_sum : Summable f := Summable.of_nonneg_of_le hf0 hfg hg_sum.summable
  have hnorm_sum : Summable fun n =>
      ‖LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s n‖ := by
    simp_rw [hterm]; exact hf_sum
  calc ‖∑' n, LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s n‖
      ≤ ∑' n, ‖LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s n‖ :=
        norm_tsum_le_tsum_norm hnorm_sum
    _ = ∑' n, f n := by simp_rw [hterm]
    _ ≤ c * (Real.pi ^ 4 / 90 - 1) := hasSum_le hfg hf_sum.hasSum hg_sum
    _ ≤ c / 12 := by
        have h := mul_le_mul_of_nonneg_left pi_pow_four_div_ninety_sub_one_le hc0.le
        linarith

/-! ## The slope -/

/-- **The slope of `ξ`.** On `Re s ≥ 5`, `‖ξ'/ξ(s) − ½ log(s/2π)‖ ≤ 4/‖s‖ + 2^{5 − Re s}/12`. -/
theorem norm_logDeriv_xi_sub_xiSlope_le {s : ℂ} (hs : 5 ≤ s.re) :
    ‖logDeriv xi s - xiSlope s‖ ≤ 4 / ‖s‖ + (2 : ℝ) ^ (5 - s.re) / 12 := by
  have hre : 1 < s.re := by linarith
  have hnorm : 5 ≤ ‖s‖ := hs.trans (Complex.re_le_norm s)
  have hr0 : 0 < ‖s‖ := by linarith
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hnorm
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hhalf : Complex.log (s / 2) = Complex.log s - (Real.log 2 : ℂ) := by
    have h2 : s / 2 = ((2⁻¹ : ℝ) : ℂ) * s := by push_cast; ring
    rw [h2, Complex.log_ofReal_mul (by norm_num) hs0, Real.log_inv]
    push_cast; ring
  have hn2 : ‖s / 2‖ = ‖s‖ / 2 := by rw [norm_div]; simp
  have hre2 : 0 < (s / 2).re := by
    have h : (s / 2).re = s.re / 2 := by simp
    rw [h]; linarith
  have hdig := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_add_half_inv_le_of_re_pos
    hre2 (by rw [hn2]; linarith)
  have hpi : (Real.log (2 * Real.pi) : ℂ) = (Real.log 2 : ℂ) + (Real.log Real.pi : ℂ) := by
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero]; push_cast; ring
  have hkey : logDeriv xi s - xiSlope s =
      1 / (2 * s) + 1 / (s - 1)
        + (Complex.digamma (s / 2) - Complex.log (s / 2) + 1 / (2 * (s / 2))) / 2
        + logDeriv riemannZeta s := by
    rw [logDeriv_xi_fourFactor hre, xiSlope, hhalf, hpi]
    field_simp
    ring
  have h1 : ‖(1 : ℂ) / (2 * s)‖ = 1 / (2 * ‖s‖) := by
    rw [norm_div, norm_one, norm_mul]; simp
  have h2 : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 / (‖s‖ - 1) := by
    rw [norm_div, norm_one]
    have h := norm_sub_norm_le s 1
    rw [norm_one] at h
    exact one_div_le_one_div_of_le (by linarith) h
  have h3 : ‖(Complex.digamma (s / 2) - Complex.log (s / 2) + 1 / (2 * (s / 2))) / 2‖ ≤
      10 / ‖s‖ ^ 2 := by
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
    calc _ ≤ 5 / ‖s / 2‖ ^ (2 : ℕ) / 2 := by gcongr
      _ = 10 / ‖s‖ ^ 2 := by rw [hn2]; field_simp; ring
  have e1 : 1 / (‖s‖ - 1) ≤ (5 / 4) / ‖s‖ := by
    rw [div_le_div_iff₀ (by linarith) hr0]; linarith
  have e2 : 10 / ‖s‖ ^ 2 ≤ 2 / ‖s‖ := by
    rw [div_le_div_iff₀ (by positivity) hr0]; nlinarith
  have e3 : 1 / (2 * ‖s‖) = (1 / 2) / ‖s‖ := by field_simp
  have e4 : (1 / 2) / ‖s‖ + (5 / 4) / ‖s‖ + 2 / ‖s‖ ≤ 4 / ‖s‖ := by
    rw [← add_div, ← add_div]; gcongr; norm_num
  rw [hkey]
  refine (norm_add₄_le).trans ?_
  have hz := norm_logDeriv_riemannZeta_le_two_rpow hs
  rw [h1]
  linarith

/-- `‖ξ'/ξ − xiSlope‖ ≤ 1` on `Re s ≥ 5`. -/
theorem norm_logDeriv_xi_sub_xiSlope_le_one {s : ℂ} (hs : 5 ≤ s.re) :
    ‖logDeriv xi s - xiSlope s‖ ≤ 1 := by
  have hnorm : 5 ≤ ‖s‖ := hs.trans (Complex.re_le_norm s)
  have h1 : 4 / ‖s‖ ≤ 4 / 5 := by gcongr
  have h2 : (2 : ℝ) ^ (5 - s.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  linarith [norm_logDeriv_xi_sub_xiSlope_le hs]

private theorem log_two_pi_le : Real.log (2 * Real.pi) ≤ 6 := by
  have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)
  linarith [Real.pi_lt_d2]

/-- `Re ξ'/ξ ≥ −4` on `Re s ≥ 5`. -/
theorem neg_four_le_re_logDeriv_xi {s : ℂ} (hs : 5 ≤ s.re) : -4 ≤ (logDeriv xi s).re := by
  have hnorm : 5 ≤ ‖s‖ := hs.trans (Complex.re_le_norm s)
  have h1 := norm_logDeriv_xi_sub_xiSlope_le_one hs
  have h2 : -1 ≤ (logDeriv xi s - xiSlope s).re :=
    (abs_le.1 ((Complex.abs_re_le_norm _).trans h1)).1
  rw [Complex.sub_re, xiSlope_re] at h2
  have h3 : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (by linarith)
  linarith [log_two_pi_le]

/-- `‖ξ'/ξ(s)‖ ≤ ½ log‖s‖ + 5` on `Re s ≥ 5`. -/
theorem norm_logDeriv_xi_le {s : ℂ} (hs : 5 ≤ s.re) :
    ‖logDeriv xi s‖ ≤ Real.log ‖s‖ / 2 + 5 := by
  have hnorm : 5 ≤ ‖s‖ := hs.trans (Complex.re_le_norm s)
  have h1 := norm_logDeriv_xi_sub_xiSlope_le_one hs
  have h3 : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (by linarith)
  have h4 : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hsl : ‖xiSlope s‖ ≤ Real.log ‖s‖ / 2 + 4 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have him := abs_xiSlope_im_lt (s := s) (by linarith)
    rw [xiSlope_re]
    have : |(Real.log ‖s‖ - Real.log (2 * Real.pi)) / 2| ≤ Real.log ‖s‖ / 2 + 3 := by
      rw [abs_le]; constructor <;> linarith [log_two_pi_le]
    linarith [Real.pi_lt_d2]
  calc ‖logDeriv xi s‖ = ‖(logDeriv xi s - xiSlope s) + xiSlope s‖ := by ring_nf
    _ ≤ ‖logDeriv xi s - xiSlope s‖ + ‖xiSlope s‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-! ## Comparison of two values -/

/-- **Two-point comparison.** If `‖ξ'/ξ − a‖ ≤ η` on the segment from `p` to `q`, on which
`Re > 1`, then `‖ξ(q) − ξ(p) e^{(q−p)a}‖ ≤ ‖ξ(p)‖ e^{Re((q−p)a)} (e^{η‖q−p‖} − 1)`. -/
theorem norm_xi_sub_mul_exp_le {p q a : ℂ} {η : ℝ} (hη : 0 < η)
    (hseg : ∀ w ∈ segment ℝ p q, 1 < w.re ∧ ‖logDeriv xi w - a‖ ≤ η) :
    ‖xi q - xi p * Complex.exp ((q - p) * a)‖ ≤
      ‖xi p‖ * Real.exp (((q - p) * a).re) * (Real.exp (η * ‖q - p‖) - 1) := by
  rcases eq_or_ne q p with rfl | hne
  · simp
  set d : ℂ := q - p with hd
  have hd0 : 0 < ‖d‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  set F : ℝ → ℂ := fun x => xi (p + x * d) with hF
  set F' : ℝ → ℂ := fun x => d * deriv xi (p + x * d) with hF'
  have hmem : ∀ x ∈ uIcc (0 : ℝ) 1, p + (x : ℂ) * d ∈ segment ℝ p q := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    rw [segment_eq_image']
    exact ⟨x, hx, by simp [hd]⟩
  have hFd : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt F (F' x) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => p + (y : ℂ) * d) d x := by
      have := ((hasDerivAt_id' x).ofReal_comp.mul_const d).const_add p
      simpa using this
    have := (xi_differentiable (p + x * d)).hasDerivAt.scomp x h1
    simpa [hF, hF', Function.comp_def, smul_eq_mul] using this
  have hε : ∀ x ∈ uIcc (0 : ℝ) 1, ‖F' x - (d * a) * F x‖ ≤ (η * ‖d‖) * ‖F x‖ := by
    intro x hx
    obtain ⟨hre, hdev⟩ := hseg _ (hmem x hx)
    have hne : xi (p + x * d) ≠ 0 := xi_ne_zero_of_one_lt_re hre
    have hderiv : deriv xi (p + x * d) = logDeriv xi (p + x * d) * xi (p + x * d) := by
      rw [logDeriv_apply, div_mul_cancel₀ _ hne]
    simp only [hF, hF']
    rw [hderiv, show d * (logDeriv xi (p + ↑x * d) * xi (p + ↑x * d)) - d * a * xi (p + ↑x * d) =
        d * (logDeriv xi (p + ↑x * d) - a) * xi (p + ↑x * d) by ring, norm_mul, norm_mul]
    calc ‖d‖ * ‖logDeriv xi (p + ↑x * d) - a‖ * ‖xi (p + ↑x * d)‖
        ≤ ‖d‖ * η * ‖xi (p + ↑x * d)‖ := by gcongr
      _ = η * ‖d‖ * ‖xi (p + ↑x * d)‖ := by ring
  have h := GaloisForLFunctions.HTGeometry.norm_sub_mul_exp_le (F := F) (F' := F') (a := d * a)
    (η := η * ‖d‖) (u := 0) (w := 1) (by positivity) hFd hε
  simp only [hF] at h
  have e1 : p + ((1 : ℝ) : ℂ) * d = q := by simp [hd]
  have e0 : p + ((0 : ℝ) : ℂ) * d = p := by simp
  have e2 : (((1 - 0 : ℝ) : ℂ) * (d * a)) = d * a := by simp
  have e3 : (1 - 0 : ℝ) * (d * a).re = (d * a).re := by simp
  have e4 : η * ‖d‖ * |(1 : ℝ) - 0| = η * ‖d‖ := by simp
  rw [e1, e0, e2, e3, e4] at h
  exact h

/-- Upper form of the two-point comparison. -/
theorem norm_xi_le_mul_exp {p q a : ℂ} {η : ℝ} (hη : 0 < η)
    (hseg : ∀ w ∈ segment ℝ p q, 1 < w.re ∧ ‖logDeriv xi w - a‖ ≤ η) :
    ‖xi q‖ ≤ ‖xi p‖ * Real.exp (((q - p) * a).re + η * ‖q - p‖) := by
  have h := norm_xi_sub_mul_exp_le hη hseg
  have hn : ‖xi p * Complex.exp ((q - p) * a)‖ = ‖xi p‖ * Real.exp (((q - p) * a).re) := by
    rw [norm_mul, Complex.norm_exp]
  have ht := norm_le_norm_add_norm_sub' (xi q) (xi p * Complex.exp ((q - p) * a))
  rw [hn] at ht
  rw [Real.exp_add, ← mul_assoc]
  nlinarith

/-- Lower form of the two-point comparison. -/
theorem le_norm_xi_of_logDeriv {p q a : ℂ} {η : ℝ} (hη : 0 < η)
    (hseg : ∀ w ∈ segment ℝ p q, 1 < w.re ∧ ‖logDeriv xi w - a‖ ≤ η) :
    ‖xi p‖ * Real.exp (((q - p) * a).re) * (2 - Real.exp (η * ‖q - p‖)) ≤ ‖xi q‖ := by
  have h := norm_xi_sub_mul_exp_le hη hseg
  have hn : ‖xi p * Complex.exp ((q - p) * a)‖ = ‖xi p‖ * Real.exp (((q - p) * a).re) := by
    rw [norm_mul, Complex.norm_exp]
  have ht := norm_le_norm_add_norm_sub (xi q) (xi p * Complex.exp ((q - p) * a))
  rw [hn] at ht
  nlinarith

/-! ## Growth along horizontal lines -/

/-- One-sided Grönwall: `Re(F'/F) ≤ K` on `[u, w]` gives `‖F(w)‖ ≤ ‖F(u)‖ e^{K(w−u)}`. -/
theorem norm_le_mul_exp_of_re_le {F F' : ℝ → ℂ} {K u w : ℝ} (huw : u ≤ w)
    (hF : ∀ x ∈ Icc u w, HasDerivAt F (F' x) x)
    (hK : ∀ x ∈ Icc u w, (F' x * starRingEnd ℂ (F x)).re ≤ K * ‖F x‖ ^ 2) :
    ‖F w‖ ≤ ‖F u‖ * Real.exp (K * (w - u)) := by
  set φ : ℝ → ℝ := fun x => ‖F x‖ ^ 2 * Real.exp (-(2 * K) * (x - u)) with hφ
  have hN : ∀ x ∈ Icc u w,
      HasDerivAt (fun y => ‖F y‖ ^ 2) (2 * (F' x * starRingEnd ℂ (F x)).re) x := by
    intro x hx
    have hG : HasDerivAt (fun y => F y * star (F y))
        (F' x * star (F x) + F x * star (F' x)) x := (hF x hx).mul (hF x hx).star
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hG
    have e : (fun y => ‖F y‖ ^ 2) = (⇑Complex.reCLM ∘ fun y => F y * star (F y)) := by
      funext y
      simp only [Function.comp_apply, Complex.reCLM_apply, Complex.star_def, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    have hval : Complex.reCLM (F' x * star (F x) + F x * star (F' x)) =
        2 * (F' x * starRingEnd ℂ (F x)).re := by
      simp only [Complex.reCLM_apply, Complex.star_def, Complex.add_re, Complex.mul_re,
        Complex.conj_re, Complex.conj_im]
      ring
    rw [e, ← hval]
    exact h
  have hφd : ∀ x ∈ Icc u w, HasDerivAt φ
      ((2 * (F' x * starRingEnd ℂ (F x)).re - 2 * K * ‖F x‖ ^ 2) *
        Real.exp (-(2 * K) * (x - u))) x := by
    intro x hx
    have hE : HasDerivAt (fun y : ℝ => Real.exp (-(2 * K) * (y - u)))
        (Real.exp (-(2 * K) * (x - u)) * (-(2 * K) * 1)) x :=
      (((hasDerivAt_id' x).sub_const u).const_mul (-(2 * K))).exp
    exact ((hN x hx).mul hE).congr_deriv (by ring)
  have hanti : AntitoneOn φ (Icc u w) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc u w)
      (fun x hx => (hφd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hφd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
      fun x hx => ?_
    have hx' := interior_subset hx
    rw [(hφd x hx').deriv]
    have := hK x hx'
    have hpos := Real.exp_pos (-(2 * K) * (x - u))
    nlinarith
  have hle := hanti (left_mem_Icc.2 huw) (right_mem_Icc.2 huw) huw
  simp only [hφ, sub_self, mul_zero, Real.exp_zero, mul_one] at hle
  have hsq : ‖F w‖ ^ 2 ≤ (‖F u‖ * Real.exp (K * (w - u))) ^ 2 := by
    have hcancel : Real.exp (-(2 * K) * (w - u)) * Real.exp (K * (w - u)) ^ 2 = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      have : -(2 * K) * (w - u) + ((2 : ℕ) : ℝ) * (K * (w - u)) = 0 := by push_cast; ring
      rw [this, Real.exp_zero]
    calc ‖F w‖ ^ 2 = ‖F w‖ ^ 2 * Real.exp (-(2 * K) * (w - u)) * Real.exp (K * (w - u)) ^ 2 := by
          rw [mul_assoc, hcancel, mul_one]
      _ ≤ ‖F u‖ ^ 2 * Real.exp (K * (w - u)) ^ 2 := by gcongr
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- **Growth to the left at a given slope.** If `Re ξ'/ξ ≥ K` on the horizontal segment from
`s − v` to `s`, in `Re ≥ 5`, then `‖ξ(s − v)‖ ≤ ‖ξ(s)‖ e^{−Kv}`. -/
theorem norm_xi_sub_le_mul_exp_of_le {s : ℂ} {v K : ℝ} (hv : 0 ≤ v) (hs : 5 ≤ s.re - v)
    (hK : ∀ x ∈ Icc (0 : ℝ) v, K ≤ (logDeriv xi (s - x)).re) :
    ‖xi (s - v)‖ ≤ ‖xi s‖ * Real.exp (-K * v) := by
  set F : ℝ → ℂ := fun x => xi (s - x) with hF
  set F' : ℝ → ℂ := fun x => -deriv xi (s - x) with hF'
  have hFd : ∀ x ∈ Icc (0 : ℝ) v, HasDerivAt F (F' x) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => s - (y : ℂ)) (-1) x := by
      have := ((hasDerivAt_id' x).ofReal_comp).const_sub s
      simpa using this
    have := (xi_differentiable (s - x)).hasDerivAt.scomp x h1
    simpa [hF, hF', Function.comp_def, smul_eq_mul] using this
  have hK' : ∀ x ∈ Icc (0 : ℝ) v, (F' x * starRingEnd ℂ (F x)).re ≤ -K * ‖F x‖ ^ 2 := by
    intro x hx
    have hre : 5 ≤ (s - (x : ℂ)).re := by simp; linarith [hx.2]
    have hne : xi (s - x) ≠ 0 := xi_ne_zero_of_one_lt_re (by linarith)
    have hderiv : deriv xi (s - x) = logDeriv xi (s - x) * xi (s - x) := by
      rw [logDeriv_apply, div_mul_cancel₀ _ hne]
    simp only [hF, hF']
    rw [hderiv, show -(logDeriv xi (s - ↑x) * xi (s - ↑x)) * (starRingEnd ℂ) (xi (s - ↑x)) =
        -(logDeriv xi (s - ↑x)) * (xi (s - ↑x) * (starRingEnd ℂ) (xi (s - ↑x))) by ring,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.re_mul_ofReal, Complex.neg_re]
    have := hK x hx
    nlinarith [sq_nonneg ‖xi (s - ↑x)‖]
  have h := norm_le_mul_exp_of_re_le hv hFd hK'
  simpa [hF] using h

/-- **Growth to the left.** `‖ξ(s − v)‖ ≤ ‖ξ(s)‖ e^{4v}` while `Re(s − v) ≥ 5`. -/
theorem norm_xi_sub_le_mul_exp {s : ℂ} {v : ℝ} (hv : 0 ≤ v) (hs : 5 ≤ s.re - v) :
    ‖xi (s - v)‖ ≤ ‖xi s‖ * Real.exp (4 * v) := by
  have h := norm_xi_sub_le_mul_exp_of_le (K := -4) hv hs fun x hx =>
    neg_four_le_re_logDeriv_xi (by simp; linarith [hx.2])
  rwa [neg_neg] at h

/-- **Growth to the right.** `‖ξ(s + v)‖ ≤ ‖ξ(s)‖ exp(v(½ log(‖s‖ + v) + 5))` for `Re s ≥ 5`. -/
theorem norm_xi_add_le_mul_exp {s : ℂ} {v : ℝ} (hs : 5 ≤ s.re) (hv : 0 ≤ v) :
    ‖xi (s + v)‖ ≤ ‖xi s‖ * Real.exp (v * (Real.log (‖s‖ + v) / 2 + 5)) := by
  set F : ℝ → ℂ := fun x => xi (s + x) with hF
  set F' : ℝ → ℂ := fun x => deriv xi (s + x) with hF'
  have hnorm : 5 ≤ ‖s‖ := hs.trans (Complex.re_le_norm s)
  have hFd : ∀ x ∈ Icc (0 : ℝ) v, HasDerivAt F (F' x) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => s + (y : ℂ)) 1 x := by
      have := ((hasDerivAt_id' x).ofReal_comp).const_add s
      simpa using this
    have := (xi_differentiable (s + x)).hasDerivAt.scomp x h1
    simpa [hF, hF', Function.comp_def, smul_eq_mul] using this
  have hK : ∀ x ∈ Icc (0 : ℝ) v, ‖F' x‖ ≤ (Real.log (‖s‖ + v) / 2 + 5) * ‖F x‖ := by
    intro x hx
    have hre : 5 ≤ (s + (x : ℂ)).re := by simp; linarith [hx.1]
    have hne : xi (s + x) ≠ 0 := xi_ne_zero_of_one_lt_re (by linarith)
    have hderiv : deriv xi (s + x) = logDeriv xi (s + x) * xi (s + x) := by
      rw [logDeriv_apply, div_mul_cancel₀ _ hne]
    simp only [hF, hF']
    rw [hderiv, norm_mul]
    gcongr
    refine (norm_logDeriv_xi_le hre).trans ?_
    have hpos : 0 < ‖s + (x : ℂ)‖ := by linarith [hre.trans (Complex.re_le_norm _)]
    have hle : ‖s + (x : ℂ)‖ ≤ ‖s‖ + v := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
      linarith [hx.2]
    have := Real.log_le_log hpos hle
    linarith
  have h := GaloisForLFunctions.HTGeometry.norm_le_mul_exp_of_norm_deriv_le_Icc hv hFd hK
  have e : (Real.log (‖s‖ + v) / 2 + 5) * (v - 0) = v * (Real.log (‖s‖ + v) / 2 + 5) := by ring
  rw [e] at h
  simpa [hF] using h

/-! ## The strip -/

theorem norm_xi_reflect (σ X : ℝ) :
    ‖xi ((σ : ℂ) + X * I)‖ = ‖xi (((1 - σ : ℝ) : ℂ) + X * I)‖ := by
  have h : ((1 - σ : ℝ) : ℂ) + X * I = starRingEnd ℂ (1 - ((σ : ℂ) + X * I)) := by
    apply Complex.ext <;> simp
  rw [h, xi_conj, Complex.norm_conj, xi_one_sub]

theorem norm_xi_neg_height (σ X : ℝ) :
    ‖xi ((σ : ℂ) + ((-X : ℝ) : ℂ) * I)‖ = ‖xi ((σ : ℂ) + X * I)‖ := by
  have h : (σ : ℂ) + ((-X : ℝ) : ℂ) * I = starRingEnd ℂ ((σ : ℂ) + X * I) := by
    apply Complex.ext <;> simp
  rw [h, xi_conj, Complex.norm_conj]

/-- In the strip `−4 ≤ Re s ≤ 5`, at every height, `‖ξ(σ + iX)‖ ≤ C (1 + |X|) ‖ξ(5 + iX)‖`. -/
theorem exists_norm_xi_le_strip_four :
    ∃ C : ℝ, 0 < C ∧ ∀ σ X : ℝ, -4 ≤ σ → σ ≤ 5 →
      ‖xi ((σ : ℂ) + X * I)‖ ≤ C * (1 + |X|) * ‖xi ((5 : ℝ) + X * I)‖ := by
  -- the compact part `|X| ≤ 8`
  have hcont : Continuous fun p : ℝ × ℝ => ‖xi ((p.1 : ℂ) + p.2 * I)‖ := by
    have := xi_differentiable.continuous
    fun_prop
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := ((-4 : ℝ), (-8 : ℝ))) (b := ((5 : ℝ), (8 : ℝ)))).exists_bound_of_continuousOn
    hcont.continuousOn
  have hcont5 : Continuous fun X : ℝ => ‖xi (((5 : ℝ) : ℂ) + X * I)‖ := by
    have := xi_differentiable.continuous
    fun_prop
  obtain ⟨X₀, -, hX₀⟩ := (isCompact_Icc (a := (-8 : ℝ)) (b := 8)).exists_isMinOn
    ⟨0, by norm_num⟩ hcont5.continuousOn
  set m : ℝ := ‖xi (((5 : ℝ) : ℂ) + X₀ * I)‖ with hm
  have hm0 : 0 < m := norm_pos_iff.2 (xi_ne_zero_of_one_lt_re (by simp))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM ((0 : ℝ), (0 : ℝ)) ⟨by constructor <;> norm_num,
    by constructor <;> norm_num⟩)
  -- large heights: the horizontal comparison and the two reflections
  have hbig : ∀ σ X : ℝ, 1 / 2 ≤ σ → σ ≤ 5 → 8 ≤ |X| →
      ‖xi ((σ : ℂ) + X * I)‖ ≤ 1200 * (1 + |X|) * ‖xi ((5 : ℝ) + X * I)‖ := by
    intro σ X h1 h5 hX
    have key : ∀ Z : ℝ, 8 ≤ Z →
        ‖xi ((σ : ℂ) + Z * I)‖ ≤ 1200 * (1 + Z) * ‖xi ((5 : ℝ) + Z * I)‖ := by
      intro Z hZ
      refine (norm_xi_horizontal_le_mul_norm_xi_five h1 h5 hZ).trans ?_
      have : 200 * (6 + Z) ≤ 1200 * (1 + Z) := by linarith
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    rcases le_total 0 X with h0 | h0
    · rw [abs_of_nonneg h0] at hX ⊢
      exact key X hX
    · rw [abs_of_nonpos h0] at hX ⊢
      have := key (-X) hX
      rwa [norm_xi_neg_height, norm_xi_neg_height] at this
  refine ⟨1200 + M / m, by positivity, fun σ X h4 h5 => ?_⟩
  have hXabs : 0 ≤ |X| := abs_nonneg X
  have h5pos : 0 ≤ ‖xi ((5 : ℝ) + X * I)‖ := norm_nonneg _
  rcases le_or_gt 8 |X| with hX | hX
  · have hb : ‖xi ((σ : ℂ) + X * I)‖ ≤ 1200 * (1 + |X|) * ‖xi ((5 : ℝ) + X * I)‖ := by
      rcases le_or_gt (1 / 2) σ with hσ | hσ
      · exact hbig σ X hσ h5 hX
      · rw [norm_xi_reflect]
        exact hbig (1 - σ) X (by linarith) (by linarith) hX
    refine hb.trans ?_
    have : 0 ≤ M / m := by positivity
    gcongr
    linarith
  · have hXI : X ∈ Icc (-8 : ℝ) 8 := by
      have := abs_lt.1 hX
      exact ⟨this.1.le, this.2.le⟩
    have h1 := hM (σ, X) ⟨⟨h4, hXI.1⟩, ⟨h5, hXI.2⟩⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h1
    have h2 : m ≤ ‖xi ((5 : ℝ) + X * I)‖ := hX₀ hXI
    calc ‖xi ((σ : ℂ) + X * I)‖ ≤ M := h1
      _ = M / m * m := by field_simp
      _ ≤ M / m * ‖xi ((5 : ℝ) + X * I)‖ := by gcongr
      _ ≤ (1200 + M / m) * (1 + |X|) * ‖xi ((5 : ℝ) + X * I)‖ := by
          have : M / m ≤ (1200 + M / m) * (1 + |X|) := by
            have : 0 ≤ M / m := by positivity
            nlinarith
          gcongr

/-- **The strip.** For `−Y ≤ σ ≤ 5`, `Y ≥ 4`, at every height,
`‖ξ(σ + iX)‖ ≤ C (1 + |X|) exp(Y(½ log(|X| + Y + 6) + 5)) ‖ξ(5 + iX)‖`. -/
theorem exists_norm_xi_le_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ Y σ X : ℝ, 4 ≤ Y → -Y ≤ σ → σ ≤ 5 →
      ‖xi ((σ : ℂ) + X * I)‖ ≤
        C * (1 + |X|) * Real.exp (Y * (Real.log (|X| + Y + 6) / 2 + 5)) *
          ‖xi ((5 : ℝ) + X * I)‖ := by
  obtain ⟨C, hC, hstrip⟩ := exists_norm_xi_le_strip_four
  refine ⟨C + 1, by linarith, fun Y σ X hY hσ h5 => ?_⟩
  have hXabs : 0 ≤ |X| := abs_nonneg X
  have h5pos : 0 ≤ ‖xi ((5 : ℝ) + X * I)‖ := norm_nonneg _
  have hlog : 0 ≤ Real.log (|X| + Y + 6) := Real.log_nonneg (by linarith)
  have hexp : 1 ≤ Real.exp (Y * (Real.log (|X| + Y + 6) / 2 + 5)) :=
    Real.one_le_exp (by positivity)
  rcases le_or_gt (-4) σ with h4 | h4
  · refine (hstrip σ X h4 h5).trans ?_
    have : C * (1 + |X|) ≤ (C + 1) * (1 + |X|) * Real.exp (Y * (Real.log (|X| + Y + 6) / 2 + 5)) := by
      have h0 : 0 ≤ (C + 1) * (1 + |X|) := by positivity
      nlinarith
    gcongr
  · -- reflect to real part `1 − σ > 5` and grow from real part `5`
    rw [norm_xi_reflect]
    set s5 : ℂ := ((5 : ℝ) : ℂ) + X * I with hs5
    have hs5re : s5.re = 5 := by simp [hs5]
    have hv : 0 ≤ (1 - σ) - 5 := by linarith
    have heq : ((1 - σ : ℝ) : ℂ) + X * I = s5 + (((1 - σ) - 5 : ℝ) : ℂ) := by
      simp only [hs5]; push_cast; ring
    have hg := norm_xi_add_le_mul_exp (s := s5) (v := (1 - σ) - 5) (by rw [hs5re]) hv
    rw [← heq] at hg
    have hn5 : ‖s5‖ ≤ 5 + |X| := by
      refine (norm_add_le _ _).trans ?_
      simp
    have h5le : 5 ≤ ‖s5‖ := by
      have := Complex.re_le_norm s5
      rwa [hs5re] at this
    have hpos5 : 0 < ‖s5‖ := by linarith
    have hlogle : Real.log (‖s5‖ + ((1 - σ) - 5)) ≤ Real.log (|X| + Y + 6) :=
      Real.log_le_log (by linarith) (by linarith)
    have hexple : Real.exp (((1 - σ) - 5) * (Real.log (‖s5‖ + ((1 - σ) - 5)) / 2 + 5)) ≤
        Real.exp (Y * (Real.log (|X| + Y + 6) / 2 + 5)) := by
      apply Real.exp_le_exp.2
      have h0 : 0 ≤ Real.log (‖s5‖ + ((1 - σ) - 5)) := Real.log_nonneg (by linarith)
      have h1 : (1 - σ) - 5 ≤ Y := by linarith
      nlinarith
    calc ‖xi (((1 - σ : ℝ) : ℂ) + X * I)‖
        ≤ ‖xi s5‖ * Real.exp (((1 - σ) - 5) * (Real.log (‖s5‖ + ((1 - σ) - 5)) / 2 + 5)) := hg
      _ ≤ ‖xi s5‖ * Real.exp (Y * (Real.log (|X| + Y + 6) / 2 + 5)) := by gcongr
      _ ≤ (C + 1) * (1 + |X|) * Real.exp (Y * (Real.log (|X| + Y + 6) / 2 + 5)) * ‖xi s5‖ := by
          have h0 : 1 ≤ (C + 1) * (1 + |X|) := by nlinarith
          have h1 : 0 ≤ Real.exp (Y * (Real.log (|X| + Y + 6) / 2 + 5)) * ‖xi s5‖ := by positivity
          nlinarith

/-! ## The slope relative to a base point -/

/-- A point of the right half-plane, to the right of `Re b − κ`, whose height differs from that of
`b` by at most `h`, has modulus at least `‖b‖/2 − h − κ`. -/
theorem le_norm_of_near_base {b w : ℂ} {κ h : ℝ} (hb : 0 ≤ b.re) (hκ : 0 ≤ κ)
    (hwκ : b.re - κ ≤ w.re) (him : |w.im - b.im| ≤ h) : ‖b‖ / 2 - h - κ ≤ ‖w‖ := by
  have hbn : ‖b‖ ≤ |b.re| + |b.im| := Complex.norm_le_abs_re_add_abs_im b
  have hc : 0 ≤ h := (abs_nonneg _).trans him
  rcases le_or_gt (‖b‖ / 2) |b.im| with h | h
  · have h1 : |b.im| - |w.im| ≤ |w.im - b.im| := by
      rw [abs_sub_comm]
      exact abs_sub_abs_le_abs_sub b.im w.im
    have h2 := Complex.abs_im_le_norm w
    linarith
  · have h1 : ‖b‖ / 2 < b.re := by
      rw [abs_of_nonneg hb] at hbn
      linarith
    have h2 := Complex.re_le_norm w
    linarith

/-- The slope at such a point differs from the slope at `b` by at most `‖w − b‖/(2m)`,
`m ≤ ‖b‖/2 − h − κ`. -/
theorem norm_xiSlope_sub_base_le {b w : ℂ} {κ h m : ℝ} (hb : 0 < b.re) (hw : 0 < w.re)
    (hκ : 0 ≤ κ) (hwκ : b.re - κ ≤ w.re) (him : |w.im - b.im| ≤ h) (hm : 0 < m)
    (hm' : m ≤ ‖b‖ / 2 - h - κ) : ‖xiSlope w - xiSlope b‖ ≤ ‖w - b‖ / (2 * m) := by
  refine norm_xiSlope_sub_le hm fun w' hw' => ?_
  rw [segment_eq_image'] at hw'
  obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hw'
  have hre : (b + θ • (w - b)).re = (1 - θ) * b.re + θ * w.re := by
    simp
    ring
  have him' : (b + θ • (w - b)).im - b.im = θ * (w.im - b.im) := by simp
  have h1θ : 0 ≤ 1 - θ := by linarith
  have hpos : 0 < (1 - θ) * b.re + θ * w.re := by
    have hμ : 0 < min b.re w.re := lt_min hb hw
    have e1 := mul_le_mul_of_nonneg_left (min_le_left b.re w.re) h1θ
    have e2 := mul_le_mul_of_nonneg_left (min_le_right b.re w.re) hθ0
    have e3 : (1 - θ) * min b.re w.re + θ * min b.re w.re = min b.re w.re := by ring
    linarith
  have hright : b.re - κ ≤ (1 - θ) * b.re + θ * w.re := by
    have e1 := mul_le_mul_of_nonneg_left (by linarith : b.re - κ ≤ b.re) h1θ
    have e2 := mul_le_mul_of_nonneg_left hwκ hθ0
    have e3 : (1 - θ) * (b.re - κ) + θ * (b.re - κ) = b.re - κ := by ring
    linarith
  have hheight : |(b + θ • (w - b)).im - b.im| ≤ h := by
    rw [him', abs_mul, abs_of_nonneg hθ0]
    exact (mul_le_of_le_one_left (abs_nonneg _) hθ1).trans him
  exact ⟨by rw [hre]; exact hpos,
    hm'.trans (le_norm_of_near_base hb.le hκ (by rw [hre]; exact hright) hheight)⟩

/-- **The slope relative to a base point.** For `Re w ≥ 5`, `Re w ≥ Re b − κ`,
`|Im w − Im b| ≤ h` and `0 < m ≤ ‖b‖/2 − h − κ`,
`‖ξ'/ξ(w) − xiSlope b‖ ≤ 4/m + 2^{5 − Re w}/12 + ‖w − b‖/(2m)`. -/
theorem norm_logDeriv_xi_sub_xiSlope_base_le {b w : ℂ} {κ h m : ℝ} (hb : 0 < b.re)
    (hw : 5 ≤ w.re) (hκ : 0 ≤ κ) (hwκ : b.re - κ ≤ w.re) (him : |w.im - b.im| ≤ h) (hm : 0 < m)
    (hm' : m ≤ ‖b‖ / 2 - h - κ) :
    ‖logDeriv xi w - xiSlope b‖ ≤ 4 / m + (2 : ℝ) ^ (5 - w.re) / 12 + ‖w - b‖ / (2 * m) := by
  have h1 := norm_logDeriv_xi_sub_xiSlope_le hw
  have h2 := norm_xiSlope_sub_base_le hb (by linarith) hκ hwκ him hm hm'
  have h3 : m ≤ ‖w‖ := hm'.trans (le_norm_of_near_base hb.le hκ hwκ him)
  have h4 : 4 / ‖w‖ ≤ 4 / m := div_le_div_of_nonneg_left (by norm_num) hm h3
  calc ‖logDeriv xi w - xiSlope b‖
      = ‖(logDeriv xi w - xiSlope w) + (xiSlope w - xiSlope b)‖ := by ring_nf
    _ ≤ ‖logDeriv xi w - xiSlope w‖ + ‖xiSlope w - xiSlope b‖ := norm_add_le _ _
    _ ≤ _ := by linarith

end

end RHTower
