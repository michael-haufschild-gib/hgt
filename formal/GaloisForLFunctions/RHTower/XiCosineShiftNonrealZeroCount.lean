import GaloisForLFunctions.RHTower.EvenOrderOnePartialFractionZeroCount
import GaloisForLFunctions.RHTower.XiCosineShiftDefectHeightPowerSaving
import GaloisForLFunctions.RHTower.XiLocalZeroDensity
import GaloisForLFunctions.RHTower.GammaVerticalRatioAsymptotic
import GaloisForLFunctions.HTGeometry.ZetaTailBound
import GaloisForLFunctions.RHTower.FarFieldAnchor

/-!
# Counting the non-real zeros of `cos(hD)Ξ`

For `0 < h ≤ ½` let `A_h(z) = (Ξ(z + ih) + Ξ(z − ih))/2`. Every zero of `A_h` has `|Im z| ≤ ½`.

* `exists_norm_logDeriv_cosineShift_le`: at `z₀ = x − i(3/2 + h)`,
  `A_h(z₀) = (ξ(2 + ix) + ξ(2 + 2h + ix))/2`. The second term dominates by a factor `≍ x^h`
  (`eventually_norm_xi_two_le_half`, Stirling with `ζ` near `1` right of `Re s = 2`). Hence
  `‖A_h'/A_h(z₀)‖ ≤ C log x`.
* With the symmetrised partial fraction (`card_le_of_even_strip`), the zeros of `A_h` within unit
  horizontal distance of `x` number `O(log x)`.
* `exists_card_cosineShift_nonrealZeros_le`: every non-real zero of `A_h` with real part in
  `[T + ½, 2T − ½]` lies within `½` of the ordinate of a zero `ρ` of `ξ` with `Re ρ > ½ + h`.
  By Ingham–Huxley, these zeros, counted with multiplicity, number at most
  `D (1 + log T)^{B+1} T^{(A(½ + h) + ε)(½ − h)}`.

`A_h` has `≍ T log T` zeros with real part in `[T, 2T]`. So for every `h > 0` all but a power-saving
proportion of them are real, unconditionally.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.EntireZeroDivisor

namespace RHTower

noncomputable section

/-! ## Bounds right of `Re s = 2` -/

theorem exists_norm_logDeriv_riemannZeta_le_of_two_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 2 ≤ s.re → ‖logDeriv riemannZeta s‖ ≤ C := by
  have hsum2 : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖) :=
    summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num))
  refine ⟨∑' n : ℕ, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖,
    tsum_nonneg fun _ => norm_nonneg _, fun s hs => ?_⟩
  have hs1 : 1 < s.re := by linarith
  have hterm : ∀ n : ℕ,
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖
        ≤ ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs with hn
    · exact le_rfl
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have h2 : ((2 : ℂ)).re = 2 := by norm_num
      rw [h2]
      apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hn1 hs
  have hsums : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖) :=
    hsum2.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  rw [logDeriv_riemannZeta_eq_neg_LSeries hs1, norm_neg, LSeries]
  exact (norm_tsum_le_tsum_norm hsums).trans (hsums.tsum_le_tsum hterm hsum2)

/-- `ξ'/ξ` is `O(log t)` on every vertical line `Re s = σ ≥ 2`. -/
theorem exists_norm_logDeriv_xi_le {σ : ℝ} (hσ : 2 ≤ σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      ‖logDeriv xi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * Real.log t := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_norm_logDeriv_riemannZeta_le_of_two_le
  set C : ℝ := 3 / 2 + |Real.log Real.pi| / 2 + C₀ + 2 with hCdef
  have hC0 : 0 < C := by rw [hCdef]; positivity
  refine ⟨C, hC0, ?_⟩
  have hdig : ∀ᶠ u : ℝ in atTop,
      ‖Complex.digamma (((σ / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ 2 * Real.log u :=
    GaloisForLFunctions.norm_digamma_vertical_le_two_log (by linarith)
  have hhalf : Tendsto (fun t : ℝ => t / 2) atTop atTop :=
    Filter.tendsto_id.atTop_div_const (by norm_num)
  filter_upwards [hhalf.eventually hdig, Filter.eventually_ge_atTop (3 : ℝ),
    (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ))] with t hdt ht3 hlog1
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hre : s.re = σ := by rw [hs]; simp
  have hsplit := logDeriv_xi_split (s := s) (by rw [hre]; linarith)
  have hsnorm : (2 : ℝ) ≤ ‖s‖ := by
    have := Complex.abs_re_le_norm s
    rw [hre, abs_of_pos (by linarith)] at this
    linarith
  have hs1norm : (1 : ℝ) ≤ ‖s - 1‖ := by
    have hre1 : (s - 1).re = σ - 1 := by rw [Complex.sub_re, hre]; norm_num
    have := Complex.abs_re_le_norm (s - 1)
    rw [hre1, abs_of_pos (by linarith)] at this
    linarith
  have hinv1 : ‖s⁻¹‖ ≤ 1 / 2 := by
    rw [norm_inv, one_div]; gcongr
  have hinv2 : ‖(s - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv, inv_le_one_iff₀]; right; exact hs1norm
  have hgamma : ‖logDeriv Complex.Gammaℝ s‖ ≤ |Real.log Real.pi| / 2 + Real.log t := by
    have hsre : (0 : ℝ) < s.re := by rw [hre]; linarith
    have hhalfs : s / 2 = ((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
      rw [hs]; push_cast; ring
    rw [logDeriv_Gammaℝ_eq hsre, hhalfs]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖-((Real.log Real.pi : ℂ) / 2)‖ = |Real.log Real.pi| / 2 := by
      rw [norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs]; norm_num
    have h2 : ‖Complex.digamma (((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I) / 2‖ ≤ Real.log t := by
      rw [norm_div]
      have hlog : Real.log (t / 2) ≤ Real.log t := Real.log_le_log (by linarith) (by linarith)
      have h2norm : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2norm]
      linarith
    linarith
  have hzeta : ‖logDeriv riemannZeta s‖ ≤ C₀ := hC₀ s (by rw [hre]; exact hσ)
  have hfinal : ‖logDeriv xi s‖ ≤ 3 / 2 + |Real.log Real.pi| / 2 + C₀ + Real.log t := by
    rw [hsplit]
    calc ‖s⁻¹ + (s - 1)⁻¹ + logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s‖
        ≤ ‖s⁻¹‖ + ‖(s - 1)⁻¹‖ + ‖logDeriv Complex.Gammaℝ s‖ + ‖logDeriv riemannZeta s‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ 3 / 2 + |Real.log Real.pi| / 2 + C₀ + Real.log t := by linarith
  have hCpos : (0 : ℝ) ≤ 3 / 2 + |Real.log Real.pi| / 2 + C₀ + 1 := by positivity
  have hmul : 3 / 2 + |Real.log Real.pi| / 2 + C₀ + Real.log t ≤ C * Real.log t := by
    rw [hCdef]; nlinarith [hlog1, hCpos]
  linarith

/-- `ξ = s(s−1)/2 · Γ_ℝ · ζ` right of `Re s = 1`. -/
theorem xi_eq_mul_Gammaℝ_zeta {s : ℂ} (hs : 1 < s.re) :
    xi s = s * (s - 1) / 2 * (Complex.Gammaℝ s * riemannZeta s) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [xi_eq_half_mul hs0 hs1, riemannZeta_def_of_ne_zero hs0]
  field_simp

theorem norm_Gammaℝ_eq_rpow_mul (s : ℂ) :
    ‖Complex.Gammaℝ s‖ = Real.pi ^ (-s.re / 2) * ‖Complex.Gamma (s / 2)‖ := by
  rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 2
  simp

/-- **Dominance.** For `h > 0`, eventually `‖ξ(2 + ix)‖ ≤ ½‖ξ(2 + 2h + ix)‖`. -/
theorem eventually_norm_xi_two_le_half {h : ℝ} (hh : 0 < h) :
    ∀ᶠ x : ℝ in atTop,
      ‖xi ((2 : ℂ) + (x : ℂ) * I)‖ ≤ 1 / 2 * ‖xi (((2 + 2 * h : ℝ) : ℂ) + (x : ℂ) * I)‖ := by
  -- the Gamma ratio
  have hΓ := gamma_vertical_ratio_norm_rpow_tendsto (a := 1) (δ := h) (by norm_num) hh.le
  have hΓev : ∀ᶠ τ : ℝ in atTop,
      Real.exp (Real.log ‖Complex.Gamma ((1 : ℝ) + (τ : ℂ) * I)‖ -
        Real.log ‖Complex.Gamma (((1 + h : ℝ) : ℂ) + (τ : ℂ) * I)‖) * τ ^ h ≤ 2 :=
    hΓ.eventually (ge_mem_nhds (by norm_num))
  have hhalf : Tendsto (fun x : ℝ => x / 2) atTop atTop :=
    Filter.tendsto_id.atTop_div_const (by norm_num)
  -- the constant
  set q : ℝ := 1 - 4 * (2 : ℝ) ^ (-(2 + 2 * h)) with hqdef
  have hq : 0 < q := by
    have h1 : (2 : ℝ) ^ (-(2 + 2 * h)) < (2 : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    have h2 : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    have h3 := mul_lt_mul_of_pos_left h1 (by norm_num : (0 : ℝ) < 4)
    rw [h2] at h3
    rw [hqdef]; linarith
  set K : ℝ := Real.pi ^ h * 2 * (2 / q) with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  -- `K (x/2)^{-h} → 0`
  have hdecay : Tendsto (fun x : ℝ => K * (x / 2) ^ (-h)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop hh).comp hhalf
    simpa using this.const_mul K
  filter_upwards [hhalf.eventually hΓev, hdecay.eventually (ge_mem_nhds (by norm_num :
      (0 : ℝ) < 1 / 2)), eventually_ge_atTop (2 : ℝ)] with x hx hdx hx2
  set s₁ : ℂ := (2 : ℂ) + (x : ℂ) * I with hs₁
  set s₂ : ℂ := ((2 + 2 * h : ℝ) : ℂ) + (x : ℂ) * I with hs₂
  have hs₁re : s₁.re = 2 := by rw [hs₁]; simp
  have hs₂re : s₂.re = 2 + 2 * h := by rw [hs₂]; simp
  have hs₁im : s₁.im = x := by rw [hs₁]; simp
  have hs₂im : s₂.im = x := by rw [hs₂]; simp
  rw [xi_eq_mul_Gammaℝ_zeta (by rw [hs₁re]; norm_num),
    xi_eq_mul_Gammaℝ_zeta (by rw [hs₂re]; linarith)]
  -- polynomial factors
  have hnorm_le : ∀ u v : ℂ, 0 ≤ u.re → u.re ≤ v.re → u.im = v.im → ‖u‖ ≤ ‖v‖ := by
    intro u v h0 h1 h2
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply, h2]
    nlinarith
  have hP : ‖s₁‖ * ‖s₁ - 1‖ ≤ ‖s₂‖ * ‖s₂ - 1‖ :=
    mul_le_mul (hnorm_le s₁ s₂ (by rw [hs₁re]; norm_num) (by rw [hs₁re, hs₂re]; linarith)
        (by rw [hs₁im, hs₂im]))
      (hnorm_le (s₁ - 1) (s₂ - 1) (by rw [Complex.sub_re, hs₁re]; norm_num)
        (by rw [Complex.sub_re, Complex.sub_re, hs₁re, hs₂re]; linarith)
        (by rw [Complex.sub_im, Complex.sub_im, hs₁im, hs₂im]))
      (norm_nonneg _) (norm_nonneg _)
  -- Gamma factors
  have hG : ‖Complex.Gammaℝ s₁‖ ≤
      ‖Complex.Gammaℝ s₂‖ * (Real.pi ^ h * 2 * (x / 2) ^ (-h)) := by
    rw [norm_Gammaℝ_eq_rpow_mul, norm_Gammaℝ_eq_rpow_mul, hs₁re, hs₂re]
    have e1 : s₁ / 2 = ((1 : ℝ) : ℂ) + ((x / 2 : ℝ) : ℂ) * I := by rw [hs₁]; push_cast; ring
    have e2 : s₂ / 2 = ((1 + h : ℝ) : ℂ) + ((x / 2 : ℝ) : ℂ) * I := by rw [hs₂]; push_cast; ring
    rw [e1, e2]
    set Γ₁ := ‖Complex.Gamma (((1 : ℝ) : ℂ) + ((x / 2 : ℝ) : ℂ) * I)‖ with hΓ₁
    set Γ₂ := ‖Complex.Gamma (((1 + h : ℝ) : ℂ) + ((x / 2 : ℝ) : ℂ) * I)‖ with hΓ₂
    have hΓ₁0 : 0 < Γ₁ := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp))
    have hΓ₂0 : 0 < Γ₂ := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
    have hτ : 0 < x / 2 := by linarith
    have hratio : Γ₁ / Γ₂ * (x / 2) ^ h ≤ 2 := by
      have := hx
      rw [Real.exp_sub, Real.exp_log hΓ₁0, Real.exp_log hΓ₂0] at this
      exact this
    have hΓle : Γ₁ ≤ 2 * Γ₂ * (x / 2) ^ (-h) := by
      have hpow : (x / 2) ^ (-h) * (x / 2) ^ h = 1 := by
        rw [← Real.rpow_add hτ]; simp
      have hpos : 0 < (x / 2) ^ h := Real.rpow_pos_of_pos hτ h
      rw [div_mul_eq_mul_div, div_le_iff₀ hΓ₂0] at hratio
      calc Γ₁ = Γ₁ * ((x / 2) ^ h * (x / 2) ^ (-h)) := by rw [mul_comm ((x / 2) ^ h), hpow, mul_one]
        _ = Γ₁ * (x / 2) ^ h * (x / 2) ^ (-h) := by ring
        _ ≤ 2 * Γ₂ * (x / 2) ^ (-h) :=
            mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hτ.le _)
    have hπ1 : Real.pi ^ (-(2 : ℝ) / 2) = Real.pi ^ (-(2 + 2 * h) / 2) * Real.pi ^ h := by
      rw [← Real.rpow_add Real.pi_pos]; congr 1; ring
    rw [hπ1]
    have hπpos : 0 < Real.pi ^ (-(2 + 2 * h) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
    have hπh : 0 < Real.pi ^ h := Real.rpow_pos_of_pos Real.pi_pos _
    calc Real.pi ^ (-(2 + 2 * h) / 2) * Real.pi ^ h * Γ₁
        ≤ Real.pi ^ (-(2 + 2 * h) / 2) * Real.pi ^ h * (2 * Γ₂ * (x / 2) ^ (-h)) :=
          mul_le_mul_of_nonneg_left hΓle (by positivity)
      _ = Real.pi ^ (-(2 + 2 * h) / 2) * Γ₂ * (Real.pi ^ h * 2 * (x / 2) ^ (-h)) := by ring
  -- zeta factors
  have hZ1 : ‖riemannZeta s₁‖ ≤ 2 := by
    have h1 := GaloisForLFunctions.HTGeometry.norm_riemannZeta_sub_one_le_rpow (s := s₁) (by rw [hs₁re])
    rw [hs₁re, Real.rpow_neg (by norm_num)] at h1
    have h2 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
    rw [h2] at h1
    have := norm_le_norm_add_norm_sub' (riemannZeta s₁) 1
    have h3 : ‖riemannZeta s₁ - 1‖ ≤ 1 := by linarith [show 4 * (4 : ℝ)⁻¹ = 1 by norm_num]
    rw [norm_one] at this
    linarith
  have hZ2 : q ≤ ‖riemannZeta s₂‖ := by
    have h1 := GaloisForLFunctions.HTGeometry.norm_riemannZeta_sub_one_le_rpow (s := s₂) (by rw [hs₂re]; linarith)
    rw [hs₂re] at h1
    have := norm_sub_norm_le (1 : ℂ) (riemannZeta s₂)
    rw [norm_one, norm_sub_rev] at this
    rw [hqdef]
    linarith
  have hZ : ‖riemannZeta s₁‖ ≤ ‖riemannZeta s₂‖ * (2 / q) := by
    have : 2 ≤ ‖riemannZeta s₂‖ * (2 / q) := by
      rw [mul_div_assoc', le_div_iff₀ hq]; nlinarith
    linarith
  -- assemble
  simp only [norm_mul, norm_div, Complex.norm_two]
  have hR : 0 ≤ ‖s₂‖ * ‖s₂ - 1‖ / 2 * (‖Complex.Gammaℝ s₂‖ * ‖riemannZeta s₂‖) := by positivity
  have hdx' : Real.pi ^ h * 2 * (x / 2) ^ (-h) * (2 / q) ≤ 1 / 2 := by
    have : Real.pi ^ h * 2 * (x / 2) ^ (-h) * (2 / q) = K * (x / 2) ^ (-h) := by rw [hK]; ring
    rw [this]; exact hdx
  calc ‖s₁‖ * ‖s₁ - 1‖ / 2 * (‖Complex.Gammaℝ s₁‖ * ‖riemannZeta s₁‖)
      ≤ ‖s₂‖ * ‖s₂ - 1‖ / 2 * ((‖Complex.Gammaℝ s₂‖ * (Real.pi ^ h * 2 * (x / 2) ^ (-h))) *
          (‖riemannZeta s₂‖ * (2 / q))) := by
        gcongr
    _ = ‖s₂‖ * ‖s₂ - 1‖ / 2 * (‖Complex.Gammaℝ s₂‖ * ‖riemannZeta s₂‖) *
          (Real.pi ^ h * 2 * (x / 2) ^ (-h) * (2 / q)) := by ring
    _ ≤ ‖s₂‖ * ‖s₂ - 1‖ / 2 * (‖Complex.Gammaℝ s₂‖ * ‖riemannZeta s₂‖) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hdx' hR
    _ = 1 / 2 * (‖s₂‖ * ‖s₂ - 1‖ / 2 * (‖Complex.Gammaℝ s₂‖ * ‖riemannZeta s₂‖)) := by ring

/-! ## The logarithmic derivative of the cosine shift below the strip -/

theorem hasDerivAt_XiC (w : ℂ) : HasDerivAt XiC (deriv xi (1 / 2 + w * I) * I) w := by
  have hin : HasDerivAt (fun w : ℂ => 1 / 2 + w * I) I w := by
    simpa using ((hasDerivAt_id w).mul_const I).const_add (1 / 2 : ℂ)
  have := (xi_differentiable (1 / 2 + w * I)).hasDerivAt.comp w hin
  have hfun : XiC = fun x => xi (1 / 2 + x * I) := by
    funext x; simp only [XiC]
  rw [hfun]
  simpa [Function.comp_def] using this

/-- `‖A_h'/A_h(x − i(3/2 + h))‖ = O(log x)`. -/
theorem exists_norm_logDeriv_cosineShift_le {h : ℝ} (hh : 0 < h) (hh2 : h ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ‖logDeriv (fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2)
        ((x : ℂ) - ((3 / 2 + h : ℝ) : ℂ) * I)‖ ≤ C * Real.log x := by
  obtain ⟨C₁, hC₁, hL₁⟩ := exists_norm_logDeriv_xi_le (σ := 2) le_rfl
  obtain ⟨C₂, hC₂, hL₂⟩ := exists_norm_logDeriv_xi_le (σ := 2 + 2 * h) (by linarith)
  refine ⟨C₁ + 2 * C₂, by positivity, ?_⟩
  filter_upwards [hL₁, hL₂, eventually_norm_xi_two_le_half hh, eventually_ge_atTop (1 : ℝ)]
    with x h1 h2 hdom hx1
  set z₀ : ℂ := (x : ℂ) - ((3 / 2 + h : ℝ) : ℂ) * I with hz₀
  set s₁ : ℂ := (2 : ℂ) + (x : ℂ) * I with hs₁
  set s₂ : ℂ := ((2 + 2 * h : ℝ) : ℂ) + (x : ℂ) * I with hs₂
  have e1 : 1 / 2 + (z₀ + h * I) * I = s₁ := by
    rw [hz₀, hs₁]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have e2 : 1 / 2 + (z₀ - h * I) * I = s₂ := by
    rw [hz₀, hs₂]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have h1' : ‖logDeriv xi s₁‖ ≤ C₁ * Real.log x := by
    have : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
    rw [this] at h1; exact h1
  have hs₁re : s₁.re = 2 := by rw [hs₁]; simp
  have hs₂re : s₂.re = 2 + 2 * h := by rw [hs₂]; simp
  have hx₁ : xi s₁ ≠ 0 := xi_ne_zero_of_one_lt_re (by rw [hs₁re]; norm_num)
  have hx₂ : xi s₂ ≠ 0 := xi_ne_zero_of_one_lt_re (by rw [hs₂re]; linarith)
  -- the derivative
  have hA : HasDerivAt (fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2)
      ((deriv xi s₁ * I + deriv xi s₂ * I) / 2) z₀ := by
    have d1 := (hasDerivAt_XiC (z₀ + h * I)).comp z₀ ((hasDerivAt_id z₀).add_const (h * I))
    have d2 := (hasDerivAt_XiC (z₀ - h * I)).comp z₀ ((hasDerivAt_id z₀).sub_const (h * I))
    rw [e1] at d1
    rw [e2] at d2
    have := (d1.add d2).div_const 2
    simpa [Function.comp_def] using this
  have hval : (XiC (z₀ + h * I) + XiC (z₀ - h * I)) / 2 = (xi s₁ + xi s₂) / 2 := by
    rw [XiC, XiC, e1, e2]
  have hd1 : deriv xi s₁ = logDeriv xi s₁ * xi s₁ := by
    rw [logDeriv_apply, div_mul_cancel₀ _ hx₁]
  have hd2 : deriv xi s₂ = logDeriv xi s₂ * xi s₂ := by
    rw [logDeriv_apply, div_mul_cancel₀ _ hx₂]
  rw [logDeriv_apply, hA.deriv, hval, hd1, hd2]
  set L₁ := logDeriv xi s₁
  set L₂ := logDeriv xi s₂
  have hden : ‖xi s₂‖ / 2 ≤ ‖xi s₁ + xi s₂‖ := by
    have := norm_sub_norm_le (xi s₂) (-xi s₁)
    rw [sub_neg_eq_add, norm_neg, add_comm] at this
    linarith
  have hx₂n : 0 < ‖xi s₂‖ := norm_pos_iff.mpr hx₂
  have hsumne : xi s₁ + xi s₂ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hden; linarith
  have hnum : ‖L₁ * xi s₁ * I + L₂ * xi s₂ * I‖ ≤ ‖L₁‖ * ‖xi s₁‖ + ‖L₂‖ * ‖xi s₂‖ := by
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_I, mul_one]
    exact le_rfl
  have heq : (L₁ * xi s₁ * I + L₂ * xi s₂ * I) / 2 / ((xi s₁ + xi s₂) / 2) =
      (L₁ * xi s₁ * I + L₂ * xi s₂ * I) / (xi s₁ + xi s₂) := by
    field_simp
  rw [heq, norm_div, div_le_iff₀ (norm_pos_iff.mpr hsumne)]
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hL₁n := norm_nonneg L₁
  calc ‖L₁ * xi s₁ * I + L₂ * xi s₂ * I‖
      ≤ ‖L₁‖ * ‖xi s₁‖ + ‖L₂‖ * ‖xi s₂‖ := hnum
    _ ≤ ‖L₁‖ * (1 / 2 * ‖xi s₂‖) + ‖L₂‖ * ‖xi s₂‖ := by gcongr
    _ = (‖L₁‖ + 2 * ‖L₂‖) * (‖xi s₂‖ / 2) := by ring
    _ ≤ ((C₁ + 2 * C₂) * Real.log x) * ‖xi s₁ + xi s₂‖ := by
        apply mul_le_mul _ hden (by positivity) (by positivity)
        nlinarith

/-! ## The count -/

/-- **Non-real zeros of `cos(hD)Ξ` are power-sparse.** For `0 < h ≤ ½` and `0 < ε ≤ 1` there are
`D, B, T₀` such that for `T ≥ T₀` every finite set of divisor copies of non-real zeros of `cos(hD)Ξ`
with real parts in `[T + ½, 2T − ½]` has at most `D (1 + log T)^{B+1} T^{(A(½ + h) + ε)(½ − h)}`
elements. -/
theorem exists_card_cosineShift_nonrealZeros_le {h ε : ℝ} (hh : 0 < h) (hh2 : h ≤ 1 / 2)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ P : Finset (ZeroCopy (fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2)),
        (∀ p ∈ P, (zeroCopyPoint _ p).im ≠ 0 ∧ T + 1 / 2 ≤ (zeroCopyPoint _ p).re ∧
          (zeroCopyPoint _ p).re ≤ 2 * T - 1 / 2) →
        (P.card : ℝ) ≤ D * (1 + Real.log T) ^ (B + 1) *
          T ^ ((inghamHuxleyExponent (1 / 2 + h) + ε) * (1 / 2 - h)) := by
  classical
  set f : ℂ → ℂ := fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2 with hfdef
  have hg := DeBruijn.riemannKernel_mul_cosh_superExp h
  have hF : DeBruijn.cosTransform (fun x => riemannKernelReal x * Real.cosh (h * x)) = f :=
    funext (DeBruijn.cosTransform_riemannKernel_mul_cosh h)
  obtain ⟨C₀, hC₀0, hC₀⟩ := hg.exists_envelope
  have hfan : AnalyticOnNhd ℂ f univ := by
    rw [← hF]; exact hg.differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hf0 : f 0 ≠ 0 := by rw [← hF]; exact hg.cosTransform_zero_ne
  have heven : ∀ z, f (-z) = f z := by rw [← hF]; exact hg.cosTransform_neg
  have hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C₀ * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
    rw [← hF]; exact hC₀
  have hstrip0 : ∀ w, f w = 0 → |w.im| ≤ 1 / 2 := by
    intro w hw
    have h1 := DeBruijn.cosineShift_zeros_im_sq_le hh hw
    have h2 : max (1 / 4 - h ^ 2) 0 ≤ (1 / 2) ^ 2 := max_le (by nlinarith) (by norm_num)
    have := sq_le_sq.mp (h1.trans h2)
    rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
  obtain ⟨D₁, hD₁, B, T₁, hT₁, hIH⟩ :=
    exists_zeroHeightBox_ncard_le_ingham_huxley (σ := 1 / 2 + h) (by linarith) (by linarith) hε hε1
  obtain ⟨C, hC, hev⟩ := exists_norm_logDeriv_cosineShift_le hh hh2
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hev
  refine ⟨29 * C * D₁, by positivity, B, max T₁ (max X₀ 2), le_trans hT₁ (le_max_left _ _),
    fun T hT P hP => ?_⟩
  have hTT₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT
  have hTX : X₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT2 : 2 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hfin := zeroHeightBox_finite (1 / 2 + h) T
  set Z := hfin.toFinset with hZ
  set Fq : XiZeroCopy → Finset (ZeroCopy f) := fun q =>
    P.filter (fun p => |(zeroCopyPoint f p).re - (q.1 : ℂ).im| < 1 / 2) with hFq
  -- every element of `P` sits in the fibre of a deep zero in the box
  have hcover : P ⊆ Z.biUnion Fq := by
    intro p hp
    obtain ⟨hpim, hplo, hphi⟩ := hP p hp
    have hzero : (XiC (zeroCopyPoint f p + h * I) + XiC (zeroCopyPoint f p - h * I)) / 2 = 0 :=
      DeBruijn.apply_zeroCopyPoint hfan p
    obtain ⟨q, hqre, hqim⟩ := exists_xiZeroCopy_of_cosineShift_nonreal hh hpim hzero
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hqim
    refine Finset.mem_biUnion.mpr ⟨q, ?_, ?_⟩
    · rw [hZ, Set.Finite.mem_toFinset]
      exact ⟨hqre.le, by linarith, by linarith⟩
    · rw [hFq, Finset.mem_filter]
      refine ⟨hp, ?_⟩
      rw [abs_sub_comm]; exact abs_lt.mpr ⟨by linarith, by linarith⟩
  -- each fibre is `O(log T)`
  have hfibre : ∀ q ∈ Z, ((Fq q).card : ℝ) ≤ 29 * C * (1 + Real.log T) := by
    intro q hq
    rw [hZ, Set.Finite.mem_toFinset] at hq
    obtain ⟨-, hqlo, hqhi⟩ := hq
    have hcount := card_le_of_even_strip hC₀0 hfan hf0 heven hbound hstrip0
      (x₀ := (q.1 : ℂ).im) (Y := 3 / 2 + h) (by linarith) (by linarith) (Fq q) (by
        intro p hp
        rw [hFq, Finset.mem_filter] at hp
        exact hp.2.le.trans (by norm_num))
    have hlogd := hX₀ ((q.1 : ℂ).im) (by linarith)
    have hlogT : Real.log ((q.1 : ℂ).im) ≤ 1 + Real.log T := by
      have hqpos : 0 < (q.1 : ℂ).im := by linarith
      have h1 : Real.log ((q.1 : ℂ).im) ≤ Real.log (2 * T) := Real.log_le_log hqpos hqhi
      rw [Real.log_mul (by norm_num) (by linarith)] at h1
      have h2 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; linarith
      linarith
    calc ((Fq q).card : ℝ) ≤ 29 * ‖logDeriv f (((q.1 : ℂ).im : ℂ) -
          ((3 / 2 + h : ℝ) : ℂ) * I)‖ := hcount
      _ ≤ 29 * (C * Real.log ((q.1 : ℂ).im)) := by gcongr
      _ ≤ 29 * C * (1 + Real.log T) := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hlogT (by positivity)
  have hZcard : (Z.card : ℝ) ≤ D₁ * (1 + Real.log T) ^ B *
      T ^ ((inghamHuxleyExponent (1 / 2 + h) + ε) * (1 / 2 - h)) := by
    have := hIH T hTT₁
    rw [show (1 : ℝ) - (1 / 2 + h) = 1 / 2 - h by ring] at this
    rw [hZ, ← Set.ncard_eq_toFinset_card _ hfin]
    exact this
  have hlog1 : 0 ≤ 1 + Real.log T := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T); linarith
  calc (P.card : ℝ) ≤ ((Z.biUnion Fq).card : ℝ) := by exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ q ∈ Z, ((Fq q).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ q ∈ Z, 29 * C * (1 + Real.log T) := Finset.sum_le_sum hfibre
    _ = (Z.card : ℝ) * (29 * C * (1 + Real.log T)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (D₁ * (1 + Real.log T) ^ B *
          T ^ ((inghamHuxleyExponent (1 / 2 + h) + ε) * (1 / 2 - h))) *
          (29 * C * (1 + Real.log T)) :=
        mul_le_mul_of_nonneg_right hZcard (by positivity)
    _ = 29 * C * D₁ * (1 + Real.log T) ^ (B + 1) *
          T ^ ((inghamHuxleyExponent (1 / 2 + h) + ε) * (1 / 2 - h)) := by
        rw [pow_succ]; ring

end

end RHTower
