import GaloisForLFunctions.RHTower.GammaJumpSymbolIdentity
import GaloisForLFunctions.HTGeometry.DigammaAsymptotic
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Logarithmic growth and reciprocal decay of the Gamma jump symbol

The Gamma jump symbol `r(η) = ψ(1+iη) + ψ(1−iη) + 2γ` is even and real, and equals
`2 Re ψ(1+iη) + 2γ`.  The vertical digamma bound therefore turns its growth into the exact
logarithm

`r(η) ≤ C log(2+|η|)`,

while termwise differentiation of the explicit series gives

`r'(η) = 4η Σ_{n≥1} n/(n²+η²)²`,   `|r'(η)| ≤ C/(1+|η|)`,

because `n² + η² ≥ 2n|η|` bounds each derivative term by `(n²+η²)^{-1}`, whose sum is the arctan
telescope.  These are the two symbol bounds an order-minus-one commutator estimate consumes.
-/

open Complex Filter

namespace GaloisForLFunctions.RHTower

noncomputable section

/-! ## The symbol as a real part -/

/-- The real part of digamma on a vertical line, as an explicit real series. -/
theorem re_digamma_vertical_series {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).re
      = -Real.eulerMascheroniConstant
        + ∑' n : ℕ, (1 / ((n : ℝ) + 1) - (σ + n) / ((σ + n) ^ 2 + t ^ 2)) := by
  have hre : (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ
  have h := _root_.RHTower.digamma_eq_neg_euler_add_tsum_gauss hre
  have hs := _root_.RHTower.summable_gaussDigammaSeriesTerm hre
  rw [h]
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  congr 1
  have hre_tsum :
      (∑' n : ℕ, _root_.RHTower.gaussDigammaSeriesTerm ((σ : ℂ) + (t : ℂ) * Complex.I) n).re
        = ∑' n : ℕ,
            (_root_.RHTower.gaussDigammaSeriesTerm ((σ : ℂ) + (t : ℂ) * Complex.I) n).re := by
    simpa using Complex.reCLM.map_tsum hs
  rw [hre_tsum]
  refine tsum_congr fun n => ?_
  have hn : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [_root_.RHTower.gaussDigammaSeriesTerm, Complex.sub_re, hn, one_div, one_div,
    ← Complex.ofReal_inv, Complex.ofReal_re, _root_.RHTower.re_inv_shift]
  ring

/-- The real part of digamma on a vertical line is even in the height. -/
theorem re_digamma_vertical_even {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    (Complex.digamma ((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)).re
      = (Complex.digamma ((σ : ℂ) + ((t : ℝ) : ℂ) * Complex.I)).re := by
  rw [re_digamma_vertical_series hσ (-t), re_digamma_vertical_series hσ t]
  congr 1
  exact tsum_congr fun n => by rw [neg_sq]

/-- **The jump multiplier is twice a digamma real part.** -/
theorem gammaJumpMultiplier_eq_re_digamma (η : ℝ) :
    gammaJumpMultiplier η
      = 2 * (Complex.digamma ((1 : ℂ) + (η : ℂ) * Complex.I)).re
        + 2 * Real.eulerMascheroniConstant := by
  have hid := gammaJumpSymbol_eq η
  have hre2 : (Complex.digamma ((1 : ℂ) + (η : ℂ) * Complex.I)).re
      + (Complex.digamma ((1 : ℂ) - (η : ℂ) * Complex.I)).re
      + 2 * Real.eulerMascheroniConstant = gammaJumpMultiplier η := by
    have hcongr := congrArg Complex.re hid
    rw [gammaJumpSymbol] at hcongr
    simpa using hcongr
  have heven : (Complex.digamma ((1 : ℂ) - (η : ℂ) * Complex.I)).re
      = (Complex.digamma ((1 : ℂ) + (η : ℂ) * Complex.I)).re := by
    have hminus : (1 : ℂ) - (η : ℂ) * Complex.I
        = ((1 : ℝ) : ℂ) + ((-η : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have hplus : (1 : ℂ) + (η : ℂ) * Complex.I
        = ((1 : ℝ) : ℂ) + ((η : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hminus, hplus]
    exact re_digamma_vertical_even (by norm_num : (0 : ℝ) < 1) η
  rw [← hre2, heven]
  ring

/-! ## Evenness -/

theorem gammaJumpTerm_neg (η : ℝ) (n : ℕ) : gammaJumpTerm (-η) n = gammaJumpTerm η n := by
  rw [gammaJumpTerm, gammaJumpTerm, neg_sq]

theorem gammaJumpMultiplier_neg (η : ℝ) :
    gammaJumpMultiplier (-η) = gammaJumpMultiplier η := by
  rw [gammaJumpMultiplier, gammaJumpMultiplier]
  congr 1
  exact tsum_congr fun n => gammaJumpTerm_neg η n

theorem gammaJumpMultiplier_abs (η : ℝ) :
    gammaJumpMultiplier |η| = gammaJumpMultiplier η := by
  rcases abs_choice η with h | h
  · rw [h]
  · rw [h, gammaJumpMultiplier_neg]

/-! ## The logarithmic growth bound -/

/-- **`r(η) = O(log(2+|η|))`.**  Past unit height the vertical digamma bound turns the symbol into
the logarithm of the modulus; below it the elementary linear bound already suffices. -/
theorem exists_gammaJumpMultiplier_log_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, gammaJumpMultiplier η ≤ C * Real.log (2 + |η|) := by
  set S : ℝ := ∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + 1) ^ 2) with hS
  have hSnn : 0 ≤ S := tsum_nonneg fun n => by positivity
  have hpi := Real.pi_pos
  set K : ℝ := max (2 * S) (4 + Real.pi + 2 * |Real.eulerMascheroniConstant|) with hK
  have hKnn : 0 ≤ K := le_trans (by positivity) (le_max_left _ _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 + K / Real.log 2, by positivity, fun η => ?_⟩
  have habs : 0 ≤ |η| := abs_nonneg η
  have hlogpos : Real.log 2 ≤ Real.log (2 + |η|) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlognn : 0 ≤ Real.log (2 + |η|) := le_trans hlog2.le hlogpos
  have hgamma : Real.eulerMascheroniConstant ≤ |Real.eulerMascheroniConstant| :=
    le_abs_self _
  have hcrude : gammaJumpMultiplier η ≤ 2 * Real.log (2 + |η|) + K := by
    rcases le_or_gt |η| 1 with hsmall | hbig
    · have h1 : gammaJumpMultiplier η ≤ S * (1 + |η|) :=
        le_trans (le_abs_self _) (abs_gammaJumpMultiplier_le η)
      have h2 : S * (1 + |η|) ≤ 2 * S := by nlinarith
      have h3 : 2 * S ≤ K := le_max_left _ _
      linarith
    · have hpos : (0 : ℝ) < |η| := lt_trans one_pos hbig
      have hbound := _root_.RHTower.re_digamma_vertical_bound_uncond
        (σ := 1) (t := |η|) (by norm_num) hpos
      rw [Complex.ofReal_one] at hbound
      have hup : (Complex.digamma ((1 : ℂ) + ((|η| : ℝ) : ℂ) * Complex.I)).re
          ≤ (1 / 2) * Real.log ((1 : ℝ) ^ 2 + |η| ^ 2)
            + (1 / |η| ^ 2 + Real.pi / (2 * |η|)) := by
        have := (abs_le.mp hbound).2
        linarith
      have hlogsq : Real.log ((1 : ℝ) ^ 2 + |η| ^ 2) ≤ 2 * Real.log (2 + |η|) := by
        have hle : (1 : ℝ) ^ 2 + |η| ^ 2 ≤ (2 + |η|) ^ 2 := by nlinarith
        have hmono := Real.log_le_log (by positivity) hle
        rwa [Real.log_pow] at hmono
      have hinv : 1 / |η| ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith
      have hinv2 : Real.pi / (2 * |η|) ≤ Real.pi / 2 := by
        apply div_le_div_of_nonneg_left hpi.le (by norm_num)
        nlinarith
      have hmul := gammaJumpMultiplier_eq_re_digamma |η|
      rw [gammaJumpMultiplier_abs] at hmul
      have hKge : 4 + Real.pi + 2 * |Real.eulerMascheroniConstant| ≤ K := le_max_right _ _
      rw [hmul]
      linarith [hup, hlogsq, hinv, hinv2, hgamma, hKge]
  have hKterm : K ≤ (K / Real.log 2) * Real.log (2 + |η|) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    nlinarith
  have hexp : (2 + K / Real.log 2) * Real.log (2 + |η|)
      = 2 * Real.log (2 + |η|) + (K / Real.log 2) * Real.log (2 + |η|) := by ring
  rw [hexp]
  linarith

/-! ## The derivative bound -/

/-- Each jump term is differentiable with the explicit derivative `2ηn/(n²+η²)²`. -/
theorem hasDerivAt_gammaJumpTerm (η : ℝ) (n : ℕ) :
    HasDerivAt (fun y : ℝ => gammaJumpTerm y n)
      (2 * η * ((n : ℝ) + 1) / ((((n : ℝ) + 1) ^ 2 + η ^ 2) ^ 2)) η := by
  set a : ℝ := (n : ℝ) + 1 with ha
  have hapos : (0 : ℝ) < a := by positivity
  have hAne : a * (a ^ 2 + η ^ 2) ≠ 0 := by positivity
  have hnum : HasDerivAt (fun y : ℝ => y ^ 2) (2 * η) η := by
    simpa using hasDerivAt_pow 2 η
  have hden : HasDerivAt (fun y : ℝ => a * (a ^ 2 + y ^ 2)) (a * (2 * η)) η := by
    have h1 : HasDerivAt (fun y : ℝ => a ^ 2 + y ^ 2) (2 * η) η := by
      simpa using (hasDerivAt_const η (a ^ 2)).add (by simpa using hasDerivAt_pow 2 η)
    simpa using h1.const_mul a
  have hdiv := hnum.div hden hAne
  have hrw : (2 * η * (a * (a ^ 2 + η ^ 2)) - η ^ 2 * (a * (2 * η)))
      / (a * (a ^ 2 + η ^ 2)) ^ 2 = 2 * η * a / ((a ^ 2 + η ^ 2) ^ 2) := by
    field_simp
    ring
  rw [hrw] at hdiv
  exact hdiv

/-- The derivative terms are dominated by the trigamma terms. -/
theorem abs_deriv_gammaJumpTerm_le (η : ℝ) (n : ℕ) :
    |2 * η * ((n : ℝ) + 1) / ((((n : ℝ) + 1) ^ 2 + η ^ 2) ^ 2)|
      ≤ 1 / (((n : ℝ) + 1) ^ 2 + η ^ 2) := by
  set a : ℝ := (n : ℝ) + 1 with ha
  have hapos : (0 : ℝ) < a := by positivity
  have hApos : (0 : ℝ) < a ^ 2 + η ^ 2 := by positivity
  have hamgm : 2 * |η| * a ≤ a ^ 2 + η ^ 2 := by
    nlinarith [sq_nonneg (a - |η|), sq_abs η, abs_nonneg η]
  have habs : |2 * η * a / ((a ^ 2 + η ^ 2) ^ 2)| = 2 * |η| * a / ((a ^ 2 + η ^ 2) ^ 2) := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (a ^ 2 + η ^ 2) ^ 2)]
    congr 1
    rw [abs_mul, abs_mul, abs_of_pos hapos, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [habs, div_le_div_iff₀ (by positivity) hApos]
  nlinarith [hamgm, hApos]

/-- The crude uniform majorant for the derivative terms. -/
theorem abs_deriv_gammaJumpTerm_le_inv_sq (η : ℝ) (n : ℕ) :
    |2 * η * ((n : ℝ) + 1) / ((((n : ℝ) + 1) ^ 2 + η ^ 2) ^ 2)|
      ≤ 1 / (((n : ℝ) + 1) ^ 2) := by
  refine (abs_deriv_gammaJumpTerm_le η n).trans ?_
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [sq_nonneg η]

/-- **The jump multiplier is differentiable, with the explicit series derivative.** -/
theorem hasDerivAt_gammaJumpMultiplier (η : ℝ) :
    HasDerivAt gammaJumpMultiplier
      (2 * ∑' n : ℕ, 2 * η * ((n : ℝ) + 1) / ((((n : ℝ) + 1) ^ 2 + η ^ 2) ^ 2)) η := by
  have hbase : HasDerivAt (fun y : ℝ => ∑' n : ℕ, gammaJumpTerm y n)
      (∑' n : ℕ, 2 * η * ((n : ℝ) + 1) / ((((n : ℝ) + 1) ^ 2 + η ^ 2) ^ 2)) η := by
    refine hasDerivAt_tsum (u := fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2)) summable_inv_succ_sq
      (fun n y => hasDerivAt_gammaJumpTerm y n) (fun n y => ?_)
      (y₀ := η) (summable_gammaJumpTerm η) η
    simpa [Real.norm_eq_abs] using abs_deriv_gammaJumpTerm_le_inv_sq y n
  simpa [gammaJumpMultiplier] using hbase.const_mul (2 : ℝ)

/-- The derivative series is summable. -/
theorem summable_deriv_gammaJumpTerm (η : ℝ) :
    Summable (fun n : ℕ => 2 * η * ((n : ℝ) + 1) / ((((n : ℝ) + 1) ^ 2 + η ^ 2) ^ 2)) := by
  refine Summable.of_norm_bounded summable_inv_succ_sq (fun n => ?_)
  simpa [Real.norm_eq_abs] using abs_deriv_gammaJumpTerm_le_inv_sq η n

/-- The trigamma majorant of the derivative series is summable. -/
theorem summable_trigamma_majorant (η : ℝ) :
    Summable (fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2 + η ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) summable_inv_succ_sq
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [sq_nonneg η]

/-- **`r'(η) = O(1/(1+|η|))`.**  Each derivative term is bounded by the corresponding trigamma
term, and the arctan telescope sums those to `1/η² + π/(2|η|)`. -/
theorem exists_deriv_gammaJumpMultiplier_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ,
      |2 * ∑' n : ℕ, 2 * η * ((n : ℝ) + 1) / ((((n : ℝ) + 1) ^ 2 + η ^ 2) ^ 2)|
        ≤ C / (1 + |η|) := by
  set S : ℝ := ∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + 1) ^ 2) with hS
  have hSnn : 0 ≤ S := tsum_nonneg fun n => by positivity
  have hpi := Real.pi_pos
  refine ⟨max (2 * (2 + Real.pi)) (4 * S), le_trans (by positivity) (le_max_left _ _), fun η => ?_⟩
  have hstep : |∑' n : ℕ, 2 * η * ((n : ℝ) + 1) / ((((n : ℝ) + 1) ^ 2 + η ^ 2) ^ 2)|
      ≤ ∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ 2 + η ^ 2) := by
    have hnorm := norm_tsum_le_tsum_norm (summable_deriv_gammaJumpTerm η).norm
    have hmono : ∑' n : ℕ, ‖2 * η * ((n : ℝ) + 1) / ((((n : ℝ) + 1) ^ 2 + η ^ 2) ^ 2)‖
        ≤ ∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ 2 + η ^ 2) :=
      Summable.tsum_mono (summable_deriv_gammaJumpTerm η).norm (summable_trigamma_majorant η)
        (fun n => by simpa [Real.norm_eq_abs] using abs_deriv_gammaJumpTerm_le η n)
    simpa [Real.norm_eq_abs] using hnorm.trans hmono
  have hden : (0 : ℝ) < 1 + |η| := by positivity
  rcases le_or_gt |η| 1 with hsmall | hbig
  · have hsum : ∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ 2 + η ^ 2) ≤ S := by
      refine Summable.tsum_mono (summable_trigamma_majorant η) summable_inv_succ_sq (fun n => ?_)
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [sq_nonneg η]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), le_div_iff₀ hden]
    have h4S : 4 * S ≤ max (2 * (2 + Real.pi)) (4 * S) := le_max_right _ _
    nlinarith [hstep, hsum, abs_nonneg η, hsmall, hSnn]
  · have hpos : (0 : ℝ) < |η| := lt_trans one_pos hbig
    have harctan : ∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ 2 + η ^ 2)
        ≤ 1 / |η| ^ 2 + Real.pi / (2 * |η|) := by
      refine Real.tsum_le_of_sum_range_le (fun n => by positivity) (fun N => ?_)
      have h := _root_.RHTower.sum_inv_sq_add_le (a := 1) (t := |η|) (by norm_num) hpos N
      refine le_trans (le_of_eq ?_) h
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [sq_abs]
      ring_nf
    have hinv : 1 / |η| ^ 2 ≤ 1 / |η| := by
      apply one_div_le_one_div_of_le hpos
      nlinarith
    have hpiterm : Real.pi / (2 * |η|) = Real.pi / 2 / |η| := (div_div Real.pi 2 |η|).symm
    have hcomb : ∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ 2 + η ^ 2) ≤ (1 + Real.pi / 2) / |η| := by
      rw [add_div]
      rw [hpiterm] at harctan
      linarith
    have hle2 : 1 + |η| ≤ 2 * |η| := by linarith
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), le_div_iff₀ hden]
    have hkey : 2 * |∑' n : ℕ, 2 * η * ((n : ℝ) + 1) / ((((n : ℝ) + 1) ^ 2 + η ^ 2) ^ 2)|
        ≤ 2 * ((1 + Real.pi / 2) / |η|) := by linarith
    have hmul : 2 * ((1 + Real.pi / 2) / |η|) * (1 + |η|)
        ≤ 2 * ((1 + Real.pi / 2) / |η|) * (2 * |η|) :=
      mul_le_mul_of_nonneg_left hle2 (by positivity)
    have hsimp : 2 * ((1 + Real.pi / 2) / |η|) * (2 * |η|) = 2 * (2 + Real.pi) := by
      field_simp
      ring
    have hCge : 2 * (2 + Real.pi) ≤ max (2 * (2 + Real.pi)) (4 * S) := le_max_left _ _
    have hmul2 : 2 * |∑' n : ℕ, 2 * η * ((n : ℝ) + 1) / ((((n : ℝ) + 1) ^ 2 + η ^ 2) ^ 2)|
        * (1 + |η|) ≤ 2 * ((1 + Real.pi / 2) / |η|) * (1 + |η|) :=
      mul_le_mul_of_nonneg_right hkey hden.le
    linarith [hmul2, hmul, hsimp.le, hsimp.ge, hCge]

end

end GaloisForLFunctions.RHTower
