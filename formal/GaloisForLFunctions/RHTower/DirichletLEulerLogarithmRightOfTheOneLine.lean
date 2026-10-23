import GaloisForLFunctions.RHTower.DirichletLLogDerivativeStrip
import GaloisForLFunctions.RHTower.DirichletCharacterPerron
import GaloisForLFunctions.RHTower.PrimeLagLandauCriterion

/-!
# The Euler logarithm of a Dirichlet `L`-function right of `Re s = 1`

For a character `χ` mod `Q` let `ℓ_χ(w) = Σ_p −log(1 − χ(p) p^{-w})` (`eulerLog`), the logarithm of
`L(w, χ)` given by the Euler product on `Re w > 1` (`exp_eulerLog`). It is holomorphic there with
`ℓ_χ' = L'/L` (`hasDerivAt_eulerLog`), and integrating `L'/L` along the horizontal segment from
`σ + it` to `2 + it`:

* `|ℓ_χ(σ + it)| ≤ 9 log log|t| + C` for `1 < σ ≤ 2`, `|t| ≥ 9` (`exists_norm_eulerLog_le_large`):
  `|L'/L| ≤ log⁹|t|/(2a)` on the strip `σ ≤ 1 + a/log⁹|t|` (`norm_deriv_div_LFunction_le_log_strip`),
  and beyond it `|L'/L(x + it)| ≤ Σ Λ(n) n^{-x} ≤ 1/(x − 1) + B` (`norm_logDeriv_LFunction_le`);
* for `χ ≠ 1`, `|ℓ_χ|` is bounded on `1 < σ ≤ 2`, `|t| ≤ 9` (`exists_norm_eulerLog_le_box`): `L'/L` is
  continuous on the closed box, where `L(·, χ)` is entire and zero-free.

Hence `|exp(z ℓ_χ(w))| ≤ e^{|z|C} log^{9|z|}|t|` for every complex exponent `z`.
-/

noncomputable section
open Filter Topology Complex Set MeasureTheory

namespace RHTower

variable {Q : ℕ} [NeZero Q]

/-- The Euler logarithm `ℓ_χ(w) = Σ_p −log(1 − χ(p) p^{-w})`. -/
def eulerLog (χ : DirichletCharacter ℂ Q) (w : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1 - χ p * ((p : ℕ) : ℂ) ^ (-w))

theorem norm_char_prime_cpow_le (χ : DirichletCharacter ℂ Q) {w : ℂ} (p : Nat.Primes) :
    ‖χ p * ((p : ℕ) : ℂ) ^ (-w)‖ ≤ ((p : ℕ) : ℝ) ^ (-w.re) := by
  rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos
    (by exact_mod_cast p.2.pos), Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (DirichletCharacter.norm_le_one χ _)

theorem prime_rpow_neg_le_half {b : ℝ} (hb : 1 ≤ b) (p : Nat.Primes) :
    ((p : ℕ) : ℝ) ^ (-b) ≤ 1 / 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
  calc ((p : ℕ) : ℝ) ^ (-b) ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ ≤ 2 ^ (-1 : ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

/-- The Euler logarithm is a logarithm of `L(w, χ)` on `Re w > 1`. -/
theorem exp_eulerLog (χ : DirichletCharacter ℂ Q) {w : ℂ} (hw : 1 < w.re) :
    Complex.exp (eulerLog χ w) = DirichletCharacter.LFunction χ w := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hw, eulerLog]
  exact DirichletCharacter.LSeries_eulerProduct_exp_log χ hw

/-- `|ℓ_χ(w)| ≤ (3/2) Σ_p p^{-Re w}` on `Re w > 1`. -/
theorem norm_eulerLog_le (χ : DirichletCharacter ℂ Q) {w : ℂ} (hw : 1 < w.re) :
    ‖eulerLog χ w‖ ≤ 3 / 2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-w.re) := by
  have hsum : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-w.re)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have hterm : ∀ p : Nat.Primes, ‖-Complex.log (1 - χ p * ((p : ℕ) : ℂ) ^ (-w))‖ ≤
      3 / 2 * ((p : ℕ) : ℝ) ^ (-w.re) := fun p => by
    rw [norm_neg, sub_eq_add_neg]
    have hy := norm_char_prime_cpow_le χ (w := w) p
    have hy2 : ‖-(χ p * ((p : ℕ) : ℂ) ^ (-w))‖ ≤ 1 / 2 := by
      rw [norm_neg]; exact hy.trans (prime_rpow_neg_le_half hw.le p)
    refine (Complex.norm_log_one_add_half_le_self hy2).trans ?_
    rw [norm_neg]
    exact mul_le_mul_of_nonneg_left hy (by norm_num)
  rw [eulerLog, ← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm ((hsum.mul_left (3 / 2)).of_nonneg_of_le (fun _ => norm_nonneg _)
    hterm)).trans (Summable.tsum_le_tsum hterm ((hsum.mul_left (3 / 2)).of_nonneg_of_le
      (fun _ => norm_nonneg _) hterm) (hsum.mul_left _))

/-- The Euler logarithm is holomorphic on `Re w > 1`. -/
theorem differentiableAt_eulerLog (χ : DirichletCharacter ℂ Q) {w : ℂ} (hw : 1 < w.re) :
    DifferentiableAt ℂ (eulerLog χ) w := by
  set b : ℝ := (1 + w.re) / 2
  have hb : 1 < b := by simp only [b]; linarith
  have hbw : b < w.re := by simp only [b]; linarith
  set U : Set ℂ := {z : ℂ | b < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsum : Summable (fun p : Nat.Primes => 3 / 2 * ((p : ℕ) : ℝ) ^ (-b)) :=
    (Nat.Primes.summable_rpow.mpr (by linarith)).mul_left _
  have hdiff : DifferentiableOn ℂ (fun z => ∑' p : Nat.Primes,
      -Complex.log (1 - χ p * ((p : ℕ) : ℂ) ^ (-z))) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm hsum (fun p z hz => ?_) hU
      (fun p z hz => ?_)
    · have hz' : b < z.re := hz
      have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
      have hy : ‖χ p * ((p : ℕ) : ℂ) ^ (-z)‖ ≤ 1 / 2 :=
        (norm_char_prime_cpow_le χ p).trans (prime_rpow_neg_le_half (by linarith) p)
      have hslit : 1 - χ p * ((p : ℕ) : ℂ) ^ (-z) ∈ Complex.slitPlane := by
        apply Complex.mem_slitPlane_of_pos_re
        have := Complex.abs_re_le_norm (χ p * ((p : ℕ) : ℂ) ^ (-z))
        rw [Complex.sub_re, Complex.one_re]
        linarith [le_abs_self (χ p * ((p : ℕ) : ℂ) ^ (-z)).re]
      refine DifferentiableAt.differentiableWithinAt ?_
      exact ((differentiableAt_const _).sub ((differentiableAt_const _).mul
        ((differentiableAt_id.neg).const_cpow (Or.inl hp0)))).clog hslit |>.neg
    · have hz' : b < z.re := hz
      rw [norm_neg, sub_eq_add_neg]
      have hy := norm_char_prime_cpow_le χ (w := z) p
      have hy2 : ‖-(χ p * ((p : ℕ) : ℂ) ^ (-z))‖ ≤ 1 / 2 := by
        rw [norm_neg]; exact hy.trans (prime_rpow_neg_le_half (by linarith) p)
      refine (Complex.norm_log_one_add_half_le_self hy2).trans ?_
      rw [norm_neg]
      refine mul_le_mul_of_nonneg_left (hy.trans ?_) (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_lt.le) (by linarith)
  exact hdiff.differentiableAt (hU.mem_nhds hbw)

/-- **`ℓ_χ' = L'/L`** on `Re w > 1`. -/
theorem hasDerivAt_eulerLog (χ : DirichletCharacter ℂ Q) {w : ℂ} (hw : 1 < w.re) :
    HasDerivAt (eulerLog χ)
      (deriv (DirichletCharacter.LFunction χ) w / DirichletCharacter.LFunction χ w) w := by
  have hg := (differentiableAt_eulerLog χ hw).hasDerivAt
  have hw1 : w ≠ 1 := by intro h; rw [h, Complex.one_re] at hw; exact lt_irrefl _ hw
  have hL := (DirichletCharacter.differentiableAt_LFunction χ w (Or.inl hw1)).hasDerivAt
  have hexp := hg.cexp
  have heq : (fun z => Complex.exp (eulerLog χ z)) =ᶠ[𝓝 w] DirichletCharacter.LFunction χ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw] with z hz
    exact exp_eulerLog χ hz
  have hexp' := hexp.congr_of_eventuallyEq heq.symm
  have huniq := hL.unique hexp'
  have hne : DirichletCharacter.LFunction χ w ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hw1) hw.le
  rw [exp_eulerLog χ hw] at huniq
  rw [huniq, mul_div_cancel_left₀ _ hne]
  exact hg

/-- On real `x > 1`: `|L'/L(x + it, χ)| ≤ Σ_n Λ(n) n^{-x} ≤ ‖ζ'/ζ(x)‖`. -/
theorem norm_logDeriv_LFunction_le (χ : DirichletCharacter ℂ Q) {x : ℝ} (hx : 1 < x) (t : ℝ) :
    ‖deriv (DirichletCharacter.LFunction χ) (x + t * I) /
        DirichletCharacter.LFunction χ (x + t * I)‖ ≤
      ‖deriv riemannZeta x / riemannZeta x‖ := by
  have hre : 1 < ((x : ℂ) + t * I).re := by simpa using hx
  have hxre : 1 < (x : ℂ).re := by simpa using hx
  rw [← norm_neg, ← neg_div, ← LSeries_character_vonMangoldt_eq χ hre]
  have hΛ := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hxre
  rw [show ‖deriv riemannZeta x / riemannZeta x‖ = ‖-deriv riemannZeta x / riemannZeta x‖ by
    rw [neg_div, norm_neg], ← hΛ]
  have hsΛ : LSeriesSummable (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) x :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hxre
  have hterm : ∀ n : ℕ, ‖LSeries.term (fun n : ℕ => χ n *
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((x : ℂ) + t * I) n‖ ≤
        ‖LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) x n‖ := fun n => by
    refine (LSeries.norm_term_le _ (by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _))).trans
      (le_of_eq ?_)
    simp only [LSeries.norm_term_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_self, add_zero]
  have hnonneg : ∀ n : ℕ, ‖LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) x n‖ =
      (LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) x n).re := fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [show ((n : ℂ) ^ (x : ℂ)) = (((n : ℝ) ^ x : ℝ) : ℂ) by
        rw [Complex.ofReal_cpow hn0.le, Complex.ofReal_natCast]]
      rw [← Complex.ofReal_div, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (Real.rpow_nonneg hn0.le _))]
  calc ‖LSeries (fun n : ℕ => χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
        ((x : ℂ) + t * I)‖
      ≤ ∑' n, ‖LSeries.term (fun n : ℕ => χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          ((x : ℂ) + t * I) n‖ :=
        norm_tsum_le_tsum_norm (hsΛ.norm.of_nonneg_of_le (fun _ => norm_nonneg _) hterm)
    _ ≤ ∑' n, ‖LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) x n‖ :=
        Summable.tsum_le_tsum hterm (hsΛ.norm.of_nonneg_of_le (fun _ => norm_nonneg _) hterm)
          hsΛ.norm
    _ = (LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) x).re := by
        rw [LSeries, Complex.re_tsum hsΛ]
        exact tsum_congr hnonneg
    _ ≤ ‖LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) x‖ :=
        Complex.re_le_norm _

/-- `‖ζ'/ζ(x)‖ ≤ 1/(x − 1) + B` for `1 < x ≤ 2`. -/
theorem exists_norm_logDeriv_zeta_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 < x → x ≤ 2 →
      ‖deriv riemannZeta x / riemannZeta x‖ ≤ 1 / (x - 1) + B := by
  obtain ⟨B₁, hB₁⟩ := exists_bound_neg_logDeriv_zeta_sub_inv
  set K : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc (5 / 4 : ℝ) 2
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hcont : ContinuousOn (fun z => deriv riemannZeta z / riemannZeta z) K := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : (x : ℂ) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [hx.1]
    have hζ : riemannZeta x ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp; linarith [hx.1])
    have han : AnalyticAt ℂ riemannZeta x :=
      analyticOn_riemannZeta x h1
    exact (han.deriv.continuousAt.div han.continuousAt hζ).continuousWithinAt
  obtain ⟨B₂, hB₂⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max (|B₁|) (|B₂|), le_max_of_le_left (abs_nonneg _), fun x hx hx2 => ?_⟩
  rcases le_total x (5 / 4) with h54 | h54
  · have h := hB₁ (x - 1) (by linarith) (by linarith)
    have hx1 : (1 : ℂ) + ((x - 1 : ℝ) : ℂ) = x := by push_cast; ring
    rw [hx1, logDeriv_apply] at h
    have h2 := norm_sub_norm_le (-(deriv riemannZeta x / riemannZeta x)) (1 / ((x - 1 : ℝ) : ℂ))
    rw [norm_neg] at h2
    have h3 : ‖(1 : ℂ) / ((x - 1 : ℝ) : ℂ)‖ = 1 / (x - 1) := by
      rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [h3] at h2
    linarith [le_max_left (|B₁|) (|B₂|), le_abs_self B₁]
  · have h := hB₂ x ⟨x, ⟨h54, hx2⟩, rfl⟩
    have h1 : 0 < 1 / (x - 1) := by apply one_div_pos.mpr; linarith
    linarith [le_max_right (|B₁|) (|B₂|), le_abs_self B₂]

/-- On a horizontal segment right of `Re = 1` the log-derivative `L'/L` is continuous. -/
theorem continuousOn_logDeriv_LFunction_segment (χ : DirichletCharacter ℂ Q) {σ : ℝ} (hσ : 1 < σ)
    (t b : ℝ) :
    ContinuousOn (fun x : ℝ => deriv (DirichletCharacter.LFunction χ) (x + t * I) /
      DirichletCharacter.LFunction χ (x + t * I)) (uIcc σ (max σ b)) := by
  intro x hx
  rw [uIcc_of_le (le_max_left _ _)] at hx
  have hz1 : ((x : ℂ) + t * I) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [hx.1]
  have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {(1 : ℂ)}ᶜ := fun z hz =>
    (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
  have han : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ((x : ℂ) + t * I) :=
    hdiff.analyticAt (isOpen_compl_singleton.mem_nhds hz1)
  have hne : DirichletCharacter.LFunction χ ((x : ℂ) + t * I) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hz1) (by simp; linarith [hx.1])
  have hpath : ContinuousAt (fun y : ℝ => (y : ℂ) + t * I) x :=
    (Complex.continuous_ofReal.add continuous_const).continuousAt
  exact ((han.deriv.continuousAt.comp hpath).div (han.continuousAt.comp hpath) hne).continuousWithinAt

/-- **The Euler logarithm as an integral of `L'/L`**: for `1 < σ ≤ 2`,
`|ℓ_χ(σ + it)| ≤ (3/2) Σ_p p^{-2} + ∫_σ^2 |L'/L(x + it)| dx`. -/
theorem norm_eulerLog_le_integral (χ : DirichletCharacter ℂ Q) {σ : ℝ} (hσ : 1 < σ)
    (hσ2 : σ ≤ 2) (t : ℝ) :
    ‖eulerLog χ (σ + t * I)‖ ≤ 3 / 2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 : ℝ)) +
      ∫ x in σ..2, ‖deriv (DirichletCharacter.LFunction χ) (x + t * I) /
        DirichletCharacter.LFunction χ (x + t * I)‖ := by
  set g : ℝ → ℂ := fun x => deriv (DirichletCharacter.LFunction χ) (x + t * I) /
    DirichletCharacter.LFunction χ (x + t * I)
  have hderiv : ∀ x ∈ uIcc σ 2, HasDerivAt (fun y : ℝ => eulerLog χ (y + t * I)) (g x) x := by
    intro x hx
    rw [uIcc_of_le hσ2] at hx
    have hx1 : 1 < ((x : ℂ) + t * I).re := by simp; linarith [hx.1]
    have h := (hasDerivAt_eulerLog χ hx1).comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).add_const ((t : ℂ) * I))
    simp only [mul_one, Function.comp_def, id] at h
    exact h.comp_ofReal
  have hcont := continuousOn_logDeriv_LFunction_segment χ hσ t 2
  rw [max_eq_right hσ2] at hcont
  have hint : IntervalIntegrable g volume σ 2 := hcont.intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have h1 : eulerLog χ (σ + t * I) = eulerLog χ (((2 : ℝ) : ℂ) + t * I) - ∫ x in σ..2, g x := by
    rw [hftc]; ring
  rw [h1]
  refine (norm_sub_le _ _).trans (add_le_add ?_ (intervalIntegral.norm_integral_le_integral_norm hσ2))
  have h2 := norm_eulerLog_le χ (w := ((2 : ℝ) : ℂ) + t * I) (by simp)
  have hre : (((2 : ℝ) : ℂ) + t * I).re = 2 := by simp
  rwa [hre] at h2

theorem characterPerronWidth_le_half' (Q : ℕ) : characterPerronWidth Q ≤ 1 / 2 := by
  have hK1 := one_le_characterLogStripConstant Q
  have hK8 : (1 : ℝ) ≤ characterLogStripConstant Q ^ (8 : ℕ) := one_le_pow₀ hK1
  unfold characterPerronWidth
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- **The Euler logarithm at large heights.** `|ℓ_χ(σ + it)| ≤ 9 log log|t| + C` for `1 < σ ≤ 2`,
`|t| ≥ 9`. -/
theorem exists_norm_eulerLog_le_large (χ : DirichletCharacter ℂ Q) :
    ∃ C : ℝ, ∀ σ t : ℝ, 1 < σ → σ ≤ 2 → 9 ≤ |t| →
      ‖eulerLog χ (σ + t * I)‖ ≤ 9 * Real.log (Real.log |t|) + C := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_logDeriv_zeta_le
  have ha : 0 < characterPerronWidth Q := characterPerronWidth_pos Q
  have hah := characterPerronWidth_le_half' Q
  set a := characterPerronWidth Q
  set S := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 : ℝ))
  refine ⟨3 / 2 * S + 1 / 2 + B - Real.log a, fun σ t hσ hσ2 ht => ?_⟩
  set L := Real.log |t|
  have hL2 : 2 < L := by
    have h := Real.log_lt_log (Real.exp_pos 2)
      (lt_of_lt_of_le exp_two_lt_eight (by linarith : (8 : ℝ) ≤ |t|))
    rwa [Real.log_exp] at h
  have hL : 0 < L := by linarith
  have hL9 : 1 ≤ L ^ (9 : ℕ) := one_le_pow₀ (by linarith)
  have hη : 0 < a / L ^ (9 : ℕ) := by positivity
  have hηh : a / L ^ (9 : ℕ) ≤ 1 / 2 := (div_le_self ha.le hL9).trans hah
  set η := a / L ^ (9 : ℕ)
  set g : ℝ → ℂ := fun x => deriv (DirichletCharacter.LFunction χ) (x + t * I) /
    DirichletCharacter.LFunction χ (x + t * I)
  have hg1 : ∀ x : ℝ, 1 < x → x ≤ 1 + η → ‖g x‖ ≤ L ^ (9 : ℕ) / (2 * a) := fun x hx1 hx2 =>
    norm_deriv_div_LFunction_le_log_strip χ ht (by linarith) hx2
  have hg2 : ∀ x : ℝ, 1 < x → x ≤ 2 → ‖g x‖ ≤ 1 / (x - 1) + B := fun x hx hx2 =>
    (norm_logDeriv_LFunction_le χ hx t).trans (hB x hx hx2)
  -- the integral of `1/(x − 1) + B` over `[c, 2]`
  have hk_int : ∀ c : ℝ, 1 < c → IntervalIntegrable (fun x : ℝ => 1 / (x - 1) + B) volume c 2 := by
    intro c hc
    refine ContinuousOn.intervalIntegrable ((continuousOn_const.div
      (continuousOn_id.sub continuousOn_const) fun x hx => ?_).add continuousOn_const)
    rw [uIcc_of_le (by linarith : c ≤ 2)] at hx
    have : 0 < x - 1 := by simp only [id]; linarith [hx.1]
    exact this.ne'
  have hk_val : ∀ c : ℝ, 1 < c → c ≤ 2 →
      ∫ x in c..2, (1 / (x - 1) + B) = Real.log (1 / (c - 1)) + B * (2 - c) := by
    intro c hc hc2
    have hinv : IntervalIntegrable (fun x : ℝ => 1 / (x - 1)) volume c 2 := by
      refine ContinuousOn.intervalIntegrable (continuousOn_const.div
        (continuousOn_id.sub continuousOn_const) fun x hx => ?_)
      rw [uIcc_of_le hc2] at hx
      have : 0 < x - 1 := by simp only [id]; linarith [hx.1]
      exact this.ne'
    rw [intervalIntegral.integral_add hinv intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul]
    have h : ∫ x in c..2, 1 / (x - 1) = Real.log (1 / (c - 1)) := by
      simp_rw [one_div]
      rw [intervalIntegral.integral_comp_sub_right (fun x => x⁻¹) 1,
        integral_inv_of_pos (by linarith) (by norm_num)]
      norm_num
    rw [h]
    ring
  have hcont := continuousOn_logDeriv_LFunction_segment χ hσ t 2
  rw [max_eq_right hσ2] at hcont
  have hint : IntervalIntegrable (fun x => ‖g x‖) volume σ 2 := hcont.norm.intervalIntegrable
  -- the integral bound
  have hlogη : Real.log (1 / η) = 9 * Real.log L - Real.log a := by
    simp only [η]
    rw [one_div_div, Real.log_div (by positivity) ha.ne', Real.log_pow]
    push_cast; ring
  have hbound : ∫ x in σ..2, ‖g x‖ ≤ 1 / 2 + Real.log (1 / η) + B := by
    rcases le_or_gt (1 + η) σ with hση | hση
    · calc ∫ x in σ..2, ‖g x‖ ≤ ∫ x in σ..2, (1 / (x - 1) + B) :=
            intervalIntegral.integral_mono_on hσ2 hint (hk_int σ hσ)
              fun x hx => hg2 x (by linarith [hx.1]) hx.2
        _ = Real.log (1 / (σ - 1)) + B * (2 - σ) := hk_val σ hσ hσ2
        _ ≤ 1 / 2 + Real.log (1 / η) + B := by
            have h1 : Real.log (1 / (σ - 1)) ≤ Real.log (1 / η) :=
              Real.log_le_log (by apply one_div_pos.mpr; linarith)
                (one_div_le_one_div_of_le hη (by linarith))
            have h2 : B * (2 - σ) ≤ B := by nlinarith
            linarith
    · have hmid : 1 + η ≤ 2 := by linarith
      have hint1 : IntervalIntegrable (fun x => ‖g x‖) volume σ (1 + η) :=
        hint.mono_set (by rw [uIcc_of_le hση.le, uIcc_of_le hσ2]; exact Icc_subset_Icc le_rfl hmid)
      have hint2 : IntervalIntegrable (fun x => ‖g x‖) volume (1 + η) 2 :=
        hint.mono_set (by rw [uIcc_of_le hmid, uIcc_of_le hσ2]; exact Icc_subset_Icc hση.le le_rfl)
      rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
      have hA : ∫ x in σ..(1 + η), ‖g x‖ ≤ 1 / 2 := by
        calc ∫ x in σ..(1 + η), ‖g x‖ ≤ ∫ _x in σ..(1 + η), L ^ (9 : ℕ) / (2 * a) :=
              intervalIntegral.integral_mono_on hση.le hint1 intervalIntegrable_const
                fun x hx => hg1 x (by linarith [hx.1]) hx.2
          _ = (1 + η - σ) * (L ^ (9 : ℕ) / (2 * a)) := by
              rw [intervalIntegral.integral_const, smul_eq_mul]
          _ ≤ η * (L ^ (9 : ℕ) / (2 * a)) :=
              mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = 1 / 2 := by simp only [η]; field_simp
      have hB' : ∫ x in (1 + η)..2, ‖g x‖ ≤ Real.log (1 / η) + B := by
        calc ∫ x in (1 + η)..2, ‖g x‖ ≤ ∫ x in (1 + η)..2, (1 / (x - 1) + B) :=
              intervalIntegral.integral_mono_on hmid hint2 (hk_int (1 + η) (by linarith))
                fun x hx => hg2 x (by linarith [hx.1]) hx.2
          _ = Real.log (1 / (1 + η - 1)) + B * (2 - (1 + η)) := hk_val _ (by linarith) hmid
          _ ≤ Real.log (1 / η) + B := by
              rw [show 1 + η - 1 = η by ring]
              have : B * (2 - (1 + η)) ≤ B := by nlinarith
              linarith
      linarith
  have hS : 0 ≤ S := tsum_nonneg fun p => by positivity
  calc ‖eulerLog χ (σ + t * I)‖ ≤ 3 / 2 * S + ∫ x in σ..2, ‖g x‖ :=
        norm_eulerLog_le_integral χ hσ hσ2 t
    _ ≤ 3 / 2 * S + (1 / 2 + Real.log (1 / η) + B) := by linarith
    _ = 9 * Real.log L + (3 / 2 * S + 1 / 2 + B - Real.log a) := by rw [hlogη]; ring

/-- **The Euler logarithm on the box.** For `χ ≠ 1`, `|ℓ_χ(σ + it)|` is bounded on `1 < σ ≤ 2`,
`|t| ≤ 9`. -/
theorem exists_norm_eulerLog_le_box {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ σ t : ℝ, 1 < σ → σ ≤ 2 → |t| ≤ 9 → ‖eulerLog χ (σ + t * I)‖ ≤ C := by
  set K : Set ℂ := (Icc (1 : ℝ) 2) ×ℂ (Icc (-9 : ℝ) 9)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have han : ∀ z, AnalyticAt ℂ (DirichletCharacter.LFunction χ) z := fun z =>
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hcont : ContinuousOn (fun z => deriv (DirichletCharacter.LFunction χ) z /
      DirichletCharacter.LFunction χ z) K := fun z hz =>
    ((han z).deriv.continuousAt.div (han z).continuousAt
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
        (Complex.mem_reProdIm.mp hz).1.1)).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  set S := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 : ℝ))
  refine ⟨3 / 2 * S + |M|, fun σ t hσ hσ2 ht => ?_⟩
  have hcont' := continuousOn_logDeriv_LFunction_segment χ hσ t 2
  rw [max_eq_right hσ2] at hcont'
  have hint : IntervalIntegrable (fun x : ℝ => ‖deriv (DirichletCharacter.LFunction χ) (x + t * I) /
      DirichletCharacter.LFunction χ (x + t * I)‖) volume σ 2 := hcont'.norm.intervalIntegrable
  have hbound : ∫ x in σ..2, ‖deriv (DirichletCharacter.LFunction χ) (x + t * I) /
      DirichletCharacter.LFunction χ (x + t * I)‖ ≤ |M| := by
    calc _ ≤ ∫ _x in σ..2, |M| := intervalIntegral.integral_mono_on hσ2 hint
          intervalIntegrable_const fun x hx => by
            have hmem : (x : ℂ) + t * I ∈ K := by
              rw [Complex.mem_reProdIm]
              simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
                sub_self, add_zero, add_im, mul_im, zero_add]
              exact ⟨⟨by linarith [hx.1], hx.2⟩, abs_le.mp ht⟩
            exact (hM _ hmem).trans (le_abs_self M)
      _ = (2 - σ) * |M| := by rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ |M| := by nlinarith [abs_nonneg M]
  exact (norm_eulerLog_le_integral χ hσ hσ2 t).trans (by linarith)

end RHTower
