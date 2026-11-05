import GaloisForLFunctions.ArithmeticProduction.TheSecondMomentIsALaplaceTransform
import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding
import GaloisForLFunctions.RHTower.EntireDirichletPolynomial
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound
import GaloisForLFunctions.RHTower.ZetaChiVerticalGrowth
import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound
import GaloisForLFunctions.RHTower.MontgomerySpacedDetectionCore

/-!
# The mollified zeta function is band-limited at height `T`

Fix a height `t₀`, a Gaussian width `w`, and a Dirichlet polynomial `M` of length `N` with coefficients bounded by `1`.  The window function

  `F(s) = ((s − 1)ζ(s)/(s + 1)) M(s) exp((s − ½ − it₀)²/(2w²))`

is holomorphic for `Re s > −1`, and the factor `(s − 1)/(s + 1)` removes the pole while keeping the modulus at `1 + O(T⁻²)` near
height `T`.  Its spectrum in the variable `u = log n` is carried by `[0, log(T²N^{3/2})]`:

* on `Re s = 2` the function is bounded by `4` times the Gaussian, so the spectrum left of `0` decays
  (`integral_norm_mollifiedWindow_right_le`);
* on `Re s = −½` the functional equation gives `|ζ| ≪ (1 + |t|)²` and `|M| ≤ N^{3/2}`, so the spectrum right of `log(T²N^{3/2})` decays
  (`exists_integral_norm_mollifiedWindow_left_le`).

Both bounds are uniform in the mollifier.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ArithmeticProduction

open _root_.RHTower

/-- The analytic Gaussian window at height `t₀`. -/
def gaussWindow (t₀ w : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((s - 1 / 2 - (t₀ : ℂ) * I) ^ 2 / (2 * (w : ℂ) ^ 2))

theorem norm_gaussWindow (t₀ w : ℝ) (s : ℂ) :
    ‖gaussWindow t₀ w s‖ =
      Real.exp (((s.re - 1 / 2) ^ 2 - (s.im - t₀) ^ 2) / (2 * w ^ 2)) := by
  unfold gaussWindow
  rw [Complex.norm_exp]
  congr 1
  have hcast : (2 * (w : ℂ) ^ 2) = ((2 * w ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.div_ofReal_re, sq (s - 1 / 2 - (t₀ : ℂ) * I), Complex.mul_re]
  have hre : (s - 1 / 2 - (t₀ : ℂ) * I).re = s.re - 1 / 2 := by simp
  have him : (s - 1 / 2 - (t₀ : ℂ) * I).im = s.im - t₀ := by simp
  rw [hre, him]
  ring

theorem differentiable_gaussWindow (t₀ w : ℝ) : Differentiable ℂ (gaussWindow t₀ w) := by
  unfold gaussWindow
  fun_prop

/-- The mollified body `((s − 1)ζ(s)/(s + 1)) M(s)`. -/
def windowBody (b : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  zetaEntire s * edPoly b (Finset.Icc 1 N) s / (s + 1)

/-- The window function. -/
def mollifiedWindow (t₀ w : ℝ) (b : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  windowBody b N s * gaussWindow t₀ w s

private theorem hIcc1 (N : ℕ) : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun _ hn => (Finset.mem_Icc.mp hn).1

theorem differentiableAt_windowBody (b : ℕ → ℂ) (N : ℕ) {s : ℂ} (hs : -1 < s.re) :
    DifferentiableAt ℂ (windowBody b N) s := by
  have hne : s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  unfold windowBody
  exact ((differentiable_zetaEntire s).mul ((differentiable_edPoly b (hIcc1 N)) s)).div (by fun_prop) hne

theorem differentiableAt_mollifiedWindow (t₀ w : ℝ) (b : ℕ → ℂ) (N : ℕ) {s : ℂ} (hs : -1 < s.re) :
    DifferentiableAt ℂ (mollifiedWindow t₀ w b N) s :=
  (differentiableAt_windowBody b N hs).mul (differentiable_gaussWindow t₀ w s)

/-! ### Polynomial times Gaussian -/

/-- `(1 + |t|)^{2j} e^{−(t−t₀)²/(2w²)}` is bounded, with an explicit constant. -/
theorem one_add_abs_pow_mul_gauss_le (j : ℕ) (t₀ t : ℝ) {w : ℝ} (hw : 0 < w) :
    (1 + |t|) ^ (2 * j) * Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) ≤
      (2 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2)) ^ j * (j.factorial : ℝ) * Real.exp 1 := by
  set A : ℝ := 2 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) with hA
  have hA0 : 0 ≤ A := by positivity
  set y : ℝ := (t - t₀) ^ 2 / (2 * w ^ 2) with hy
  have hy0 : 0 ≤ y := by positivity
  have hτ : (t - t₀) ^ 2 = 2 * w ^ 2 * y := by
    rw [hy]
    field_simp
  have htri : 1 + |t| ≤ (1 + |t₀|) * (1 + |t - t₀|) := by
    have h1 : |t| ≤ |t - t₀| + |t₀| := by
      have := abs_add_le (t - t₀) t₀
      simpa using this
    have h2 : 0 ≤ |t₀| * |t - t₀| := by positivity
    nlinarith
  have hsq : (1 + |t|) ^ 2 ≤ A * (1 + y) := by
    have h1 : (1 + |t|) ^ 2 ≤ ((1 + |t₀|) * (1 + |t - t₀|)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) htri 2
    have h2 : (1 + |t - t₀|) ^ 2 ≤ 2 * (1 + (t - t₀) ^ 2) := by
      have := sq_abs (t - t₀)
      nlinarith [sq_nonneg (1 - |t - t₀|)]
    have h3 : 2 * (1 + (t - t₀) ^ 2) ≤ 2 * ((1 + 2 * w ^ 2) * (1 + y)) := by
      rw [hτ]
      have : 0 ≤ w ^ 2 * y := by positivity
      nlinarith
    calc (1 + |t|) ^ 2 ≤ (1 + |t₀|) ^ 2 * (1 + |t - t₀|) ^ 2 := by rw [← mul_pow]; exact h1
      _ ≤ (1 + |t₀|) ^ 2 * (2 * ((1 + 2 * w ^ 2) * (1 + y))) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
      _ = A * (1 + y) := by rw [hA]; ring
  have hpow : (1 + |t|) ^ (2 * j) ≤ (A * (1 + y)) ^ j := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hsq j
  have hfact := Real.pow_div_factorial_le_exp (1 + y) (by positivity) j
  have hfpos : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  rw [div_le_iff₀ hfpos] at hfact
  have hEsplit : Real.exp (1 + y) * Real.exp (-y) = Real.exp 1 := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE := Real.exp_pos (-y)
  calc (1 + |t|) ^ (2 * j) * Real.exp (-y) ≤ (A * (1 + y)) ^ j * Real.exp (-y) :=
        mul_le_mul_of_nonneg_right hpow hE.le
    _ = A ^ j * (1 + y) ^ j * Real.exp (-y) := by rw [mul_pow]
    _ ≤ A ^ j * (Real.exp (1 + y) * j.factorial) * Real.exp (-y) := by gcongr
    _ = A ^ j * j.factorial * (Real.exp (1 + y) * Real.exp (-y)) := by ring
    _ = _ := by rw [hEsplit]

/-- `(1 + |t|)^j e^{−(t−t₀)²/(2w²)}` is bounded. -/
theorem exists_one_add_abs_pow_mul_gauss_le (j : ℕ) (t₀ : ℝ) {w : ℝ} (hw : 0 < w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      (1 + |t|) ^ j * Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) ≤ C := by
  refine ⟨(2 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2)) ^ j * (j.factorial : ℝ) * Real.exp 1,
    by positivity, fun t => ?_⟩
  have hbase : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    (one_add_abs_pow_mul_gauss_le j t₀ t hw)
  exact pow_le_pow_right₀ hbase (by omega)

/-! ### Growth of the body -/

/-- Polynomial growth of `(s − 1)ζ(s)` on a vertical strip. -/
theorem exists_norm_zetaEntire_le {M : ℝ} (hM : 1 ≤ M) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ M →
      ‖zetaEntire s‖ ≤ C * (1 + |s.im|) ^ k := by
  obtain ⟨C₁, N, hC₁, hstrip⟩ := exists_bound_norm_riemannZeta_strip M
  have hK : IsCompact (Icc (-1 : ℝ) M ×ℂ Icc (-1 : ℝ) 1) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn differentiable_zetaEntire.continuous.continuousOn
  have hM5 : 0 ≤ M + 1 := by linarith
  refine ⟨(M + 1) * C₁ + max C₂ 0, N + 1, by positivity, fun s h1 h2 => ?_⟩
  have hbase : (1 : ℝ) ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
  have hpow1 : (1 : ℝ) ≤ (1 + |s.im|) ^ (N + 1) := one_le_pow₀ hbase
  rcases le_total 1 |s.im| with hbig | hsmall
  · have hne : s ≠ 1 := by
      intro h
      rw [h] at hbig
      simp at hbig
      linarith
    rw [zetaEntire_eq hne]
    have hσ : |s.re| ≤ M := abs_le.mpr ⟨by linarith, h2⟩
    have hz := hstrip s.re s.im hσ hbig
    rw [Complex.re_add_im] at hz
    have hs1 : ‖s - 1‖ ≤ (M + 1) * (1 + |s.im|) := by
      have h3 : ‖s - 1‖ ≤ |(s - 1).re| + |(s - 1).im| := Complex.norm_le_abs_re_add_abs_im _
      have h4 : |(s - 1).re| ≤ M + 1 := by
        rw [abs_le]
        simp only [Complex.sub_re, Complex.one_re]
        constructor <;> linarith
      have h5 : (s - 1).im = s.im := by simp
      rw [h5] at h3
      nlinarith [abs_nonneg s.im]
    have hmono : |s.im| ^ N ≤ (1 + |s.im|) ^ N :=
      pow_le_pow_left₀ (abs_nonneg _) (by linarith) N
    calc ‖(s - 1) * riemannZeta s‖ = ‖s - 1‖ * ‖riemannZeta s‖ := norm_mul _ _
      _ ≤ ((M + 1) * (1 + |s.im|)) * (C₁ * (1 + |s.im|) ^ N) :=
        mul_le_mul hs1 (hz.trans (mul_le_mul_of_nonneg_left hmono hC₁)) (norm_nonneg _)
          (by positivity)
      _ = (M + 1) * C₁ * (1 + |s.im|) ^ (N + 1) := by ring
      _ ≤ ((M + 1) * C₁ + max C₂ 0) * (1 + |s.im|) ^ (N + 1) := by
        have : 0 ≤ max C₂ 0 * (1 + |s.im|) ^ (N + 1) := by positivity
        nlinarith
  · have hmem : s ∈ Icc (-1 : ℝ) M ×ℂ Icc (-1 : ℝ) 1 :=
      Complex.mem_reProdIm.mpr ⟨⟨h1, h2⟩, abs_le.mp hsmall⟩
    have h3 := (hC₂ s hmem).trans (le_max_left C₂ 0)
    have hmax0 : (0 : ℝ) ≤ max C₂ 0 := le_max_right _ _
    calc ‖zetaEntire s‖ ≤ max C₂ 0 := h3
      _ ≤ max C₂ 0 * (1 + |s.im|) ^ (N + 1) := le_mul_of_one_le_right hmax0 hpow1
      _ ≤ ((M + 1) * C₁ + max C₂ 0) * (1 + |s.im|) ^ (N + 1) := by
        have : 0 ≤ (M + 1) * C₁ * (1 + |s.im|) ^ (N + 1) := by positivity
        nlinarith

/-- `|M(s)| ≤ N^{3/2}` on `Re s ≥ −½`. -/
theorem norm_edPoly_le_three_halves {b : ℕ → ℂ} {N : ℕ} (hb : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1)
    {s : ℂ} (hs : -(1 / 2) ≤ s.re) :
    ‖edPoly b (Finset.Icc 1 N) s‖ ≤ (N : ℝ) ^ ((3 : ℝ) / 2) := by
  unfold edPoly
  have hterm : ∀ n ∈ Finset.Icc 1 N, ‖b n * ((n : ℝ) : ℂ) ^ (-s)‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast h2
    rw [norm_mul, Complex.ofReal_natCast, Complex.norm_natCast_cpow_of_pos h1, Complex.neg_re]
    have h3 : (n : ℝ) ^ (-s.re) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
      calc (n : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) :=
            Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by linarith) hnN (by norm_num)
    calc ‖b n‖ * (n : ℝ) ^ (-s.re) ≤ 1 * (N : ℝ) ^ ((1 : ℝ) / 2) :=
          mul_le_mul (hb n hn) h3 (by positivity) (by norm_num)
      _ = _ := one_mul _
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ hterm).trans (le_of_eq ?_))
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hN0, Real.rpow_one]

/-- `|M(s)| ≤ 2` on `Re s = 2`. -/
theorem norm_edPoly_le_two {b : ℕ → ℂ} {N : ℕ} (hb : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) {s : ℂ}
    (hs : s.re = 2) : ‖edPoly b (Finset.Icc 1 N) s‖ ≤ 2 := by
  unfold edPoly
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun n hn => ?_) (sum_Icc_inv_sq_le_two N)
  obtain ⟨h1, -⟩ := Finset.mem_Icc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
  rw [norm_mul, Complex.ofReal_natCast, Complex.norm_natCast_cpow_of_pos h1, Complex.neg_re, hs]
  have h3 : (n : ℝ) ^ (-(2 : ℝ)) = ((n : ℝ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hn0.le]
    norm_num
  rw [h3]
  exact mul_le_of_le_one_left (by positivity) (hb n hn)

private theorem re_line (x t : ℝ) : (((1 / 2 + x : ℝ) : ℂ) + (t : ℂ) * I).re = 1 / 2 + x := by simp

private theorem im_line (x t : ℝ) : (((1 / 2 + x : ℝ) : ℂ) + (t : ℂ) * I).im = t := by simp

/-- The window function decays on the strip `−½ ≤ Re s ≤ 2`. -/
theorem exists_stripDecay_mollifiedWindow (t₀ : ℝ) {w : ℝ} (hw : 0 < w) {b : ℕ → ℂ} {N : ℕ}
    (hb : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) :
    ∃ C : ℝ, StripDecay (mollifiedWindow t₀ w b N) (-1) (3 / 2) C := by
  obtain ⟨C₁, k, hC₁, hZ⟩ := exists_norm_zetaEntire_le (M := 2) (by norm_num)
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_one_add_abs_pow_mul_gauss_le (k + 2) t₀ hw
  refine ⟨C₁ * (N : ℝ) ^ ((3 : ℝ) / 2) * 2 * Real.exp (9 / 4 / (2 * w ^ 2)) * C₂, ?_, ?_⟩
  · intro s hs
    refine differentiableAt_mollifiedWindow t₀ w b N ?_
    have := hs.1
    norm_num at this
    linarith
  · intro s hs
    have h1 : -(1 / 2) ≤ s.re := by
      have := hs.1
      norm_num at this
      linarith
    have h2 : s.re ≤ 2 := by
      have := hs.2
      norm_num at this
      linarith
    have hs1 : (1 / 2 : ℝ) ≤ ‖s + 1‖ := by
      have h3 := Complex.abs_re_le_norm (s + 1)
      have h4 : (s + 1).re = s.re + 1 := by simp
      rw [h4] at h3
      have h5 := le_abs_self (s.re + 1)
      linarith
    have hbody : ‖windowBody b N s‖ ≤ (C₁ * (1 + |s.im|) ^ k) * (N : ℝ) ^ ((3 : ℝ) / 2) * 2 := by
      unfold windowBody
      rw [norm_div, norm_mul, div_eq_mul_inv]
      have hinv : ‖s + 1‖⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
      exact mul_le_mul (mul_le_mul (hZ s (by linarith) (by linarith))
        (norm_edPoly_le_three_halves hb h1) (norm_nonneg _) (by positivity)) hinv (by positivity)
        (by positivity)
    have hgauss : ‖gaussWindow t₀ w s‖ ≤
        Real.exp (9 / 4 / (2 * w ^ 2)) * Real.exp (-((s.im - t₀) ^ 2 / (2 * w ^ 2))) := by
      rw [norm_gaussWindow, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hsq : (s.re - 1 / 2) ^ 2 ≤ 9 / 4 := by nlinarith
      have hd : 0 < 2 * w ^ 2 := by positivity
      rw [show 9 / 4 / (2 * w ^ 2) + -((s.im - t₀) ^ 2 / (2 * w ^ 2)) =
        (9 / 4 - (s.im - t₀) ^ 2) / (2 * w ^ 2) by ring]
      exact div_le_div_of_nonneg_right (by linarith) hd.le
    have hpow : (1 + s.im ^ 2) ≤ (1 + |s.im|) ^ 2 := by
      have := sq_abs s.im
      nlinarith [abs_nonneg s.im]
    have hdecay := hC₂ s.im
    have hpos : 0 < 1 + s.im ^ 2 := by positivity
    rw [le_div_iff₀ hpos]
    unfold mollifiedWindow
    rw [norm_mul]
    have hprod : ‖windowBody b N s‖ * ‖gaussWindow t₀ w s‖ ≤
        (C₁ * (1 + |s.im|) ^ k * (N : ℝ) ^ ((3 : ℝ) / 2) * 2) *
          (Real.exp (9 / 4 / (2 * w ^ 2)) * Real.exp (-((s.im - t₀) ^ 2 / (2 * w ^ 2)))) :=
      mul_le_mul hbody hgauss (norm_nonneg _) (by positivity)
    have hE := Real.exp_pos (-((s.im - t₀) ^ 2 / (2 * w ^ 2)))
    calc ‖windowBody b N s‖ * ‖gaussWindow t₀ w s‖ * (1 + s.im ^ 2)
        ≤ ((C₁ * (1 + |s.im|) ^ k * (N : ℝ) ^ ((3 : ℝ) / 2) * 2) *
            (Real.exp (9 / 4 / (2 * w ^ 2)) * Real.exp (-((s.im - t₀) ^ 2 / (2 * w ^ 2))))) *
              (1 + |s.im|) ^ 2 :=
          mul_le_mul hprod hpow hpos.le (by positivity)
      _ = C₁ * (N : ℝ) ^ ((3 : ℝ) / 2) * 2 * Real.exp (9 / 4 / (2 * w ^ 2)) *
            ((1 + |s.im|) ^ (k + 2) * Real.exp (-((s.im - t₀) ^ 2 / (2 * w ^ 2)))) := by ring
      _ ≤ C₁ * (N : ℝ) ^ ((3 : ℝ) / 2) * 2 * Real.exp (9 / 4 / (2 * w ^ 2)) * C₂ :=
          mul_le_mul_of_nonneg_left hdecay (by positivity)

/-! ### Gaussian integrals -/

theorem integrable_gauss (t₀ : ℝ) {w : ℝ} (hw : 0 < w) :
    Integrable fun t : ℝ => Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) := by
  have hb : 0 < 1 / (2 * w ^ 2) := by positivity
  have h := (integrable_exp_neg_mul_sq hb).comp_sub_right t₀
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only
  congr 1
  field_simp

theorem integral_gauss (t₀ : ℝ) {w : ℝ} (hw : 0 < w) :
    ∫ t : ℝ, Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) = w * √(2 * Real.pi) := by
  have hb : 0 < 1 / (2 * w ^ 2) := by positivity
  have h : ∫ t : ℝ, Real.exp (-(1 / (2 * w ^ 2)) * (t - t₀) ^ 2) =
      ∫ t : ℝ, Real.exp (-(1 / (2 * w ^ 2)) * t ^ 2) :=
    integral_sub_right_eq_self (fun t : ℝ => Real.exp (-(1 / (2 * w ^ 2)) * t ^ 2)) t₀
  have hcongr : ∀ t : ℝ, Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) =
      Real.exp (-(1 / (2 * w ^ 2)) * (t - t₀) ^ 2) := by
    intro t
    congr 1
    field_simp
  simp_rw [hcongr]
  rw [h, integral_gaussian]
  have hval : Real.pi / (1 / (2 * w ^ 2)) = w ^ 2 * (2 * Real.pi) := by
    field_simp
  rw [hval, Real.sqrt_mul (by positivity), Real.sqrt_sq hw.le]

/-- **The spectrum right of the band is controlled.**  On `Re s = 2`, `|F| ≤ 4` times the Gaussian. -/
theorem integral_norm_mollifiedWindow_right_le (t₀ : ℝ) {w : ℝ} (hw : 0 < w) {b : ℕ → ℂ} {N : ℕ}
    (hb : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) :
    ∫ t : ℝ, ‖lineFun (mollifiedWindow t₀ w b N) (3 / 2) t‖ ≤
      4 * Real.exp (9 / 4 / (2 * w ^ 2)) * (w * √(2 * Real.pi)) := by
  have hpt : ∀ t : ℝ, ‖lineFun (mollifiedWindow t₀ w b N) (3 / 2) t‖ ≤
      4 * Real.exp (9 / 4 / (2 * w ^ 2)) * Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) := by
    intro t
    unfold lineFun mollifiedWindow
    set s : ℂ := ((1 / 2 + 3 / 2 : ℝ) : ℂ) + (t : ℂ) * I with hs
    have hre : s.re = 2 := by
      rw [hs, re_line]
      norm_num
    have him : s.im = t := by rw [hs, im_line]
    have hne : s ≠ 1 := by
      intro h
      rw [h] at hre
      norm_num at hre
    have hne' : s + 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp [hre] at this
      linarith
    have hratio : ‖s - 1‖ / ‖s + 1‖ ≤ 1 := by
      rw [div_le_one (norm_pos_iff.mpr hne')]
      rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
        Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.sub_im, Complex.add_im,
        Complex.one_im, hre]
      nlinarith
    have hz : ‖riemannZeta s‖ ≤ 2 := by
      have h := Sieve.norm_riemannZeta_le (s := s) (by rw [hre]; norm_num)
      rw [hre] at h
      norm_num at h
      linarith
    have hbody : ‖windowBody b N s‖ ≤ 4 := by
      unfold windowBody
      rw [zetaEntire_eq hne, norm_div, norm_mul, norm_mul]
      have hM := norm_edPoly_le_two hb hre
      calc ‖s - 1‖ * ‖riemannZeta s‖ * ‖edPoly b (Finset.Icc 1 N) s‖ / ‖s + 1‖
          = (‖s - 1‖ / ‖s + 1‖) * (‖riemannZeta s‖ * ‖edPoly b (Finset.Icc 1 N) s‖) := by ring
        _ ≤ 1 * (2 * 2) := mul_le_mul hratio (mul_le_mul hz hM (norm_nonneg _) (by norm_num))
            (by positivity) (by norm_num)
        _ = 4 := by norm_num
    have hgauss : ‖gaussWindow t₀ w s‖ =
        Real.exp (9 / 4 / (2 * w ^ 2)) * Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) := by
      rw [norm_gaussWindow, hre, him, ← Real.exp_add]
      congr 1
      ring
    rw [norm_mul, hgauss]
    calc ‖windowBody b N s‖ * (Real.exp (9 / 4 / (2 * w ^ 2)) *
          Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))))
        ≤ 4 * (Real.exp (9 / 4 / (2 * w ^ 2)) * Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2)))) :=
          mul_le_mul_of_nonneg_right hbody (by positivity)
      _ = _ := by ring
  have hmono := integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
    ((integrable_gauss t₀ hw).const_mul (4 * Real.exp (9 / 4 / (2 * w ^ 2))))
    (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul, integral_gauss t₀ hw] at hmono
  exact hmono

/-- `|ζ(−½ + it)| ≪ (1 + |t|)²`, from the functional equation. -/
theorem exists_norm_riemannZeta_left_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖riemannZeta ((-(1 / 2) : ℝ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ 2 := by
  obtain ⟨C, hC, hχ⟩ := exists_bound_norm_zetaChi_vertical (σ := -(1 / 2)) (by norm_num) (by norm_num)
    (by norm_num)
  refine ⟨3 * C, by positivity, fun t => ?_⟩
  set s : ℂ := ((-(1 / 2) : ℝ) : ℂ) + (t : ℂ) * I with hs
  have hre : s.re = -(1 / 2) := by
    rw [hs]
    simp
  have hne0 : s ≠ 0 := by
    intro h
    rw [h] at hre
    norm_num at hre
  have hne1 : s ≠ 1 := by
    intro h
    rw [h] at hre
    norm_num at hre
  have hG : Complex.Gammaℝ (1 - s) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by simp [hre]; norm_num)
  rw [zeta_eq_zetaChi_mul hne0 hne1 hG, norm_mul]
  have hz : ‖riemannZeta (1 - s)‖ ≤ 3 := by
    have h1re : (1 - s).re = 3 / 2 := by
      simp [hre]
      norm_num
    have h := Sieve.norm_riemannZeta_le (s := 1 - s) (by rw [h1re]; norm_num)
    rw [h1re] at h
    norm_num at h
    linarith
  calc ‖zetaChi s‖ * ‖riemannZeta (1 - s)‖ ≤ (C * (1 + |t|) ^ 2) * 3 :=
        mul_le_mul (hχ t) hz (norm_nonneg _) (by positivity)
    _ = 3 * C * (1 + |t|) ^ 2 := by ring

/-- The Gaussian moment bound. -/
theorem integral_one_add_abs_sq_mul_gauss_le (t₀ : ℝ) {w : ℝ} (hw : 0 < w) :
    ∫ t : ℝ, (1 + |t|) ^ 2 * Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) ≤
      4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * √(2 * Real.pi)) := by
  have hw' : 0 < √2 * w := by positivity
  have hpt : ∀ t : ℝ, (1 + |t|) ^ 2 * Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) ≤
      4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) *
        Real.exp (-((t - t₀) ^ 2 / (2 * (√2 * w) ^ 2))) := by
    intro t
    set y : ℝ := (t - t₀) ^ 2 / (2 * w ^ 2) with hy
    have hy0 : 0 ≤ y := by positivity
    have hτ : (t - t₀) ^ 2 = 2 * w ^ 2 * y := by
      rw [hy]
      field_simp
    have hy2 : (t - t₀) ^ 2 / (2 * (√2 * w) ^ 2) = y / 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hy]
      field_simp
    rw [hy2]
    have htri : 1 + |t| ≤ (1 + |t₀|) * (1 + |t - t₀|) := by
      have h1 : |t| ≤ |t - t₀| + |t₀| := by
        have := abs_add_le (t - t₀) t₀
        simpa using this
      have h2 : 0 ≤ |t₀| * |t - t₀| := by positivity
      nlinarith
    have h1 : (1 + |t|) ^ 2 ≤ (1 + |t₀|) ^ 2 * (1 + |t - t₀|) ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) htri 2
    have h2 : (1 + |t - t₀|) ^ 2 ≤ 2 * ((1 + 2 * w ^ 2) * (1 + y)) := by
      have h3 := sq_abs (t - t₀)
      have h4 : 0 ≤ w ^ 2 * y := by positivity
      rw [hτ] at h3
      nlinarith [sq_nonneg (1 - |t - t₀|)]
    have h3 : (1 + y) * Real.exp (-y) ≤ 2 * Real.exp (-(y / 2)) := by
      have h4 : 1 + y / 2 ≤ Real.exp (y / 2) := by linarith [Real.add_one_le_exp (y / 2)]
      have h5 : Real.exp (-y) = Real.exp (-(y / 2)) * Real.exp (-(y / 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h6 : (1 + y) ≤ 2 * Real.exp (y / 2) := by linarith
      have h7 : Real.exp (y / 2) * Real.exp (-(y / 2)) = 1 := by
        rw [← Real.exp_add]
        simp
      have h8 := Real.exp_pos (-(y / 2))
      calc (1 + y) * Real.exp (-y) ≤ (2 * Real.exp (y / 2)) * Real.exp (-y) :=
            mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le
        _ = 2 * (Real.exp (y / 2) * Real.exp (-(y / 2))) * Real.exp (-(y / 2)) := by rw [h5]; ring
        _ = 2 * Real.exp (-(y / 2)) := by rw [h7]; ring
    calc (1 + |t|) ^ 2 * Real.exp (-y)
        ≤ ((1 + |t₀|) ^ 2 * (2 * ((1 + 2 * w ^ 2) * (1 + y)))) * Real.exp (-y) :=
          mul_le_mul_of_nonneg_right
            (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))) (Real.exp_pos _).le
      _ = 2 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * ((1 + y) * Real.exp (-y)) := by ring
      _ ≤ 2 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (2 * Real.exp (-(y / 2))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun t => by positivity)
    ((integrable_gauss t₀ hw').const_mul (4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2)))
    (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul, integral_gauss t₀ hw'] at hmono
  exact hmono

/-- **The spectrum left of the band is controlled.**  On `Re s = −½` the functional equation gives a bound polynomial in the height,
with the mollifier contributing `N^{3/2}`. -/
theorem exists_integral_norm_mollifiedWindow_left_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (t₀ : ℝ) {w : ℝ} (_ : 0 < w) {b : ℕ → ℂ} {N : ℕ}
      (_ : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1),
      ∫ t : ℝ, ‖lineFun (mollifiedWindow t₀ w b N) (-1) t‖ ≤
        A * (N : ℝ) ^ ((3 : ℝ) / 2) * Real.exp (1 / (2 * w ^ 2)) *
          (4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * √(2 * Real.pi))) := by
  obtain ⟨C, hC, hζ⟩ := exists_norm_riemannZeta_left_le
  refine ⟨3 * C, by positivity, ?_⟩
  intro t₀ w hw b N hb
  have hpt : ∀ t : ℝ, ‖lineFun (mollifiedWindow t₀ w b N) (-1) t‖ ≤
      (3 * C) * (N : ℝ) ^ ((3 : ℝ) / 2) * Real.exp (1 / (2 * w ^ 2)) *
        ((1 + |t|) ^ 2 * Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2)))) := by
    intro t
    unfold lineFun mollifiedWindow
    set s : ℂ := ((1 / 2 + -1 : ℝ) : ℂ) + (t : ℂ) * I with hs
    have hre : s.re = -(1 / 2) := by
      rw [hs, re_line]
      norm_num
    have him : s.im = t := by rw [hs, im_line]
    have hne : s ≠ 1 := by
      intro h
      rw [h] at hre
      norm_num at hre
    have hne' : s + 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp [hre] at this
      linarith
    have hratio : ‖s - 1‖ / ‖s + 1‖ ≤ 3 := by
      rw [div_le_iff₀ (norm_pos_iff.mpr hne')]
      have hsq : ‖s - 1‖ ^ 2 ≤ (3 * ‖s + 1‖) ^ 2 := by
        rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.sub_im, Complex.add_im,
          Complex.one_im, hre]
        nlinarith [mul_self_nonneg s.im]
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq
    have hs' : s = ((-(1 / 2) : ℝ) : ℂ) + (t : ℂ) * I := by
      rw [hs]
      norm_num
    have hz : ‖riemannZeta s‖ ≤ C * (1 + |t|) ^ 2 := by
      rw [hs']
      exact hζ t
    have hM := norm_edPoly_le_three_halves hb (s := s) (by rw [hre])
    have hbody : ‖windowBody b N s‖ ≤ 3 * (C * (1 + |t|) ^ 2) * (N : ℝ) ^ ((3 : ℝ) / 2) := by
      unfold windowBody
      rw [zetaEntire_eq hne, norm_div, norm_mul, norm_mul]
      calc ‖s - 1‖ * ‖riemannZeta s‖ * ‖edPoly b (Finset.Icc 1 N) s‖ / ‖s + 1‖
          = (‖s - 1‖ / ‖s + 1‖) * (‖riemannZeta s‖ * ‖edPoly b (Finset.Icc 1 N) s‖) := by ring
        _ ≤ 3 * ((C * (1 + |t|) ^ 2) * (N : ℝ) ^ ((3 : ℝ) / 2)) :=
          mul_le_mul hratio (mul_le_mul hz hM (norm_nonneg _) (by positivity)) (by positivity)
            (by norm_num)
        _ = _ := by ring
    have hgauss : ‖gaussWindow t₀ w s‖ =
        Real.exp (1 / (2 * w ^ 2)) * Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) := by
      rw [norm_gaussWindow, hre, him, ← Real.exp_add]
      congr 1
      ring
    rw [norm_mul, hgauss]
    calc ‖windowBody b N s‖ * (Real.exp (1 / (2 * w ^ 2)) * Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))))
        ≤ (3 * (C * (1 + |t|) ^ 2) * (N : ℝ) ^ ((3 : ℝ) / 2)) *
            (Real.exp (1 / (2 * w ^ 2)) * Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2)))) :=
          mul_le_mul_of_nonneg_right hbody (by positivity)
      _ = _ := by ring
  have hbound : ∀ᵐ t : ℝ, 0 ≤ (1 + |t|) ^ 2 * Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) :=
    Filter.Eventually.of_forall fun t => by positivity
  -- integrability of the moment comes from the bound by a wider Gaussian
  have hw' : 0 < √2 * w := by positivity
  have hmomint : Integrable fun t : ℝ => (1 + |t|) ^ 2 * Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) := by
    obtain ⟨C₂, hC₂0, hC₂⟩ := exists_one_add_abs_pow_mul_gauss_le 2 t₀ hw'
    have hg := (integrable_gauss t₀ hw').const_mul C₂
    refine Integrable.mono' hg (Continuous.aestronglyMeasurable (by fun_prop))
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have hsplit : Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) =
        Real.exp (-((t - t₀) ^ 2 / (2 * (√2 * w) ^ 2))) *
          Real.exp (-((t - t₀) ^ 2 / (2 * (√2 * w) ^ 2))) := by
      rw [← Real.exp_add, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      field_simp
      ring
    rw [hsplit, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hC₂ t) (Real.exp_pos _).le
  have hmono := integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
    (hmomint.const_mul ((3 * C) * (N : ℝ) ^ ((3 : ℝ) / 2) * Real.exp (1 / (2 * w ^ 2))))
    (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul] at hmono
  refine hmono.trans (mul_le_mul_of_nonneg_left (integral_one_add_abs_sq_mul_gauss_le t₀ hw)
    (by positivity))

end GaloisForLFunctions.ArithmeticProduction
