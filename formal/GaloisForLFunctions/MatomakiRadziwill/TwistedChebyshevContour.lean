import GaloisForLFunctions.MatomakiRadziwill.LFunctionLogDerivStrip
import GaloisForLFunctions.RHTower.Sieve.InvZetaRegular
import GaloisForLFunctions.RHTower.Sieve.PerronErrorTotalChebyshev
import GaloisForLFunctions.RHTower.Sieve.ChebyshevMasterInequality

/-!
# The twisted Chebyshev sum by a contour shift

For a nonprincipal character `χ` and real `τ`, the coefficients `c_n = χ(n)Λ(n)n^{-iτ}`
(`twistedVM`) have Dirichlet series `−L'/L(s + iτ, χ)` on `Re s > 1`.  Truncated Perron at
`x = N + ½`, abscissa `σ₀ ∈ (1, 2]` and height `T` (`Sieve.norm_tsum_lt_sub_perron_integral_le`),
followed by Cauchy's theorem on the rectangle `[σ₁, σ₀] × [−T, T]`
(`Sieve.integral_vertical_sub_eq_horizontal_rect`) gives the master inequality
(`norm_twistedChebyshev_le`): if `L(u + i(t + τ), χ) ≠ 0` and `‖L'/L(u + i(t + τ), χ)‖ ≤ B` for
`σ₁ ≤ u ≤ σ₀`, `|t| ≤ T`, then

`‖Σ_{n ≤ N} c_n‖ ≤ E_Perron(N, σ₀, T) + (1/2π)(2T B x^{σ₁}/σ₁ + 2(σ₀ − σ₁) B x^{σ₀}/T)`,

`E_Perron` the explicit truncation error of the untwisted Chebyshev sum
(`Sieve.perron_error_vonMangoldt_total_le`), since `‖c_n‖ ≤ Λ(n)`.  There is no main term: `χ ≠ 1`
makes `L(·, χ)` entire, and the rectangle avoids `s = 0`.
-/

open Complex LSeries ArithmeticFunction RHTower.Sieve
open scoped LSeries.notation

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

variable {q : ℕ} [NeZero q]

/-- The twisted von Mangoldt coefficients `χ(n)Λ(n)n^{-iτ}`. -/
def twistedVM (χ : DirichletCharacter ℂ q) (τ : ℝ) (n : ℕ) : ℂ :=
  χ n * ((Λ n : ℝ) : ℂ) * (n : ℂ) ^ (-((τ : ℂ) * I))

omit [NeZero q] in
theorem twistedVM_zero (χ : DirichletCharacter ℂ q) (τ : ℝ) : twistedVM χ τ 0 = 0 := by
  simp [twistedVM]

omit [NeZero q] in
theorem norm_twistedVM_le (χ : DirichletCharacter ℂ q) (τ : ℝ) (n : ℕ) :
    ‖twistedVM χ τ n‖ ≤ ‖((Λ n : ℝ) : ℂ)‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [twistedVM]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hpow : ‖(n : ℂ) ^ (-((τ : ℂ) * I))‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    simp
  rw [twistedVM, norm_mul, norm_mul, hpow, mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)

/-- The Dirichlet series of the twisted coefficients is `−L'/L(s + iτ, χ)`. -/
theorem tsum_twistedVM_cpow (χ : DirichletCharacter ℂ q) (τ : ℝ) {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, twistedVM χ τ n * (n : ℂ) ^ (-s) =
      -logDeriv (DirichletCharacter.LFunction χ) (s + (τ : ℂ) * I) := by
  have hs' : 1 < (s + (τ : ℂ) * I).re := by simpa using hs
  rw [logDeriv_apply, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs',
    DirichletCharacter.LFunction_eq_LSeries χ hs', ← neg_div,
    ← DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs', LSeries]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [twistedVM]
  rw [term_of_ne_zero hn, twistedVM]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hsplit : (n : ℂ) ^ (-(s + (τ : ℂ) * I)) = (n : ℂ) ^ (-((τ : ℂ) * I)) * (n : ℂ) ^ (-s) := by
    rw [← Complex.cpow_add _ _ hn0]
    ring_nf
  rw [div_eq_mul_inv, ← Complex.cpow_neg, hsplit]
  simp only [Pi.mul_apply]
  ring

omit [NeZero q] in
/-- The Perron sum at a half-integer cutoff is the partial sum over `1 ≤ n ≤ N`. -/
theorem tsum_indicator_twistedVM_eq (χ : DirichletCharacter ℂ q) (τ : ℝ) (N : ℕ) :
    ∑' n : ℕ, (if (n : ℝ) < (N : ℝ) + 1 / 2 then twistedVM χ τ n else 0)
      = ∑ n ∈ Finset.Icc 1 N, twistedVM χ τ n := by
  classical
  have hsupp : ∀ n : ℕ, n ∉ Finset.range (N + 1) →
      (if (n : ℝ) < (N : ℝ) + 1 / 2 then twistedVM χ τ n else 0) = 0 := by
    intro n hn
    rw [Finset.mem_range] at hn
    refine if_neg ?_
    have : (N : ℝ) + 1 ≤ (n : ℝ) := by
      have : N + 1 ≤ n := by omega
      exact_mod_cast this
    linarith
  rw [tsum_eq_sum hsupp]
  have hterm : ∀ n ∈ Finset.range (N + 1),
      (if (n : ℝ) < (N : ℝ) + 1 / 2 then twistedVM χ τ n else 0) = twistedVM χ τ n := by
    intro n hn
    rw [Finset.mem_range] at hn
    refine if_pos ?_
    have : (n : ℝ) ≤ (N : ℝ) := by
      have : n ≤ N := by omega
      exact_mod_cast this
    linarith
  rw [Finset.sum_congr rfl hterm]
  rw [show Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega]
  rw [Finset.sum_insert (by simp), twistedVM_zero, zero_add]

/-- The shifted Perron integrand `−L'/L(s + iτ, χ) · x^s/s`. -/
def twistedPerronIntegrand (χ : DirichletCharacter ℂ q) (τ x : ℝ) (s : ℂ) : ℂ :=
  (-logDeriv (DirichletCharacter.LFunction χ) (s + (τ : ℂ) * I)) * ((x : ℂ) ^ s / s)

/-- `logDeriv L` is differentiable wherever `L ≠ 0`, for nonprincipal `χ`. -/
theorem differentiableAt_logDeriv_LFunction (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {w : ℂ}
    (hw : DirichletCharacter.LFunction χ w ≠ 0) :
    DifferentiableAt ℂ (logDeriv (DirichletCharacter.LFunction χ)) w := by
  have hL : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hdL : DifferentiableAt ℂ (deriv (DirichletCharacter.LFunction χ)) w :=
    ((hL.differentiableOn.deriv isOpen_univ) w (Set.mem_univ w)).differentiableAt
      (isOpen_univ.mem_nhds (Set.mem_univ w))
  have h : DifferentiableAt ℂ
      (fun z => deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z) w :=
    hdL.div (hL w) hw
  exact h

/-- The shifted line point: `(u + it) + iτ = u + i(t + τ)`. -/
theorem line_add_shift (u t τ : ℝ) :
    ((u : ℂ) + (t : ℂ) * I) + (τ : ℂ) * I = (u : ℂ) + ((t + τ : ℝ) : ℂ) * I := by
  push_cast; ring

/-- The integrand is holomorphic on the rectangle when `L(· + iτ)` has no zero there. -/
theorem differentiableOn_twistedPerronIntegrand (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {τ x σ₁ σ₀ T : ℝ} (hx : 0 < x) (hσ₁ : 0 < σ₁) (hσ₁₀ : σ₁ ≤ σ₀) (hT0 : 0 ≤ T)
    (hne : ∀ u t : ℝ, σ₁ ≤ u → u ≤ σ₀ → |t| ≤ T →
      DirichletCharacter.LFunction χ ((u : ℂ) + ((t + τ : ℝ) : ℂ) * I) ≠ 0) :
    DifferentiableOn ℂ (twistedPerronIntegrand χ τ x) (Set.uIcc σ₁ σ₀ ×ℂ Set.uIcc (-T) T) := by
  intro s hs
  rw [Complex.mem_reProdIm] at hs
  have hre := hs.1
  have him := hs.2
  rw [Set.uIcc_of_le hσ₁₀] at hre
  have hT : |s.im| ≤ T := by
    rw [Set.uIcc_of_le (by linarith)] at him
    exact abs_le.mpr ⟨him.1, him.2⟩
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hre
    linarith [hre.1]
  have hpt : s + (τ : ℂ) * I = (s.re : ℂ) + ((s.im + τ : ℝ) : ℂ) * I := by
    conv_lhs => rw [← Complex.re_add_im s]
    exact line_add_shift s.re s.im τ
  have hLne : DirichletCharacter.LFunction χ (s + (τ : ℂ) * I) ≠ 0 := by
    rw [hpt]; exact hne s.re s.im hre.1 hre.2 hT
  have h1 : DifferentiableAt ℂ (fun z : ℂ => -logDeriv (DirichletCharacter.LFunction χ)
      (z + (τ : ℂ) * I)) s := by
    have hshift : DifferentiableAt ℂ (fun z : ℂ => z + (τ : ℂ) * I) s :=
      differentiableAt_id.add_const _
    exact ((differentiableAt_logDeriv_LFunction χ hχ hLne).comp s hshift).neg
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := by simpa using hx.ne'
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ z / z) s :=
    (differentiableAt_id.const_cpow (Or.inl hxne)).div differentiableAt_id hs0
  exact (h1.mul h2).differentiableWithinAt

/-- Pointwise bound for the integrand: `‖G(u + it)‖ ≤ B · x^u / ‖u + it‖`. -/
theorem norm_twistedPerronIntegrand_le (χ : DirichletCharacter ℂ q) {τ x u t B : ℝ}
    (hx : 0 < x)
    (hB : ‖logDeriv (DirichletCharacter.LFunction χ) ((u : ℂ) + ((t + τ : ℝ) : ℂ) * I)‖ ≤ B) :
    ‖twistedPerronIntegrand χ τ x ((u : ℂ) + (t : ℂ) * I)‖
      ≤ B * (x ^ u / ‖(u : ℂ) + (t : ℂ) * I‖) := by
  rw [twistedPerronIntegrand, line_add_shift, norm_mul, norm_neg, norm_div,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : ((u : ℂ) + (t : ℂ) * I).re = u := by simp
  rw [hre]
  exact mul_le_mul_of_nonneg_right hB (by positivity)

/-- **The master inequality for the twisted Chebyshev sum.** -/
theorem norm_twistedChebyshev_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ : ℝ) {N : ℕ}
    (hN : 1 ≤ N) {σ₁ σ₀ T B : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₀ : σ₁ ≤ σ₀) (hσ₀ : 1 < σ₀) (hσ₀2 : σ₀ ≤ 2)
    (hT : 0 < T)
    (hstrip : ∀ u t : ℝ, σ₁ ≤ u → u ≤ σ₀ → |t| ≤ T →
      DirichletCharacter.LFunction χ ((u : ℂ) + ((t + τ : ℝ) : ℂ) * I) ≠ 0 ∧
      ‖logDeriv (DirichletCharacter.LFunction χ) ((u : ℂ) + ((t + τ : ℝ) : ℂ) * I)‖ ≤ B) :
    ‖∑ n ∈ Finset.Icc 1 N, twistedVM χ τ n‖
      ≤ ((1 / (Real.pi * T * Real.log 2)) * (((N : ℝ) + 1 / 2) ^ σ₀ * (8 / (σ₀ - 1) ^ 2))
          + (16 * Real.log (2 * ((N : ℝ) + 1 / 2)) * ((N : ℝ) + 1 / 2) / (Real.pi * T))
            * (4 * (1 + Real.log ((2 * N + 2 : ℕ) : ℝ))))
        + (1 / (2 * Real.pi)) * (B * (((N : ℝ) + 1 / 2) ^ σ₁ / σ₁) * (2 * T)
          + 2 * (B * (((N : ℝ) + 1 / 2) ^ σ₀ / T) * (σ₀ - σ₁))) := by
  set x : ℝ := (N : ℝ) + 1 / 2 with hxdef
  have hx : 0 < x := by positivity
  have hx1 : 1 ≤ x := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hσ₀0 : 0 < σ₀ := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hstrip σ₁ 0 le_rfl hσ₁₀ (by simp [hT.le])).2
  set c : ℕ → ℂ := twistedVM χ τ with hcdef
  -- Perron
  have hne : ∀ n : ℕ, (n : ℝ) ≠ x := by
    intro n hcon
    have h2 : (2 * n : ℤ) = 2 * (N : ℤ) + 1 := by
      have : (2 * (n : ℝ)) = 2 * (N : ℝ) + 1 := by rw [hcon, hxdef]; ring
      exact_mod_cast this
    omega
  have hconvΛ := summable_vonMangoldt_perron hx hσ₀
  have hconv : Summable (fun n : ℕ => ‖c n‖ * (x / n) ^ σ₀) :=
    hconvΛ.of_nonneg_of_le (fun n => by positivity)
      (fun n => mul_le_mul_of_nonneg_right (norm_twistedVM_le χ τ n) (by positivity))
  have hdefΛ := summable_perron_error (c := fun n : ℕ => ((Λ n : ℝ) : ℂ)) hx hσ₀0 hT hconvΛ
  have hdef := summable_perron_error (c := c) hx hσ₀0 hT hconv
  have hperron := norm_tsum_lt_sub_perron_integral_le (c := c) (twistedVM_zero χ τ) hx hne hσ₀0 hT
    hconv hdef
  rw [tsum_indicator_twistedVM_eq] at hperron
  have hintegrand : ∀ t : ℝ,
      (∑' n : ℕ, c n * ((n : ℂ) ^ (-((σ₀ : ℂ) + (t : ℝ) * I))))
        * ((x : ℂ) ^ ((σ₀ : ℂ) + (t : ℝ) * I) / ((σ₀ : ℂ) + (t : ℝ) * I))
      = twistedPerronIntegrand χ τ x ((σ₀ : ℂ) + (t : ℂ) * I) := by
    intro t
    rw [twistedPerronIntegrand, hcdef, tsum_twistedVM_cpow χ τ (by simpa using hσ₀)]
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
    twistedPerronIntegrand χ τ x ((σ₀ : ℂ) + (t : ℂ) * I)) (fun t _ => hintegrand t)] at hperron
  -- the Perron error is at most the untwisted one
  have herr : (∑' n : ℕ, ‖c n‖ * ((x / n) ^ σ₀ / (Real.pi * T * |Real.log (x / n)|)))
      ≤ ∑' n : ℕ, ‖((Λ n : ℝ) : ℂ)‖ * ((x / n) ^ σ₀ / (Real.pi * T * |Real.log (x / n)|)) :=
    hdef.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (norm_twistedVM_le χ τ n)
      (by positivity)) hdefΛ
  have htotal := perron_error_vonMangoldt_total_le (N := N) hN hσ₀ hσ₀2 hT
  -- the contour shift
  have hdiff := differentiableOn_twistedPerronIntegrand χ hχ (τ := τ) hx hσ₁ hσ₁₀ hT.le
    (fun u t hu1 hu2 ht => (hstrip u t hu1 hu2 ht).1)
  have hshift := integral_vertical_sub_eq_horizontal_rect (G := twistedPerronIntegrand χ τ x)
    (c := σ₁) (d := σ₀) T hdiff
  set V₀ := ∫ y : ℝ in (-T)..T, twistedPerronIntegrand χ τ x ((σ₀ : ℂ) + (y : ℂ) * I) with hV₀
  set V₁ := ∫ y : ℝ in (-T)..T, twistedPerronIntegrand χ τ x ((σ₁ : ℂ) + (y : ℂ) * I) with hV₁
  set Hp := ∫ u : ℝ in σ₁..σ₀, twistedPerronIntegrand χ τ x ((u : ℂ) + ((T : ℝ) : ℂ) * I) with hHp
  set Hm := ∫ u : ℝ in σ₁..σ₀, twistedPerronIntegrand χ τ x ((u : ℂ) + ((-T : ℝ) : ℂ) * I)
    with hHm
  have hV₀le : ‖V₀‖ ≤ ‖V₁‖ + ‖Hp‖ + ‖Hm‖ := by
    have h1 : I • V₀ = I • V₁ + (Hp - Hm) := by rw [← hshift]; abel
    have h2 : ‖I • V₀‖ = ‖V₀‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    have h3 : ‖I • V₁‖ = ‖V₁‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    rw [← h2, h1]
    calc ‖I • V₁ + (Hp - Hm)‖ ≤ ‖I • V₁‖ + ‖Hp - Hm‖ := norm_add_le _ _
      _ ≤ ‖V₁‖ + (‖Hp‖ + ‖Hm‖) := by rw [h3]; gcongr; exact norm_sub_le _ _
      _ = ‖V₁‖ + ‖Hp‖ + ‖Hm‖ := by ring
  -- the left edge
  have hV₁le : ‖V₁‖ ≤ B * (x ^ σ₁ / σ₁) * (2 * T) := by
    have hb : ∀ t ∈ Set.uIoc (-T) T,
        ‖twistedPerronIntegrand χ τ x ((σ₁ : ℂ) + (t : ℂ) * I)‖ ≤ B * (x ^ σ₁ / σ₁) := by
      intro t ht
      rw [Set.uIoc_of_le (by linarith)] at ht
      have htT : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      refine le_trans (norm_twistedPerronIntegrand_le χ hx (hstrip σ₁ t le_rfl hσ₁₀ htT).2) ?_
      refine mul_le_mul_of_nonneg_left ?_ hB0
      have hden : σ₁ ≤ ‖(σ₁ : ℂ) + (t : ℂ) * I‖ := by
        have h := Complex.abs_re_le_norm ((σ₁ : ℂ) + (t : ℂ) * I)
        have hre : ((σ₁ : ℂ) + (t : ℂ) * I).re = σ₁ := by simp
        rw [hre, abs_of_pos hσ₁] at h
        exact h
      exact div_le_div_of_nonneg_left (by positivity) hσ₁ hden
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
    have hlen : |T - -T| = 2 * T := by rw [sub_neg_eq_add, abs_of_pos (by linarith)]; ring
    rw [hlen] at h
    exact h
  -- the horizontal edges
  have hH : ∀ y : ℝ, |y| = T →
      ‖∫ u : ℝ in σ₁..σ₀, twistedPerronIntegrand χ τ x ((u : ℂ) + (y : ℂ) * I)‖
        ≤ B * (x ^ σ₀ / T) * (σ₀ - σ₁) := by
    intro y hy
    have hb : ∀ u ∈ Set.uIoc σ₁ σ₀,
        ‖twistedPerronIntegrand χ τ x ((u : ℂ) + (y : ℂ) * I)‖ ≤ B * (x ^ σ₀ / T) := by
      intro u hu
      rw [Set.uIoc_of_le hσ₁₀] at hu
      refine le_trans (norm_twistedPerronIntegrand_le χ hx
        (hstrip u y hu.1.le hu.2 (le_of_eq hy)).2) ?_
      refine mul_le_mul_of_nonneg_left ?_ hB0
      have hden : T ≤ ‖(u : ℂ) + (y : ℂ) * I‖ := by
        have h := Complex.abs_im_le_norm ((u : ℂ) + (y : ℂ) * I)
        have him : ((u : ℂ) + (y : ℂ) * I).im = y := by simp
        rw [him, hy] at h
        exact h
      have hxu : x ^ u ≤ x ^ σ₀ := Real.rpow_le_rpow_of_exponent_le hx1 hu.2
      calc x ^ u / ‖(u : ℂ) + (y : ℂ) * I‖ ≤ x ^ σ₀ / ‖(u : ℂ) + (y : ℂ) * I‖ :=
            div_le_div_of_nonneg_right hxu (norm_nonneg _)
        _ ≤ x ^ σ₀ / T := div_le_div_of_nonneg_left (by positivity) hT hden
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [abs_of_nonneg (by linarith)] at h
    exact h
  have hHp' : ‖Hp‖ ≤ B * (x ^ σ₀ / T) * (σ₀ - σ₁) := by
    have h := hH T (abs_of_pos hT)
    simpa [hHp] using h
  have hHm' : ‖Hm‖ ≤ B * (x ^ σ₀ / T) * (σ₀ - σ₁) := by
    have h := hH (-T) (by rw [abs_neg, abs_of_pos hT])
    simpa [hHm] using h
  -- assembly
  have hfinal : ‖∑ n ∈ Finset.Icc 1 N, c n‖
      ≤ ‖∑ n ∈ Finset.Icc 1 N, c n - ((1 / (2 * Real.pi) : ℝ) : ℂ) * V₀‖
        + (1 / (2 * Real.pi)) * ‖V₀‖ := by
    have h := norm_le_norm_sub_add (∑ n ∈ Finset.Icc 1 N, c n) (((1 / (2 * Real.pi) : ℝ) : ℂ) * V₀)
    have h2 : ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * V₀‖ = (1 / (2 * Real.pi)) * ‖V₀‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hscale : (1 / (2 * Real.pi)) * ‖V₀‖ ≤ (1 / (2 * Real.pi)) * (B * (x ^ σ₁ / σ₁) * (2 * T)
      + 2 * (B * (x ^ σ₀ / T) * (σ₀ - σ₁))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have hP : ‖∑ n ∈ Finset.Icc 1 N, c n - ((1 / (2 * Real.pi) : ℝ) : ℂ) * V₀‖
      ≤ (1 / (Real.pi * T * Real.log 2)) * (x ^ σ₀ * (8 / (σ₀ - 1) ^ 2))
        + (16 * Real.log (2 * x) * x / (Real.pi * T)) * (4 * (1 + Real.log ((2 * N + 2 : ℕ) : ℝ))) :=
    le_trans hperron (le_trans herr htotal)
  linarith

end

end GaloisForLFunctions.MatomakiRadziwill
