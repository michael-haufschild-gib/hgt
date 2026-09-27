import GaloisForLFunctions.RHTower.SelbergSymbolCriticalStrip
import GaloisForLFunctions.RHTower.MertensFirst
import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic

/-!
# The archimedean horizon of the Weil symbol of `ζ`

For a polar-constrained `C²` test `f`, the explicit formula writes the zero side of `ζ` as the
symbol form `W(f, h) = ∫ h_{f ⋆ h̃}(τ)(μ(τ) + P_X(τ)) dτ` (`zeta_W_eq_integral_mu_add_PX_bilinear`,
valid for every `C²` second test `h`).  This module shows that its frequencies above an
archimedean horizon `exp(O(√X))` never produce negativity, and then removes them with a
smoothing kernel.

* **Horizon** (`mu_add_PX_nonneg_of_horizon_le`).
  - `Re ψ(¼ + iτ/2) ≥ log(1 + |τ|/4) - 7`, from two steps of `ψ(s+1) = ψ(s) + 1/s` and
    `|ψ(z) - log z| ≤ 3/|z|`.
  - `Σ_{n ≤ N} Λ(n)/√n ≤ 34√N`, by dyadic induction from Chebyshev's bound.
  - Hence `μ + P_X ≥ (log(1 + |τ|/4) - E)/(2π)` with `E = 10 + 68√X`, which is nonnegative for
    `|τ| ≥ 4e^E`.
* **Plancherel** (`integral_norm_sq_paperFT_eq`): `∫|h_f|² = 2π∫|f|²`, from inversion of `f ⋆ f̃` at
  `0`.
* **Smoothing** (`smoothedTest`).
  - The test `g = f ⋆ w_b ⋆ w_b / c_b²`, with `w_b = (b² - u²)₊^{5/2}` and `c_b = ∫w_b`, has
    transform `h_g = h_f · q_b²`, where `q_b = ŵ_b/c_b`.
  - On the real line `q_b` is real and `0 ≤ 1 - q_b² ≤ (bτ)²`.
  - `q_b` is Lipschitz near the real axis and decays like `400/(b³(1 + |Re z|)²)`.
* **The high-frequency part is harmless** (`re_W_sub_W_smoothedTest_ge`).
  `Re(W(f, f) - W(f, g)) ≥ -E(4b e^E)² ∫|f|²` with `X = e^{2(a+2)}`.  So `W(f, f)` equals the
  zero sum `W(f, g)`, whose weights `q_b(γ_ρ)²` are negligible for `|γ_ρ| ≫ 1/b`, up to an error
  that is small once `b ≪ e^{-2E}`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ArithmeticFunction

noncomputable section
namespace RHTower

open Zeta23

/-! ### The prime weight of the symbol -/

/-- `Σ_{n ≤ N} Λ(n) ≤ 7N`. -/
theorem sum_vonMangoldt_Icc_le_seven (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, (Λ d : ℝ) ≤ 7 * N := by
  have h := Mertens.sum_vonMangoldt_Icc_le N
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
    linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-- **Chebyshev in square-root form.**  `Σ_{n ≤ N} Λ(n)/√n ≤ 34 √N`, by dyadic induction: the
block `(N/2, N]` costs at most `√2 · 7 √N`. -/
theorem sum_vonMangoldt_div_sqrt_le (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, (Λ n : ℝ) / Real.sqrt n ≤ 34 * Real.sqrt N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hsplit : Finset.Ioc 0 N = Finset.Ioc 0 (N / 2) ∪ Finset.Ioc (N / 2) N := by
    ext n; simp only [Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Ioc 0 (N / 2)) (Finset.Ioc (N / 2) N) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_Ioc] at h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj]
  have hlow := ih (N / 2) (Nat.div_lt_self hN (by norm_num))
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN := Real.sqrt_pos.mpr hNr
  -- the top block
  have hblock : ∑ n ∈ Finset.Ioc (N / 2) N, (Λ n : ℝ) / Real.sqrt n ≤
      Real.sqrt 2 / Real.sqrt N * (7 * N) := by
    have hpt : ∀ n ∈ Finset.Ioc (N / 2) N,
        (Λ n : ℝ) / Real.sqrt n ≤ Real.sqrt 2 / Real.sqrt N * (Λ n : ℝ) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hn2 : (N : ℝ) < 2 * n := by
        have : N < 2 * n := by omega
        exact_mod_cast this
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hsn := Real.sqrt_pos.mpr hn0
      have hΛ : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
      have hs : Real.sqrt N ≤ Real.sqrt 2 * Real.sqrt n := by
        rw [← Real.sqrt_mul (by norm_num)]
        exact Real.sqrt_le_sqrt (by linarith)
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hsn hsN]
      nlinarith
    have hsum : ∑ n ∈ Finset.Ioc (N / 2) N, (Λ n : ℝ) ≤ 7 * N := by
      refine le_trans ?_ (sum_vonMangoldt_Icc_le_seven N)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn; simp only [Finset.mem_Ioc] at hn; simp only [Finset.mem_Icc]; omega
      · intro n _ _; exact ArithmeticFunction.vonMangoldt_nonneg
    calc ∑ n ∈ Finset.Ioc (N / 2) N, (Λ n : ℝ) / Real.sqrt n
        ≤ ∑ n ∈ Finset.Ioc (N / 2) N, Real.sqrt 2 / Real.sqrt N * (Λ n : ℝ) :=
          Finset.sum_le_sum hpt
      _ = Real.sqrt 2 / Real.sqrt N * ∑ n ∈ Finset.Ioc (N / 2) N, (Λ n : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ Real.sqrt 2 / Real.sqrt N * (7 * N) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
  -- the lower block by induction
  have hhalf : Real.sqrt ((N / 2 : ℕ) : ℝ) * Real.sqrt 2 ≤ Real.sqrt N := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
    apply Real.sqrt_le_sqrt
    have : (N / 2) * 2 ≤ N := Nat.div_mul_le_self N 2
    exact_mod_cast this
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs2l : (1.414 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hNN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNr.le
  have hblock' : Real.sqrt 2 / Real.sqrt N * (7 * N) = 7 * Real.sqrt 2 * Real.sqrt N := by
    field_simp
    nlinarith [hNN]
  rw [hblock'] at hblock
  have hsqh := Real.sqrt_nonneg ((N / 2 : ℕ) : ℝ)
  -- `34 s_h + 7√2 √N ≤ 34 √N` from `s_h √2 ≤ √N`
  have key : 34 * Real.sqrt ((N / 2 : ℕ) : ℝ) ≤ 34 * Real.sqrt N / Real.sqrt 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hfin : 34 * Real.sqrt N / Real.sqrt 2 + 7 * Real.sqrt 2 * Real.sqrt N ≤
      34 * Real.sqrt N := by
    rw [div_add' _ _ _ (by positivity), div_le_iff₀ (by positivity)]
    have e : 7 * Real.sqrt 2 * Real.sqrt N * Real.sqrt 2 = 14 * Real.sqrt N := by
      have : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      nlinarith
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right hs2l hsN.le]
  linarith

/-! ### The archimedean weight of the symbol -/

/-- `Re ψ(¼ + iτ/2) ≥ log(1 + |τ|/4) - 7`: two steps of `ψ(s+1) = ψ(s) + 1/s` and the half-plane
bound `|ψ(z) - log z| ≤ 3/|z|` at `z + 2`. -/
theorem log_sub_seven_le_re_digamma_quarter (τ : ℝ) :
    Real.log (1 + |τ| / 4) - 7 ≤ (Complex.digamma (1 / 4 + I * τ / 2)).re := by
  set z : ℂ := 1 / 4 + I * τ / 2 with hz
  have hzre : z.re = 1 / 4 := by simp [hz]
  have hzim : z.im = τ / 2 := by simp [hz]
  have hne0 : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    rw [hzre] at this
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hne1 : ∀ m : ℕ, z + 1 ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp only [Complex.add_re, hzre, Complex.one_re, Complex.neg_re, Complex.natCast_re] at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h1 := Complex.digamma_apply_add_one z hne0
  have h2 := Complex.digamma_apply_add_one (z + 1) hne1
  have hz2 : z + 1 + 1 = z + 2 := by ring
  rw [hz2] at h2
  have hdig : Complex.digamma z = Complex.digamma (z + 2) - z⁻¹ - (z + 1)⁻¹ := by
    rw [h2, h1]; ring
  have hre2 : (z + 2).re = 9 / 4 := by simp [hzre]; norm_num
  have him2 : (z + 2).im = τ / 2 := by simp [hzim]
  have hn2 : 9 / 4 ≤ ‖z + 2‖ := by
    have := Complex.abs_re_le_norm (z + 2)
    rw [hre2, abs_of_pos (by norm_num)] at this
    exact this
  have hn2' : |τ| / 2 ≤ ‖z + 2‖ := by
    have := Complex.abs_im_le_norm (z + 2)
    rw [him2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at this
    exact this
  have hbound := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos
    (z := z + 2) (by rw [hre2]; norm_num) (by linarith)
  have hre_dig : Real.log ‖z + 2‖ - 3 / ‖z + 2‖ ≤ (Complex.digamma (z + 2)).re := by
    have h := Complex.abs_re_le_norm (Complex.digamma (z + 2) - Complex.log (z + 2))
    rw [Complex.sub_re, Complex.log_re] at h
    have := neg_abs_le ((Complex.digamma (z + 2)).re - Real.log ‖z + 2‖)
    linarith
  have hlogn : Real.log (1 + |τ| / 4) ≤ Real.log ‖z + 2‖ :=
    Real.log_le_log (by positivity) (by linarith)
  have h3 : 3 / ‖z + 2‖ ≤ 4 / 3 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hinv : (z⁻¹).re ≤ 4 := by
    rw [Complex.inv_re, Complex.normSq_apply, hzre, hzim]
    rw [div_le_iff₀ (by nlinarith [sq_nonneg (τ / 2)])]
    nlinarith [sq_nonneg (τ / 2)]
  have hinv1 : ((z + 1)⁻¹).re ≤ 4 / 5 := by
    have hr : (z + 1).re = 5 / 4 := by simp [hzre]; norm_num
    have hi : (z + 1).im = τ / 2 := by simp [hzim]
    rw [Complex.inv_re, Complex.normSq_apply, hr, hi]
    rw [div_le_iff₀ (by nlinarith [sq_nonneg (τ / 2)])]
    nlinarith [sq_nonneg (τ / 2)]
  rw [hdig, Complex.sub_re, Complex.sub_re]
  linarith

/-- `μ(τ) ≥ (log(1 + |τ|/4) - 10)/(2π)`. -/
theorem mu_ge_log (τ : ℝ) : (Real.log (1 + |τ| / 4) - 10) / (2 * π) ≤ mu τ := by
  have h := log_sub_seven_le_re_digamma_quarter τ
  have hπ : Real.log π ≤ 3 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_lt_d2]
  have hπ0 : 0 < 2 * π := by positivity
  have e : mu τ = ((Complex.digamma (1 / 4 + I * τ / 2)).re - Real.log π) / (2 * π) := by
    unfold mu; field_simp
  rw [e, div_le_div_iff_of_pos_right hπ0]
  linarith

/-- `P_X(τ) ≥ -(34/π)√X`. -/
theorem PX_ge_neg_sqrt {X : ℝ} (hX : 0 ≤ X) (τ : ℝ) : -(34 / π * Real.sqrt X) ≤ PX X τ := by
  unfold PX
  have hsum : ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (Λ n : ℝ) / Real.sqrt n * Real.cos (τ * Real.log n) ≤
      34 * Real.sqrt X := by
    calc ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (Λ n : ℝ) / Real.sqrt n * Real.cos (τ * Real.log n)
        ≤ ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (Λ n : ℝ) / Real.sqrt n := by
          refine Finset.sum_le_sum fun n _ => ?_
          have h0 : 0 ≤ (Λ n : ℝ) / Real.sqrt n :=
            div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
          exact mul_le_of_le_one_right h0 (Real.cos_le_one _)
      _ ≤ 34 * Real.sqrt (⌊X⌋₊ : ℝ) := sum_vonMangoldt_div_sqrt_le _
      _ ≤ 34 * Real.sqrt X := by
          gcongr; exact Nat.floor_le hX
  have hπ := Real.pi_pos
  have h := mul_le_mul_of_nonneg_left hsum (le_of_lt (one_div_pos.mpr hπ))
  have e : 34 / π * Real.sqrt X = 1 / π * (34 * Real.sqrt X) := by ring
  linarith

/-- The exponent `10 + 68√X` of the archimedean horizon of the symbol `μ + P_X`. -/
def horizonExponent (X : ℝ) : ℝ := 10 + 68 * Real.sqrt X

theorem horizonExponent_pos (X : ℝ) : 0 < horizonExponent X := by
  unfold horizonExponent; positivity

/-- `μ + P_X ≥ (log(1 + |τ|/4) - (10 + 68√X))/(2π)`. -/
theorem mu_add_PX_ge {X : ℝ} (hX : 0 ≤ X) (τ : ℝ) :
    (Real.log (1 + |τ| / 4) - horizonExponent X) / (2 * π) ≤ mu τ + PX X τ := by
  have h1 := mu_ge_log τ
  have h2 := PX_ge_neg_sqrt hX τ
  have hπ := Real.pi_pos
  have e : (Real.log (1 + |τ| / 4) - horizonExponent X) / (2 * π) =
      (Real.log (1 + |τ| / 4) - 10) / (2 * π) - 34 / π * Real.sqrt X := by
    unfold horizonExponent; field_simp; ring
  linarith

/-- **The archimedean horizon.**  Above `|τ| = 4 e^{10 + 68√X}` the symbol `μ + P_X` is
nonnegative. -/
theorem mu_add_PX_nonneg_of_horizon_le {X : ℝ} (hX : 0 ≤ X) {τ : ℝ}
    (hτ : 4 * Real.exp (horizonExponent X) ≤ |τ|) : 0 ≤ mu τ + PX X τ := by
  refine le_trans ?_ (mu_add_PX_ge hX τ)
  apply div_nonneg _ (by positivity)
  have : horizonExponent X ≤ Real.log (1 + |τ| / 4) := by
    rw [← Real.log_exp (horizonExponent X)]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  linarith

/-- Everywhere, `μ + P_X ≥ -(10 + 68√X)/(2π)`. -/
theorem neg_horizonExponent_le_mu_add_PX {X : ℝ} (hX : 0 ≤ X) (τ : ℝ) :
    -(horizonExponent X / (2 * π)) ≤ mu τ + PX X τ := by
  refine le_trans ?_ (mu_add_PX_ge hX τ)
  have : 0 ≤ Real.log (1 + |τ| / 4) := Real.log_nonneg (by linarith [abs_nonneg τ])
  rw [← neg_div, div_le_div_iff_of_pos_right (by positivity)]
  linarith

/-! ### Plancherel and the bilinear symbol form -/

/-- **Plancherel.**  `∫ |h_f|² = 2π ∫ |f|²` for a `C²` test of compact support, by inversion of
`k = f ⋆ f̃` at `0`. -/
theorem integral_norm_sq_paperFT_eq {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 = 2 * π * ∫ u : ℝ, ‖f u‖ ^ 2 := by
  obtain ⟨hfc, hkd, -, hki, hFk⟩ := weilTest_self_data hf hfs
  have hinv := EF.k_add_k_neg hkd.continuous hki hFk 0
  simp only [neg_zero, mul_zero, Real.cos_zero, Complex.ofReal_one, mul_one] at hinv
  have hk0 : EF.weilTest f f 0 = ((∫ u : ℝ, ‖f u‖ ^ 2 : ℝ) : ℂ) := by
    rw [weilTest_apply, ← integral_complex_ofReal]
    congr 1 with t
    rw [sub_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hint : ∫ τ : ℝ, paperFT (EF.weilTest f f) τ = ((∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1 with τ
    rw [paperFT_weilTest_self_ofReal hf.continuous hfc]
  rw [hk0, hint] at hinv
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : ((∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 : ℝ) : ℂ) =
      ((2 * π * ∫ u : ℝ, ‖f u‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    field_simp at hinv ⊢
    linear_combination -hinv
  exact_mod_cast h2

/-- The zero side of `W(f, h)` is summable for `C²` tests of compact support. -/
theorem zeta_Wsummand_summable {f h : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ 2 h)
    (hfc : HasCompactSupport f) (hhc : HasCompactSupport h) :
    Summable (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f h ρ) := by
  have hkd := EF.weilTest_contDiff hf hh.continuous hfc
  have hkc := EF.weilTest_hasCompactSupport hfc hhc
  obtain ⟨hsum, -⟩ := WeilEF.EF_lit_zetaZeroConfig _ hkd hkc
  have hfac := EF.paperFT_weilTest hf.continuous hh.continuous hfc hhc
  refine hsum.congr fun ρ => ?_
  simp only [ZeroConfig.Wsummand, hfac, mul_assoc]

/-- **The bilinear symbol form.**  For a polar-constrained `C²` test `f` and any `C²` test `h`,
both supported in `[-A, A]`, `W(f, h) = ∫ h_{f ⋆ h̃}(τ)(μ(τ) + P_X(τ)) dτ` with `X = e^{2A}`. -/
theorem zeta_W_eq_integral_mu_add_PX_bilinear {A : ℝ} {f h : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hh : ContDiff ℝ 2 h) (hfs : tsupport f ⊆ Icc (-A) A) (hhs : tsupport h ⊆ Icc (-A) A)
    (hp : paperFT f (I / 2) = 0) (hm : paperFT f (-(I / 2)) = 0) :
    zetaZeroConfig.W f h =
      ∫ τ : ℝ, paperFT (EF.weilTest f h) τ * ((mu τ + PX (Real.exp (2 * A)) τ : ℝ) : ℂ) := by
  have hfs' : tsupport f ⊆ Icc (-(2 * A / 2)) (2 * A / 2) := by
    rwa [mul_div_cancel_left₀ _ two_ne_zero]
  have hhs' : tsupport h ⊆ Icc (-(2 * A / 2)) (2 * A / 2) := by
    rwa [mul_div_cancel_left₀ _ two_ne_zero]
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  have hhc : HasCompactSupport h :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport h) hhs
  set k := EF.weilTest f h with hk
  have hkd : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hh.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hhc
  have hks : tsupport k ⊆ Icc (-(2 * A)) (2 * A) := EF.tsupport_weilTest_subset hfs' hhs'
  have hFk := EF.integrable_fourier_of_contDiff_two hkd hkc
  have hμ := EF.integrable_paperFT_mul_mu hkd hkc gammaFacts
  have hPX := EF.integrable_paperFT_mul_PX (2 * A) hFk
  obtain ⟨-, heq⟩ := WeilEF.EF_lit_zetaZeroConfig k hkd hkc
  have hfac := EF.paperFT_weilTest hf.continuous hh.continuous hfc hhc
  have hterm : (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℂ) * paperFT k (gammaOf ρ)) =
      fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f h ρ := by
    ext ρ; simp only [ZeroConfig.Wsummand, hk, hfac, mul_assoc]
  have hpole1 : paperFT k (I / 2) = 0 := by rw [hk, hfac, hp, zero_mul]
  have hpole2 : paperFT k (-I / 2) = 0 := by rw [hk, hfac, neg_div, hm, zero_mul]
  rw [ZeroConfig.W, ← hterm, heq, EF.literatureRHS, hpole1, hpole2, zero_add, zero_sub,
    EF.prime_term hkd.continuous hks hFk, EF.gamma_term, ← integral_add hPX hμ]
  congr 1
  ext τ
  push_cast
  ring

/-! ### The smoothing kernel -/

/-- `∫ (b² - u²)₊^{5/2}`, the mass of the kernel. -/
def kernelMass (b : ℝ) : ℝ := ∫ u, sinhTestWeight b u

/-- `q_b(z) = ŵ_b(z)/ŵ_b(0)`, the normalized transform of `w_b = (b² - u²)₊^{5/2}`. -/
def kernelQ (b : ℝ) (z : ℂ) : ℂ :=
  paperFT (fun u => (sinhTestWeight b u : ℂ)) z / (kernelMass b : ℂ)

theorem kernelMass_ge {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) : 27 / 64 * b ^ 7 ≤ kernelMass b := by
  have h := sinhTestWeight_cosh_energy_ge' hb 0
  simp only [zero_mul, Real.cosh_zero, mul_one] at h
  have hx0 : 0 < 3 * b ^ 2 / 4 := by positivity
  have hx1 : 3 * b ^ 2 / 4 ≤ 1 := by nlinarith
  have hr : (3 * b ^ 2 / 4) ^ (3 : ℝ) ≤ (3 * b ^ 2 / 4) ^ (5 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by norm_num)
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hr
  unfold kernelMass
  calc 27 / 64 * b ^ 7 = b * (3 * b ^ 2 / 4) ^ 3 := by ring
    _ ≤ b * (3 * b ^ 2 / 4) ^ (5 / 2 : ℝ) := mul_le_mul_of_nonneg_left hr hb.le
    _ ≤ _ := h

theorem kernelMass_pos {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) : 0 < kernelMass b :=
  lt_of_lt_of_le (by positivity) (kernelMass_ge hb hb1)

theorem integral_norm_kernel_eq (b : ℝ) :
    ∫ u, ‖((sinhTestWeight b u : ℝ) : ℂ)‖ = kernelMass b := by
  unfold kernelMass
  congr 1 with u
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sinhTestWeight_nonneg b u)]

/-- `q_b(z) = conj q_b(z̄)`: the kernel is real and even. -/
theorem conj_kernelQ_conj (b : ℝ) (z : ℂ) : conj (kernelQ b (conj z)) = kernelQ b z := by
  unfold kernelQ
  rw [map_div₀, conj_paperFT_conj_of_even (sinhTestWeight_even b), Complex.conj_ofReal]

theorem norm_kernelQ_le {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (z : ℂ) :
    ‖kernelQ b z‖ ≤ Real.exp (|z.im| * b) := by
  have hm := kernelMass_pos hb hb1
  unfold kernelQ
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm, div_le_iff₀ hm]
  have h := norm_paperFT_le (f := fun u => ((sinhTestWeight b u : ℝ) : ℂ))
    ((sinhTestWeight_contDiff b).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_of_support_subset_abs (sinhTestWeight_supp hb.le))).ofReal
    (fun u hu => sinhTestWeight_supp hb.le u (fun h => hu (by simp [h]))) z
  rwa [integral_norm_kernel_eq] at h

/-- The kernel transform is Lipschitz near the real axis. -/
theorem norm_kernelQ_sub_le {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {z₁ z₂ : ℂ}
    (hz : b * ‖z₁ - z₂‖ ≤ 1) :
    ‖kernelQ b z₁ - kernelQ b z₂‖ ≤ 2 * b * ‖z₁ - z₂‖ * Real.exp (|z₂.im| * b) := by
  have hm := kernelMass_pos hb hb1
  have h := norm_paperFT_sub_le (sinhTestWeight_contDiff b).continuous
    (sinhTestWeight_supp hb.le) hz
  have habs : ∫ u, |sinhTestWeight b u| = kernelMass b := by
    unfold kernelMass; congr 1 with u; exact abs_of_nonneg (sinhTestWeight_nonneg b u)
  rw [habs] at h
  unfold kernelQ
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm, div_le_iff₀ hm]
  exact h

/-- On the real line `q_b(τ)` is a real number `r` with `0 ≤ 1 - r² ≤ (bτ)²`. -/
theorem kernelQ_real {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (τ : ℝ) :
    ∃ r : ℝ, kernelQ b τ = (r : ℂ) ∧ 0 ≤ 1 - r ^ 2 ∧ 1 - r ^ 2 ≤ (b * τ) ^ 2 := by
  have hm := kernelMass_pos hb hb1
  have hreal : (kernelQ b τ).im = 0 := by
    have h := conj_kernelQ_conj b (τ : ℂ)
    rw [Complex.conj_ofReal] at h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  set r := (kernelQ b τ).re with hr
  have hq : kernelQ b τ = (r : ℂ) := Complex.ext (by simp [hr]) (by simp [hreal])
  have hnorm := norm_kernelQ_le hb hb1 (τ : ℂ)
  simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero] at hnorm
  rw [hq, Complex.norm_real, Real.norm_eq_abs] at hnorm
  -- `1 - r = (1/c) ∫ w_b(u)(1 - cos τu) ≤ (bτ)²/2`
  have hcont : Continuous (fun u => sinhTestWeight b u) := (sinhTestWeight_contDiff b).continuous
  have hcs : HasCompactSupport (fun u => sinhTestWeight b u) :=
    hasCompactSupport_of_support_subset_abs (sinhTestWeight_supp hb.le)
  have hre : r * kernelMass b = ∫ u, sinhTestWeight b u * Real.cos (τ * u) := by
    have hmc : (kernelMass b : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    have h1 : kernelQ b τ * (kernelMass b : ℂ) =
        paperFT (fun u => (sinhTestWeight b u : ℂ)) τ := by
      unfold kernelQ; exact div_mul_cancel₀ _ hmc
    rw [hq] at h1
    have h2 := congrArg Complex.re h1
    rw [← Complex.ofReal_mul, Complex.ofReal_re, paperFT_def] at h2
    have hint : Integrable (fun u : ℝ => ((sinhTestWeight b u : ℝ) : ℂ) * cexp (I * τ * u)) :=
      ((Complex.continuous_ofReal.comp hcont).mul (by fun_prop)).integrable_of_hasCompactSupport
        (hcs.comp_left Complex.ofReal_zero).mul_right
    have hre' := integral_re hint
    simp only [RCLike.re_to_complex] at hre'
    rw [h2, ← hre']
    congr 1 with u
    rw [show I * (τ : ℂ) * (u : ℂ) = ((τ * u : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul, mul_one,
      add_zero, zero_add, Complex.mul_im]
  have hdef : kernelMass b - r * kernelMass b ≤ (b * τ) ^ 2 / 2 * kernelMass b := by
    rw [hre]
    unfold kernelMass
    have hi1 : Integrable (fun u => sinhTestWeight b u) := hcont.integrable_of_hasCompactSupport hcs
    have hi2 : Integrable (fun u => sinhTestWeight b u * Real.cos (τ * u)) :=
      (hcont.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
    rw [← integral_sub hi1 hi2, ← integral_const_mul]
    refine integral_mono (hi1.sub hi2) (hi1.const_mul _) fun u => ?_
    simp only
    have hw := sinhTestWeight_nonneg b u
    have hcos := Real.one_sub_sq_div_two_le_cos (x := τ * u)
    by_cases hu : |u| ≤ b
    · have hu2 : u ^ 2 ≤ b ^ 2 := by nlinarith [abs_nonneg u, sq_abs u]
      have : 1 - Real.cos (τ * u) ≤ (b * τ) ^ 2 / 2 := by nlinarith [sq_nonneg τ]
      nlinarith
    · push Not at hu
      rw [sinhTestWeight_eq_zero hb.le hu]; simp
  have h1r : 1 - r ≤ (b * τ) ^ 2 / 2 := by
    have := hdef
    rw [show kernelMass b - r * kernelMass b = (1 - r) * kernelMass b by ring] at this
    exact le_of_mul_le_mul_right this hm
  have hr1 : |r| ≤ 1 := hnorm
  refine ⟨r, hq, ?_, ?_⟩
  · nlinarith [abs_le.mp hr1, sq_abs r]
  · have hr1' := abs_le.mp hr1
    nlinarith

/-- **Decay of the kernel.**  `|q_b(z)| ≤ e^{b|Im z|} · 400/(b³(1 + |Re z|)²)` for `0 < b ≤ 1`. -/
theorem norm_kernelQ_le_decay {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (z : ℂ) :
    ‖kernelQ b z‖ ≤ Real.exp (|z.im| * b) * 400 / (b ^ 3 * (1 + |z.re|) ^ 2) := by
  have hm := kernelMass_ge hb hb1
  have hm0 := kernelMass_pos hb hb1
  have hS : ContDiff ℝ 2 (fun u => (sinhTestWeight b u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (sinhTestWeight_contDiff b)
  have hSs : ∀ u, (fun u => (sinhTestWeight b u : ℂ)) u ≠ 0 → |u| ≤ b := fun u hu =>
    sinhTestWeight_supp hb.le u (fun h => hu (by simp [h]))
  have hd := norm_paperFT_le_decay hS hSs z
  change _ ≤ Real.exp _ * (4 * testNorm (sinhTestWeight b)) / _ at hd
  have hT := testNorm_sinhTestWeight_le hb.le
  have hT' : 4 * testNorm (sinhTestWeight b) ≤ 168 * b ^ 4 := by
    have : b ^ 6 ≤ b ^ 4 := pow_le_pow_of_le_one hb.le hb1 (by norm_num)
    nlinarith [testNorm_nonneg (sinhTestWeight b)]
  unfold kernelQ
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0, div_le_iff₀ hm0]
  have hD : 0 < (1 + |z.re|) ^ 2 := by positivity
  have hE := Real.exp_pos (|z.im| * b)
  calc ‖paperFT (fun u => (sinhTestWeight b u : ℂ)) z‖
      ≤ Real.exp (|z.im| * b) * (4 * testNorm (sinhTestWeight b)) / (1 + |z.re|) ^ 2 := hd
    _ ≤ Real.exp (|z.im| * b) * (168 * b ^ 4) / (1 + |z.re|) ^ 2 := by gcongr
    _ ≤ Real.exp (|z.im| * b) * 400 / (b ^ 3 * (1 + |z.re|) ^ 2) * (27 / 64 * b ^ 7) := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hD (by positivity)]
        have : 0 < Real.exp (|z.im| * b) * (1 + |z.re|) ^ 2 * b ^ 7 := by positivity
        nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)

/-! ### The smoothed test `g = f ⋆ w_b ⋆ w_b / c²` -/

/-- The kernel `w_b` as a complex function. -/
def smoothingKernelFun (b : ℝ) : ℝ → ℂ := fun u => ((sinhTestWeight b u : ℝ) : ℂ)

/-- The smoothed test with transform `h_f · q_b²`. -/
def smoothedTest (b : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun u => ((1 / kernelMass b ^ 2 : ℝ) : ℂ) *
    EF.weilTest (EF.weilTest f (smoothingKernelFun b)) (smoothingKernelFun b) u

theorem continuous_smoothingKernelFun (b : ℝ) : Continuous (smoothingKernelFun b) :=
  Complex.continuous_ofReal.comp (sinhTestWeight_contDiff b).continuous

theorem hasCompactSupport_smoothingKernelFun {b : ℝ} (hb : 0 ≤ b) :
    HasCompactSupport (smoothingKernelFun b) :=
  hasCompactSupport_of_support_subset_abs
    fun u hu => sinhTestWeight_supp hb u (fun h => hu (by simp [smoothingKernelFun, h]))

theorem tsupport_smoothingKernelFun_subset {b : ℝ} (hb : 0 ≤ b) :
    tsupport (smoothingKernelFun b) ⊆ Icc (-b) b :=
  tsupport_subset_of_support_subset_abs
    fun u hu => sinhTestWeight_supp hb u (fun h => hu (by simp [smoothingKernelFun, h]))

/-- Supports add under the Weil convolution `f ⋆ g̃`. -/
theorem tsupport_weilTest_subset_add {f g : ℝ → ℂ} {A B : ℝ}
    (hfs : tsupport f ⊆ Icc (-A) A) (hgs : tsupport g ⊆ Icc (-B) B) :
    tsupport (EF.weilTest f g) ⊆ Icc (-(A + B)) (A + B) := by
  have hgs' : tsupport g ⊆ Icc (-(2 * B / 2)) (2 * B / 2) := by
    rwa [mul_div_cancel_left₀ _ two_ne_zero]
  refine closure_minimal ?_ isClosed_Icc
  refine (support_convolution_subset _).trans ?_
  rintro x ⟨u, hu, v, hv, rfl⟩
  have hu' := hfs (subset_tsupport _ hu)
  have hv' := EF.tsupport_tilde_subset hgs' (subset_tsupport _ hv)
  rw [mul_div_cancel_left₀ _ two_ne_zero] at hv'
  simp only [mem_Icc] at hu' hv' ⊢
  constructor <;> linarith [hu'.1, hu'.2, hv'.1, hv'.2]

theorem smoothedTest_contDiff {b : ℝ} (hb : 0 ≤ b) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) : ContDiff ℝ 2 (smoothedTest b f) := by
  have h1 := EF.weilTest_contDiff hf (continuous_smoothingKernelFun b) hfc
  have h1c := EF.weilTest_hasCompactSupport hfc (hasCompactSupport_smoothingKernelFun hb)
  exact contDiff_const.mul (EF.weilTest_contDiff h1 (continuous_smoothingKernelFun b) h1c)

theorem hasCompactSupport_smoothedTest {b : ℝ} (hb : 0 ≤ b) {f : ℝ → ℂ}
    (hfc : HasCompactSupport f) : HasCompactSupport (smoothedTest b f) := by
  have h1c := EF.weilTest_hasCompactSupport hfc (hasCompactSupport_smoothingKernelFun hb)
  exact (EF.weilTest_hasCompactSupport h1c (hasCompactSupport_smoothingKernelFun hb)).mul_left

theorem tsupport_smoothedTest_subset {b A : ℝ} (hb : 0 ≤ b) {f : ℝ → ℂ}
    (hfs : tsupport f ⊆ Icc (-A) A) :
    tsupport (smoothedTest b f) ⊆ Icc (-(A + 2 * b)) (A + 2 * b) := by
  have h1 := tsupport_weilTest_subset_add hfs (tsupport_smoothingKernelFun_subset hb)
  have h2 := tsupport_weilTest_subset_add h1 (tsupport_smoothingKernelFun_subset hb)
  refine (closure_mono (Function.support_mul_subset_right _ _)).trans ?_
  rw [show A + 2 * b = A + b + b by ring]
  exact h2

/-- `h_g(z) = h_f(z) q_b(z)²`. -/
theorem paperFT_smoothedTest {b : ℝ} (hb : 0 ≤ b) {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (z : ℂ) :
    paperFT (smoothedTest b f) z = paperFT f z * kernelQ b z ^ 2 := by
  have hK := continuous_smoothingKernelFun b
  have hKc := hasCompactSupport_smoothingKernelFun hb
  have h1 : Continuous (EF.weilTest f (smoothingKernelFun b)) := by
    unfold EF.weilTest
    exact hfc.continuous_convolution_left _ hf (EF.continuous_tilde hK).locallyIntegrable
  have h1c := EF.weilTest_hasCompactSupport hfc hKc
  have hconst : paperFT (smoothedTest b f) z = ((1 / kernelMass b ^ 2 : ℝ) : ℂ) *
      paperFT (EF.weilTest (EF.weilTest f (smoothingKernelFun b)) (smoothingKernelFun b)) z := by
    unfold smoothedTest
    rw [paperFT_def, paperFT_def, ← integral_const_mul]
    congr 1 with u
    ring
  have hconj : conj (paperFT (smoothingKernelFun b) (conj z)) = paperFT (smoothingKernelFun b) z :=
    conj_paperFT_conj_of_even (sinhTestWeight_even b) z
  rw [hconst, EF.paperFT_weilTest h1 hK h1c hKc, EF.paperFT_weilTest hf hK hfc hKc, hconj]
  unfold kernelQ
  change _ = _ * (paperFT (smoothingKernelFun b) z / _) ^ 2
  push_cast
  ring

/-! ### The symbol side of the split -/

theorem integrable_paperFT_mul_mu_add_PX {k : ℝ → ℂ} (hkd : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (L : ℝ) :
    Integrable (fun τ : ℝ => paperFT k τ * ((mu τ + PX (Real.exp L) τ : ℝ) : ℂ)) := by
  have hFk := EF.integrable_fourier_of_contDiff_two hkd hkc
  have hμ := EF.integrable_paperFT_mul_mu hkd hkc gammaFacts
  have hPX := EF.integrable_paperFT_mul_PX L hFk
  refine (hμ.add hPX).congr (Eventually.of_forall fun τ => ?_)
  simp only [Pi.add_apply]
  push_cast
  ring

/-- **The high-frequency part is harmless.**  For a polar-constrained `C²` test `f` on `[-a, a]`
and `0 < b ≤ 1`, with `X = e^{2(a+2)}` and `E = 10 + 68√X`:
`Re(W(f, f) - W(f, g)) ≥ -E (4b e^E)² ∫|f|²`.  The symbol form of the difference has density
`|h_f|²(1 - q_b²)(μ + P_X)`; above `|τ| = 4e^E` the symbol is nonnegative, and below it
`0 ≤ 1 - q_b² ≤ (4b e^E)²`. -/
theorem re_W_sub_W_smoothedTest_ge {a b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hp : paperFT f (I / 2) = 0) (hm : paperFT f (-(I / 2)) = 0) :
    -(horizonExponent (Real.exp (2 * (a + 2))) *
        (4 * b * Real.exp (horizonExponent (Real.exp (2 * (a + 2))))) ^ 2 *
        ∫ u, ‖f u‖ ^ 2) ≤
      (zetaZeroConfig.W f f - zetaZeroConfig.W f (smoothedTest b f)).re := by
  set A := a + 2 with hA
  set X := Real.exp (2 * A) with hX
  set E := horizonExponent X with hE
  have hX0 : 0 ≤ X := (Real.exp_pos _).le
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  have hfA : tsupport f ⊆ Icc (-A) A := hfs.trans (Icc_subset_Icc (by linarith) (by linarith))
  set g := smoothedTest b f with hgdef
  have hg : ContDiff ℝ 2 g := smoothedTest_contDiff hb.le hf hfc
  have hgc : HasCompactSupport g := hasCompactSupport_smoothedTest hb.le hfc
  have hgA : tsupport g ⊆ Icc (-A) A :=
    (tsupport_smoothedTest_subset hb.le hfs).trans (Icc_subset_Icc (by linarith) (by linarith))
  have h1 := zeta_W_eq_integral_mu_add_PX_bilinear hf hf hfA hfA hp hm
  have h2 := zeta_W_eq_integral_mu_add_PX_bilinear hf hg hfA hgA hp hm
  have hk1 := EF.weilTest_contDiff hf hf.continuous hfc
  have hk1c := EF.weilTest_hasCompactSupport hfc hfc
  have hk2 := EF.weilTest_contDiff hf hg.continuous hfc
  have hk2c := EF.weilTest_hasCompactSupport hfc hgc
  have i1 := integrable_paperFT_mul_mu_add_PX hk1 hk1c (2 * A)
  have i2 := integrable_paperFT_mul_mu_add_PX hk2 hk2c (2 * A)
  rw [h1, h2, ← integral_sub i1 i2]
  have i12 : Integrable (fun τ : ℝ =>
      paperFT (EF.weilTest f f) τ * ((mu τ + PX X τ : ℝ) : ℂ) -
        paperFT (EF.weilTest f g) τ * ((mu τ + PX X τ : ℝ) : ℂ)) := i1.sub i2
  have iR : Integrable (fun τ : ℝ =>
      (paperFT (EF.weilTest f f) τ * ((mu τ + PX X τ : ℝ) : ℂ) -
        paperFT (EF.weilTest f g) τ * ((mu τ + PX X τ : ℝ) : ℂ)).re) := i12.re
  have hre := integral_re i12
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  -- the pointwise bound
  have hfacf := EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc
  have hfacg := EF.paperFT_weilTest hf.continuous hg.continuous hfc hgc
  have hpt : ∀ τ : ℝ, -(E / (2 * π) * (4 * b * Real.exp E) ^ 2) * ‖paperFT f τ‖ ^ 2 ≤
      (paperFT (EF.weilTest f f) τ * ((mu τ + PX X τ : ℝ) : ℂ) -
        paperFT (EF.weilTest f g) τ * ((mu τ + PX X τ : ℝ) : ℂ)).re := by
    intro τ
    obtain ⟨r, hr, hr0, hr1⟩ := kernelQ_real hb hb1 τ
    have hgτ : paperFT g (conj (τ : ℂ)) = paperFT f τ * (r : ℂ) ^ 2 := by
      rw [Complex.conj_ofReal, hgdef, paperFT_smoothedTest hb.le hf.continuous hfc, hr]
    have hval : paperFT (EF.weilTest f f) τ * ((mu τ + PX X τ : ℝ) : ℂ) -
        paperFT (EF.weilTest f g) τ * ((mu τ + PX X τ : ℝ) : ℂ) =
        ((‖paperFT f τ‖ ^ 2 * (1 - r ^ 2) * (mu τ + PX X τ) : ℝ) : ℂ) := by
      rw [hfacf, hfacg, hgτ]
      simp only [Complex.conj_ofReal, map_mul, map_pow]
      have hn : paperFT f τ * conj (paperFT f τ) = ((‖paperFT f τ‖ : ℝ) : ℂ) ^ 2 :=
        Complex.mul_conj' _
      push_cast
      linear_combination ((mu τ + PX X τ : ℂ) * (1 - (r : ℂ) ^ 2)) * hn
    rw [hval, Complex.ofReal_re]
    have hN := sq_nonneg ‖paperFT f τ‖
    have hπ := Real.pi_pos
    have hE0 : 0 < E := horizonExponent_pos X
    rcases le_or_gt (4 * Real.exp E) |τ| with hτ | hτ
    · have hs := mu_add_PX_nonneg_of_horizon_le hX0 hτ
      have : 0 ≤ ‖paperFT f τ‖ ^ 2 * (1 - r ^ 2) * (mu τ + PX X τ) := by positivity
      have : 0 ≤ E / (2 * π) * (4 * b * Real.exp E) ^ 2 := by positivity
      nlinarith
    · have hs := neg_horizonExponent_le_mu_add_PX hX0 τ
      have hbτ : (b * τ) ^ 2 ≤ (4 * b * Real.exp E) ^ 2 := by
        have : |b * τ| ≤ 4 * b * Real.exp E := by
          rw [abs_mul, abs_of_pos hb]; nlinarith
        nlinarith [sq_abs (b * τ), abs_nonneg (b * τ)]
      have h1r : 1 - r ^ 2 ≤ (4 * b * Real.exp E) ^ 2 := hr1.trans hbτ
      have hq : (1 - r ^ 2) * (mu τ + PX X τ) ≥ -((4 * b * Real.exp E) ^ 2 * (E / (2 * π))) := by
        have hE2 : 0 ≤ E / (2 * π) := by positivity
        nlinarith
      nlinarith
  have hplan := integral_norm_sq_paperFT_eq hf hfs
  have hi2 := integrable_normSq_paperFT hf hfs
  have hmono := integral_mono (hi2.const_mul (-(E / (2 * π) * (4 * b * Real.exp E) ^ 2))) iR hpt
  rw [integral_const_mul, hplan] at hmono
  have hπ := Real.pi_pos
  have e : -(E / (2 * π) * (4 * b * Real.exp E) ^ 2) * (2 * π * ∫ u, ‖f u‖ ^ 2) =
      -(E * (4 * b * Real.exp E) ^ 2 * ∫ u, ‖f u‖ ^ 2) := by field_simp
  rw [e] at hmono
  exact hmono

end RHTower
