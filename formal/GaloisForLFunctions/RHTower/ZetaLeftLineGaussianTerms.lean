import GaloisForLFunctions.RHTower.ZetaLeftLineGaussianIntegrals

/-!
# The three Gaussian left-line integrals

With `G(s) = r^s g_T(s)`, `s_t = −½ + it`, `X = T/r ≥ 1`, `T ≥ 1`:

* (`exists_leftLine_sq_logDeriv`) `∫ (ζ'²/ζ)(s_t) G(s_t) dt = −2πr Σ ℓ(n) J_T(nr) + O(T)`;
* (`exists_leftLine_logDeriv`) `∫ (ζ'/ζ)(s_t) G(s_t) dt = O(T (log T + 1))`;
* (`exists_leftLine_zetaChi_logDeriv`) `∫ χ(s_t) (ζ'/ζ)(s_t) G(s_t) dt = O(T (log T + 1))`.

The kernel sums are controlled by `|J_T(y)| ≤ C min(1, (T/y)²)` and the layer bound.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower.GaussZeroSum

noncomputable section

/-- The decay profile `φ(u) = min(1, u⁻²)`. -/
def decayProfile (u : ℝ) : ℝ := min 1 (u ^ 2)⁻¹

theorem decayProfile_le_one (u : ℝ) : decayProfile u ≤ 1 := min_le_left _ _

theorem decayProfile_nonneg (u : ℝ) : 0 ≤ decayProfile u :=
  le_min zero_le_one (inv_nonneg.mpr (sq_nonneg u))

theorem decayProfile_mul_sq_le (u : ℝ) (hu : 0 < u) : decayProfile u * u ^ 2 ≤ 1 := by
  have h : decayProfile u ≤ (u ^ 2)⁻¹ := min_le_right _ _
  calc decayProfile u * u ^ 2 ≤ (u ^ 2)⁻¹ * u ^ 2 := mul_le_mul_of_nonneg_right h (sq_nonneg u)
    _ = 1 := inv_mul_cancel₀ (by positivity)

/-- `|J_T(y)| ≤ C min(1, (T/y)²)`. -/
theorem exists_abs_leftKernel_le_decay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → ∀ y : ℝ, 0 < y →
      |leftKernel T y| ≤ C * decayProfile (y / T) := by
  obtain ⟨C₂, hC₂, h₂⟩ := exists_abs_leftKernel_le_sq
  set C₁ : ℝ := 2 * Real.sqrt 2 * Real.exp 5 with hC₁
  refine ⟨max C₁ C₂, le_trans (by positivity) (le_max_left _ _), fun T hT y hy => ?_⟩
  have hT0 : 0 < T := by linarith
  unfold decayProfile
  rcases le_total 1 ((y / T) ^ 2)⁻¹ with h | h
  · rw [min_eq_left h, mul_one]
    exact (abs_leftKernel_le hT y).trans (le_max_left _ _)
  · rw [min_eq_right h]
    have h2 := h₂ T hT y hy
    calc |leftKernel T y| ≤ C₂ * T ^ 2 / y ^ 2 := h2
      _ = C₂ * ((y / T) ^ 2)⁻¹ := by field_simp
      _ ≤ max C₁ C₂ * ((y / T) ^ 2)⁻¹ := by gcongr; exact le_max_right _ _

/-- **Kernel sums.**  For `c ≥ 0` with `c(0) = 0` and `Σ_{a ≤ m} c(a) ≤ K m (log m + 1)^k`:
`Σ c(n) |J_T(nr)|` converges and is at most `C_J · 48 K X (log X + 1)^k`, `X = T/r ≥ 1`. -/
theorem tsum_mul_abs_leftKernel_le {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (hc0 : c 0 = 0) {K : ℝ}
    (hK : 0 ≤ K) {k : ℕ} (hk : k ≤ 2)
    (hpart : ∀ m : ℕ, ∑ a ∈ Finset.Icc 1 m, c a ≤ K * m * (Real.log m + 1) ^ k)
    {CJ : ℝ} (hCJ : 0 ≤ CJ)
    (hJ : ∀ T : ℝ, 1 ≤ T → ∀ y : ℝ, 0 < y → |leftKernel T y| ≤ CJ * decayProfile (y / T))
    {T r : ℝ} (hT : 1 ≤ T) (hr : 0 < r) (hX : 1 ≤ T / r) :
    Summable (fun n => c n * |leftKernel T (n * r)|) ∧
      ∑' n, c n * |leftKernel T (n * r)| ≤ CJ * (48 * K * (T / r) * (Real.log (T / r) + 1) ^ k) := by
  have hT0 : 0 < T := by linarith
  have hpos : ∀ n, 0 ≤ c n * |leftKernel T (n * r)| := fun n => mul_nonneg (hc n) (abs_nonneg _)
  have hrange : ∀ N : ℕ, ∑ n ∈ Finset.range N, c n * |leftKernel T (n * r)| ≤
      CJ * (48 * K * (T / r) * (Real.log (T / r) + 1) ^ k) := by
    intro N
    have hsub : ∑ n ∈ Finset.range N, c n * |leftKernel T (n * r)| ≤
        ∑ n ∈ Finset.Icc 1 N, c n * |leftKernel T (n * r)| := by
      rw [Finset.range_eq_Ico]
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp
      rw [Finset.sum_eq_sum_Ico_succ_bot hN, hc0, zero_mul, zero_add]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun n hn => by rw [Finset.mem_Ico] at hn; rw [Finset.mem_Icc]; omega)
        (fun n _ _ => hpos n)
    refine hsub.trans ?_
    have hpt : ∀ n ∈ Finset.Icc 1 N, c n * |leftKernel T (n * r)| ≤
        CJ * (c n * decayProfile (n / (T / r))) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have h := hJ T hT (n * r) (by positivity)
      have he : n * r / T = n / (T / r) := by field_simp
      rw [he] at h
      calc c n * |leftKernel T (n * r)| ≤ c n * (CJ * decayProfile (n / (T / r))) :=
            mul_le_mul_of_nonneg_left h (hc n)
        _ = _ := by ring
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_mul_weight_le_layers hc hK hk hpart decayProfile_le_one
      decayProfile_mul_sq_le hX N) hCJ
  exact ⟨summable_of_sum_range_le hpos hrange, Real.tsum_le_of_sum_range_le hpos hrange⟩

/-- The kernel sum, as an `if n = 0` series in `ℂ`. -/
theorem norm_tsum_ite_leftKernel_le {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (hc0 : c 0 = 0) {K : ℝ}
    (hK : 0 ≤ K) {k : ℕ} (hk : k ≤ 2)
    (hpart : ∀ m : ℕ, ∑ a ∈ Finset.Icc 1 m, c a ≤ K * m * (Real.log m + 1) ^ k)
    {CJ : ℝ} (hCJ : 0 ≤ CJ)
    (hJ : ∀ T : ℝ, 1 ≤ T → ∀ y : ℝ, 0 < y → |leftKernel T y| ≤ CJ * decayProfile (y / T))
    {T r : ℝ} (hT : 1 ≤ T) (hr : 0 < r) (hX : 1 ≤ T / r) :
    ‖∑' n : ℕ, (if n = 0 then (0 : ℂ) else (c n : ℂ) * leftKernel T (n * r))‖ ≤
      CJ * (48 * K * (T / r) * (Real.log (T / r) + 1) ^ k) := by
  obtain ⟨hsum, hle⟩ := tsum_mul_abs_leftKernel_le hc hc0 hK hk hpart hCJ hJ hT hr hX
  have hnorm : ∀ n : ℕ, ‖(if n = 0 then (0 : ℂ) else (c n : ℂ) * leftKernel T (n * r))‖ =
      c n * |leftKernel T (n * r)| := by
    intro n
    split_ifs with h
    · subst h; simp [hc0]
    · rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (hc n)]
  have hs : Summable fun n : ℕ => ‖(if n = 0 then (0 : ℂ) else (c n : ℂ) * leftKernel T (n * r))‖ := by
    simp_rw [hnorm]; exact hsum
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  simp_rw [hnorm]
  exact hle

/-! ## Dirichlet series on `Re w = 3/2` -/

theorem LSeriesSummable_logVM {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable (fun n => (logVM n : ℂ)) w := by
  rw [← logMul_vonMangoldt_convolution_one]
  have hab : LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < w.re :=
    lt_of_le_of_lt abscissa_vonMangoldt_le (by exact_mod_cast hw)
  exact (LSeriesSummable_of_abscissaOfAbsConv_lt_re (by rwa [LSeries.abscissaOfAbsConv_logMul])).convolution
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re (lt_of_le_of_lt abscissa_one_le (by exact_mod_cast hw)))

theorem abscissa_logVM_le : LSeries.abscissaOfAbsConv (fun n => (logVM n : ℂ)) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    LSeriesSummable_logVM (by simpa using hy)

theorem continuous_LSeries_one_sub_leftPt {f : ℕ → ℂ} (hf : LSeries.abscissaOfAbsConv f ≤ 1) :
    Continuous fun t => LSeries f (1 - leftPt t) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hmem : (1 - leftPt t) ∈ {s : ℂ | LSeries.abscissaOfAbsConv f < s.re} := by
    show LSeries.abscissaOfAbsConv f < ((1 - leftPt t).re : EReal)
    have : (1 - leftPt t).re = 3 / 2 := by simp [leftPt]; norm_num
    rw [this]
    exact lt_of_le_of_lt hf (by exact_mod_cast (by norm_num : (1 : ℝ) < 3 / 2))
  have hopen : IsOpen {s : ℂ | LSeries.abscissaOfAbsConv f < s.re} :=
    isOpen_lt continuous_const (continuous_coe_real_ereal.comp Complex.continuous_re)
  have hc : ContinuousAt (fun t : ℝ => 1 - leftPt t) t :=
    (continuous_const.sub continuous_leftPt).continuousAt
  exact ContinuousAt.comp (g := LSeries f) (f := fun t : ℝ => 1 - leftPt t)
    ((LSeries_differentiableOn f).differentiableAt (hopen.mem_nhds hmem)).continuousAt hc

theorem exists_norm_LSeries_one_sub_leftPt_le {f : ℕ → ℂ} (hf : LSeriesSummable f ((3 / 2 : ℝ) : ℂ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, ‖LSeries f (1 - leftPt t)‖ ≤ K := by
  refine ⟨∑' n, ‖LSeries.term f ((3 / 2 : ℝ) : ℂ) n‖, tsum_nonneg fun _ => norm_nonneg _, fun t => ?_⟩
  have hre : (1 - leftPt t).re = 3 / 2 := by simp [leftPt]; norm_num
  exact norm_LSeries_le_of_re hre hf

/-! ## Rule A on the left line -/

theorem gW2_sub_eq (T r : ℝ) (s : ℂ) :
    gW2 T r s - (Real.log r : ℂ) ^ 2 * gW T r s =
      (2 * (Real.log r : ℂ) * (2 * (s - 1 / 2) / (T : ℂ) ^ 2) + (2 * (s - 1 / 2) / (T : ℂ) ^ 2) ^ 2 +
        2 / (T : ℂ) ^ 2) * gW T r s := by
  unfold gW2; ring

theorem norm_two_mul_leftPt_sub_half_div_le {T : ℝ} (hT : 1 ≤ T) (t : ℝ) :
    ‖2 * (leftPt t - 1 / 2) / (T : ℂ) ^ 2‖ ≤ 2 * (1 + |t|) / T ^ 2 := by
  have hT0 : 0 < T := by linarith
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0,
    show ‖(2 : ℂ)‖ = 2 by norm_num]
  gcongr
  exact norm_leftPt_sub_half_le t

/-- The correction `∫ ζ(s_t) (G'' − log²r · G)(s_t) dt` is `O(T)`. -/
theorem exists_norm_integral_gW2_sub_le {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      ∫ t : ℝ, ‖(gW2 T r (leftPt t) - (Real.log r : ℂ) ^ 2 * gW T r (leftPt t)) *
        riemannZeta (leftPt t)‖ ≤ C * T := by
  obtain ⟨C0, hC00, hC0⟩ := exists_norm_riemannZeta_leftPt_le
  set L : ℝ := |Real.log r| with hL
  set E : ℝ := Real.exp (5 / 2) * Real.sqrt (2 * Real.pi) with hE
  refine ⟨C0 * r ^ (-1 / 2 : ℝ) * E * (8 * L + 26), by positivity, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  set M : ℝ → ℝ := fun t => C0 * r ^ (-1 / 2 : ℝ) * (4 * L / T ^ 2 * ((1 + |t|) ^ 2 *
      Real.exp ((1 - t ^ 2) / T ^ 2)) + 4 / T ^ 4 * ((1 + |t|) ^ 3 *
      Real.exp ((1 - t ^ 2) / T ^ 2)) + 2 / T ^ 2 * ((1 + |t|) ^ 1 *
      Real.exp ((1 - t ^ 2) / T ^ 2))) with hM
  have hint2 := integrable_poly_gauss_real 2 hT
  have hint3 := integrable_poly_gauss_real 3 hT
  have hint1 := integrable_poly_gauss_real 1 hT
  have hMint : Integrable M :=
    (((hint2.const_mul _).add (hint3.const_mul _)).add (hint1.const_mul _)).const_mul _
  have hpt : ∀ t, ‖(gW2 T r (leftPt t) - (Real.log r : ℂ) ^ 2 * gW T r (leftPt t)) *
      riemannZeta (leftPt t)‖ ≤ M t := by
    intro t
    rw [gW2_sub_eq, norm_mul, norm_mul, norm_gW_leftPt hr]
    have hu := norm_two_mul_leftPt_sub_half_div_le hT t
    have hζ := hC0 t
    have hcoef : ‖2 * (Real.log r : ℂ) * (2 * (leftPt t - 1 / 2) / (T : ℂ) ^ 2) +
        (2 * (leftPt t - 1 / 2) / (T : ℂ) ^ 2) ^ 2 + 2 / (T : ℂ) ^ 2‖ ≤
        2 * L * (2 * (1 + |t|) / T ^ 2) + (2 * (1 + |t|) / T ^ 2) ^ 2 + 2 / T ^ 2 := by
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
      · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, show ‖(2 : ℂ)‖ = 2 by norm_num]
        gcongr
      · rw [norm_pow]; gcongr
      · rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0,
          show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hE0 : 0 ≤ Real.exp ((1 - t ^ 2) / T ^ 2) := (Real.exp_pos _).le
    have h1t : 0 ≤ 1 + |t| := by linarith [abs_nonneg t]
    calc ‖2 * (Real.log r : ℂ) * (2 * (leftPt t - 1 / 2) / (T : ℂ) ^ 2) +
          (2 * (leftPt t - 1 / 2) / (T : ℂ) ^ 2) ^ 2 + 2 / (T : ℂ) ^ 2‖ *
          (r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2)) * ‖riemannZeta (leftPt t)‖
        ≤ (2 * L * (2 * (1 + |t|) / T ^ 2) + (2 * (1 + |t|) / T ^ 2) ^ 2 + 2 / T ^ 2) *
          (r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2)) * (C0 * (1 + |t|) ^ 1) := by
          gcongr
      _ = M t := by simp only [hM]; ring
  calc ∫ t : ℝ, ‖(gW2 T r (leftPt t) - (Real.log r : ℂ) ^ 2 * gW T r (leftPt t)) *
        riemannZeta (leftPt t)‖
      ≤ ∫ t : ℝ, M t := integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
        hMint (Eventually.of_forall hpt)
    _ = C0 * r ^ (-1 / 2 : ℝ) * (4 * L / T ^ 2 * (∫ t : ℝ, (1 + |t|) ^ 2 *
          Real.exp ((1 - t ^ 2) / T ^ 2)) + 4 / T ^ 4 * (∫ t : ℝ, (1 + |t|) ^ 3 *
          Real.exp ((1 - t ^ 2) / T ^ 2)) + 2 / T ^ 2 * (∫ t : ℝ, (1 + |t|) ^ 1 *
          Real.exp ((1 - t ^ 2) / T ^ 2))) := by
        simp only [hM]
        have ha1 := integral_add ((hint2.const_mul (4 * L / T ^ 2)).add
          (hint3.const_mul (4 / T ^ 4))) (hint1.const_mul (2 / T ^ 2))
        have ha2 := integral_add (hint2.const_mul (4 * L / T ^ 2)) (hint3.const_mul (4 / T ^ 4))
        simp only [Pi.add_apply] at ha1 ha2
        rw [integral_const_mul, ha1, ha2, integral_const_mul, integral_const_mul, integral_const_mul]
    _ ≤ C0 * r ^ (-1 / 2 : ℝ) * (4 * L / T ^ 2 * (2 * E * T ^ 3) + 4 / T ^ 4 * (6 * E * T ^ 4) +
          2 / T ^ 2 * (1 * E * T ^ 2)) := by
        have h2 := integral_poly_gauss_le 2 hT
        have h3 := integral_poly_gauss_le 3 hT
        have h1 := integral_poly_gauss_le 1 hT
        simp only [Nat.factorial, Nat.succ_eq_add_one, Nat.cast_mul,
          Nat.cast_one, zero_add, one_mul, mul_one] at h1 h2 h3
        gcongr
        · rw [hE]; linarith
        · rw [hE]; norm_num at h3 ⊢; linarith
        · rw [hE]; linarith
    _ = C0 * r ^ (-1 / 2 : ℝ) * E * (8 * L * T + 24 + 2) := by field_simp; ring
    _ ≤ C0 * r ^ (-1 / 2 : ℝ) * E * (8 * L + 26) * T := by
        have hL0 : 0 ≤ L := abs_nonneg _
        have : 8 * L * T + 24 + 2 ≤ (8 * L + 26) * T := by nlinarith
        calc C0 * r ^ (-1 / 2 : ℝ) * E * (8 * L * T + 24 + 2)
            ≤ C0 * r ^ (-1 / 2 : ℝ) * E * ((8 * L + 26) * T) := by gcongr
          _ = _ := by ring

/-- Chebyshev: `Σ_{a ≤ m} Λ(a) ≤ (log 4 + 4) m`. -/
theorem sum_vonMangoldt_le (m : ℕ) :
    ∑ a ∈ Finset.Icc 1 m, ArithmeticFunction.vonMangoldt a ≤
      (Real.log 4 + 4) * m * (Real.log m + 1) ^ 0 := by
  have h := Chebyshev.psi_le_const_mul_self (x := (m : ℝ)) (Nat.cast_nonneg m)
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast] at h
  have hsplit : ∑ a ∈ Finset.Icc 0 m, ArithmeticFunction.vonMangoldt a =
      ∑ a ∈ Finset.Icc 1 m, ArithmeticFunction.vonMangoldt a := by
    refine (Finset.sum_subset (Finset.Icc_subset_Icc_left (by norm_num)) fun x hx hnx => ?_).symm
    have : x = 0 := by
      rw [Finset.mem_Icc] at hx hnx; omega
    rw [this]; simp
  rw [pow_zero, mul_one]
  linarith

theorem continuous_logDeriv_riemannZeta_leftPt :
    Continuous fun t => logDeriv riemannZeta (leftPt t) := by
  refine continuousOn_of_analytic_leftStrip fun z hz => ?_
  have hz1 := ne_one_of_mem_leftStrip hz
  have han := analyticAt_riemannZeta_of_ne_one hz1
  have : logDeriv riemannZeta = fun w => deriv riemannZeta w / riemannZeta w := by
    funext w; exact logDeriv_apply _ _
  rw [this]
  exact han.deriv.continuousAt.div han.continuousAt (riemannZeta_ne_zero_of_mem_leftStrip hz)

theorem continuous_deriv_logDeriv_zetaChi_leftPt :
    Continuous fun t => deriv (logDeriv zetaChi) (leftPt t) :=
  continuousOn_of_analytic_leftStrip fun _ hz => continuousAt_deriv_logDeriv_zetaChi hz

theorem continuous_deriv_zetaChi_leftPt : Continuous fun t => deriv zetaChi (leftPt t) :=
  continuousOn_of_analytic_leftStrip fun _ hz =>
    (zetaChi_analyticAt (gammaR_one_sub_ne_zero_of_mem_leftStrip hz)).deriv.continuousAt

/-- **Landau–Gonek on the left line**: `∫ |(ζ'/ζ)(s_t) G(s_t)| dt ≤ C T (log T + 1)`. -/
theorem exists_leftLine_logDeriv {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      Integrable (fun t => logDeriv riemannZeta (leftPt t) * gW T r (leftPt t)) ∧
      ∫ t : ℝ, ‖logDeriv riemannZeta (leftPt t) * gW T r (leftPt t)‖ ≤ C * T * (Real.log T + 1) := by
  obtain ⟨CD, hCD0, hCD⟩ := exists_norm_logDeriv_zetaChi_leftPt_le
  obtain ⟨KΛ, hKΛ0, hKΛ⟩ := exists_norm_LSeries_one_sub_leftPt_le
    (f := fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num))
  set E : ℝ := Real.exp (5 / 2) * Real.sqrt (2 * Real.pi) with hE
  refine ⟨r ^ (-1 / 2 : ℝ) * E * (3 * CD + KΛ), by positivity, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  set M : ℝ → ℝ := fun t => r ^ (-1 / 2 : ℝ) * ((CD * (2 + Real.log T) + KΛ) *
      ((1 + |t|) ^ 0 * Real.exp ((1 - t ^ 2) / T ^ 2)) +
      CD / T * ((1 + |t|) ^ 1 * Real.exp ((1 - t ^ 2) / T ^ 2))) with hM
  have hint0 := integrable_poly_gauss_real 0 hT
  have hint1 := integrable_poly_gauss_real 1 hT
  have hMint : Integrable M := ((hint0.const_mul _).add (hint1.const_mul _)).const_mul _
  have hpt : ∀ t, ‖logDeriv riemannZeta (leftPt t) * gW T r (leftPt t)‖ ≤ M t := by
    intro t
    rw [norm_mul, norm_gW_leftPt hr, logDeriv_riemannZeta_eq_leftStrip (leftPt_mem_leftStrip t)]
    have h1 := hCD t
    have h2 := hKΛ t
    have hlog : Real.log (1 + |t|) ≤ 1 + Real.log T + |t| / T := by
      have hpos : 0 < 1 + |t| := by linarith [abs_nonneg t]
      have hfac : 1 + |t| ≤ (2 * T) * (1 + |t| / T) := by
        have e : (2 * T) * (1 + |t| / T) = 2 * T + 2 * |t| := by field_simp
        rw [e]; nlinarith [abs_nonneg t]
      have := Real.log_le_log hpos hfac
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hT0.ne'] at this
      have hl2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
      have hlx : Real.log (1 + |t| / T) ≤ |t| / T := by
        have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + |t| / T); linarith
      linarith
    have hn : ‖logDeriv zetaChi (leftPt t) +
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 - leftPt t)‖ ≤
        CD * (2 + Real.log T) + KΛ + CD / T * (1 + |t|) := by
      refine (norm_add_le _ _).trans ?_
      have : CD * (1 + Real.log (1 + |t|)) ≤ CD * (2 + Real.log T) + CD / T * (1 + |t|) := by
        have hTt : |t| / T ≤ (1 + |t|) / T := by gcongr; linarith
        calc CD * (1 + Real.log (1 + |t|)) ≤ CD * (1 + (1 + Real.log T + |t| / T)) := by gcongr
          _ = CD * (2 + Real.log T) + CD * (|t| / T) := by ring
          _ ≤ CD * (2 + Real.log T) + CD * ((1 + |t|) / T) := by gcongr
          _ = _ := by ring
      linarith
    have hE0 := (Real.exp_pos ((1 - t ^ 2) / T ^ 2)).le
    calc ‖logDeriv zetaChi (leftPt t) +
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 - leftPt t)‖ *
          (r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2))
        ≤ (CD * (2 + Real.log T) + KΛ + CD / T * (1 + |t|)) *
          (r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2)) := by gcongr
      _ = M t := by simp only [hM]; ring
  have hcont : Continuous fun t => logDeriv riemannZeta (leftPt t) * gW T r (leftPt t) :=
    continuous_logDeriv_riemannZeta_leftPt.mul (continuous_gW_leftPt hr)
  refine ⟨hMint.mono' hcont.aestronglyMeasurable (Eventually.of_forall hpt), ?_⟩
  calc ∫ t : ℝ, ‖logDeriv riemannZeta (leftPt t) * gW T r (leftPt t)‖
      ≤ ∫ t : ℝ, M t := integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
        hMint (Eventually.of_forall hpt)
    _ = r ^ (-1 / 2 : ℝ) * ((CD * (2 + Real.log T) + KΛ) *
          (∫ t : ℝ, (1 + |t|) ^ 0 * Real.exp ((1 - t ^ 2) / T ^ 2)) +
          CD / T * (∫ t : ℝ, (1 + |t|) ^ 1 * Real.exp ((1 - t ^ 2) / T ^ 2))) := by
        simp only [hM]
        rw [integral_const_mul, integral_add (hint0.const_mul _) (hint1.const_mul _),
          integral_const_mul, integral_const_mul]
    _ ≤ r ^ (-1 / 2 : ℝ) * ((CD * (2 + Real.log T) + KΛ) * (1 * E * T ^ 1) +
          CD / T * (1 * E * T ^ 2)) := by
        have h0 := integral_poly_gauss_le 0 hT
        have h1 := integral_poly_gauss_le 1 hT
        simp only [Nat.factorial, Nat.cast_one, zero_add, Nat.succ_eq_add_one, mul_one,
          one_mul] at h0 h1
        gcongr
        · rw [hE]; simpa using h0
        · rw [hE]; simpa using h1
    _ = r ^ (-1 / 2 : ℝ) * E * T * (CD * (3 + Real.log T) + KΛ) := by field_simp; ring
    _ ≤ r ^ (-1 / 2 : ℝ) * E * (3 * CD + KΛ) * T * (Real.log T + 1) := by
        have : CD * (3 + Real.log T) + KΛ ≤ (3 * CD + KΛ) * (Real.log T + 1) := by nlinarith
        calc r ^ (-1 / 2 : ℝ) * E * T * (CD * (3 + Real.log T) + KΛ)
            ≤ r ^ (-1 / 2 : ℝ) * E * T * ((3 * CD + KΛ) * (Real.log T + 1)) := by gcongr
          _ = _ := by ring

theorem one_lt_re_one_sub_leftPt (t : ℝ) : 1 < (1 - leftPt t).re := by simp [leftPt]; norm_num

/-- `ζ(s_t) = χ(s_t) Σ n^{s_t − 1}`. -/
theorem riemannZeta_leftPt_eq_LSeries (t : ℝ) :
    riemannZeta (leftPt t) = zetaChi (leftPt t) * LSeries (1 : ℕ → ℂ) (1 - leftPt t) := by
  rw [riemannZeta_eq_of_mem_leftStrip (leftPt_mem_leftStrip t),
    LSeries_one_eq_riemannZeta (one_lt_re_one_sub_leftPt t)]

theorem tsum_ite_one_eq (T r : ℝ) :
    ∑' n : ℕ, (if n = 0 then (0 : ℂ) else (1 : ℕ → ℂ) n * leftKernel T (n * r)) =
      ∑' n : ℕ, (if n = 0 then (0 : ℂ) else
        (((if n = 0 then (0 : ℝ) else 1) : ℝ) : ℂ) * leftKernel T (n * r)) := by
  congr 1; funext n; split_ifs <;> simp

/-- **Rule A on the left line**: `∫ (ζ'²/ζ)(s_t) G(s_t) dt = −2πr Σ ℓ(n) J_T(nr) + O(T)`. -/
theorem exists_leftLine_sq_logDeriv {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → 1 ≤ T / r →
      ‖(∫ t : ℝ, deriv riemannZeta (leftPt t) ^ 2 / riemannZeta (leftPt t) * gW T r (leftPt t)) +
          2 * Real.pi * r * ∑' n : ℕ, (if n = 0 then (0 : ℂ) else
            (logVM n : ℂ) * leftKernel T (n * r))‖ ≤ C * T := by
  obtain ⟨CJ, hCJ0, hCJ⟩ := exists_abs_leftKernel_le_decay
  obtain ⟨C1, hC10, hC1⟩ := exists_norm_integral_gW2_sub_le hr
  obtain ⟨C0, hC00, hC0⟩ := exists_norm_riemannZeta_leftPt_le
  obtain ⟨C5, hC50, hC5⟩ := exists_norm_deriv_logDeriv_zetaChi_leftPt_le
  obtain ⟨Cχ, hCχ0, hCχ⟩ := exists_norm_zetaChi_leftPt_le
  obtain ⟨C2, N2, hC20, hC2⟩ := exists_norm_deriv_deriv_riemannZeta_leftPt_le
  obtain ⟨Kℓ, hKℓ0, hKℓ⟩ := exists_norm_LSeries_one_sub_leftPt_le
    (f := fun n => (logVM n : ℂ)) (LSeriesSummable_logVM (by norm_num))
  set L : ℝ := Real.log r with hL
  set E : ℝ := Real.exp (5 / 2) * Real.sqrt (2 * Real.pi) with hE
  refine ⟨L ^ 2 * (2 * Real.pi * r) * (CJ * (48 * 1 / r)) + C1 + C0 * C5 * r ^ (-1 / 2 : ℝ) * E,
    by positivity, fun T hT hX => ?_⟩
  have hT0 : 0 < T := by linarith
  -- the three pieces
  set A : ℝ → ℂ := fun t => gW T r (leftPt t) * deriv (deriv riemannZeta) (leftPt t) with hA
  set B : ℝ → ℂ := fun t => riemannZeta (leftPt t) * deriv (logDeriv zetaChi) (leftPt t) *
    gW T r (leftPt t) with hB
  set Cc : ℝ → ℂ := fun t => zetaChi (leftPt t) * LSeries (fun n => (logVM n : ℂ)) (1 - leftPt t) *
    gW T r (leftPt t) with hCc
  have hpw : ∀ t, deriv riemannZeta (leftPt t) ^ 2 / riemannZeta (leftPt t) * gW T r (leftPt t) =
      A t - B t - Cc t := by
    intro t
    rw [sq_deriv_div_riemannZeta_eq_leftStrip (leftPt_mem_leftStrip t)]
    simp only [hA, hB, hCc]; ring
  have hIA : Integrable A := integrable_of_poly_gauss
    ((continuous_gW_leftPt hr).mul continuous_deriv_deriv_riemannZeta_leftPt) hT
    (C := r ^ (-1 / 2 : ℝ) * C2) (N := N2) fun t => by
      simp only [hA]
      rw [norm_mul, norm_gW_leftPt hr]
      have := hC2 t
      calc r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2) * ‖deriv (deriv riemannZeta) (leftPt t)‖
          ≤ r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2) * (C2 * (1 + |t|) ^ N2) := by gcongr
        _ = _ := by ring
  have hBpt : ∀ t, ‖B t‖ ≤ C0 * C5 * r ^ (-1 / 2 : ℝ) * ((1 + |t|) ^ 0 *
      Real.exp ((1 - t ^ 2) / T ^ 2)) := by
    intro t
    simp only [hB]
    rw [norm_mul, norm_mul, norm_gW_leftPt hr]
    have h1 := hC0 t
    have h2 := hC5 t
    have h1t : 0 < 1 + |t| := by linarith [abs_nonneg t]
    have hprod : ‖riemannZeta (leftPt t)‖ * ‖deriv (logDeriv zetaChi) (leftPt t)‖ ≤ C0 * C5 := by
      calc ‖riemannZeta (leftPt t)‖ * ‖deriv (logDeriv zetaChi) (leftPt t)‖
          ≤ (C0 * (1 + |t|) ^ 1) * ‖deriv (logDeriv zetaChi) (leftPt t)‖ := by gcongr
        _ = C0 * (‖deriv (logDeriv zetaChi) (leftPt t)‖ * (1 + |t|)) := by ring
        _ ≤ C0 * C5 := by gcongr
    calc ‖riemannZeta (leftPt t)‖ * ‖deriv (logDeriv zetaChi) (leftPt t)‖ *
          (r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2))
        ≤ C0 * C5 * (r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2)) := by gcongr
      _ = _ := by ring
  have hIB : Integrable B := integrable_of_poly_gauss
    ((continuous_riemannZeta_leftPt.mul continuous_deriv_logDeriv_zetaChi_leftPt).mul
      (continuous_gW_leftPt hr)) hT (C := C0 * C5 * r ^ (-1 / 2 : ℝ)) (N := 0)
    fun t => (hBpt t).trans (le_of_eq (by ring))
  have hIC : Integrable Cc := integrable_of_poly_gauss
    ((continuous_zetaChi_leftPt.mul (continuous_LSeries_one_sub_leftPt abscissa_logVM_le)).mul
      (continuous_gW_leftPt hr)) hT (C := Cχ * Kℓ * r ^ (-1 / 2 : ℝ)) (N := 1) fun t => by
      simp only [hCc]
      rw [norm_mul, norm_mul, norm_gW_leftPt hr]
      have h1 := hCχ t
      have h2 := hKℓ t
      calc ‖zetaChi (leftPt t)‖ * ‖LSeries (fun n => (logVM n : ℂ)) (1 - leftPt t)‖ *
            (r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2))
          ≤ (Cχ * (1 + |t|) ^ 1) * Kℓ * (r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2)) := by
            gcongr
        _ = _ := by ring
  -- integrate
  have hsplit : ∫ t : ℝ, deriv riemannZeta (leftPt t) ^ 2 / riemannZeta (leftPt t) *
      gW T r (leftPt t) = (∫ t, A t) - (∫ t, B t) - ∫ t, Cc t := by
    simp_rw [hpw]
    have h1 := integral_sub (hIA.sub hIB) hIC
    have h2 := integral_sub hIA hIB
    simp only [Pi.sub_apply] at h1 h2
    rw [h1, h2]
  -- `∫ A = log² r ∫ G ζ + ∫ (G'' − log² r G) ζ`
  have hgζ : Integrable fun t => gW T r (leftPt t) * riemannZeta (leftPt t) :=
    integrable_of_poly_gauss ((continuous_gW_leftPt hr).mul continuous_riemannZeta_leftPt) hT
      (C := r ^ (-1 / 2 : ℝ) * C0) (N := 1) fun t => by
        rw [norm_mul, norm_gW_leftPt hr]
        have := hC0 t
        calc r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2) * ‖riemannZeta (leftPt t)‖
            ≤ r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2) * (C0 * (1 + |t|) ^ 1) := by gcongr
          _ = _ := by ring
  have hcorr_int : Integrable fun t => (gW2 T r (leftPt t) - (L : ℂ) ^ 2 * gW T r (leftPt t)) *
      riemannZeta (leftPt t) := by
    have h2 : Integrable fun t => gW2 T r (leftPt t) * riemannZeta (leftPt t) := by
      obtain ⟨C0', _, h0'⟩ := exists_norm_riemannZeta_leftPt_le
      exact integrable_of_poly_gauss ((continuous_gW2_leftPt hr).mul continuous_riemannZeta_leftPt)
        hT (C := ((|Real.log r| + 2) ^ 2 + 2) * r ^ (-1 / 2 : ℝ) * C0') (N := 2 + 1) fun t => by
          rw [norm_mul]
          have h1 := norm_gW2_leftPt_le hT hr t
          have h2 := h0' t
          calc ‖gW2 T r (leftPt t)‖ * ‖riemannZeta (leftPt t)‖
              ≤ (((|Real.log r| + 2) ^ 2 + 2) * r ^ (-1 / 2 : ℝ) * (1 + |t|) ^ 2 *
                  Real.exp ((1 - t ^ 2) / T ^ 2)) * (C0' * (1 + |t|) ^ 1) :=
                mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
            _ = _ := by rw [pow_add]; ring
    refine (h2.sub (hgζ.const_mul ((L : ℂ) ^ 2))).congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply]; ring
  have hAeq : ∫ t, A t = (L : ℂ) ^ 2 * (∫ t, gW T r (leftPt t) * riemannZeta (leftPt t)) +
      ∫ t, (gW2 T r (leftPt t) - (L : ℂ) ^ 2 * gW T r (leftPt t)) * riemannZeta (leftPt t) := by
    simp only [hA]
    rw [integral_deriv_deriv_riemannZeta_mul hT hr, ← integral_const_mul,
      ← integral_add (hgζ.const_mul _) hcorr_int]
    congr 1; funext t; ring
  -- the two Dirichlet-series integrals
  have hζint : ∫ t, gW T r (leftPt t) * riemannZeta (leftPt t) =
      2 * Real.pi * r * ∑' n : ℕ, (if n = 0 then (0 : ℂ) else (1 : ℕ → ℂ) n * leftKernel T (n * r)) := by
    rw [← integral_zetaChi_mul_LSeries LSeriesSummable_one_three_halves hT hr]
    congr 1; funext t
    rw [riemannZeta_leftPt_eq_LSeries]; unfold gW; ring
  have hCint : ∫ t, Cc t = 2 * Real.pi * r * ∑' n : ℕ, (if n = 0 then (0 : ℂ) else
      (logVM n : ℂ) * leftKernel T (n * r)) := by
    simp only [hCc]
    rw [← integral_zetaChi_mul_LSeries (LSeriesSummable_logVM (by norm_num)) hT hr]
    congr 1
  -- bounds
  have hJ1 := norm_tsum_ite_leftKernel_le (c := fun n => if n = 0 then (0 : ℝ) else 1)
    (fun n => by split_ifs <;> norm_num) (by simp) zero_le_one (k := 0) (by norm_num)
    (fun m => by
      rw [Finset.sum_congr rfl (fun a ha => if_neg (by
        have := (Finset.mem_Icc.mp ha).1; omega) : ∀ a ∈ Finset.Icc 1 m,
          (if a = 0 then (0 : ℝ) else 1) = 1)]
      simp) hCJ0 hCJ hT hr hX
  rw [← tsum_ite_one_eq] at hJ1
  have hcorr := hC1 T hT
  have hBint : ∫ t, ‖B t‖ ≤ C0 * C5 * r ^ (-1 / 2 : ℝ) * E * T := by
    have h0 := integral_poly_gauss_le 0 hT
    calc ∫ t, ‖B t‖ ≤ ∫ t : ℝ, C0 * C5 * r ^ (-1 / 2 : ℝ) * ((1 + |t|) ^ 0 *
          Real.exp ((1 - t ^ 2) / T ^ 2)) :=
          integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
            ((integrable_poly_gauss_real 0 hT).const_mul _) (Eventually.of_forall hBpt)
      _ = C0 * C5 * r ^ (-1 / 2 : ℝ) * ∫ t : ℝ, (1 + |t|) ^ 0 * Real.exp ((1 - t ^ 2) / T ^ 2) :=
          integral_const_mul _ _
      _ ≤ C0 * C5 * r ^ (-1 / 2 : ℝ) * (E * T) := by
          gcongr
          simp only [Nat.factorial_zero, Nat.cast_one, one_mul, zero_add, pow_one] at h0
          rw [hE]; exact h0
      _ = _ := by ring
  rw [hsplit, hAeq, hζint, hCint]
  have key : (L : ℂ) ^ 2 * (2 * Real.pi * r * ∑' n : ℕ, (if n = 0 then (0 : ℂ) else
        (1 : ℕ → ℂ) n * leftKernel T (n * r))) +
      (∫ t, (gW2 T r (leftPt t) - (L : ℂ) ^ 2 * gW T r (leftPt t)) * riemannZeta (leftPt t)) -
      (∫ t, B t) - 2 * Real.pi * r * ∑' n : ℕ, (if n = 0 then (0 : ℂ) else
        (logVM n : ℂ) * leftKernel T (n * r)) +
      2 * Real.pi * r * ∑' n : ℕ, (if n = 0 then (0 : ℂ) else (logVM n : ℂ) * leftKernel T (n * r)) =
      (L : ℂ) ^ 2 * (2 * Real.pi * r) * ∑' n : ℕ, (if n = 0 then (0 : ℂ) else
        (1 : ℕ → ℂ) n * leftKernel T (n * r)) +
      (∫ t, (gW2 T r (leftPt t) - (L : ℂ) ^ 2 * gW T r (leftPt t)) * riemannZeta (leftPt t)) -
      ∫ t, B t := by ring
  rw [key]
  have hn1 : ‖(L : ℂ) ^ 2 * (2 * Real.pi * r) * ∑' n : ℕ, (if n = 0 then (0 : ℂ) else
      (1 : ℕ → ℂ) n * leftKernel T (n * r))‖ ≤ L ^ 2 * (2 * Real.pi * r) * (CJ * (48 * 1 / r)) * T := by
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have h2pr : ‖(2 * Real.pi * r : ℂ)‖ = 2 * Real.pi * r := by
      rw [show (2 * Real.pi * r : ℂ) = ((2 * Real.pi * r : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h2pr]
    have hJ1' : ‖∑' n : ℕ, (if n = 0 then (0 : ℂ) else (1 : ℕ → ℂ) n * leftKernel T (n * r))‖ ≤
        CJ * (48 * 1 / r) * T := by
      refine hJ1.trans (le_of_eq ?_)
      rw [pow_zero, mul_one]; field_simp
    calc L ^ 2 * (2 * Real.pi * r) *
          ‖∑' n : ℕ, (if n = 0 then (0 : ℂ) else (1 : ℕ → ℂ) n * leftKernel T (n * r))‖
        ≤ L ^ 2 * (2 * Real.pi * r) * (CJ * (48 * 1 / r) * T) := by gcongr
      _ = _ := by ring
  have hn2 := norm_integral_le_integral_norm (μ := volume) (fun t => (gW2 T r (leftPt t) -
    (L : ℂ) ^ 2 * gW T r (leftPt t)) * riemannZeta (leftPt t))
  have hn3 := norm_integral_le_integral_norm (μ := volume) B
  calc _ ≤ ‖(L : ℂ) ^ 2 * (2 * Real.pi * r) * ∑' n : ℕ, (if n = 0 then (0 : ℂ) else
          (1 : ℕ → ℂ) n * leftKernel T (n * r))‖ +
        ‖∫ t, (gW2 T r (leftPt t) - (L : ℂ) ^ 2 * gW T r (leftPt t)) * riemannZeta (leftPt t)‖ +
        ‖∫ t, B t‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
    _ ≤ L ^ 2 * (2 * Real.pi * r) * (CJ * (48 * 1 / r)) * T + C1 * T +
          C0 * C5 * r ^ (-1 / 2 : ℝ) * E * T := by
        gcongr
        · exact hn2.trans hcorr
        · exact hn3.trans hBint
    _ = _ := by ring

/-- **The `χ`-twisted sum on the left line**: `∫ χ(s_t) (ζ'/ζ)(s_t) G(s_t) dt = O(T)`. -/
theorem exists_leftLine_zetaChi_logDeriv {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → 1 ≤ T / r →
      Integrable (fun t => zetaChi (leftPt t) * logDeriv riemannZeta (leftPt t) * gW T r (leftPt t)) ∧
      ‖∫ t : ℝ, zetaChi (leftPt t) * logDeriv riemannZeta (leftPt t) * gW T r (leftPt t)‖ ≤ C * T := by
  obtain ⟨CJ, hCJ0, hCJ⟩ := exists_abs_leftKernel_le_decay
  obtain ⟨Cχ, hCχ0, hCχ⟩ := exists_norm_zetaChi_leftPt_le
  obtain ⟨Cd, hCd0, hCd⟩ := exists_norm_deriv_zetaChi_leftPt_le
  obtain ⟨KΛ, hKΛ0, hKΛ⟩ := exists_norm_LSeries_one_sub_leftPt_le
    (f := fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num))
  set L : ℝ := Real.log r with hL
  set E : ℝ := Real.exp (5 / 2) * Real.sqrt (2 * Real.pi) with hE
  set A₁ : ℝ := 2 * Real.sqrt 2 * Real.exp 5 with hA₁
  refine ⟨|L| * (2 * Real.pi * r) * A₁ + Cχ * r ^ (-1 / 2 : ℝ) * (4 * E) +
    2 * Real.pi * r * (CJ * (48 * (Real.log 4 + 4) / r)), by positivity, fun T hT hX => ?_⟩
  have hT0 : 0 < T := by linarith
  -- integrability of the pieces
  have hP : Integrable fun t => gW T r (leftPt t) * deriv zetaChi (leftPt t) :=
    integrable_of_poly_gauss ((continuous_gW_leftPt hr).mul continuous_deriv_zetaChi_leftPt) hT
      (C := r ^ (-1 / 2 : ℝ) * Cd) (N := 2) fun t => by
        rw [norm_mul, norm_gW_leftPt hr]
        have := hCd t
        calc r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2) * ‖deriv zetaChi (leftPt t)‖
            ≤ r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2) * (Cd * (1 + |t|) ^ 2) := by gcongr
          _ = _ := by ring
  have hQ : Integrable fun t => zetaChi (leftPt t) *
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 - leftPt t) * gW T r (leftPt t) :=
    integrable_of_poly_gauss ((continuous_zetaChi_leftPt.mul
      (continuous_LSeries_one_sub_leftPt abscissa_vonMangoldt_le)).mul (continuous_gW_leftPt hr)) hT
      (C := Cχ * KΛ * r ^ (-1 / 2 : ℝ)) (N := 1) fun t => by
        rw [norm_mul, norm_mul, norm_gW_leftPt hr]
        have h1 := hCχ t
        have h2 := hKΛ t
        calc ‖zetaChi (leftPt t)‖ *
              ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 - leftPt t)‖ *
              (r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2))
            ≤ (Cχ * (1 + |t|) ^ 1) * KΛ * (r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2)) := by
              gcongr
          _ = _ := by ring
  have hpw : ∀ t, zetaChi (leftPt t) * logDeriv riemannZeta (leftPt t) * gW T r (leftPt t) =
      gW T r (leftPt t) * deriv zetaChi (leftPt t) + zetaChi (leftPt t) *
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 - leftPt t) * gW T r (leftPt t) := by
    intro t
    rw [zetaChi_mul_logDeriv_riemannZeta_eq (leftPt_mem_leftStrip t)]
    ring
  have hint : Integrable fun t => zetaChi (leftPt t) * logDeriv riemannZeta (leftPt t) *
      gW T r (leftPt t) := by
    simp_rw [hpw]; exact hP.add hQ
  refine ⟨hint, ?_⟩
  simp_rw [hpw]
  rw [integral_add hP hQ]
  -- `∫ G χ' = −∫ G' χ` by parts
  have hdχ : ∀ t, HasDerivAt (fun u => zetaChi (leftPt u)) (deriv zetaChi (leftPt t) * I) t :=
    fun t => hasDerivAt_comp_leftPt
      (differentiableAt_zetaChi_of_mem_leftStrip (leftPt_mem_leftStrip t)).hasDerivAt
  have hg0 : ∀ t, HasDerivAt (fun u => gW T r (leftPt u)) (gW1 T r (leftPt t) * I) t := fun t =>
    hasDerivAt_comp_leftPt (hasDerivAt_gW hr _)
  have hG1χ : Integrable fun t => gW1 T r (leftPt t) * zetaChi (leftPt t) :=
    integrable_of_poly_gauss ((continuous_gW1_leftPt hr).mul continuous_zetaChi_leftPt) hT
      (C := (|L| + 2) * r ^ (-1 / 2 : ℝ) * Cχ) (N := 1 + 1) fun t => by
        rw [norm_mul]
        have h1 := norm_gW1_leftPt_le hT hr t
        have h2 := hCχ t
        calc ‖gW1 T r (leftPt t)‖ * ‖zetaChi (leftPt t)‖
            ≤ ((|Real.log r| + 2) * r ^ (-1 / 2 : ℝ) * (1 + |t|) ^ 1 *
                Real.exp ((1 - t ^ 2) / T ^ 2)) * (Cχ * (1 + |t|) ^ 1) :=
              mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          _ = _ := by rw [pow_add]; ring
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun t => gW T r (leftPt t)) (v := fun t => zetaChi (leftPt t))
    (u' := fun t => gW1 T r (leftPt t) * I) (v' := fun t => deriv zetaChi (leftPt t) * I)
    (fun t _ => hg0 t) (fun t _ => hdχ t)
    ((hP.mul_const I).congr (Eventually.of_forall fun t => by simp only [Pi.mul_apply]; ring))
    ((hG1χ.mul_const I).congr (Eventually.of_forall fun t => by simp only [Pi.mul_apply]; ring))
    (integrable_of_poly_gauss ((continuous_gW_leftPt hr).mul continuous_zetaChi_leftPt) hT
      (C := r ^ (-1 / 2 : ℝ) * Cχ) (N := 1) fun t => by
        simp only [Pi.mul_apply]
        rw [norm_mul, norm_gW_leftPt hr]
        have := hCχ t
        calc r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2) * ‖zetaChi (leftPt t)‖
            ≤ r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2) * (Cχ * (1 + |t|) ^ 1) := by gcongr
          _ = _ := by ring)
  have hP' : ∫ t, gW T r (leftPt t) * deriv zetaChi (leftPt t) =
      -∫ t, gW1 T r (leftPt t) * zetaChi (leftPt t) := by
    have e1 : ∫ t, gW T r (leftPt t) * (deriv zetaChi (leftPt t) * I) =
        I * ∫ t, gW T r (leftPt t) * deriv zetaChi (leftPt t) := by
      rw [← integral_const_mul]; congr 1; funext t; ring
    have e2 : ∫ t, gW1 T r (leftPt t) * I * zetaChi (leftPt t) =
        I * ∫ t, gW1 T r (leftPt t) * zetaChi (leftPt t) := by
      rw [← integral_const_mul]; congr 1; funext t; ring
    rw [e1, e2] at hibp
    exact mul_left_cancel₀ Complex.I_ne_zero (by rw [hibp]; ring)
  -- `G' = (log r + u) G`: the `log r` part is the exact kernel at `y = r`
  have hsplit1 : ∫ t, gW1 T r (leftPt t) * zetaChi (leftPt t) =
      (L : ℂ) * (∫ t, zetaChi (leftPt t) * (r : ℂ) ^ leftPt t * gaussWeight T (leftPt t)) +
        ∫ t, (2 * (leftPt t - 1 / 2) / (T : ℂ) ^ 2) * gW T r (leftPt t) * zetaChi (leftPt t) := by
    have hI1 : Integrable fun t => zetaChi (leftPt t) * (r : ℂ) ^ leftPt t *
        gaussWeight T (leftPt t) :=
      integrable_of_poly_gauss ((continuous_zetaChi_leftPt.mul (continuous_cpow_leftPt hr)).mul
        (continuous_gaussWeight_leftPt T)) hT (C := Cχ * r ^ (-1 / 2 : ℝ)) (N := 1) fun t => by
          rw [norm_mul, norm_mul, norm_cpow_leftPt hr, norm_gaussWeight_leftPt]
          have := hCχ t
          calc ‖zetaChi (leftPt t)‖ * r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2)
              ≤ (Cχ * (1 + |t|) ^ 1) * r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2) := by
                gcongr
            _ = _ := by ring
    have hI2 : Integrable fun t => (2 * (leftPt t - 1 / 2) / (T : ℂ) ^ 2) * gW T r (leftPt t) *
        zetaChi (leftPt t) := by
      refine (hG1χ.sub (hI1.const_mul (L : ℂ))).congr (Eventually.of_forall fun t => ?_)
      simp only [Pi.sub_apply, gW1, gW]; ring
    rw [← integral_const_mul, ← integral_add (hI1.const_mul _) hI2]
    congr 1; funext t; simp only [gW1, gW]; ring
  have hQint : ∫ t, zetaChi (leftPt t) *
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 - leftPt t) * gW T r (leftPt t) =
      2 * Real.pi * r * ∑' n : ℕ, (if n = 0 then (0 : ℂ) else
        (ArithmeticFunction.vonMangoldt n : ℂ) * leftKernel T (n * r)) :=
    integral_zetaChi_mul_LSeries (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)) hT hr
  rw [hP', hsplit1, integral_zetaChi_mul_cpow_mul_gaussWeight hT hr, hQint]
  -- bounds
  have hb1 : ‖(L : ℂ) * (2 * Real.pi * r * leftKernel T r)‖ ≤ |L| * (2 * Real.pi * r) * A₁ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hk := abs_leftKernel_le hT r
    have : ‖(2 * Real.pi * r * leftKernel T r : ℂ)‖ ≤ 2 * Real.pi * r * A₁ := by
      rw [show (2 * Real.pi * r * leftKernel T r : ℂ) = ((2 * Real.pi * r * leftKernel T r : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi * r)]
      gcongr
    calc |L| * ‖(2 * Real.pi * r * leftKernel T r : ℂ)‖ ≤ |L| * (2 * Real.pi * r * A₁) := by gcongr
      _ = _ := by ring
  have hb2 : ‖∫ t, (2 * (leftPt t - 1 / 2) / (T : ℂ) ^ 2) * gW T r (leftPt t) *
      zetaChi (leftPt t)‖ ≤ Cχ * r ^ (-1 / 2 : ℝ) * (4 * E) * T := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hpt : ∀ t, ‖(2 * (leftPt t - 1 / 2) / (T : ℂ) ^ 2) * gW T r (leftPt t) *
        zetaChi (leftPt t)‖ ≤ 2 * Cχ * r ^ (-1 / 2 : ℝ) / T ^ 2 * ((1 + |t|) ^ 2 *
          Real.exp ((1 - t ^ 2) / T ^ 2)) := by
      intro t
      rw [norm_mul, norm_mul, norm_gW_leftPt hr]
      have h1 := norm_two_mul_leftPt_sub_half_div_le hT t
      have h2 := hCχ t
      calc ‖2 * (leftPt t - 1 / 2) / (T : ℂ) ^ 2‖ * (r ^ (-1 / 2 : ℝ) *
            Real.exp ((1 - t ^ 2) / T ^ 2)) * ‖zetaChi (leftPt t)‖
          ≤ (2 * (1 + |t|) / T ^ 2) * (r ^ (-1 / 2 : ℝ) * Real.exp ((1 - t ^ 2) / T ^ 2)) *
              (Cχ * (1 + |t|) ^ 1) := by gcongr
        _ = _ := by ring
    have h2 := integral_poly_gauss_le 2 hT
    calc ∫ t, ‖(2 * (leftPt t - 1 / 2) / (T : ℂ) ^ 2) * gW T r (leftPt t) * zetaChi (leftPt t)‖
        ≤ ∫ t : ℝ, 2 * Cχ * r ^ (-1 / 2 : ℝ) / T ^ 2 * ((1 + |t|) ^ 2 *
            Real.exp ((1 - t ^ 2) / T ^ 2)) :=
          integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
            ((integrable_poly_gauss_real 2 hT).const_mul _) (Eventually.of_forall hpt)
      _ = 2 * Cχ * r ^ (-1 / 2 : ℝ) / T ^ 2 *
            ∫ t : ℝ, (1 + |t|) ^ 2 * Real.exp ((1 - t ^ 2) / T ^ 2) := integral_const_mul _ _
      _ ≤ 2 * Cχ * r ^ (-1 / 2 : ℝ) / T ^ 2 * (2 * E * T ^ 3) := by
          gcongr
          simp only [Nat.factorial, Nat.succ_eq_add_one, Nat.cast_mul, Nat.cast_one, zero_add,
            one_mul] at h2
          rw [hE]; norm_num at h2 ⊢; linarith
      _ = Cχ * r ^ (-1 / 2 : ℝ) * (4 * E) * T := by field_simp; ring
  have hb3 := norm_tsum_ite_leftKernel_le (c := fun n => ArithmeticFunction.vonMangoldt n)
    (fun n => ArithmeticFunction.vonMangoldt_nonneg) (by simp)
    (by positivity : (0 : ℝ) ≤ Real.log 4 + 4) (k := 0) (by norm_num) sum_vonMangoldt_le hCJ0 hCJ
    hT hr hX
  rw [pow_zero, mul_one] at hb3
  have hb3' : ‖(2 * Real.pi * r : ℂ) * ∑' n : ℕ, (if n = 0 then (0 : ℂ) else
      (ArithmeticFunction.vonMangoldt n : ℂ) * leftKernel T (n * r))‖ ≤
      2 * Real.pi * r * (CJ * (48 * (Real.log 4 + 4) / r)) * T := by
    rw [norm_mul, show (2 * Real.pi * r : ℂ) = ((2 * Real.pi * r : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc 2 * Real.pi * r * ‖∑' n : ℕ, (if n = 0 then (0 : ℂ) else
          (ArithmeticFunction.vonMangoldt n : ℂ) * leftKernel T (n * r))‖
        ≤ 2 * Real.pi * r * (CJ * (48 * (Real.log 4 + 4) * (T / r))) := by gcongr
      _ = _ := by field_simp
  calc ‖-((L : ℂ) * (2 * Real.pi * r * leftKernel T r) +
        ∫ t, (2 * (leftPt t - 1 / 2) / (T : ℂ) ^ 2) * gW T r (leftPt t) * zetaChi (leftPt t)) +
        2 * Real.pi * r * ∑' n : ℕ, (if n = 0 then (0 : ℂ) else
          (ArithmeticFunction.vonMangoldt n : ℂ) * leftKernel T (n * r))‖
      ≤ ‖(L : ℂ) * (2 * Real.pi * r * leftKernel T r)‖ +
        ‖∫ t, (2 * (leftPt t - 1 / 2) / (T : ℂ) ^ 2) * gW T r (leftPt t) * zetaChi (leftPt t)‖ +
        ‖(2 * Real.pi * r : ℂ) * ∑' n : ℕ, (if n = 0 then (0 : ℂ) else
          (ArithmeticFunction.vonMangoldt n : ℂ) * leftKernel T (n * r))‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
        gcongr
        exact norm_add_le _ _
    _ ≤ |L| * (2 * Real.pi * r) * A₁ + Cχ * r ^ (-1 / 2 : ℝ) * (4 * E) * T +
        2 * Real.pi * r * (CJ * (48 * (Real.log 4 + 4) / r)) * T := by gcongr
    _ ≤ _ := by
        have h1 : |L| * (2 * Real.pi * r) * A₁ ≤ |L| * (2 * Real.pi * r) * A₁ * T :=
          le_mul_of_one_le_right (by positivity) hT
        nlinarith

end

end RHTower.GaussZeroSum
