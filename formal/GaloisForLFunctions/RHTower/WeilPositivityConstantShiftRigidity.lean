import GaloisForLFunctions.RHTower.WeilPositivityMertensConstantObstruction
import GaloisForLFunctions.RHTower.WeilPositivityLogDensityMaximality

/-!
# Weil positivity pins the constant shift of the von Mangoldt weights

Replace the von Mangoldt weights `Λ(n)` of the finite-atom Weil symbol of `ζ` by real weights
`lam(n)`, and call `lam` Weil-positive if the symbol energy is nonnegative on every
polar-constrained `C²` test at every level.

**Theorem** (`polar_mertens_constant_nonpos_of_weilAtomSymbol_nonneg`).  If the deviation from `Λ`
has a polar Mertens expansion
`∑_{2 ≤ n ≤ x} (lam(n) - Λ(n)) n^{-1/2} = 2κ√x + A log x + B + o(1)`
and `lam` is Weil-positive, then `B ≤ 0`.  The square-root slope `κ` is a pole of the deviation's
Dirichlet series at `s = 1`, and the logarithmic slope `A` a pole at `s = ½`; neither is restricted.

**Corollary** (`vonMangoldt_sub_const_not_weilPositive`).  For every `c > 0` the weights
`Λ(n) - c` are not Weil-positive: here `κ = -c`, `A = 0` and `B = c(1 - ζ(½)) ≥ 2c`, with
`ζ(½) = lim (∑_{n ≤ N} n^{-1/2} - 2√N) ≤ -1` (`halfPowerConstant`).

**Corollary** (`eq_zero_of_vonMangoldt_add_const_weilPositive`).  If `Λ + c` is Weil-positive, then
`c = 0`.  The upward direction is the density ceiling (`vonMangoldt_add_const_not_weilPositive`);
the downward direction is the central constant above.  The line `Λ + ℝ` meets the Weil-positive
weights at most in `Λ`.

## Mechanism

The tests are the spread radical tests `f_{R,S}` of `WeilPositivityMertensConstantObstruction`,
whose zero side is `O(S^{10} e^{-S})`, whose mass is at least `cS`, and whose transform vanishes at
`0` and `±i/2`.  With `φ = Re(k + k(-·))`, `k = f ⋆ f̃`, Abel summation gives the square-root slope
the weight `2κ ∫₁^{e^L} (φ ∘ log)'(t) √t dt = -2κφ(0) - κ ∫₀^L φ(u) e^{u/2} du`.  The polar
constraint turns the last integral into `-∫₀^L φ(u) e^{-u/2} du`
(`integral_weilTestEvenPart_mul_cosh_eq_zero`), which is `2φ(0)` up to `4 sup|φ'|` and an
exponentially small term (`abs_integral_mul_exp_neg_half_sub_le`).  The slope therefore contributes
`O(|κ| sup|φ'|)`, bounded uniformly in `S`, while the constant contributes `-2Bφ(0) ≍ -BS`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ArithmeticFunction

noncomputable section
namespace RHTower

open Zeta23

/-- **Polar cancellation.**  For a polar-constrained `C²` test supported in `[-a, a]` and `L > 2a`,
the even part `φ` of its Weil test satisfies `∫₀^L φ(u)(e^{u/2} + e^{-u/2}) du = 0`. -/
theorem integral_weilTestEvenPart_mul_cosh_eq_zero {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hp : paperFT f (I / 2) = 0)
    (hm : paperFT f (-(I / 2)) = 0) {L : ℝ} (hL : 2 * a < L) :
    ∫ u in (0 : ℝ)..L, weilTestEvenPart f u * (Real.exp (u / 2) + Real.exp (-(u / 2))) = 0 := by
  obtain ⟨hfc, hkd, hks, -, -⟩ := weilTest_self_data hf hfs
  set k := EF.weilTest f f with hk
  have hkc : Continuous k := hkd.continuous
  have hkcs : HasCompactSupport k :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport k) hks
  set w : ℝ → ℂ := fun u => ((Real.exp (u / 2) + Real.exp (-(u / 2)) : ℝ) : ℂ) with hw
  have hwc : Continuous w := by rw [hw]; fun_prop
  have hweven : ∀ u, w (-u) = w u := fun u => by
    simp only [hw]; congr 1; rw [show -u / 2 = -(u / 2) by ring, neg_neg, add_comm]
  set g : ℝ → ℂ := fun u => k u * w u with hg
  have hgc : Continuous g := hkc.mul hwc
  have hL0 : 0 ≤ L := by linarith
  have hsplit : ∫ u in (0 : ℝ)..L, (k u + k (-u)) * w u = ∫ u in (-L)..L, g u := by
    have h1 : ∫ u in (0 : ℝ)..L, (k u + k (-u)) * w u =
        (∫ u in (0 : ℝ)..L, g u) + ∫ u in (0 : ℝ)..L, g (-u) := by
      have hi1 : IntervalIntegrable g volume 0 L := hgc.intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun u => g (-u)) volume 0 L :=
        (hgc.comp continuous_neg).intervalIntegrable _ _
      rw [← intervalIntegral.integral_add hi1 hi2]
      congr 1; funext u; simp only [hg, hweven]; ring
    rw [h1, intervalIntegral.integral_comp_neg (fun u => g u), neg_zero, add_comm,
      intervalIntegral.integral_add_adjacent_intervals (hgc.intervalIntegrable _ _)
        (hgc.intervalIntegrable _ _)]
  have hfull : ∫ u in (-L)..L, g u = ∫ u, g u := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_
    have : k u = 0 := image_eq_zero_of_notMem_tsupport fun hmem => hu (by
      have := hks hmem
      exact ⟨by linarith [this.1], by linarith [this.2]⟩)
    simp [hg, this]
  have hexp : ∀ u : ℝ, w u = cexp (I * (-(I / 2)) * u) + cexp (I * (I / 2) * u) := by
    intro u
    simp only [hw]; push_cast
    congr 1
    · congr 1; ring_nf; rw [I_sq]; ring
    · congr 1; ring_nf; rw [I_sq]; ring
  have hint : ∀ z : ℂ, Integrable (fun u : ℝ => k u * cexp (I * z * u)) := fun z =>
    (hkc.mul (by fun_prop)).integrable_of_hasCompactSupport hkcs.mul_right
  have hsum : ∫ u, g u = paperFT k (-(I / 2)) + paperFT k (I / 2) := by
    unfold paperFT
    rw [← integral_add (hint _) (hint _)]
    congr 1; funext u; simp only [hg, hexp]; ring
  have hk1 : paperFT k (I / 2) = 0 := by
    rw [hk, EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc, hp, zero_mul]
  have hk2 : paperFT k (-(I / 2)) = 0 := by
    rw [hk, EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc, hm, zero_mul]
  have hre : ∫ u in (0 : ℝ)..L, weilTestEvenPart f u * (Real.exp (u / 2) + Real.exp (-(u / 2))) =
      Complex.reCLM (∫ u in (0 : ℝ)..L, (k u + k (-u)) * w u) := by
    have hii : IntervalIntegrable (fun u => (k u + k (-u)) * w u) volume 0 L :=
      ((hkc.add (hkc.comp continuous_neg)).mul hwc).intervalIntegrable _ _
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hii]
    congr 1; funext u
    simp only [Complex.reCLM_apply, hw, weilTestEvenPart, hk]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hre, hsplit, hfull, hsum, hk1, hk2, add_zero, map_zero]

theorem rexp_log_div_two_eq_sqrt {t : ℝ} (ht : 0 < t) : Real.exp (Real.log t / 2) = Real.sqrt t := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]; ring_nf

/-- **The square-root moment of a logarithmic derivative.**  If `φ` is `C¹` and `φ(L) = 0`, then
`∫₁^{e^L} (φ ∘ log)'(t) √t dt = -φ(0) - ½ ∫₀^L φ(u) e^{u/2} du`. -/
theorem integral_deriv_comp_log_mul_sqrt {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {L : ℝ} (hL : 0 ≤ L)
    (hφL : φ L = 0) :
    ∫ t in Ioc 1 (Real.exp L), deriv (fun t => φ (Real.log t)) t * Real.sqrt t =
      -φ 0 - 1 / 2 * ∫ u in (0 : ℝ)..L, φ u * Real.exp (u / 2) := by
  set b := Real.exp L with hb
  have hb1 : 1 ≤ b := Real.one_le_exp hL
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hφc : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  set F : ℝ → ℝ := fun t => φ (Real.log t) with hF
  have hFd : ∀ t : ℝ, 0 < t → HasDerivAt F (deriv φ (Real.log t) * t⁻¹) t := fun t ht =>
    (hφd (Real.log t)).hasDerivAt.comp t (Real.hasDerivAt_log ht.ne')
  have hFd' : ∀ t : ℝ, 0 < t → deriv F t = deriv φ (Real.log t) * t⁻¹ :=
    fun t ht => (hFd t ht).deriv
  have hgc : Continuous (fun u => φ u * Real.exp (u / 2)) := by
    have := hφ.continuous; fun_prop
  set Φ₁ : ℝ → ℝ := fun v => ∫ u in (0 : ℝ)..v, φ u * Real.exp (u / 2) with hΦ₁
  have hΦ₁d : ∀ v : ℝ, HasDerivAt Φ₁ (φ v * Real.exp (v / 2)) v := fun v =>
    intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable _ _)
      hgc.aestronglyMeasurable.stronglyMeasurableAtFilter hgc.continuousAt
  set Ψ : ℝ → ℝ := fun t => F t * Real.sqrt t - 1 / 2 * Φ₁ (Real.log t) with hΨ
  have hΨd : ∀ t ∈ uIcc 1 b, HasDerivAt Ψ (deriv φ (Real.log t) * t⁻¹ * Real.sqrt t) t := by
    intro t ht
    rw [uIcc_of_le hb1] at ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht.1
    have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have h1 := (hFd t ht0).mul (Real.hasDerivAt_sqrt ht0.ne')
    have h2 := ((hΦ₁d (Real.log t)).comp t (Real.hasDerivAt_log ht0.ne')).const_mul (1 / 2)
    have h3 := h1.sub h2
    refine h3.congr_deriv ?_
    rw [rexp_log_div_two_eq_sqrt ht0]
    have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
    have key : Real.sqrt t * t⁻¹ = 1 / Real.sqrt t := by
      rw [eq_div_iff hs0.ne', mul_assoc, mul_comm t⁻¹, ← mul_assoc, hsq,
        mul_inv_cancel₀ ht0.ne']
    have hFt : F t = φ (Real.log t) := rfl
    rw [hFt, mul_assoc (φ (Real.log t)), key]
    ring
  have hcont : ContinuousOn (fun t => deriv φ (Real.log t) * t⁻¹ * Real.sqrt t) (Icc 1 b) := by
    have hne : ∀ t ∈ Icc 1 b, t ≠ 0 := fun t ht => ne_of_gt (lt_of_lt_of_le one_pos ht.1)
    exact ((hφc.comp_continuousOn (Real.continuousOn_log.mono hne)).mul
      (continuousOn_inv₀.mono hne)).mul Real.continuous_sqrt.continuousOn
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hΨd
    (by rw [intervalIntegrable_iff_integrableOn_Icc_of_le hb1]
        exact hcont.integrableOn_compact isCompact_Icc)
  rw [intervalIntegral.integral_of_le hb1] at hftc
  have hcongr : ∫ t in Ioc 1 b, deriv (fun t => φ (Real.log t)) t * Real.sqrt t =
      ∫ t in Ioc 1 b, deriv φ (Real.log t) * t⁻¹ * Real.sqrt t :=
    setIntegral_congr_fun measurableSet_Ioc fun t ht => by
      show deriv F t * Real.sqrt t = _
      rw [hFd' t (lt_trans one_pos ht.1)]
  rw [hcongr, hftc]
  simp only [hΨ, hF, hb, Real.log_exp, Real.log_one, hφL, hΦ₁, intervalIntegral.integral_same,
    Real.sqrt_one]
  ring

/-- `∫₀^L e^{-u/2} du = 2 - 2e^{-L/2}`. -/
theorem integral_exp_neg_half_div (L : ℝ) :
    ∫ u in (0 : ℝ)..L, Real.exp (-(u / 2)) = 2 - 2 * Real.exp (-(L / 2)) := by
  have hd : ∀ u ∈ uIcc (0 : ℝ) L, HasDerivAt (fun u => -2 * Real.exp (-(u / 2)))
      (Real.exp (-(u / 2))) u := by
    intro u _
    have := ((hasDerivAt_id u).div_const 2).neg.exp.const_mul (-2)
    refine this.congr_deriv ?_
    simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun u : ℝ => Real.exp (-(u / 2))).intervalIntegrable _ _)]
  simp; ring

/-- `∫₀^L u e^{-u/2} du ≤ 4`. -/
theorem integral_mul_exp_neg_half_le {L : ℝ} (hL : 0 ≤ L) :
    ∫ u in (0 : ℝ)..L, u * Real.exp (-(u / 2)) ≤ 4 := by
  have hd : ∀ u ∈ uIcc (0 : ℝ) L, HasDerivAt (fun u => -(2 * u + 4) * Real.exp (-(u / 2)))
      (u * Real.exp (-(u / 2))) u := by
    intro u _
    have h1 := (((hasDerivAt_id u).const_mul 2).add_const 4).neg
    have h2 := ((hasDerivAt_id u).div_const 2).neg.exp
    refine (h1.mul h2).congr_deriv ?_
    simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun u : ℝ => u * Real.exp (-(u / 2))).intervalIntegrable _ _)]
  have : 0 ≤ (2 * L + 4) * Real.exp (-(L / 2)) := by positivity
  simp; nlinarith

/-- **The polar exponential moment.**  For `φ` `C¹` with `|φ'| ≤ M` and `L ≥ 0`,
`|∫₀^L φ(u) e^{-u/2} du - 2φ(0)| ≤ 2|φ(0)| e^{-L/2} + 4M`. -/
theorem abs_integral_mul_exp_neg_half_sub_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {M : ℝ}
    (hM : ∀ u, |deriv φ u| ≤ M) {L : ℝ} (hL : 0 ≤ L) :
    |(∫ u in (0 : ℝ)..L, φ u * Real.exp (-(u / 2))) - 2 * φ 0| ≤
      2 * |φ 0| * Real.exp (-(L / 2)) + 4 * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hmvt : ∀ u : ℝ, |φ u - φ 0| ≤ M * |u| := by
    intro u
    have := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (x := 0) (y := u)
      (fun x _ => hφd.differentiableAt) (fun x _ => by rw [Real.norm_eq_abs]; exact hM x)
      convex_univ (mem_univ _) (mem_univ _)
    simpa [Real.norm_eq_abs] using this
  have hc1 : Continuous (fun u => φ u * Real.exp (-(u / 2))) := by
    have := hφ.continuous; fun_prop
  have hc2 : Continuous (fun u => (φ u - φ 0) * Real.exp (-(u / 2))) := by
    have := hφ.continuous; fun_prop
  have hsplit : (∫ u in (0 : ℝ)..L, φ u * Real.exp (-(u / 2))) - 2 * φ 0 =
      (∫ u in (0 : ℝ)..L, (φ u - φ 0) * Real.exp (-(u / 2))) -
        2 * φ 0 * Real.exp (-(L / 2)) := by
    have hi2 : IntervalIntegrable (fun u : ℝ => φ 0 * Real.exp (-(u / 2))) volume 0 L :=
      (by fun_prop : Continuous fun u : ℝ => φ 0 * Real.exp (-(u / 2))).intervalIntegrable 0 L
    have h := intervalIntegral.integral_sub (hc1.intervalIntegrable 0 L) hi2
    have hconst : ∫ u in (0 : ℝ)..L, φ 0 * Real.exp (-(u / 2)) =
        φ 0 * (2 - 2 * Real.exp (-(L / 2))) := by
      rw [intervalIntegral.integral_const_mul, integral_exp_neg_half_div]
    have hcongr : ∫ u in (0 : ℝ)..L, (φ u - φ 0) * Real.exp (-(u / 2)) =
        ∫ u in (0 : ℝ)..L, (φ u * Real.exp (-(u / 2)) - φ 0 * Real.exp (-(u / 2))) := by
      congr 1; funext u; ring
    rw [hcongr, h, hconst]; ring
  have hbound : |∫ u in (0 : ℝ)..L, (φ u - φ 0) * Real.exp (-(u / 2))| ≤ 4 * M := by
    have hgi : IntervalIntegrable (fun u : ℝ => M * u * Real.exp (-(u / 2))) volume 0 L :=
      (by fun_prop : Continuous fun u : ℝ => M * u * Real.exp (-(u / 2))).intervalIntegrable 0 L
    have h := intervalIntegral.norm_integral_le_of_norm_le hL
      (Eventually.of_forall fun u (hu : u ∈ Ioc 0 L) => by
        have := hmvt u
        rw [abs_of_pos hu.1] at this
        show ‖(φ u - φ 0) * Real.exp (-(u / 2))‖ ≤ M * u * Real.exp (-(u / 2))
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le) hgi
    rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    have heq : ∫ u in (0 : ℝ)..L, M * u * Real.exp (-(u / 2)) =
        M * ∫ u in (0 : ℝ)..L, u * Real.exp (-(u / 2)) := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext u; ring
    rw [heq]
    nlinarith [integral_mul_exp_neg_half_le hL]
  rw [hsplit]
  refine (abs_sub _ _).trans ?_
  have : |2 * φ 0 * Real.exp (-(L / 2))| = 2 * |φ 0| * Real.exp (-(L / 2)) := by
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]; norm_num
  rw [this]; linarith


/-! ### The polar Mertens expansion of the symbol energy -/

/-- **Symbol energy under a polar Mertens expansion.**  For a polar-constrained `C²` test `f` on
`[-a, a]` with `|φ'| ≤ M`, weights `lam` and reals `κ, A, B`, let
`ε(t) = ∑_{2 ≤ n ≤ t} (lam(n) - Λ(n))/√n - 2κ√t - A log t - B`, bounded by `E` on `[1, T]` and by
`η` beyond `T`.  Then the symbol energy is at most
`2π(‖W‖ - A|h_f(0)|² - 2B‖f‖₂² + |κ|(4‖f‖₂² e^{-(2a+1)/2} + 4M) + M E log T + M η (2a+1))`.
The square-root slope `2κ√t` is cancelled by the polar constraint up to the exponential moment of
`φ(0) - φ`. -/
theorem integral_weilAtomSymbol_le_polar_mertens {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hp : paperFT f (I / 2) = 0)
    (hm : paperFT f (-(I / 2)) = 0) (lam : ℕ → ℝ) (κ A B : ℝ) {M : ℝ}
    (hM : ∀ u, |deriv (weilTestEvenPart f) u| ≤ M) {T E η : ℝ} (hT1 : 1 ≤ T)
    (hTb : T ≤ Real.exp (2 * a + 1))
    (hE : ∀ t ∈ Icc 1 T, |(∑ n ∈ Finset.Icc 0 ⌊t⌋₊, weilPerturbationWeight lam n) -
      2 * κ * Real.sqrt t - A * Real.log t - B| ≤ E)
    (hη : ∀ t, T ≤ t → |(∑ n ∈ Finset.Icc 0 ⌊t⌋₊, weilPerturbationWeight lam n) -
      2 * κ * Real.sqrt t - A * Real.log t - B| ≤ η) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) ≤
      2 * π * (‖zetaZeroConfig.W f f‖ - A * ‖paperFT f 0‖ ^ 2 -
        2 * B * (∫ x : ℝ, ‖f x‖ ^ 2) +
        |κ| * (4 * (∫ x : ℝ, ‖f x‖ ^ 2) * Real.exp (-((2 * a + 1) / 2)) + 4 * M) +
        M * E * Real.log T + M * η * (2 * a + 1)) := by
  set φ := weilTestEvenPart f with hφdef
  set L := 2 * a + 1 with hL
  set b := Real.exp L with hb
  set m := ∫ x : ℝ, ‖f x‖ ^ 2 with hmdef
  have hm0 : 0 ≤ m := integral_nonneg fun _ => by positivity
  have hL0 : 0 ≤ L := by linarith
  have hb1 : 1 ≤ b := Real.one_le_exp hL0
  have hφ2 : ContDiff ℝ 2 φ := contDiff_weilTestEvenPart hf hfs
  have hφ1 : ContDiff ℝ 1 φ := hφ2.of_le (by norm_num)
  have hφL : φ L = 0 := weilTestEvenPart_eq_zero hf hfs (by rw [abs_of_nonneg hL0]; linarith)
  have hφ0 : φ 0 = 2 * m := weilTestEvenPart_zero f
  have hI := integral_weilAtomSymbol_eq_mertens ha hf hfs hp hm lam A B
  set C : ℝ → ℝ := fun t => ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, weilPerturbationWeight lam n with hC
  set D : ℝ → ℝ := fun t => deriv (fun t => φ (Real.log t)) t with hD
  have hφd : Differentiable ℝ φ := hφ1.differentiable (by norm_num)
  have hDeq : ∀ t : ℝ, 0 < t → D t = deriv φ (Real.log t) * t⁻¹ := fun t ht =>
    ((hφd (Real.log t)).hasDerivAt.comp t (Real.hasDerivAt_log ht.ne')).deriv
  have hne : ∀ t ∈ Icc 1 b, t ≠ 0 := fun t ht => ne_of_gt (lt_of_lt_of_le one_pos ht.1)
  have hDcont : ContinuousOn (fun t => deriv φ (Real.log t) * t⁻¹) (Icc 1 b) :=
    ((hφ1.continuous_deriv le_rfl).comp_continuousOn (Real.continuousOn_log.mono hne)).mul
      (continuousOn_inv₀.mono hne)
  have hint1 : IntegrableOn (fun t => D t * (C t - A * Real.log t - B)) (Ioc 1 b) :=
    integrableOn_deriv_comp_log_mul_remainder hφ1 (weilPerturbationWeight lam) A B
  have hint2 : IntegrableOn (fun t => D t * Real.sqrt t) (Ioc 1 b) := by
    refine ((IntegrableOn.congr_fun ((hDcont.mul Real.continuous_sqrt.continuousOn).integrableOn_compact
      isCompact_Icc) (fun t ht => ?_) measurableSet_Icc)).mono_set Ioc_subset_Icc_self
    rw [hDeq t (lt_of_lt_of_le one_pos ht.1)]; rfl
  have hint3 : IntegrableOn (fun t => D t * (C t - 2 * κ * Real.sqrt t - A * Real.log t - B))
      (Ioc 1 b) := by
    refine (hint1.sub (hint2.const_mul (2 * κ))).congr_fun (fun t _ => ?_) measurableSet_Ioc
    simp only [Pi.sub_apply]; ring
  have hsplit : ∫ t in Ioc 1 b, D t * (C t - A * Real.log t - B) =
      2 * κ * (∫ t in Ioc 1 b, D t * Real.sqrt t) +
        ∫ t in Ioc 1 b, D t * (C t - 2 * κ * Real.sqrt t - A * Real.log t - B) := by
    rw [← integral_const_mul, ← integral_add (hint2.const_mul (2 * κ)) hint3]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    ring
  -- the square-root slope
  have hI1 := integral_deriv_comp_log_mul_sqrt hφ1 hL0 hφL
  have hpolar := integral_weilTestEvenPart_mul_cosh_eq_zero ha hf hfs hp hm
    (show 2 * a < L by rw [hL]; linarith)
  have hsplitp : ∫ u in (0 : ℝ)..L, φ u * Real.exp (u / 2) =
      -∫ u in (0 : ℝ)..L, φ u * Real.exp (-(u / 2)) := by
    have hc1 : Continuous (fun u => φ u * Real.exp (u / 2)) := by
      have := hφ1.continuous; fun_prop
    have hc2 : Continuous (fun u => φ u * Real.exp (-(u / 2))) := by
      have := hφ1.continuous; fun_prop
    have hi1 : IntervalIntegrable (fun u => φ u * Real.exp (u / 2)) volume 0 L :=
      hc1.intervalIntegrable 0 L
    have hi2 : IntervalIntegrable (fun u => φ u * Real.exp (-(u / 2))) volume 0 L :=
      hc2.intervalIntegrable 0 L
    have h := intervalIntegral.integral_add hi1 hi2
    have hcongr : ∫ u in (0 : ℝ)..L, weilTestEvenPart f u *
        (Real.exp (u / 2) + Real.exp (-(u / 2))) =
        ∫ u in (0 : ℝ)..L, (φ u * Real.exp (u / 2) + φ u * Real.exp (-(u / 2))) := by
      congr 1; funext u; rw [hφdef]; ring
    rw [hcongr, h] at hpolar
    linarith
  have hJ := abs_integral_mul_exp_neg_half_sub_le hφ1 hM hL0
  rw [hφ0] at hJ
  have hslope : |2 * κ * (∫ t in Ioc 1 b, D t * Real.sqrt t)| ≤
      |κ| * (4 * m * Real.exp (-(L / 2)) + 4 * M) := by
    have heq : 2 * κ * (∫ t in Ioc 1 b, D t * Real.sqrt t) =
        κ * ((∫ u in (0 : ℝ)..L, φ u * Real.exp (-(u / 2))) - 2 * (2 * m)) := by
      rw [hD, hI1, hsplitp, hφ0]; ring
    rw [heq, abs_mul]
    refine mul_le_mul_of_nonneg_left (hJ.trans (le_of_eq ?_)) (abs_nonneg _)
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * m)]; ring
  -- the remainder
  have hrem := abs_integral_deriv_comp_log_mul_le hφ1 hM hT1 hTb hE hη hint3
  rw [Real.log_exp] at hrem
  have hWre := Complex.re_le_norm (zetaZeroConfig.W f f)
  have hπ : 0 < π := Real.pi_pos
  rw [hI, hsplit]
  have hX : (zetaZeroConfig.W f f).re - (A * ‖paperFT f 0‖ ^ 2 + 2 * B * m) +
      (2 * κ * (∫ t in Ioc 1 b, D t * Real.sqrt t) +
        ∫ t in Ioc 1 b, D t * (C t - 2 * κ * Real.sqrt t - A * Real.log t - B)) ≤
      ‖zetaZeroConfig.W f f‖ - A * ‖paperFT f 0‖ ^ 2 - 2 * B * m +
        |κ| * (4 * m * Real.exp (-(L / 2)) + 4 * M) + M * E * Real.log T + M * η * L := by
    have h1 := (le_abs_self _).trans hslope
    have h2 := (le_abs_self _).trans hrem
    linarith
  have := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ 2 * π)
  linarith


/-- A polar Mertens expansion `C(t) = 2κ√t + A log t + B + o(1)` has bounded remainder on every
initial range and remainder at most `η` beyond some `T`. -/
theorem exists_polar_mertens_remainder_bounds {c : ℕ → ℝ} {κ A B : ℝ}
    (hlim : Tendsto (fun t : ℝ => (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) - 2 * κ * Real.sqrt t -
      A * Real.log t) atTop (𝓝 B))
    {η : ℝ} (hη : 0 < η) :
    ∃ T E : ℝ, 1 ≤ T ∧
      (∀ t ∈ Icc 1 T, |(∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) - 2 * κ * Real.sqrt t - A * Real.log t -
        B| ≤ E) ∧
      ∀ t, T ≤ t → |(∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) - 2 * κ * Real.sqrt t - A * Real.log t - B| ≤
        η := by
  have hε : Tendsto (fun t : ℝ => (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) - 2 * κ * Real.sqrt t -
      A * Real.log t - B) atTop (𝓝 0) := by
    have h := hlim.sub_const B
    rwa [sub_self] at h
  obtain ⟨T₀, hT₀⟩ := (hε.eventually (Metric.closedBall_mem_nhds 0 hη)).exists_forall_of_atTop
  refine ⟨max T₀ 1, (∑ n ∈ Finset.Icc 0 ⌊max T₀ 1⌋₊, |c n|) +
    2 * |κ| * Real.sqrt (max T₀ 1) + |A| * Real.log (max T₀ 1) + |B|,
    le_max_right _ _, fun t ht => ?_, fun t ht => ?_⟩
  · have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht.1
    have hlogT : Real.log t ≤ Real.log (max T₀ 1) := Real.log_le_log (by linarith [ht.1]) ht.2
    have hsqrtT : Real.sqrt t ≤ Real.sqrt (max T₀ 1) := Real.sqrt_le_sqrt ht.2
    have hsum : |∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n| ≤ ∑ n ∈ Finset.Icc 0 ⌊max T₀ 1⌋₊, |c n| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor ht.2)) fun _ _ _ => abs_nonneg _)
    have hA : |A * Real.log t| ≤ |A| * Real.log (max T₀ 1) := by
      rw [abs_mul, abs_of_nonneg hlog0]; exact mul_le_mul_of_nonneg_left hlogT (abs_nonneg _)
    have hK : |2 * κ * Real.sqrt t| ≤ 2 * |κ| * Real.sqrt (max T₀ 1) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg t), abs_two]
      exact mul_le_mul_of_nonneg_left hsqrtT (by positivity)
    calc |(∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) - 2 * κ * Real.sqrt t - A * Real.log t - B|
        ≤ |∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n| + |2 * κ * Real.sqrt t| + |A * Real.log t| + |B| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_sub _ _
      _ ≤ _ := by gcongr
  · have := hT₀ t (le_trans (le_max_left _ _) ht)
    rwa [Real.dist_eq, sub_zero] at this

/-- **Weil positivity forces a nonpositive central Mertens constant, square-root slope included.**
Let `lam : ℕ → ℝ` be prime-side weights whose deviation from the von Mangoldt function has a polar
Mertens expansion
`∑_{2 ≤ n ≤ x} (lam(n) - Λ(n)) n^{-1/2} = 2κ√x + A log x + B + o(1)`.
If the finite-atom Weil symbol with weights `lam` has nonnegative energy on every polar-constrained
`C²` test at every level, then `B ≤ 0`.  Neither the square-root slope `κ` (a pole of the
deviation's Dirichlet series at `s = 1`, cancelled by the polar constraint) nor the logarithmic
slope `A` (cancelled by `h_f(0) = 0`) is restricted by this family of tests. -/
theorem polar_mertens_constant_nonpos_of_weilAtomSymbol_nonneg {lam : ℕ → ℝ} {κ A B : ℝ}
    (hlim : Tendsto (fun x : ℝ =>
      (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n) -
        2 * κ * Real.sqrt x - A * Real.log x) atTop (𝓝 B))
    (hpos : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) :
    B ≤ 0 := by
  by_contra hB
  push Not at hB
  obtain ⟨Lg, hLg0, hLg⟩ := exists_lipschitz_mertensProbe
  set M₀ := 8 * ((∫ u : ℝ, ‖riemannPhiKernel u‖) * ∫ u : ℝ, ‖weilBumpPolarFree u‖) ^ 2 * Lg
    with hM₀
  have hM₀0 : 0 ≤ M₀ := by positivity
  obtain ⟨c₁, S₁, hc₁, hmassS⟩ := exists_integral_norm_sq_mertensTest_log_ge
  obtain ⟨K, hK0, hWS⟩ := exists_norm_W_mertensTest_log_le
  have hlim' : Tendsto (fun t : ℝ => (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, weilPerturbationWeight lam n) -
      2 * κ * Real.sqrt t - A * Real.log t) atTop (𝓝 B) :=
    hlim.congr fun t => by rw [sum_weilPerturbationWeight_eq]
  set η := B * c₁ / (25 * (M₀ + 1)) with hηdef
  have hη0 : 0 < η := by positivity
  obtain ⟨T, E, hT1, hE, hη⟩ := exists_polar_mertens_remainder_bounds hlim' hη0
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hE 1 ⟨le_rfl, hT1⟩)
  have hWlim : Tendsto (fun S : ℝ => K * (S ^ 9 * Real.exp (-S))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 9).const_mul K
  have hexpLim : Tendsto (fun S : ℝ => 4 * |κ| * Real.exp (-S)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul (4 * |κ|)
  obtain ⟨S, ⟨hWsmall, hexpSmall⟩, hSbig⟩ := (((hWlim.eventually (ge_mem_nhds (by positivity :
    (0 : ℝ) < B * c₁ / 5))).and (hexpLim.eventually (ge_mem_nhds hB))).and
      (eventually_ge_atTop (max (max S₁ (Real.exp 1))
        (max T (5 * (M₀ * E * Real.log T + 4 * |κ| * M₀) / (B * c₁)))))).exists
  have hS₁ : S₁ ≤ S := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hSbig
  have hSe : Real.exp 1 ≤ S := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hSbig
  have hST : T ≤ S := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hSbig
  have hSE : 5 * (M₀ * E * Real.log T + 4 * |κ| * M₀) / (B * c₁) ≤ S :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hSbig
  have hS0 : 0 < S := lt_of_lt_of_le (Real.exp_pos 1) hSe
  have hS1 : 1 ≤ S := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hSe
  have hRS : Real.log S ≤ S := Real.log_le_self hS0.le
  have hR0 : 0 ≤ Real.log S := Real.log_nonneg hS1
  set a := Real.log S + S with ha
  have ha0 : 0 ≤ a := by linarith
  have hTb : T ≤ Real.exp (2 * a + 1) :=
    hST.trans (le_trans (by linarith) (Real.add_one_le_exp (2 * a + 1)))
  have hf := contDiff_mertensTest (Real.log S) S
  have hfs : tsupport (mertensTest (Real.log S) S) ⊆ Icc (-a) a := tsupport_mertensTest hS0
  have hbound := integral_weilAtomSymbol_le_polar_mertens ha0 hf hfs
    (paperFT_mertensTest_half_I hS0) (paperFT_mertensTest_neg_half_I hS0) lam κ A B
    (abs_deriv_weilTestEvenPart_mertensTest_le hR0 hRS hS0 hLg0 hLg) hT1 hTb hE hη
  rw [paperFT_mertensTest_zero hS0, norm_zero, ← hM₀] at hbound
  have hpos' := hpos a ha0 _ hf hfs (paperFT_mertensTest_half_I hS0)
    (paperFT_mertensTest_neg_half_I hS0)
  set m := ∫ x : ℝ, ‖mertensTest (Real.log S) S x‖ ^ 2 with hmdef
  have hm : c₁ * S ≤ m := hmassS S hS₁
  have hm0 : 0 ≤ m := le_trans (by positivity) hm
  have hW : ‖zetaZeroConfig.W (mertensTest (Real.log S) S) (mertensTest (Real.log S) S)‖ ≤
      B * c₁ / 5 * S := by
    refine (hWS S hSe).trans ?_
    calc K * S ^ 10 * Real.exp (-S) = K * (S ^ 9 * Real.exp (-S)) * S := by ring
      _ ≤ B * c₁ / 5 * S := mul_le_mul_of_nonneg_right hWsmall hS0.le
  have hexpL : Real.exp (-((2 * a + 1) / 2)) ≤ Real.exp (-S) :=
    Real.exp_le_exp.mpr (by rw [ha]; linarith)
  have hκm : |κ| * (4 * m * Real.exp (-((2 * a + 1) / 2))) ≤ B * m := by
    calc |κ| * (4 * m * Real.exp (-((2 * a + 1) / 2)))
        ≤ |κ| * (4 * m * Real.exp (-S)) := by gcongr
      _ = 4 * |κ| * Real.exp (-S) * m := by ring
      _ ≤ B * m := mul_le_mul_of_nonneg_right hexpSmall hm0
  have h1 : M₀ * E * Real.log T + 4 * |κ| * M₀ ≤ B * c₁ / 5 * S := by
    have := (div_le_iff₀ (by positivity : 0 < B * c₁)).mp hSE
    linarith
  have h2 : M₀ * η * (2 * a + 1) ≤ B * c₁ / 5 * S := by
    have hηM : M₀ * η ≤ B * c₁ / 25 := by
      rw [hηdef, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_pos hB hc₁]
    have ha' : 2 * a + 1 ≤ 5 * S := by rw [ha]; linarith
    calc M₀ * η * (2 * a + 1) ≤ B * c₁ / 25 * (5 * S) :=
          mul_le_mul hηM ha' (by linarith) (by positivity)
      _ = B * c₁ / 5 * S := by ring
  have hBm : B * (c₁ * S) ≤ B * m := mul_le_mul_of_nonneg_left hm hB.le
  have hX : ‖zetaZeroConfig.W (mertensTest (Real.log S) S) (mertensTest (Real.log S) S)‖ -
        A * 0 ^ 2 - 2 * B * m +
        |κ| * (4 * m * Real.exp (-((2 * a + 1) / 2)) + 4 * M₀) +
        M₀ * E * Real.log T + M₀ * η * (2 * a + 1) < 0 := by
    have : 0 < B * c₁ * S := by positivity
    nlinarith
  have hπ : 0 < π := Real.pi_pos
  have := mul_neg_of_pos_of_neg (by positivity : (0 : ℝ) < 2 * π) hX
  linarith

/-! ### Half-power partial sums -/


/-- The defect `∑_{n=1}^N n^{-1/2} - 2√N`. -/
def halfPowerDefect (N : ℕ) : ℝ := (∑ n ∈ Finset.Icc 1 N, 1 / Real.sqrt n) - 2 * Real.sqrt N

/-- `2√n √(n+1) ≤ 2n + 1` (arithmetic–geometric mean). -/
theorem two_sqrt_mul_sqrt_succ_le (n : ℕ) :
    2 * Real.sqrt n * Real.sqrt (n + 1) ≤ 2 * n + 1 := by
  have h1 : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have h2 : Real.sqrt (n + 1) ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
  nlinarith [sq_nonneg (Real.sqrt (n + 1) - Real.sqrt n)]

/-- `1/√(n+1) ≤ 2(√(n+1) - √n)`. -/
theorem inv_sqrt_succ_le (n : ℕ) :
    1 / Real.sqrt (n + 1) ≤ 2 * (Real.sqrt (n + 1) - Real.sqrt n) := by
  have hs : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have h2 : Real.sqrt (n + 1) ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
  rw [div_le_iff₀ hs]
  nlinarith [two_sqrt_mul_sqrt_succ_le n]

/-- `2(√(n+1) - √n) ≤ 1/√n` for `n ≥ 1`. -/
theorem two_sqrt_succ_sub_le {n : ℕ} (hn : 1 ≤ n) :
    2 * (Real.sqrt (n + 1) - Real.sqrt n) ≤ 1 / Real.sqrt n := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have h1 : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  rw [le_div_iff₀ hs]
  nlinarith [two_sqrt_mul_sqrt_succ_le n]

theorem halfPowerDefect_succ (N : ℕ) :
    halfPowerDefect (N + 1) =
      halfPowerDefect N + 1 / Real.sqrt (N + 1) - 2 * (Real.sqrt (N + 1) - Real.sqrt N) := by
  unfold halfPowerDefect
  rw [Finset.sum_Icc_succ_top (by omega)]
  push_cast; ring

theorem halfPowerDefect_antitone : Antitone halfPowerDefect := by
  refine antitone_nat_of_succ_le fun N => ?_
  rw [halfPowerDefect_succ]
  linarith [inv_sqrt_succ_le N]

theorem halfPowerDefect_one : halfPowerDefect 1 = -1 := by
  simp [halfPowerDefect]; norm_num

/-- `0 ≤ D(N) - D(M) ≤ 1/√N - 1/√M` for `1 ≤ N ≤ M`. -/
theorem halfPowerDefect_sub_le {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    halfPowerDefect N - halfPowerDefect M ≤ 1 / Real.sqrt N - 1 / Real.sqrt M := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    rw [halfPowerDefect_succ]
    have := two_sqrt_succ_sub_le (le_trans hN hNM)
    push_cast
    linarith

theorem halfPowerDefect_ge (N : ℕ) : -2 ≤ halfPowerDefect N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [halfPowerDefect]
  · have h := halfPowerDefect_sub_le (le_refl 1) hN
    rw [halfPowerDefect_one] at h
    have : 0 ≤ 1 / Real.sqrt N := by positivity
    linarith

/-- The limit `ζ(½) = lim (∑_{n ≤ N} n^{-1/2} - 2√N)`, as the infimum of the decreasing defect. -/
def halfPowerConstant : ℝ := ⨅ N, halfPowerDefect N

theorem tendsto_halfPowerDefect :
    Tendsto halfPowerDefect atTop (𝓝 halfPowerConstant) :=
  tendsto_atTop_ciInf halfPowerDefect_antitone ⟨-2, by
    rintro _ ⟨N, rfl⟩; exact halfPowerDefect_ge N⟩

theorem halfPowerConstant_le : halfPowerConstant ≤ -1 := by
  rw [← halfPowerDefect_one]
  exact ciInf_le ⟨-2, by rintro _ ⟨N, rfl⟩; exact halfPowerDefect_ge N⟩ 1

/-- `√x - √⌊x⌋ ≤ 1/√x` for `x ≥ 1`. -/
theorem sqrt_sub_sqrt_floor_le {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt x - Real.sqrt ⌊x⌋₊ ≤ 1 / Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hfl' : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  have hf2 : Real.sqrt (⌊x⌋₊ : ℝ) ^ 2 = ⌊x⌋₊ := Real.sq_sqrt (Nat.cast_nonneg _)
  have hf0 : 0 ≤ Real.sqrt (⌊x⌋₊ : ℝ) := Real.sqrt_nonneg _
  have hle : Real.sqrt (⌊x⌋₊ : ℝ) ≤ Real.sqrt x := Real.sqrt_le_sqrt hfl
  rw [le_div_iff₀ hs]
  nlinarith

/-- `∑_{2 ≤ n ≤ x} n^{-1/2} - 2√x → ζ(½) - 1`. -/
theorem tendsto_sum_inv_sqrt_sub :
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, 1 / Real.sqrt n) - 2 * Real.sqrt x)
      atTop (𝓝 (halfPowerConstant - 1)) := by
  have hD := tendsto_halfPowerDefect.comp tendsto_nat_floor_atTop (α := ℝ)
  have hsq : Tendsto (fun x : ℝ => Real.sqrt x - Real.sqrt ⌊x⌋₊) atTop (𝓝 0) := by
    have hinv : Tendsto (fun x : ℝ => 1 / Real.sqrt x) atTop (𝓝 0) := by
      refine (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).congr fun x => ?_
      simp
    refine squeeze_zero' ?_ ?_ hinv
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      exact sub_nonneg.mpr (Real.sqrt_le_sqrt (Nat.floor_le hx))
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      exact sqrt_sub_sqrt_floor_le hx
  have hlim := (hD.sub_const 1).sub (hsq.const_mul 2)
  rw [mul_zero, sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have h1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff _ |>.mpr hx
  simp only [Function.comp_apply, halfPowerDefect]
  have hsplit : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 1 / Real.sqrt n =
      1 + ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, 1 / Real.sqrt n := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc h1]
    simp only [Nat.cast_one, Real.sqrt_one, div_one]
    congr 1
  rw [hsplit]; ring


/-! ### The constant shift -/

/-- **Constant shifts below `Λ` are not Weil-positive.**  For every `c > 0` some polar-constrained
`C²` test has negative symbol energy with weights `Λ(n) - c`.  The deviation `-c` has polar
Mertens expansion `-c ∑_{2 ≤ n ≤ x} n^{-1/2} = -2c√x + c(1 - ζ(½)) + o(1)`, and `1 - ζ(½) ≥ 2`. -/
theorem vonMangoldt_sub_const_not_weilPositive {c : ℝ} (hc : 0 < c) :
    ¬ (∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) - c)
          ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) := by
  intro hpos
  have hlim : Tendsto (fun x : ℝ =>
      (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (((ArithmeticFunction.vonMangoldt n : ℝ) - c) -
        ArithmeticFunction.vonMangoldt n) / Real.sqrt n) -
        2 * (-c) * Real.sqrt x - 0 * Real.log x) atTop
      (𝓝 (-c * (halfPowerConstant - 1))) := by
    refine (tendsto_sum_inv_sqrt_sub.const_mul (-c)).congr fun x => ?_
    have hs : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (((ArithmeticFunction.vonMangoldt n : ℝ) - c) -
        ArithmeticFunction.vonMangoldt n) / Real.sqrt n =
        -c * ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, 1 / Real.sqrt n := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => ?_; ring
    rw [hs]; ring
  have hB := polar_mertens_constant_nonpos_of_weilAtomSymbol_nonneg hlim hpos
  have := halfPowerConstant_le
  nlinarith

/-- **Weil positivity pins the constant shift.**  If the weights `Λ(n) + c` are Weil-positive, then
`c = 0`: upward shifts break the density ceiling, downward shifts the central Mertens constant. -/
theorem eq_zero_of_vonMangoldt_add_const_weilPositive {c : ℝ}
    (hpos : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + c)
          ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) :
    c = 0 := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · refine absurd ?_ (vonMangoldt_sub_const_not_weilPositive (neg_pos.mpr hc))
    simpa only [sub_neg_eq_add] using hpos
  · exact hc
  · exact absurd hpos (vonMangoldt_add_const_not_weilPositive hc)

end RHTower
