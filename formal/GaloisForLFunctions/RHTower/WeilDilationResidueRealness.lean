import GaloisForLFunctions.RHTower.WeilDilationCriticalLineShift

/-!
# Weil positivity forces the functional equation at the critical zeros

Let `S` be a finite set of positive integers and `b` real.  Let `B(s) = Σ_{m ∈ S} b(m) m^{-s}`, and
let `w(n) = Σ_{m ∈ S, m ∣ n} b(m) Λ(n/m)`, whose Dirichlet series is `−B(s) ζ'/ζ(s)`.

* **Tangent criterion** (`dilation_tangent_criterion`).  If `Λ + w` is Weil-positive, then the
  analytic bump-cube shift integrand `V(t)` on the critical line has `Re V(t) ≤ 0` for every `t`.
  Off the zeros of `ζ`, `V(t) = |ξ(½+it)|⁶ |ĥ(t)|² B(½+it)(−ζ'/ζ)(½+it)`
  (`dilationShiftIntegrand_bumpCube_critical_eq`).
  - Proof: spread radical tests `twistTest 0 τ₀ (log S) S` have energy
    `2π Re W_ζ − 2 Re ∫ V |q̂_S|² − 2 Re Err` (`integral_weilAtomSymbol_dilated_twistTest`).
  - The zero side is `O(S^{10} e^{-S})`, the truncation error is `O(S⁷ e^{-S})`
    (`tendsto_dilation_error`), and `(1/S) ∫ V |q̂_S|² → V(τ₀) ∫ |κ̂|⁴`
    (`tendsto_integral_probe_concentration`).
* **Residue realness** (`dilationPoly_im_eq_zero_of_weilPositive`).  If `Λ + w` is Weil-positive, then
  `Im B(½+iγ) = 0` at every zero `½+iγ` of `ζ` on the critical line; equivalently `B(ρ) = B(1−ρ)`.
  - Near a zero of order `m`, `(t−γ) Re[B(−ζ'/ζ)](½+it) → −m Im B(½+iγ)`, so a nonzero imaginary
    part makes `Re V` positive on one side of `γ`.
  - The residues of the perturbation's Dirichlet series at the critical zeros must be real: Weil
    positivity imposes the degree-zero functional equation `B(s) = B(1−s)` on the zero set.
* `single_dilation_critical_ordinates`: if `Λ(n) + c Λ(n/m)` is Weil-positive (`m ≥ 2`, `c ≠ 0`),
  every critical ordinate `γ` satisfies `γ log m ∈ π ℤ`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ArithmeticFunction

noncomputable section
namespace RHTower

open Zeta23 Zeta23.WeilEF

/-! ### Concentration of the spread probe -/

/-- The fourth moment `∫ |κ̂|⁴` of the probe profile. -/
def probeQuartic : ℝ := ∫ v : ℝ, ‖paperFT weilBumpC v‖ ^ 4

theorem integrable_norm_paperFT_weilBumpC_pow_four :
    Integrable (fun v : ℝ => ‖paperFT weilBumpC v‖ ^ 4) := by
  obtain ⟨Cκ, hCκ0, hCκ⟩ := exists_norm_paperFT_weilBumpC_le
  have hmaj : Integrable (fun v : ℝ => Cκ ^ 4 * (1 + ‖v‖) ^ (-(2 : ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2)
      (by rw [Module.finrank_self]; norm_num)).const_mul _
  refine hmaj.mono' ?_ (Eventually.of_forall fun v => ?_)
  · exact ((differentiable_paperFT (contDiff_weilBumpC.continuous)
      hasCompactSupport_weilBumpC).continuous.comp Complex.continuous_ofReal).norm.pow 4
      |>.aestronglyMeasurable
  · have h1 := hCκ v
    have hv : 0 < 1 + |v| := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h2 : ‖paperFT weilBumpC v‖ ^ 4 ≤ (Cκ / (1 + |v|) ^ 2) ^ 4 := by
      gcongr
    refine h2.trans ?_
    rw [Real.norm_eq_abs, Real.rpow_neg hv.le,
      show (1 + |v|) ^ (2 : ℝ) = (1 + |v|) ^ 2 by norm_cast, div_pow, ← pow_mul]
    have h1v : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
    have hp : (1 + |v|) ^ 2 ≤ (1 + |v|) ^ (2 * 4) := pow_le_pow_right₀ h1v (by norm_num)
    rw [div_eq_mul_inv]
    gcongr


theorem norm_paperFT_twistProbe_sq {τ₀ Sp : ℝ} (hSp : 0 < Sp) (t : ℝ) :
    ‖paperFT (twistProbe τ₀ Sp) t‖ ^ 2 = Sp ^ 2 * ‖paperFT weilBumpC ((Sp * (t - τ₀) : ℝ) : ℂ)‖ ^ 4 := by
  rw [paperFT_twistProbe_real hSp, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hSp]
  ring

/-- **Concentration of the spread probe.**  For continuous bounded `V`,
`(1/S) ∫ V(t) |q̂_S(t)|² dt → V(τ₀) ∫ |κ̂|⁴` as `S → ∞`. -/
theorem tendsto_integral_probe_concentration {V : ℝ → ℂ} (hVc : Continuous V) {M : ℝ}
    (hVb : ∀ t, ‖V t‖ ≤ M) (τ₀ : ℝ) :
    Tendsto (fun Sp : ℝ => ((1 / Sp : ℝ) : ℂ) *
        ∫ t : ℝ, V t * ((‖paperFT (twistProbe τ₀ Sp) t‖ ^ 2 : ℝ) : ℂ)) atTop
      (𝓝 (V τ₀ * (probeQuartic : ℂ))) := by
  set κ4 : ℝ → ℝ := fun v => ‖paperFT weilBumpC v‖ ^ 4 with hκ4
  have hκi : Integrable κ4 := integrable_norm_paperFT_weilBumpC_pow_four
  have hκc : Continuous κ4 := ((differentiable_paperFT (contDiff_weilBumpC.continuous)
    hasCompactSupport_weilBumpC).continuous.comp Complex.continuous_ofReal).norm.pow 4
  -- rescaled form
  have hresc : ∀ Sp : ℝ, 0 < Sp → ((1 / Sp : ℝ) : ℂ) *
      ∫ t : ℝ, V t * ((‖paperFT (twistProbe τ₀ Sp) t‖ ^ 2 : ℝ) : ℂ) =
      ∫ y : ℝ, V (τ₀ + y / Sp) * ((κ4 y : ℝ) : ℂ) := by
    intro Sp hSp
    have h1 : ∫ t : ℝ, V t * ((‖paperFT (twistProbe τ₀ Sp) t‖ ^ 2 : ℝ) : ℂ) =
        ∫ u : ℝ, V (τ₀ + u) * ((Sp ^ 2 * κ4 (Sp * u) : ℝ) : ℂ) := by
      rw [← integral_add_left_eq_self (μ := volume) _ τ₀]
      congr 1; funext u
      rw [norm_paperFT_twistProbe_sq hSp]
      simp only [hκ4, add_sub_cancel_left]
    have h2 : ∫ u : ℝ, V (τ₀ + u) * ((Sp ^ 2 * κ4 (Sp * u) : ℝ) : ℂ) =
        (Sp : ℂ) * ∫ y : ℝ, V (τ₀ + y / Sp) * ((κ4 y : ℝ) : ℂ) := by
      have := Measure.integral_comp_mul_left
        (fun y : ℝ => V (τ₀ + y / Sp) * ((Sp ^ 2 * κ4 y : ℝ) : ℂ)) Sp
      simp only [mul_div_cancel_left₀ _ hSp.ne'] at this
      rw [this, abs_of_pos (inv_pos.mpr hSp), ← integral_smul, ← integral_const_mul]
      congr 1; funext y
      rw [Complex.real_smul]; push_cast
      have hSpC : (Sp : ℂ) ≠ 0 := by exact_mod_cast hSp.ne'
      field_simp
    rw [h1, h2, ← mul_assoc]
    have hSpC : (Sp : ℂ) ≠ 0 := by exact_mod_cast hSp.ne'
    rw [show ((1 / Sp : ℝ) : ℂ) * (Sp : ℂ) = 1 by push_cast; field_simp, one_mul]
  have hlim : Tendsto (fun Sp : ℝ => ∫ y : ℝ, V (τ₀ + y / Sp) * ((κ4 y : ℝ) : ℂ)) atTop
      (𝓝 (∫ y : ℝ, V τ₀ * ((κ4 y : ℝ) : ℂ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => M * κ4 y) ?_ ?_
      (hκi.const_mul M) ?_
    · filter_upwards with Sp
      exact ((hVc.comp (continuous_const.add (continuous_id.div_const Sp))).mul
        (Complex.continuous_ofReal.comp hκc)).aestronglyMeasurable
    · filter_upwards with Sp
      filter_upwards with y
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (hVb _) (by positivity)
    · filter_upwards with y
      refine ((hVc.tendsto τ₀).comp ?_).mul_const _
      have : Tendsto (fun Sp : ℝ => y / Sp) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
      simpa using (tendsto_const_nhds (x := τ₀)).add this
  have hval : ∫ y : ℝ, V τ₀ * ((κ4 y : ℝ) : ℂ) = V τ₀ * (probeQuartic : ℂ) := by
    rw [integral_const_mul, integral_complex_ofReal]; rfl
  rw [hval] at hlim
  exact hlim.congr' (eventually_gt_atTop 0 |>.mono fun Sp hSp => (hresc Sp hSp).symm)


/-! ### The energy of the spread test under the dilated weights -/

theorem dilatedVonMangoldt_zero (S : Finset ℕ) (b : ℕ → ℝ) : dilatedVonMangoldt S b 0 = 0 := by
  unfold dilatedVonMangoldt
  refine Finset.sum_eq_zero fun m _ => ?_
  simp

theorem dilatedVonMangoldt_one (S : Finset ℕ) (b : ℕ → ℝ) : dilatedVonMangoldt S b 1 = 0 := by
  unfold dilatedVonMangoldt
  refine Finset.sum_eq_zero fun m _ => ?_
  split_ifs with h
  · have : m = 1 := Nat.dvd_one.mp h
    subst this; simp
  · rfl

theorem weilTest_log_eq_zero_of_floor_lt {a : ℝ} {f : ℝ → ℂ} (hfs : tsupport f ⊆ Icc (-a) a)
    {n : ℕ} (hn : ⌊Real.exp (2 * a)⌋₊ < n) : EF.weilTest f f (Real.log n) = 0 := by
  have hx : Real.exp (2 * a) < n := Nat.lt_of_floor_lt hn
  have hn0 : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hx
  have hlog : 2 * a < Real.log n := (Real.lt_log_iff_exp_lt hn0).mpr hx
  have hl0 : 0 ≤ Real.log n := by
    have : (1 : ℝ) ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp at hn0
      · exact_mod_cast h0
    exact Real.log_nonneg this
  have hh : ∀ u, a < |u| → f u = 0 := by
    intro u hu
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hfs hmem
    rw [mem_Icc] at this
    have := abs_le.mpr ⟨this.1, this.2⟩
    linarith
  exact weilTest_self_eq_zero hh (by rw [abs_of_nonneg hl0]; exact hlog)

/-- The dilated atom sum of a test at level `a` is twice the real part of its one-sided line
integral. -/
theorem sum_dilated_atomCoeff_eq {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) {S : Finset ℕ} (hS : ∀ m ∈ S, 1 ≤ m) (b : ℕ → ℝ)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) :
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, dilatedVonMangoldt S b n / Real.sqrt n *
        atomCoeff f n =
      2 * ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, dilationPoly S b (c + t * I) *
        Hfn (EF.weilTest f f) (c + t * I) * (-logDeriv riemannZeta (c + t * I))).re := by
  set N := ⌊Real.exp (2 * a)⌋₊
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  have hk : ContDiff ℝ 2 (EF.weilTest f f) := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport (EF.weilTest f f) := EF.weilTest_hasCompactSupport hfc hfc
  rw [dilated_prime_side_line hk hkc hc1 hc2 hS b]
  have hsupp : ∀ n ∉ Finset.Icc 2 N,
      ((dilatedVonMangoldt S b n / Real.sqrt n : ℝ) : ℂ) * EF.weilTest f f (Real.log n) = 0 := by
    intro n hn
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    rcases hn with h | h
    · interval_cases n
      · simp [dilatedVonMangoldt_zero]
      · simp [dilatedVonMangoldt_one]
    · rw [weilTest_log_eq_zero_of_floor_lt hfs h, mul_zero]
  rw [tsum_eq_sum hsupp, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.re_ofReal_mul]
  unfold atomCoeff
  rw [weilTest_self_neg, Complex.add_re, Complex.conj_re]
  ring


theorem continuous_dilationShiftIntegrand_line {S : Finset ℕ} (b : ℕ → ℝ) {k : ℝ → ℂ}
    (hk : Continuous k) (hkc : HasCompactSupport k) {c : ℝ} (hc : 0 < c) :
    Continuous fun t : ℝ => dilationShiftIntegrand S b k ((c : ℂ) + t * I) := by
  have hd := differentiableOn_dilationShiftIntegrand S b hk hkc
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hmem : ((c : ℂ) + t * I) ∈ {s : ℂ | 0 < s.re} := by simp [hc]
  exact ContinuousAt.comp (g := dilationShiftIntegrand S b k) (f := fun t : ℝ => (c : ℂ) + t * I)
    ((hd _ hmem).differentiableAt (hU.mem_nhds hmem)).continuousAt
    (by fun_prop : Continuous fun t : ℝ => (c : ℂ) + t * I).continuousAt

theorem integrable_dilationShiftIntegrand_line {S : Finset ℕ} (hS : ∀ m ∈ S, 1 ≤ m)
    (b : ℕ → ℝ) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hk1 : Hfn k 1 = 0) {c : ℝ} (hc1 : 1 / 2 ≤ c) (hc2 : c ≤ 3 / 2) :
    Integrable fun t : ℝ => dilationShiftIntegrand S b k ((c : ℂ) + t * I) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_dilationShiftIntegrand_le hS b hk hkc hk1
  refine ((integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
    (by rw [Module.finrank_self]; norm_num : (Module.finrank ℝ ℝ : ℝ) < 3 / 2)).const_mul K).mono'
    (continuous_dilationShiftIntegrand_line b hk.continuous hkc (by linarith)).aestronglyMeasurable
    (Eventually.of_forall fun t => hK c t hc1 hc2)

theorem energy_combine {X Sd : ℝ} {W E₁ E₂ : ℂ} (h1 : X = 2 * π * W.re)
    (h2 : Sd = 2 * ((1 / (2 * Real.pi) : ℂ) * (E₁ + E₂)).re) :
    X - 2 * π * Sd = 2 * π * W.re - 2 * E₂.re - 2 * E₁.re := by
  have hre : ((1 / (2 * Real.pi) : ℂ) * (E₁ + E₂)).re = (E₁.re + E₂.re) / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; rfl,
      Complex.re_ofReal_mul, Complex.add_re]
    ring
  rw [h1, h2, hre]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **Energy of the spread test.**  For the dilated weights `Λ + w` and the spread radical test
`F = twistTest 0 τ₀ (log S) S` at level `a = 3 log S + S`,
`E(F) = 2π Re W_ζ(F) − 2 Re ∫ V(t) |q̂_S(t)|² dt − 2 Re Err`,
with `V` the bump-cube shift integrand on the critical line and `Err` the truncation error on
`Re s = c`. -/
theorem integral_weilAtomSymbol_dilated_twistTest {S : Finset ℕ} (hS : ∀ m ∈ S, 1 ≤ m)
    (b : ℕ → ℝ) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) {τ₀ Sp : ℝ} (hSp : 1 ≤ Sp) :
    ∫ τ : ℝ, ‖paperFT (twistTest 0 τ₀ (Real.log Sp) Sp) τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + dilatedVonMangoldt S b n)
          ⌊Real.exp (2 * (3 * Real.log Sp + Sp))⌋₊ (τ / (2 * π)) =
      2 * π * (zetaZeroConfig.W (twistTest 0 τ₀ (Real.log Sp) Sp)
          (twistTest 0 τ₀ (Real.log Sp) Sp)).re -
        2 * (∫ t : ℝ, dilationShiftIntegrand S b (EF.weilTest bumpCube bumpCube)
            (((1 / 2 : ℝ) : ℂ) + t * I) *
          ((‖paperFT (twistProbe τ₀ Sp) t‖ ^ 2 : ℝ) : ℂ)).re -
        2 * (∫ t : ℝ, dilationPoly S b ((c : ℂ) + t * I) *
          (Hfn (EF.weilTest (twistTest 0 τ₀ (Real.log Sp) Sp) (twistTest 0 τ₀ (Real.log Sp) Sp))
              ((c : ℂ) + t * I) -
            riemannPhiTransform ((c : ℂ) + t * I) ^ 3 * xiConj ((c : ℂ) + t * I) ^ 3 *
              Hfn (EF.weilTest (dilationProbe τ₀ Sp) (dilationProbe τ₀ Sp)) ((c : ℂ) + t * I)) *
          (-logDeriv riemannZeta ((c : ℂ) + t * I))).re := by
  have hSp0 : 0 < Sp := by linarith
  set R := Real.log Sp with hR
  set F := twistTest 0 τ₀ R Sp with hFdef
  set a := 3 * R + Sp with hadef
  set N := ⌊Real.exp (2 * a)⌋₊ with hN
  set G := dilationProbe τ₀ Sp with hGdef
  have hFc : ContDiff ℝ 2 F := contDiff_twistTest 0 τ₀ R Sp
  have hFs : tsupport F ⊆ Icc (-a) a := tsupport_twistTest hSp0
  have hFcs : HasCompactSupport F :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport F) hFs
  have hp : paperFT F (I / 2) = 0 := by
    rw [hFdef, paperFT_twistTest_factor hSp0, paperFT_weilRadicalTest_half_I, zero_mul]
  have hm : paperFT F (-(I / 2)) = 0 := by
    rw [hFdef, paperFT_twistTest_factor hSp0, paperFT_weilRadicalTest_neg_half_I, zero_mul]
  -- split the weights
  have hsplit : ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 *
      weilAtomSymbol (fun n => (Λ n : ℝ) + dilatedVonMangoldt S b n) N (τ / (2 * π)) =
      (∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * weilAtomSymbol (fun n => (Λ n : ℝ)) N (τ / (2 * π))) -
        2 * π * ∑ n ∈ Finset.Icc 2 N, dilatedVonMangoldt S b n / Real.sqrt n * atomCoeff F n := by
    rw [integral_weilAtomSymbol_eq_archEnergy_sub hFc hFs _ le_rfl,
      integral_weilAtomSymbol_eq_archEnergy_sub hFc hFs _ le_rfl]
    have : ∑ n ∈ Finset.Icc 2 N, ((Λ n : ℝ) + dilatedVonMangoldt S b n) / Real.sqrt n *
        atomCoeff F n = ∑ n ∈ Finset.Icc 2 N, (Λ n : ℝ) / Real.sqrt n * atomCoeff F n +
        ∑ n ∈ Finset.Icc 2 N, dilatedVonMangoldt S b n / Real.sqrt n * atomCoeff F n := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [this]; ring
  -- the von Mangoldt part is the zero side
  have hW := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hFc hFs hp hm
  have hWre : (∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * weilAtomSymbol (fun n => (Λ n : ℝ)) N (τ / (2 * π))) =
      2 * π * (zetaZeroConfig.W F F).re := by
    rw [hW, Complex.ofReal_re, ← hN]; field_simp
  -- the dilated part through the line integral
  have hdil := sum_dilated_atomCoeff_eq hFc hFs hS b hc1 hc2
  -- the line integral splits into the shift integrand and the error
  have hG1 : Hfn (EF.weilTest G G) 1 = 0 := Hfn_weilTest_dilationProbe_one hSp0
  have hGc : ContDiff ℝ 2 (EF.weilTest G G) :=
    EF.weilTest_contDiff (contDiff_dilationProbe τ₀ Sp) (contDiff_dilationProbe τ₀ Sp).continuous
      (hasCompactSupport_dilationProbe hSp0)
  have hGcs : HasCompactSupport (EF.weilTest G G) :=
    EF.weilTest_hasCompactSupport (hasCompactSupport_dilationProbe hSp0)
      (hasCompactSupport_dilationProbe hSp0)
  have hkF : ContDiff ℝ 2 (EF.weilTest F F) := EF.weilTest_contDiff hFc hFc.continuous hFcs
  have hkFc : HasCompactSupport (EF.weilTest F F) := EF.weilTest_hasCompactSupport hFcs hFcs
  have hshiftI := integrable_dilationShiftIntegrand_line hS b hGc hGcs hG1 (by linarith) hc2
  have hBbd : ∀ t : ℝ, ‖dilationPoly S b ((c : ℂ) + t * I)‖ ≤ ∑ m ∈ S, |b m| := fun t =>
    norm_dilationPoly_le hS b (by simp; linarith)
  have hBc : Continuous fun t : ℝ => dilationPoly S b ((c : ℂ) + t * I) := by
    unfold dilationPoly
    refine continuous_finsetSum _ fun m hm => continuous_const.mul ?_
    have hm1 := hS m hm
    have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    exact (by fun_prop : Continuous fun t : ℝ => -((c : ℂ) + t * I)).const_cpow (Or.inl hmC)
  have htotI : Integrable fun t : ℝ => dilationPoly S b ((c : ℂ) + t * I) *
      Hfn (EF.weilTest F F) ((c : ℂ) + t * I) * (-logDeriv riemannZeta ((c : ℂ) + t * I)) := by
    have h := ((integrable_Hfn_mul_logDeriv_zeta hkF hkFc hc1 hc2).neg).bdd_mul
      hBc.aestronglyMeasurable (Eventually.of_forall hBbd)
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.neg_apply]; ring
  have hpt : ∀ t : ℝ, dilationPoly S b ((c : ℂ) + t * I) *
      Hfn (EF.weilTest F F) ((c : ℂ) + t * I) * (-logDeriv riemannZeta ((c : ℂ) + t * I)) =
      dilationPoly S b ((c : ℂ) + t * I) *
        (Hfn (EF.weilTest F F) ((c : ℂ) + t * I) -
          riemannPhiTransform ((c : ℂ) + t * I) ^ 3 * xiConj ((c : ℂ) + t * I) ^ 3 *
            Hfn (EF.weilTest G G) ((c : ℂ) + t * I)) *
        (-logDeriv riemannZeta ((c : ℂ) + t * I)) +
      dilationShiftIntegrand S b (EF.weilTest G G) ((c : ℂ) + t * I) := by
    intro t
    have hre : 0 < ((c : ℂ) + t * I).re := by simp; linarith
    have hne1 : ((c : ℂ) + t * I) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hζ : riemannZeta ((c : ℂ) + t * I) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
    rw [dilationShiftIntegrand_eq hG1 hre hne1 hζ]
    ring
  have herrI : Integrable fun t : ℝ => dilationPoly S b ((c : ℂ) + t * I) *
      (Hfn (EF.weilTest F F) ((c : ℂ) + t * I) -
        riemannPhiTransform ((c : ℂ) + t * I) ^ 3 * xiConj ((c : ℂ) + t * I) ^ 3 *
          Hfn (EF.weilTest G G) ((c : ℂ) + t * I)) *
      (-logDeriv riemannZeta ((c : ℂ) + t * I)) := by
    refine (htotI.sub hshiftI).congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply]; rw [hpt t]; ring
  have hJ : ∫ t : ℝ, dilationPoly S b ((c : ℂ) + t * I) *
      Hfn (EF.weilTest F F) ((c : ℂ) + t * I) * (-logDeriv riemannZeta ((c : ℂ) + t * I)) =
      (∫ t : ℝ, dilationPoly S b ((c : ℂ) + t * I) *
        (Hfn (EF.weilTest F F) ((c : ℂ) + t * I) -
          riemannPhiTransform ((c : ℂ) + t * I) ^ 3 * xiConj ((c : ℂ) + t * I) ^ 3 *
            Hfn (EF.weilTest G G) ((c : ℂ) + t * I)) *
        (-logDeriv riemannZeta ((c : ℂ) + t * I))) +
      ∫ t : ℝ, dilationShiftIntegrand S b (EF.weilTest bumpCube bumpCube)
          (((1 / 2 : ℝ) : ℂ) + t * I) * ((‖paperFT (twistProbe τ₀ Sp) t‖ ^ 2 : ℝ) : ℂ) := by
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_add herrI hshiftI,
      integral_dilationShiftIntegrand_eq hS b hGc hGcs hG1 (by linarith) hc2]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    exact dilationShiftIntegrand_dilationProbe_critical b hSp0 t
  have hsum := hdil
  rw [hJ] at hsum
  rw [hsplit]
  exact energy_combine hWre hsum


/-! ### Size of the probe part -/

theorem bumpCube_eq_zero {x : ℝ} (hx : 3 / 4 < |x|) : bumpCube x = 0 := by
  have h2 : ∀ u : ℝ, 1 / 2 < |u| → convolution weilBumpPolarFree weilBumpPolarFree
      (ContinuousLinearMap.mul ℝ ℂ) volume u = 0 := fun u hu =>
    convolution_mul_eq_zero_of_abs_gt (a := 1 / 4) (b := 1 / 4)
      (fun _ h => weilBumpPolarFree_eq_zero h) (fun _ h => weilBumpPolarFree_eq_zero h)
      (by linarith)
  exact convolution_mul_eq_zero_of_abs_gt (a := 1 / 2) (b := 1 / 4) h2
    (fun _ h => weilBumpPolarFree_eq_zero h) (by linarith)

theorem dilationProbe_eq_zero {τ₀ Sp x : ℝ} (hSp : 0 < Sp) (hx : Sp + 3 / 4 < |x|) :
    dilationProbe τ₀ Sp x = 0 :=
  convolution_mul_eq_zero_of_abs_gt (a := 3 / 4) (b := Sp) (fun _ h => bumpCube_eq_zero h)
    (fun _ h => twistProbe_eq_zero hSp h) (by linarith)

theorem exists_norm_twistProbe_le : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ τ₀ Sp x : ℝ,
    ‖twistProbe τ₀ Sp x‖ ≤ Cq := by
  obtain ⟨C, hC⟩ := continuous_twistBump.bounded_above_of_compact_support hasCompactSupport_twistBump
  refine ⟨max C 0, le_max_right _ _, fun τ₀ Sp x => ?_⟩
  simp only [twistProbe, twistModulate, norm_mul, Complex.norm_exp]
  have : (I * ((-τ₀ : ℝ) : ℂ) * (x : ℂ)).re = 0 := by simp
  rw [this, Real.exp_zero, mul_one]
  exact (hC _).trans (le_max_left _ _)

theorem norm_convolution_mul_le_of_bound {f g : ℝ → ℂ} {B : ℝ} (hg : ∀ x, ‖g x‖ ≤ B)
    (hf : Integrable f) (x : ℝ) :
    ‖convolution f g (ContinuousLinearMap.mul ℝ ℂ) volume x‖ ≤ (∫ t : ℝ, ‖f t‖) * B := by
  rw [convolution_def]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_mul_const]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    (hf.norm.mul_const B) (Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.mul_apply', norm_mul]
  exact mul_le_mul_of_nonneg_left (hg _) (norm_nonneg _)

theorem exists_norm_dilationProbe_le : ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ τ₀ Sp x : ℝ,
    ‖dilationProbe τ₀ Sp x‖ ≤ Cg := by
  obtain ⟨Cq, hCq0, hCq⟩ := exists_norm_twistProbe_le
  have hi : Integrable bumpCube :=
    contDiff_bumpCube.continuous.integrable_of_hasCompactSupport hasCompactSupport_bumpCube
  refine ⟨(∫ t : ℝ, ‖bumpCube t‖) * Cq, by positivity, fun τ₀ Sp x => ?_⟩
  exact norm_convolution_mul_le_of_bound (hCq τ₀ Sp) hi x

theorem integral_norm_dilationProbe_sq_mul_exp_le {Cg : ℝ} (hCg : ∀ τ₀ Sp x : ℝ,
    ‖dilationProbe τ₀ Sp x‖ ≤ Cg) {τ₀ Sp : ℝ} (hSp : 0 < Sp) (y : ℝ) :
    ∫ x : ℝ, ‖dilationProbe τ₀ Sp x‖ ^ 2 * Real.exp (2 * y * x) ≤
      Cg ^ 2 * Real.exp (2 * |y| * (Sp + 3 / 4)) * (2 * (Sp + 3 / 4)) := by
  set L := Sp + 3 / 4 with hL
  have hL0 : 0 ≤ L := by linarith
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg τ₀ Sp 0)
  have hmaj : Integrable ((Icc (-L) L).indicator fun _ : ℝ => Cg ^ 2 * Real.exp (2 * |y| * L)) :=
    (integrableOn_const (by simp [Real.volume_Icc]) (by
      rw [← ofReal_norm]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Icc
  calc ∫ x : ℝ, ‖dilationProbe τ₀ Sp x‖ ^ 2 * Real.exp (2 * y * x)
      ≤ ∫ x : ℝ, (Icc (-L) L).indicator (fun _ : ℝ => Cg ^ 2 * Real.exp (2 * |y| * L)) x := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity) hmaj
          (Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ Icc (-L) L
        · rw [indicator_of_mem hx]
          have hxL : |x| ≤ L := abs_le.mpr ⟨hx.1, hx.2⟩
          have h1 : ‖dilationProbe τ₀ Sp x‖ ^ 2 ≤ Cg ^ 2 := by
            gcongr; exact hCg τ₀ Sp x
          have h2 : Real.exp (2 * y * x) ≤ Real.exp (2 * |y| * L) := by
            apply Real.exp_le_exp.mpr
            have : y * x ≤ |y| * L := by
              calc y * x ≤ |y * x| := le_abs_self _
                _ = |y| * |x| := abs_mul _ _
                _ ≤ |y| * L := mul_le_mul_of_nonneg_left hxL (abs_nonneg _)
            linarith
          exact mul_le_mul h1 h2 (by positivity) (by positivity)
        · rw [indicator_of_notMem hx]
          have hxL : L < |x| := by
            by_contra h; push Not at h; exact hx ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩
          simp only; rw [dilationProbe_eq_zero hSp hxL]; simp
    _ = Cg ^ 2 * Real.exp (2 * |y| * L) * (2 * L) := by
        rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
          smul_eq_mul]
        ring


/-! ### The error tends to zero -/

theorem probeQuartic_pos : 0 < probeQuartic := by
  have hc : 0 < Real.cos (1 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
    by linarith [Real.pi_gt_three]⟩
  have hκc : Continuous fun v : ℝ => ‖paperFT weilBumpC v‖ ^ 4 :=
    ((differentiable_paperFT (contDiff_weilBumpC.continuous)
      hasCompactSupport_weilBumpC).continuous.comp Complex.continuous_ofReal).norm.pow 4
  unfold probeQuartic
  rw [integral_pos_iff_support_of_nonneg (fun _ => by positivity)
    integrable_norm_paperFT_weilBumpC_pow_four]
  have hsub : Ioo (-1 : ℝ) 1 ⊆ Function.support fun v : ℝ => ‖paperFT weilBumpC v‖ ^ 4 := by
    intro v hv
    have hv1 : |v| ≤ 1 := (abs_lt.mpr ⟨hv.1, hv.2⟩).le
    have := norm_paperFT_weilBumpC_ge hv1
    simp only [Function.mem_support, ne_eq]
    have : 0 < ‖paperFT weilBumpC v‖ := lt_of_lt_of_le (by positivity) this
    positivity
  exact lt_of_lt_of_le (by simp [Real.volume_Ioo]) (measure_mono hsub)

theorem tail_mass_log_le {Sp : ℝ} (hSp : Real.exp 1 ≤ Sp) :
    ∫ u : ℝ, ‖riemannPhiTail (Real.log Sp) u‖ * Real.exp (1 * |u|) ≤
      40 * jacobiThetaTailConstant * Real.exp π / (6 * π - 6) * Sp ^ 6 * Real.exp (-Sp ^ 2) := by
  have hSp0 : 0 < Sp := lt_of_lt_of_le (Real.exp_pos 1) hSp
  have hL : 1 ≤ Real.log Sp := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hSp
  have h := integral_norm_riemannPhiTail_mul_exp_le (b := 1) hL (by norm_num)
  refine h.trans ?_
  have hM : 0 ≤ jacobiThetaTailConstant := jacobiThetaTailConstant_nonneg
  have hc6 : 0 < 6 * π - 6 := by nlinarith [Real.pi_gt_three]
  have hE0 : 0 ≤ 40 * jacobiThetaTailConstant * Real.exp π / (6 * π - 6) := by positivity
  have h6 : Real.exp (6 * (Real.log Sp - 1 / 4)) ≤ Sp ^ 6 := by
    calc Real.exp (6 * (Real.log Sp - 1 / 4)) ≤ Real.exp (6 * Real.log Sp) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = Sp ^ 6 := by
          rw [show (6 : ℝ) * Real.log Sp = (6 : ℕ) * Real.log Sp by norm_num, Real.exp_nat_mul,
            Real.exp_log hSp0]
  have hsq : Real.exp (2 * (Real.log Sp - 1 / 4)) = Sp ^ 2 * Real.exp (-(1 / 2)) := by
    rw [show 2 * (Real.log Sp - 1 / 4) = (2 : ℕ) * Real.log Sp + -(1 / 2) by push_cast; ring,
      Real.exp_add, Real.exp_nat_mul, Real.exp_log hSp0]
  have hhalf : 1 / 2 ≤ Real.exp (-(1 / 2)) := by
    rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
    have := Real.exp_one_lt_d9
    have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have hexp : Real.exp (-π * Real.exp (2 * (Real.log Sp - 1 / 4))) ≤ Real.exp (-Sp ^ 2) := by
    apply Real.exp_le_exp.mpr
    rw [hsq]
    have : 1 ≤ π * Real.exp (-(1 / 2)) := by nlinarith [Real.pi_gt_three]
    nlinarith [sq_nonneg Sp]
  calc 40 * jacobiThetaTailConstant * Real.exp π / (6 * π - 6) *
        Real.exp (6 * (Real.log Sp - 1 / 4)) * Real.exp (-π * Real.exp (2 * (Real.log Sp - 1 / 4)))
      ≤ 40 * jacobiThetaTailConstant * Real.exp π / (6 * π - 6) * Sp ^ 6 * Real.exp (-Sp ^ 2) := by
        gcongr


/-- The truncation error of the spread tests at `R = log S` tends to zero as `S → ∞`. -/
theorem tendsto_dilation_error {S : Finset ℕ} (hS : ∀ m ∈ S, 1 ≤ m) (b : ℕ → ℝ) (τ₀ : ℝ) :
    Tendsto (fun Sp : ℝ => ∫ t : ℝ, dilationPoly S b (((5 / 4 : ℝ) : ℂ) + t * I) *
        (Hfn (EF.weilTest (twistTest 0 τ₀ (Real.log Sp) Sp) (twistTest 0 τ₀ (Real.log Sp) Sp))
            (((5 / 4 : ℝ) : ℂ) + t * I) -
          riemannPhiTransform (((5 / 4 : ℝ) : ℂ) + t * I) ^ 3 *
            xiConj (((5 / 4 : ℝ) : ℂ) + t * I) ^ 3 *
            Hfn (EF.weilTest (dilationProbe τ₀ Sp) (dilationProbe τ₀ Sp))
              (((5 / 4 : ℝ) : ℂ) + t * I)) *
        (-logDeriv riemannZeta (((5 / 4 : ℝ) : ℂ) + t * I))) atTop (𝓝 0) := by
  obtain ⟨Mζ, hMζ0, hErr⟩ := exists_norm_integral_dilation_error_le hS b (c := 5 / 4)
    (by norm_num) (by norm_num)
  obtain ⟨Cg, hCg0, hCg⟩ := exists_norm_dilationProbe_le
  set CB := ∑ m ∈ S, |b m| with hCB
  set CX := ∫ u : ℝ, ‖riemannPhiKernel u‖ * Real.exp (1 * |u|) with hCX
  set E₀ := 40 * jacobiThetaTailConstant * Real.exp π / (6 * π - 6) with hE₀
  have hCB0 : 0 ≤ CB := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hCX0 : 0 ≤ CX := integral_nonneg fun _ => by positivity
  have hM : 0 ≤ jacobiThetaTailConstant := jacobiThetaTailConstant_nonneg
  have hc6 : 0 < 6 * π - 6 := by nlinarith [Real.pi_gt_three]
  have hE00 : 0 ≤ E₀ := by rw [hE₀]; positivity
  set D₀ := (2 * CX + 1) * (3 * (CX + 1) ^ 4) with hD₀
  set C₂ := CB * Mζ * D₀ * E₀ * π * (4 * Cg ^ 2 * Real.exp 2) * 2 with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  -- eventually ε ≤ 1
  have hεsmall : ∀ᶠ Sp : ℝ in atTop, E₀ * Sp ^ 6 * Real.exp (-Sp ^ 2) ≤ 1 := by
    have h1 : Tendsto (fun Sp : ℝ => E₀ * (Sp ^ 6 * Real.exp (-Sp))) atTop (𝓝 0) := by
      simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 6).const_mul E₀
    filter_upwards [h1.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      eventually_ge_atTop (1 : ℝ)] with Sp hSp h1Sp
    calc E₀ * Sp ^ 6 * Real.exp (-Sp ^ 2) ≤ E₀ * (Sp ^ 6 * Real.exp (-Sp)) := by
          rw [mul_assoc]; gcongr; nlinarith
      _ ≤ 1 := hSp
  refine squeeze_zero_norm' ?_ ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 7).const_mul C₂
    |>.congr' (Eventually.of_forall fun _ => rfl) |> fun h => by simpa using h)
  filter_upwards [hεsmall, eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (3 : ℝ)]
    with Sp hsm he h3
  have hSp0 : 0 < Sp := by linarith
  set ε := ∫ u : ℝ, ‖riemannPhiTail (Real.log Sp) u‖ * Real.exp (1 * |u|) with hε
  have hε0 : 0 ≤ ε := integral_nonneg fun _ => by positivity
  have hεb : ε ≤ E₀ * Sp ^ 6 * Real.exp (-Sp ^ 2) := tail_mass_log_le he
  have hε1 : ε ≤ 1 := hεb.trans hsm
  have hΔ : (2 * CX * ε + ε ^ 2) * (3 * (CX + ε) ^ 4) ≤ D₀ * ε := by
    have h1 : 2 * CX * ε + ε ^ 2 ≤ (2 * CX + 1) * ε := by nlinarith
    have h2 : 3 * (CX + ε) ^ 4 ≤ 3 * (CX + 1) ^ 4 := by gcongr
    calc (2 * CX * ε + ε ^ 2) * (3 * (CX + ε) ^ 4) ≤ (2 * CX + 1) * ε * (3 * (CX + 1) ^ 4) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = D₀ * ε := by rw [hD₀]; ring
  have hJ : ∀ y : ℝ, |y| ≤ 1 → ∫ x : ℝ, ‖dilationProbe τ₀ Sp x‖ ^ 2 * Real.exp (2 * y * x) ≤
      Cg ^ 2 * Real.exp (2 * (Sp + 1)) * (2 * (Sp + 1)) := by
    intro y hy
    refine (integral_norm_dilationProbe_sq_mul_exp_le hCg hSp0 y).trans ?_
    have h1 : Real.exp (2 * |y| * (Sp + 3 / 4)) ≤ Real.exp (2 * (Sp + 1)) :=
      Real.exp_le_exp.mpr (by nlinarith [abs_nonneg y])
    have h2 : 2 * (Sp + 3 / 4) ≤ 2 * (Sp + 1) := by linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (by positivity)
      (by positivity)
  have hJp := hJ (5 / 4 - 1 / 2) (by rw [abs_le]; constructor <;> norm_num)
  have hJm := hJ (1 / 2 - 5 / 4) (by rw [abs_le]; constructor <;> norm_num)
  have hmain := hErr τ₀ (Real.log Sp) Sp hSp0
  refine hmain.trans ?_
  have hexp : Real.exp (-Sp ^ 2) * Real.exp (2 * (Sp + 1)) ≤ Real.exp 2 * Real.exp (-Sp) := by
    rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
  calc CB * Mζ * ((2 * CX * ε + ε ^ 2) * (3 * (CX + ε) ^ 4)) *
        (π * ((∫ x : ℝ, ‖dilationProbe τ₀ Sp x‖ ^ 2 * Real.exp (2 * (5 / 4 - 1 / 2) * x)) +
          ∫ x : ℝ, ‖dilationProbe τ₀ Sp x‖ ^ 2 * Real.exp (2 * (1 / 2 - 5 / 4) * x)))
      ≤ CB * Mζ * (D₀ * (E₀ * Sp ^ 6 * Real.exp (-Sp ^ 2))) *
        (π * (Cg ^ 2 * Real.exp (2 * (Sp + 1)) * (2 * (Sp + 1)) +
          Cg ^ 2 * Real.exp (2 * (Sp + 1)) * (2 * (Sp + 1)))) := by
        have hΔ' := hΔ.trans (mul_le_mul_of_nonneg_left hεb (by positivity))
        have hJs : π * ((∫ x : ℝ, ‖dilationProbe τ₀ Sp x‖ ^ 2 * Real.exp (2 * (5 / 4 - 1 / 2) * x)) +
            ∫ x : ℝ, ‖dilationProbe τ₀ Sp x‖ ^ 2 * Real.exp (2 * (1 / 2 - 5 / 4) * x)) ≤
            π * (Cg ^ 2 * Real.exp (2 * (Sp + 1)) * (2 * (Sp + 1)) +
              Cg ^ 2 * Real.exp (2 * (Sp + 1)) * (2 * (Sp + 1))) := by
          gcongr
        have hJ0 : 0 ≤ π * ((∫ x : ℝ, ‖dilationProbe τ₀ Sp x‖ ^ 2 *
            Real.exp (2 * (5 / 4 - 1 / 2) * x)) +
            ∫ x : ℝ, ‖dilationProbe τ₀ Sp x‖ ^ 2 * Real.exp (2 * (1 / 2 - 5 / 4) * x)) := by
          have := Real.pi_pos
          have h1 : 0 ≤ ∫ x : ℝ, ‖dilationProbe τ₀ Sp x‖ ^ 2 * Real.exp (2 * (5 / 4 - 1 / 2) * x) :=
            integral_nonneg fun _ => by positivity
          have h2 : 0 ≤ ∫ x : ℝ, ‖dilationProbe τ₀ Sp x‖ ^ 2 * Real.exp (2 * (1 / 2 - 5 / 4) * x) :=
            integral_nonneg fun _ => by positivity
          positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left hΔ' (by positivity)) hJs hJ0 (by positivity)
    _ = CB * Mζ * D₀ * E₀ * π * (4 * Cg ^ 2) * (Sp ^ 6 * (Sp + 1)) *
        (Real.exp (-Sp ^ 2) * Real.exp (2 * (Sp + 1))) := by ring
    _ ≤ CB * Mζ * D₀ * E₀ * π * (4 * Cg ^ 2) * (Sp ^ 6 * (2 * Sp)) *
        (Real.exp 2 * Real.exp (-Sp)) := by
        gcongr; linarith
    _ = C₂ * (Sp ^ 7 * Real.exp (-Sp)) := by rw [hC₂]; ring


/-! ### The tangent criterion -/

/-- **Tangent criterion for dilated weights.**  If `Λ + Σ_{m ∈ S} b(m) Λ(·/m)` is Weil-positive, then
for every `τ₀` the bump-cube shift integrand on the critical line has nonpositive real part:
`Re [B(½+iτ₀) ξ(½+iτ₀)³ ξ̄(½+iτ₀)³ H(½+iτ₀) (−ζ'/ζ)(½+iτ₀)] ≤ 0`, in its analytic form (valid at the
zeros of `ζ` as well).  Spread radical tests concentrated at `τ₀` have energy
`−2 S Re V(τ₀) ∫|κ̂|⁴ + o(S)`. -/
theorem dilation_tangent_criterion {S : Finset ℕ} (hS : ∀ m ∈ S, 1 ≤ m) (b : ℕ → ℝ)
    (hW : WeilPositive fun n => (Λ n : ℝ) + dilatedVonMangoldt S b n) (τ₀ : ℝ) :
    (dilationShiftIntegrand S b (EF.weilTest bumpCube bumpCube)
      (((1 / 2 : ℝ) : ℂ) + τ₀ * I)).re ≤ 0 := by
  set V : ℝ → ℂ := fun t => dilationShiftIntegrand S b (EF.weilTest bumpCube bumpCube)
    (((1 / 2 : ℝ) : ℂ) + t * I) with hVdef
  have hk : ContDiff ℝ 2 (EF.weilTest bumpCube bumpCube) :=
    EF.weilTest_contDiff contDiff_bumpCube contDiff_bumpCube.continuous hasCompactSupport_bumpCube
  have hkc : HasCompactSupport (EF.weilTest bumpCube bumpCube) :=
    EF.weilTest_hasCompactSupport hasCompactSupport_bumpCube hasCompactSupport_bumpCube
  obtain ⟨KV, hKV0, hKV⟩ := exists_norm_dilationShiftIntegrand_le hS b hk hkc
    Hfn_weilTest_bumpCube_one
  have hVb : ∀ t, ‖V t‖ ≤ KV := by
    intro t
    refine (hKV (1 / 2) t le_rfl (by norm_num)).trans ?_
    have h1 : (1 + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [norm_nonneg t]) (by norm_num)
    nlinarith
  have hVc : Continuous V :=
    continuous_dilationShiftIntegrand_line b hk.continuous hkc (by norm_num)
  have hconc := tendsto_integral_probe_concentration hVc hVb τ₀
  obtain ⟨KW, hKW0, hKWb⟩ := exists_norm_W_twistTest_log_le 0 τ₀
  have herr := tendsto_dilation_error hS b τ₀
  -- the normalized energy and its limit
  set E : ℝ → ℝ := fun Sp => ∫ τ : ℝ, ‖paperFT (twistTest 0 τ₀ (Real.log Sp) Sp) τ‖ ^ 2 *
      weilAtomSymbol (fun n => (Λ n : ℝ) + dilatedVonMangoldt S b n)
        ⌊Real.exp (2 * (3 * Real.log Sp + Sp))⌋₊ (τ / (2 * π)) with hEdef
  have hEnn : ∀ᶠ Sp : ℝ in atTop, 0 ≤ E Sp / Sp := by
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with Sp hSp
    have hSp0 : 0 < Sp := lt_of_lt_of_le (Real.exp_pos 1) hSp
    have hlog : 0 ≤ Real.log Sp := Real.log_nonneg (le_trans (Real.one_le_exp (by norm_num)) hSp)
    have ha : 0 ≤ 3 * Real.log Sp + Sp := by positivity
    have hFc := contDiff_twistTest 0 τ₀ (Real.log Sp) Sp
    have hFs := tsupport_twistTest (α := 0) (τ₀ := τ₀) (R := Real.log Sp) hSp0
    have hp : paperFT (twistTest 0 τ₀ (Real.log Sp) Sp) (I / 2) = 0 := by
      rw [paperFT_twistTest_factor hSp0, paperFT_weilRadicalTest_half_I, zero_mul]
    have hm : paperFT (twistTest 0 τ₀ (Real.log Sp) Sp) (-(I / 2)) = 0 := by
      rw [paperFT_twistTest_factor hSp0, paperFT_weilRadicalTest_neg_half_I, zero_mul]
    exact div_nonneg (hW _ ha _ hFc hFs hp hm) hSp0.le
  have hEdecomp : ∀ᶠ Sp : ℝ in atTop, E Sp / Sp =
      2 * π * (zetaZeroConfig.W (twistTest 0 τ₀ (Real.log Sp) Sp)
          (twistTest 0 τ₀ (Real.log Sp) Sp)).re / Sp -
        2 * (((1 / Sp : ℝ) : ℂ) * ∫ t : ℝ, V t *
          ((‖paperFT (twistProbe τ₀ Sp) t‖ ^ 2 : ℝ) : ℂ)).re -
        2 * (∫ t : ℝ, dilationPoly S b (((5 / 4 : ℝ) : ℂ) + t * I) *
          (Hfn (EF.weilTest (twistTest 0 τ₀ (Real.log Sp) Sp) (twistTest 0 τ₀ (Real.log Sp) Sp))
              (((5 / 4 : ℝ) : ℂ) + t * I) -
            riemannPhiTransform (((5 / 4 : ℝ) : ℂ) + t * I) ^ 3 *
              xiConj (((5 / 4 : ℝ) : ℂ) + t * I) ^ 3 *
              Hfn (EF.weilTest (dilationProbe τ₀ Sp) (dilationProbe τ₀ Sp))
                (((5 / 4 : ℝ) : ℂ) + t * I)) *
          (-logDeriv riemannZeta (((5 / 4 : ℝ) : ℂ) + t * I))).re / Sp := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Sp hSp
    have hSp0 : 0 < Sp := by linarith
    have h := integral_weilAtomSymbol_dilated_twistTest hS b (c := 5 / 4) (by norm_num)
      (by norm_num) (τ₀ := τ₀) hSp
    simp only [hEdef]
    rw [h, Complex.re_ofReal_mul]
    field_simp
    ring
  -- limits of the three pieces
  have hL1 : Tendsto (fun Sp : ℝ => 2 * π * (zetaZeroConfig.W (twistTest 0 τ₀ (Real.log Sp) Sp)
      (twistTest 0 τ₀ (Real.log Sp) Sp)).re / Sp) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 9).const_mul
      (2 * π * KW)).congr' (Eventually.of_forall fun _ => rfl) |> fun h => by simpa using h)
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with Sp hSp
    have hSp0 : 0 < Sp := lt_of_lt_of_le (Real.exp_pos 1) hSp
    have hb := (hKWb Sp hSp).1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hSp0, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
      div_le_iff₀ hSp0]
    have hre := Complex.abs_re_le_norm (zetaZeroConfig.W (twistTest 0 τ₀ (Real.log Sp) Sp)
      (twistTest 0 τ₀ (Real.log Sp) Sp))
    have hπ := Real.pi_pos
    calc 2 * π * |(zetaZeroConfig.W (twistTest 0 τ₀ (Real.log Sp) Sp)
          (twistTest 0 τ₀ (Real.log Sp) Sp)).re| ≤ 2 * π * (KW * Sp ^ 10 * Real.exp (-Sp)) := by
          gcongr; exact hre.trans hb
      _ = 2 * π * KW * (Sp ^ 9 * Real.exp (-Sp)) * Sp := by ring
  have hL2 : Tendsto (fun Sp : ℝ => 2 * (((1 / Sp : ℝ) : ℂ) * ∫ t : ℝ, V t *
      ((‖paperFT (twistProbe τ₀ Sp) t‖ ^ 2 : ℝ) : ℂ)).re) atTop
      (𝓝 (2 * (V τ₀ * (probeQuartic : ℂ)).re)) :=
    ((Complex.continuous_re.tendsto _).comp hconc).const_mul 2
  have hL3 : Tendsto (fun Sp : ℝ => 2 * (∫ t : ℝ, dilationPoly S b (((5 / 4 : ℝ) : ℂ) + t * I) *
          (Hfn (EF.weilTest (twistTest 0 τ₀ (Real.log Sp) Sp) (twistTest 0 τ₀ (Real.log Sp) Sp))
              (((5 / 4 : ℝ) : ℂ) + t * I) -
            riemannPhiTransform (((5 / 4 : ℝ) : ℂ) + t * I) ^ 3 *
              xiConj (((5 / 4 : ℝ) : ℂ) + t * I) ^ 3 *
              Hfn (EF.weilTest (dilationProbe τ₀ Sp) (dilationProbe τ₀ Sp))
                (((5 / 4 : ℝ) : ℂ) + t * I)) *
          (-logDeriv riemannZeta (((5 / 4 : ℝ) : ℂ) + t * I))).re / Sp) atTop (𝓝 0) := by
    have h1 := ((Complex.continuous_re.tendsto _).comp herr).const_mul 2
    simp only [Complex.zero_re, mul_zero] at h1
    have h2 : Tendsto (fun Sp : ℝ => Sp⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have := h1.mul h2
    simp only [mul_zero] at this
    exact this.congr' (Eventually.of_forall fun Sp => by simp [div_eq_mul_inv, Function.comp])
  have hlim := (hL1.sub hL2).sub hL3
  rw [zero_sub, sub_zero] at hlim
  have hlim' := hlim.congr' (hEdecomp.mono fun Sp h => h.symm)
  have hge := ge_of_tendsto hlim' hEnn
  have hq := probeQuartic_pos
  rw [Complex.re_mul_ofReal] at hge
  nlinarith


/-! ### Residues at the critical zeros are real -/

theorem riemannZeta_not_eventually_zero {s : ℂ} (hs : s ≠ 1) :
    ¬ ∀ᶠ z in 𝓝 s, riemannZeta z = 0 := by
  intro h
  have hU : AnalyticOnNhd ℂ riemannZeta {1}ᶜ := fun z hz => analyticAt_riemannZeta_of_ne_one hz
  have hconn := (isConnected_compl_singleton_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num) (1 : ℂ)).isPreconnected
  have h2 := hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hs h
    (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
  rw [riemannZeta_two] at h2
  simp only [Pi.zero_apply, div_eq_zero_iff, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, Complex.ofReal_eq_zero, Real.pi_ne_zero, or_self] at h2

/-- On the critical line, off the zeros, the bump-cube shift integrand is
`|ξ|⁶ |ĥ|² · B (−ζ'/ζ)`. -/
theorem dilationShiftIntegrand_bumpCube_critical_eq {S : Finset ℕ} (b : ℕ → ℝ) {t : ℝ}
    (hζ : riemannZeta ((1 / 2 : ℂ) + t * I) ≠ 0) :
    dilationShiftIntegrand S b (EF.weilTest bumpCube bumpCube) (((1 / 2 : ℝ) : ℂ) + t * I) =
      ((‖riemannPhiTransform ((1 / 2 : ℂ) + t * I)‖ ^ 6 * ‖paperFT bumpCube t‖ ^ 2 : ℝ) : ℂ) *
        (dilationPoly S b ((1 / 2 : ℂ) + t * I) *
          (-logDeriv riemannZeta ((1 / 2 : ℂ) + t * I))) := by
  have hcast : (((1 / 2 : ℝ) : ℂ) + t * I) = (1 / 2 : ℂ) + t * I := by push_cast; ring
  rw [hcast]
  have hre : 0 < ((1 / 2 : ℂ) + t * I).re := by simp
  have hne1 : ((1 / 2 : ℂ) + t * I) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [dilationShiftIntegrand_eq Hfn_weilTest_bumpCube_one hre hne1 hζ]
  have hK : Hfn (EF.weilTest bumpCube bumpCube) ((1 / 2 : ℂ) + t * I) =
      ((‖paperFT bumpCube t‖ ^ 2 : ℝ) : ℂ) := by
    have hHc : Continuous bumpCube := contDiff_bumpCube.continuous
    unfold Hfn
    have hz : ((1 / 2 : ℂ) + t * I - 1 / 2) / I = (t : ℂ) := by
      have hI : (I : ℂ) ≠ 0 := I_ne_zero
      field_simp; ring
    rw [hz, EF.paperFT_weilTest hHc hHc hasCompactSupport_bumpCube hasCompactSupport_bumpCube,
      Complex.conj_ofReal, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hX := riemannPhiTransform_mul_xiConj_critical t
  calc dilationPoly S b ((1 / 2 : ℂ) + t * I) * riemannPhiTransform ((1 / 2 : ℂ) + t * I) ^ 3 *
        xiConj ((1 / 2 : ℂ) + t * I) ^ 3 * Hfn (EF.weilTest bumpCube bumpCube)
          ((1 / 2 : ℂ) + t * I) * -logDeriv riemannZeta ((1 / 2 : ℂ) + t * I)
      = dilationPoly S b ((1 / 2 : ℂ) + t * I) * (riemannPhiTransform ((1 / 2 : ℂ) + t * I) ^ 3 *
          xiConj ((1 / 2 : ℂ) + t * I) ^ 3) * Hfn (EF.weilTest bumpCube bumpCube)
          ((1 / 2 : ℂ) + t * I) * -logDeriv riemannZeta ((1 / 2 : ℂ) + t * I) := by ring
    _ = _ := by rw [hX, hK]; push_cast; ring


theorem paperFT_bumpCube_zero_ne : paperFT bumpCube 0 ≠ 0 := by
  rw [paperFT_bumpCube, paperFT_weilBumpPolarFree]
  have h := norm_paperFT_weilBumpC_ge (v := 0) (by simp)
  have hc : 0 < Real.cos (1 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
    by linarith [Real.pi_gt_three]⟩
  have hne : paperFT weilBumpC ((0 : ℝ) : ℂ) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h; linarith
  push_cast at hne
  apply pow_ne_zero
  apply mul_ne_zero _ hne
  norm_num

theorem eventually_paperFT_bumpCube_ne_zero (γ : ℝ) :
    ∀ᶠ t : ℝ in 𝓝[≠] γ, paperFT bumpCube (t : ℂ) ≠ 0 := by
  have hd : Differentiable ℂ (paperFT bumpCube) :=
    differentiable_paperFT contDiff_bumpCube.continuous hasCompactSupport_bumpCube
  rcases (hd.analyticAt (γ : ℂ)).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hA : AnalyticOnNhd ℂ (paperFT bumpCube) Set.univ := fun z _ => hd.analyticAt z
    have h0 := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ _) h (Set.mem_univ (0 : ℂ))
    exact paperFT_bumpCube_zero_ne h0
  · have hmap : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] γ) (𝓝[≠] (γ : ℂ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (Complex.continuous_ofReal.tendsto γ |>.mono_left nhdsWithin_le_nhds)
        (eventually_mem_nhdsWithin.mono fun t ht => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
          exact_mod_cast ht)
    exact hmap.eventually h


theorem riemannPhiTransform_ne_zero_of_zeta_ne_zero {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) : riemannPhiTransform s ≠ 0 := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  rw [riemannPhiTransform_eq_zeta hs hs1]
  exact mul_ne_zero (div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) two_ne_zero)
    (mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hs) hζ)

/-- **Weil positivity forces the dilation polynomial to be real at the critical zeros.**  If the
dilated weights `Λ + Σ_{m ∈ S} b(m) Λ(·/m)` are Weil-positive, then `Im B(½+iγ) = 0` at every
zero `½+iγ` of `ζ` on the critical line.  Equivalently `B(ρ) = B(1−ρ)` there: the residues of the
perturbation's Dirichlet series at the critical zeros are real.

Near such a zero of order `m`, `(t−γ) Re[B (−ζ'/ζ)](½+it) → −m Im B(½+iγ)`.  A nonzero limit makes
the real part positive on one side of `γ`, where the positive weight `|ξ|⁶ |ĥ|²` does not vanish,
and this contradicts the tangent criterion. -/
theorem dilationPoly_im_eq_zero_of_weilPositive {S : Finset ℕ} (hS : ∀ m ∈ S, 1 ≤ m)
    (b : ℕ → ℝ) (hW : WeilPositive fun n => (Λ n : ℝ) + dilatedVonMangoldt S b n) {γ : ℝ}
    (hγ : riemannZeta ((1 / 2 : ℂ) + γ * I) = 0) :
    (dilationPoly S b ((1 / 2 : ℂ) + γ * I)).im = 0 := by
  set ρ : ℂ := (1 / 2 : ℂ) + γ * I with hρ
  have hρ1 : ρ ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp [hρ] at this
  obtain ⟨m, g, hga, hg0, hfac⟩ :=
    (analyticAt_riemannZeta_of_ne_one hρ1).exists_eventuallyEq_pow_smul_nonzero_iff.mpr
      (riemannZeta_not_eventually_zero hρ1)
  simp only [smul_eq_mul] at hfac
  have hm : m ≠ 0 := by
    rintro rfl
    have h0 := hfac.self_of_nhds
    simp only [sub_self, pow_zero, one_mul] at h0
    exact hg0 (h0 ▸ hγ)
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  set L : ℝ → ℂ := fun t => (1 / 2 : ℂ) + t * I with hLdef
  have hLc : Continuous L := by fun_prop
  have hLmap : Tendsto L (𝓝[≠] γ) (𝓝[≠] ρ) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((hLc.tendsto γ).mono_left nhdsWithin_le_nhds)
      (eventually_mem_nhdsWithin.mono fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
        intro h
        have := congrArg Complex.im h
        simp [hLdef, hρ] at this
        exact ht this)
  have hgne : ∀ᶠ z in 𝓝 ρ, g z ≠ 0 := hga.continuousAt.eventually_ne hg0
  have hgd : ∀ᶠ z in 𝓝 ρ, DifferentiableAt ℂ g z :=
    hga.eventually_analyticAt.mono fun z hz => hz.differentiableAt
  have hfac' := hfac.eventually_nhds
  have hlog : ∀ᶠ z in 𝓝[≠] ρ, logDeriv riemannZeta z = ((k + 1 : ℕ) : ℂ) / (z - ρ) +
      logDeriv g z ∧ riemannZeta z ≠ 0 := by
    filter_upwards [nhdsWithin_le_nhds (hgne.and (hgd.and hfac')), self_mem_nhdsWithin]
      with z ⟨hgz, hgdz, hfz⟩ hzρ
    have hzρ' : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
    have hpow : (z - ρ) ^ (k + 1) ≠ 0 := pow_ne_zero _ hzρ'
    have hfz' : riemannZeta =ᶠ[𝓝 z] fun w => (w - ρ) ^ (k + 1) * g w := hfz
    have hζz : riemannZeta z = (z - ρ) ^ (k + 1) * g z := hfz'.eq_of_nhds
    refine ⟨?_, by rw [hζz]; exact mul_ne_zero hpow hgz⟩
    have hderiv : deriv riemannZeta z = deriv (fun w => (w - ρ) ^ (k + 1) * g w) z :=
      hfz'.deriv_eq
    have hd1 : HasDerivAt (fun w : ℂ => (w - ρ) ^ (k + 1))
        (((k + 1 : ℕ) : ℂ) * (z - ρ) ^ k) z := by
      have := (hasDerivAt_pow (k + 1) (z - ρ)).comp z ((hasDerivAt_id z).sub_const ρ)
      simpa [Function.comp_def] using this
    have hd : HasDerivAt (fun w : ℂ => (w - ρ) ^ (k + 1) * g w)
        (((k + 1 : ℕ) : ℂ) * (z - ρ) ^ k * g z + (z - ρ) ^ (k + 1) * deriv g z) z :=
      hd1.mul hgdz.hasDerivAt
    rw [logDeriv_apply, hderiv, hζz, hd.deriv, logDeriv_apply]
    field_simp
    ring
  -- the comparison function
  set Bf : ℂ → ℂ := dilationPoly S b with hBf
  have hBc : Continuous Bf := by
    rw [hBf]; unfold dilationPoly
    refine continuous_finsetSum _ fun m hm => continuous_const.mul ?_
    have hm1 := hS m hm
    have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    exact continuous_neg.const_cpow (Or.inl hmC)
  have hlgc : ContinuousAt (logDeriv g) ρ := by
    have h1 := hga.deriv.continuousAt
    have h2 := hga.continuousAt
    have : logDeriv g = fun z => deriv g z / g z := funext fun z => logDeriv_apply g z
    rw [this]
    exact h1.div h2 hg0
  set Q : ℝ → ℝ := fun t => -((k + 1 : ℕ) : ℝ) * (Bf (L t)).im -
    (t - γ) * (Bf (L t) * logDeriv g (L t)).re with hQdef
  have hQc : ContinuousAt Q γ := by
    have h1 : ContinuousAt (fun t => Bf (L t)) γ := (hBc.comp hLc).continuousAt
    have h2 : ContinuousAt (fun t => logDeriv g (L t)) γ := by
      have : L γ = ρ := rfl
      exact ContinuousAt.comp (g := logDeriv g) (f := L) (this ▸ hlgc) hLc.continuousAt
    exact ((continuous_const.continuousAt.mul (Complex.continuous_im.continuousAt.comp h1)).sub
      ((continuous_id.sub continuous_const).continuousAt.mul
        (Complex.continuous_re.continuousAt.comp (h1.mul h2))))
  have hQγ : Q γ = -((k + 1 : ℕ) : ℝ) * (Bf ρ).im := by simp [hQdef, hLdef, hρ]
  have hQlim : Tendsto Q (𝓝[≠] γ) (𝓝 (-((k + 1 : ℕ) : ℝ) * (Bf ρ).im)) :=
    hQγ ▸ hQc.tendsto.mono_left nhdsWithin_le_nhds
  -- the identity with the real part on the critical line
  have hid : ∀ᶠ t in 𝓝[≠] γ, (Bf (L t) * -logDeriv riemannZeta (L t)).re * (t - γ) = Q t ∧
      riemannZeta (L t) ≠ 0 := by
    filter_upwards [hLmap.eventually hlog, self_mem_nhdsWithin] with t ⟨hlt, hζt⟩ ht
    refine ⟨?_, hζt⟩
    have htγ : (t : ℂ) - γ ≠ 0 := by
      have : t - γ ≠ 0 := sub_ne_zero.mpr ht
      exact_mod_cast this
    have hLρ : L t - ρ = ((t : ℂ) - γ) * I := by simp [hLdef, hρ]; ring
    rw [hlt, hLρ]
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    have : Bf (L t) * -(((k + 1 : ℕ) : ℂ) / (((t : ℂ) - γ) * I) + logDeriv g (L t)) =
        (((k + 1 : ℕ) : ℂ) * I * Bf (L t) - ((t : ℂ) - γ) * (Bf (L t) * logDeriv g (L t))) /
          ((t : ℂ) - γ) := by
      field_simp
      linear_combination (-(Bf (L t) * ((k + 1 : ℕ) : ℂ))) * Complex.I_sq
    rw [this, hQdef]
    simp only
    rw [show (((((k + 1 : ℕ) : ℂ) * I * Bf (L t) - ((t : ℂ) - γ) * (Bf (L t) * logDeriv g (L t))) /
        ((t : ℂ) - γ)).re * (t - γ)) =
        ((((k + 1 : ℕ) : ℂ) * I * Bf (L t) - ((t : ℂ) - γ) * (Bf (L t) * logDeriv g (L t))) /
        ((t : ℂ) - γ) * ((t - γ : ℝ) : ℂ)).re by
      rw [Complex.re_mul_ofReal]]
    rw [show ((t - γ : ℝ) : ℂ) = (t : ℂ) - γ by push_cast; rfl, div_mul_cancel₀ _ htγ]
    simp [Complex.sub_re, Complex.mul_re]
    ring
  -- positive weights
  have hwt := eventually_paperFT_bumpCube_ne_zero γ
  have hcrit := dilation_tangent_criterion hS b hW
  -- a violation on the appropriate side
  have hviol : ∀ t : ℝ, riemannZeta (L t) ≠ 0 → paperFT bumpCube (t : ℂ) ≠ 0 →
      0 < (Bf (L t) * -logDeriv riemannZeta (L t)).re → False := by
    intro t hζt hht hpos
    have hX : riemannPhiTransform (L t) ≠ 0 :=
      riemannPhiTransform_ne_zero_of_zeta_ne_zero (by simp [hLdef]) (by
        intro h; have := congrArg Complex.re h; simp [hLdef] at this) hζt
    have heq := dilationShiftIntegrand_bumpCube_critical_eq (S := S) b (t := t) hζt
    have hc := hcrit t
    rw [heq, Complex.re_ofReal_mul] at hc
    have hw : 0 < ‖riemannPhiTransform ((1 / 2 : ℂ) + t * I)‖ ^ 6 * ‖paperFT bumpCube t‖ ^ 2 := by
      have := norm_pos_iff.mpr hX
      have := norm_pos_iff.mpr hht
      positivity
    have := mul_pos hw hpos
    linarith
  by_contra hβ
  rcases lt_or_gt_of_ne hβ with hneg | hpos
  · -- `Im B < 0`: the limit of `Q` is positive; use `t > γ`
    have hL0 : 0 < -((k + 1 : ℕ) : ℝ) * (Bf ρ).im := by
      have : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      nlinarith
    have hev : ∀ᶠ t in 𝓝[>] γ, 0 < Q t ∧ ((Bf (L t) * -logDeriv riemannZeta (L t)).re *
        (t - γ) = Q t ∧ riemannZeta (L t) ≠ 0) ∧ paperFT bumpCube (t : ℂ) ≠ 0 ∧ γ < t :=
      ((((hQlim.eventually_const_lt hL0).and hid).and hwt).filter_mono (nhdsGT_le_nhdsNE γ)).and
        self_mem_nhdsWithin |>.mono fun t ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩
    obtain ⟨t, hQt, ⟨hidt, hζt⟩, hht, htγ⟩ := hev.exists
    refine hviol t hζt hht ?_
    have htg : 0 < t - γ := sub_pos.mpr htγ
    rw [← hidt] at hQt
    exact pos_of_mul_pos_left hQt htg.le
  · -- `Im B > 0`: the limit of `Q` is negative; use `t < γ`
    have hL0 : -((k + 1 : ℕ) : ℝ) * (Bf ρ).im < 0 := by
      have : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      nlinarith
    have hev : ∀ᶠ t in 𝓝[<] γ, Q t < 0 ∧ ((Bf (L t) * -logDeriv riemannZeta (L t)).re *
        (t - γ) = Q t ∧ riemannZeta (L t) ≠ 0) ∧ paperFT bumpCube (t : ℂ) ≠ 0 ∧ t < γ :=
      ((((hQlim.eventually_lt_const hL0).and hid).and hwt).filter_mono (nhdsLT_le_nhdsNE γ)).and
        self_mem_nhdsWithin |>.mono fun t ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩
    obtain ⟨t, hQt, ⟨hidt, hζt⟩, hht, htγ⟩ := hev.exists
    refine hviol t hζt hht ?_
    have htg : t - γ < 0 := sub_neg.mpr htγ
    rw [← hidt] at hQt
    by_contra hle
    push Not at hle
    have := mul_nonneg_of_nonpos_of_nonpos hle htg.le
    linarith


/-- **A single dilation pins the critical ordinates.**  If `Λ(n) + c Λ(n/m)` (`m ≥ 2`, `c ≠ 0`) is
Weil-positive, then every zero `½+iγ` of `ζ` on the critical line has `γ log m ∈ π ℤ`: all
critical ordinates lie on the lattice `(π/log m) ℤ`. -/
theorem single_dilation_critical_ordinates {m : ℕ} (hm : 2 ≤ m) {c : ℝ} (hc : c ≠ 0)
    (hW : WeilPositive fun n => (Λ n : ℝ) + dilatedVonMangoldt {m} (fun _ => c) n) {γ : ℝ}
    (hγ : riemannZeta ((1 / 2 : ℂ) + γ * I) = 0) :
    ∃ j : ℤ, γ * Real.log m = j * Real.pi := by
  have hS : ∀ m' ∈ ({m} : Finset ℕ), 1 ≤ m' := by
    intro m' hm'; rw [Finset.mem_singleton] at hm'; omega
  have h := dilationPoly_im_eq_zero_of_weilPositive hS (fun _ => c) hW hγ
  unfold dilationPoly at h
  rw [Finset.sum_singleton, natCast_cpow_neg_eq_sqrt_mul_exp (by omega)] at h
  have hexp : -((1 / 2 : ℂ) + γ * I - 1 / 2) * Real.log m = ((-(γ * Real.log m) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [hexp, Complex.exp_mul_I] at h
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.add_im, Complex.mul_re, sub_zero] at h
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im] at h
  simp at h
  rcases h with h | h | h
  · exact absurd h hc
  · omega
  · obtain ⟨j, hj⟩ := Real.sin_eq_zero_iff.mp h
    exact ⟨j, hj.symm⟩

end RHTower

