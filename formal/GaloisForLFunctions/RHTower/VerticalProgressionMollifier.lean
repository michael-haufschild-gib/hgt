import GaloisForLFunctions.RHTower.VerticalProgressionCutoffSums
import GaloisForLFunctions.RHTower.Sieve.LinearMollifierGcdForms
import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneral
import GaloisForLFunctions.RHTower.BurnolResidueCriticalLineKernelL2

/-!
# The linear mollifier and the long smoothed Dirichlet series of `ζ`

* `linMoll N s = Σ_{h ≤ N} b_N(h) h^{−s}` with `b_N(h) = μ(h) log(N/h)/log N`;
  `|b_N(h)| ≤ 1` and `‖M_N(½ + it)‖ ≤ 2√N` (`norm_linMoll_critPt_le`).
* **Long smoothed series** (`exists_norm_zeta_sub_smoothSum_le`): on the critical line, for every
  `x > 0` and `|t| ≥ 1`,

  `‖ζ(½ + it) − Σ_n n^{−½−it} V(n/x)‖ ≤ C (1 + |t|)/x + x^{1/2} e^{1/4 − t²}`.

  This is the Gaussian smooth AFE: the dual integral on `Re w = −1` is `≪ (1 + |t|)/x` because
  `|ζ(−½ + iu)| ≪ 1 + |u|`, and the residue at `w = 1 − s` carries `e^{(½ − it)²}`.
* **Mollified coefficients** (`smoothSum_mul_linMoll`): `Σ_n n^{−s} V(n/X) · M_N(s) =
  Σ_m a(m) m^{−s}` with `a(m) = Σ_{h | m, h ≤ N} b_N(h) V((m/h)/X)`.
-/

open Complex MeasureTheory Set Filter

namespace RHTower.VerticalAP

noncomputable section

/-- The critical point `½ + it`. -/
def critPt (t : ℝ) : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I

@[simp] theorem critPt_re (t : ℝ) : (critPt t).re = 1 / 2 := by simp [critPt]

@[simp] theorem critPt_im (t : ℝ) : (critPt t).im = t := by simp [critPt]

/-- The linear mollifier `M_N(s) = Σ_{h ≤ N} b_N(h) h^{−s}`. -/
def linMoll (N : ℕ) (s : ℂ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 N, (Sieve.linearMollifierCoeff N h : ℂ) * (h : ℂ) ^ (-s)

theorem abs_linearMollifierCoeff_le_one {N h : ℕ} (hh : h ∈ Finset.Icc 1 N) :
    |Sieve.linearMollifierCoeff N h| ≤ 1 := by
  obtain ⟨h1, hN⟩ := Finset.mem_Icc.mp hh
  unfold Sieve.linearMollifierCoeff
  have hμ : |((ArithmeticFunction.moebius h : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast h1
  have hNR : (h : ℝ) ≤ N := by exact_mod_cast hN
  have hlog0 : 0 ≤ Real.log ((N : ℝ) / h) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hlogle : Real.log ((N : ℝ) / h) ≤ Real.log N := by
    rw [Real.log_div (ne_of_gt (by linarith)) (ne_of_gt (by linarith))]
    linarith [Real.log_nonneg hhR]
  rw [abs_div, abs_mul, abs_of_nonneg hlog0]
  rcases eq_or_lt_of_le (Real.log_nonneg (hhR.trans hNR)) with h0 | hpos
  · rw [← h0]; simp
  · rw [abs_of_pos hpos, div_le_one hpos]
    calc |((ArithmeticFunction.moebius h : ℤ) : ℝ)| * Real.log ((N : ℝ) / h)
        ≤ 1 * Real.log N := mul_le_mul hμ hlogle hlog0 zero_le_one
      _ = Real.log N := one_mul _

theorem sum_Icc_inv_sqrt_le (N : ℕ) :
    ∑ h ∈ Finset.Icc 1 N, ((h : ℝ) ^ (1 / 2 : ℝ))⁻¹ ≤ 2 * Real.sqrt N := by
  have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := rfl
  rw [hIcc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  refine le_trans (le_of_eq ?_) (ZetaNotch.sum_range_inv_sqrt_le N)
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Real.sqrt_eq_rpow]
  push_cast
  ring_nf

theorem norm_linMoll_critPt_le (N : ℕ) (t : ℝ) : ‖linMoll N (critPt t)‖ ≤ 2 * Real.sqrt N := by
  unfold linMoll
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun h hh => ?_).trans (sum_Icc_inv_sqrt_le N))
  have hpos : 0 < h := (Finset.mem_Icc.mp hh).1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_natCast_cpow_of_pos hpos]
  have hre : (-critPt t).re = -(1 / 2) := by simp
  rw [hre, Real.rpow_neg (Nat.cast_nonneg _)]
  calc |Sieve.linearMollifierCoeff N h| * ((h : ℝ) ^ (1 / 2 : ℝ))⁻¹
      ≤ 1 * ((h : ℝ) ^ (1 / 2 : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right (abs_linearMollifierCoeff_le_one hh) (by positivity)
    _ = ((h : ℝ) ^ (1 / 2 : ℝ))⁻¹ := one_mul _

/-! ## The long smoothed series of `ζ` on the critical line -/

/-- **Long smoothed series.** `‖ζ(½+it) − Σ n^{−½−it} V(n/x)‖ ≤ C(1+|t|)/x + x^{1/2} e^{1/4−t²}`
for `x > 0`, `|t| ≥ 1`. -/
theorem exists_norm_zeta_sub_smoothSum_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta (critPt t) -
          ∑' n : ℕ, (n + 1 : ℂ) ^ (-critPt t) * smoothAFECutoff ((n + 1 : ℝ) / x)‖ ≤
        C * (1 + |t|) / x + x ^ (1 / 2 : ℝ) * Real.exp (1 / 4 - t ^ 2) := by
  set Kζ : ℝ := GaloisForLFunctions.zetaHalfPlaneBound (3 / 2) / (2 * Real.pi) with hKζ
  have hKζ0 : 0 ≤ Kζ := by
    have := (norm_nonneg _).trans
      (GaloisForLFunctions.norm_riemannZeta_le_halfPlane (c := 3 / 2) (by norm_num)
        (z := 3 / 2) (by norm_num))
    positivity
  set G : ℝ := ∫ v : ℝ, (1 + |v|) * Real.exp (-(v ^ 2)) with hG
  have hGint : Integrable (fun v : ℝ => (1 + |v|) * Real.exp (-(v ^ 2))) := by
    simpa using ZetaNotch.integrable_one_add_abs_pow_mul_exp_neg_sq 1
  have hG0 : 0 ≤ G := integral_nonneg fun v => by positivity
  refine ⟨1 / (2 * Real.pi) * (Kζ * Real.exp 1 * G), by positivity, fun x hx t ht => ?_⟩
  have hs1 : critPt t ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; rw [this] at ht; norm_num at ht
  have hafe := riemannZeta_eq_tsum_smoothAFECutoff_sub_dual_sub_residue_general hx hs1
    (by simp) (by simp; norm_num)
  rw [hafe]
  have hrw : (∑' n : ℕ, (n + 1 : ℂ) ^ (-critPt t) * smoothAFECutoff ((n + 1 : ℝ) / x)) -
      smoothAFEZetaDualMellinGeneral (critPt t) x - smoothAFEZetaShiftedPoleResidue (critPt t) x -
      ∑' n : ℕ, (n + 1 : ℂ) ^ (-critPt t) * smoothAFECutoff ((n + 1 : ℝ) / x) =
      -(smoothAFEZetaDualMellinGeneral (critPt t) x + smoothAFEZetaShiftedPoleResidue (critPt t) x) := by
    ring
  rw [hrw, norm_neg]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · -- the dual integral on `Re w = −1`
    unfold smoothAFEZetaDualMellinGeneral
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hpt : ∀ v : ℝ, ‖smoothAFEZetaMellinIntegrand (critPt t) x (((-1 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        (Kζ * Real.exp 1 * (1 + |t|) / x) * ((1 + |v|) * Real.exp (-(v ^ 2))) := by
      intro v
      unfold smoothAFEZetaMellinIntegrand
      have hpt : critPt t + (((-1 : ℝ) : ℂ) + (v : ℂ) * I) = smoothAFEZetaLeftLinePt (t + v) := by
        unfold critPt smoothAFEZetaLeftLinePt; push_cast; ring
      rw [hpt, norm_mul, norm_mul]
      have hz := norm_riemannZeta_leftLine_le_linear (t + v)
      have hpt2 : ‖smoothAFEZetaLeftLinePt (t + v)‖ ≤ (1 + |t|) * (1 + |v|) := by
        unfold smoothAFEZetaLeftLinePt
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs]
        have := abs_add_le t v
        nlinarith [abs_nonneg t, abs_nonneg v]
      have hxw : ‖(x : ℂ) ^ (((-1 : ℝ) : ℂ) + (v : ℂ) * I)‖ = x⁻¹ := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp [Real.rpow_neg_one]
      have hK := norm_smoothAFEGaussianKernel_vertical_le_of_ne (σ := -1) (by norm_num) v
      rw [hxw]
      have hK' : ‖smoothAFEGaussianKernel (((-1 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
          Real.exp 1 * Real.exp (-(v ^ 2)) := by
        simpa using hK
      calc ‖riemannZeta (smoothAFEZetaLeftLinePt (t + v))‖ * x⁻¹ *
            ‖smoothAFEGaussianKernel (((-1 : ℝ) : ℂ) + (v : ℂ) * I)‖
          ≤ (Kζ * ((1 + |t|) * (1 + |v|))) * x⁻¹ * (Real.exp 1 * Real.exp (-(v ^ 2))) := by
            gcongr
            exact hz.trans (mul_le_mul_of_nonneg_left hpt2 hKζ0)
        _ = (Kζ * Real.exp 1 * (1 + |t|) / x) * ((1 + |v|) * Real.exp (-(v ^ 2))) := by
            field_simp
    have hI := norm_integral_le_of_norm_le (hGint.const_mul _) (Eventually.of_forall hpt)
    rw [integral_const_mul, ← hG] at hI
    calc 1 / (2 * Real.pi) * ‖∫ v : ℝ, smoothAFEZetaMellinIntegrand (critPt t) x
          (((-1 : ℝ) : ℂ) + (v : ℂ) * I)‖
        ≤ 1 / (2 * Real.pi) * ((Kζ * Real.exp 1 * (1 + |t|) / x) * G) :=
          mul_le_mul_of_nonneg_left hI (by positivity)
      _ = 1 / (2 * Real.pi) * (Kζ * Real.exp 1 * G) * (1 + |t|) / x := by ring
  · -- the residue at `w = 1 − s`
    unfold smoothAFEZetaShiftedPoleResidue
    have h1s : (1 : ℂ) - critPt t = ((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
      unfold critPt; push_cast; ring
    rw [h1s, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_exp]
    have hre1 : (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I).re = 1 / 2 := by simp
    have hre2 : ((((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) ^ (2 : ℕ)).re = 1 / 4 - t ^ 2 := by
      simp [pow_two]; ring
    rw [hre1, hre2]
    have hden : 1 ≤ ‖((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I‖ := by
      refine ht.trans ?_
      have := Complex.abs_im_le_norm (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)
      simpa [abs_neg] using this
    rw [div_le_iff₀ (by linarith)]
    calc x ^ (1 / 2 : ℝ) * Real.exp (1 / 4 - t ^ 2)
        = x ^ (1 / 2 : ℝ) * Real.exp (1 / 4 - t ^ 2) * 1 := (mul_one _).symm
      _ ≤ x ^ (1 / 2 : ℝ) * Real.exp (1 / 4 - t ^ 2) *
            ‖((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I‖ :=
          mul_le_mul_of_nonneg_left hden (by positivity)

/-! ## The mollified coefficients -/

/-- `a(m) = Σ_{h | m, h ≤ N} b_N(h) V((m/h)/X)`. -/
def mollCoeff (N : ℕ) (X : ℝ) (m : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 N,
    if h ∣ m then (Sieve.linearMollifierCoeff N h : ℂ) * smoothAFECutoff (((m / h : ℕ) : ℝ) / X)
    else 0

theorem summable_smoothSum {X : ℝ} (hX : 0 < X) {s : ℂ} (hs : 0 ≤ s.re) :
    Summable (fun n : ℕ => (n + 1 : ℂ) ^ (-s) * smoothAFECutoff ((n + 1 : ℝ) / X)) := by
  obtain ⟨K, hK, hKb⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 2) two_pos
  have hsum : Summable (fun n : ℕ => K * X ^ (2 : ℝ) * (((n : ℝ) + 1) ^ (2 : ℝ))⁻¹) := by
    have := (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)).comp_injective
      (add_left_injective 1)
    refine (this.congr fun n => ?_).mul_left (K * X ^ (2 : ℝ))
    simp
  refine hsum.of_norm_bounded fun n => ?_
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [norm_mul]
  have h1 : ‖(n + 1 : ℂ) ^ (-s)‖ ≤ 1 := by
    have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_cpow_eq_rpow_re_of_pos hn]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [n.cast_nonneg (α := ℝ)])
      (by simp; exact hs)
  have h2 := hKb (div_pos hn hX)
  have h3 : ((n + 1 : ℝ) / X) ^ (-(2 : ℝ)) = X ^ (2 : ℝ) * (((n : ℝ) + 1) ^ (2 : ℝ))⁻¹ := by
    rw [Real.rpow_neg (div_pos hn hX).le, Real.div_rpow hn.le hX.le, inv_div, div_eq_mul_inv]
  rw [h3] at h2
  calc ‖(n + 1 : ℂ) ^ (-s)‖ * ‖smoothAFECutoff ((n + 1 : ℝ) / X)‖
      ≤ 1 * (K * (X ^ (2 : ℝ) * (((n : ℝ) + 1) ^ (2 : ℝ))⁻¹)) :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = K * X ^ (2 : ℝ) * (((n : ℝ) + 1) ^ (2 : ℝ))⁻¹ := by ring

/-- **The mollified series.** `Σ_n n^{−s} V(n/X) · M_N(s) = Σ_m a(m) m^{−s}`. -/
theorem smoothSum_mul_linMoll (N : ℕ) {X : ℝ} (hX : 0 < X) {s : ℂ} (hs : 0 ≤ s.re) :
    (∑' n : ℕ, (n + 1 : ℂ) ^ (-s) * smoothAFECutoff ((n + 1 : ℝ) / X)) * linMoll N s =
      ∑' m : ℕ, mollCoeff N X (m + 1) * (m + 1 : ℂ) ^ (-s) := by
  set F : ℕ → ℕ → ℂ := fun h m =>
    if h ∣ (m + 1) then (Sieve.linearMollifierCoeff N h : ℂ) *
      smoothAFECutoff ((((m + 1) / h : ℕ) : ℝ) / X) * (m + 1 : ℂ) ^ (-s) else 0 with hF
  have hterm : ∀ h ∈ Finset.Icc 1 N,
      (Sieve.linearMollifierCoeff N h : ℂ) * (h : ℂ) ^ (-s) *
        (∑' n : ℕ, (n + 1 : ℂ) ^ (-s) * smoothAFECutoff ((n + 1 : ℝ) / X)) = ∑' m : ℕ, F h m := by
    intro h hh
    have hpos : 0 < h := (Finset.mem_Icc.mp hh).1
    set e : ℕ → ℕ := fun n => h * (n + 1) - 1 with he
    have he_inj : Function.Injective e := by
      intro a b hab
      simp only [he] at hab
      have h1 : 1 ≤ h * (a + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have h2 : 1 ≤ h * (b + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have : h * (a + 1) = h * (b + 1) := by omega
      have := Nat.eq_of_mul_eq_mul_left hpos this
      omega
    have hsupp : Function.support (F h) ⊆ Set.range e := by
      intro m hm
      have hdvd : h ∣ m + 1 := by
        by_contra hnd; exact hm (by simp [hF, hnd])
      obtain ⟨q, hq⟩ := hdvd
      have hq1 : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · rw [h0, mul_zero] at hq; omega
        · exact h0
      refine ⟨q - 1, ?_⟩
      simp only [he]
      rw [Nat.sub_add_cancel hq1, ← hq]
      omega
    rw [← he_inj.tsum_eq hsupp, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    have hdvd : h ∣ e n + 1 := by
      refine ⟨n + 1, ?_⟩
      simp only [he]
      have : 1 ≤ h * (n + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    have hen : e n + 1 = h * (n + 1) := by
      simp only [he]
      have : 1 ≤ h * (n + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    simp only [hF, if_pos hdvd]
    have hen' : ((e n : ℂ) + 1) = ((h * (n + 1) : ℕ) : ℂ) := by
      rw [← hen]; push_cast; ring
    rw [hen, Nat.mul_div_cancel_left _ hpos, hen', Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    push_cast
    ring
  have hsumF : ∀ h ∈ Finset.Icc 1 N, Summable (F h) := by
    intro h hh
    have hpos : 0 < h := (Finset.mem_Icc.mp hh).1
    obtain ⟨K, hK, hKb⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 2) two_pos
    have hsum : Summable (fun m : ℕ => K * ((h : ℝ) * X) ^ (2 : ℝ) * (((m : ℝ) + 1) ^ (2 : ℝ))⁻¹) := by
      have := (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)).comp_injective
        (add_left_injective 1)
      refine (this.congr fun n => ?_).mul_left _
      simp
    refine hsum.of_norm_bounded fun m => ?_
    by_cases hd : h ∣ m + 1
    · simp only [hF, if_pos hd]
      obtain ⟨q, hq⟩ := hd
      have hq0 : 0 < q := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · rw [h0, mul_zero] at hq; omega
        · exact h0
      rw [hq, Nat.mul_div_cancel_left _ hpos]
      have hqX : 0 < (q : ℝ) / X := div_pos (by exact_mod_cast hq0) hX
      have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hb := abs_linearMollifierCoeff_le_one hh
      have hV := hKb hqX
      have hpow : ‖(m + 1 : ℂ) ^ (-s)‖ ≤ 1 := by
        have : ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_cpow_eq_rpow_re_of_pos hm]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [m.cast_nonneg (α := ℝ)])
          (by simp; exact hs)
      have hqm : (q : ℝ) = ((m : ℝ) + 1) / h := by
        have : ((m + 1 : ℕ) : ℝ) = (h : ℝ) * q := by exact_mod_cast hq
        push_cast at this
        field_simp
        linarith
      have hVeq : ((q : ℝ) / X) ^ (-(2 : ℝ)) =
          ((h : ℝ) * X) ^ (2 : ℝ) * (((m : ℝ) + 1) ^ (2 : ℝ))⁻¹ := by
        rw [hqm, Real.rpow_neg (by positivity), Real.div_rpow (by positivity) hX.le,
          Real.div_rpow hm.le (by positivity), Real.mul_rpow (by positivity) hX.le]
        field_simp
      rw [hVeq] at hV
      calc |Sieve.linearMollifierCoeff N h| * ‖smoothAFECutoff ((q : ℝ) / X)‖ *
            ‖(m + 1 : ℂ) ^ (-s)‖
          ≤ 1 * (K * (((h : ℝ) * X) ^ (2 : ℝ) * (((m : ℝ) + 1) ^ (2 : ℝ))⁻¹)) * 1 := by
            gcongr
        _ = K * ((h : ℝ) * X) ^ (2 : ℝ) * (((m : ℝ) + 1) ^ (2 : ℝ))⁻¹ := by ring
    · simp only [hF, if_neg hd, norm_zero]
      positivity
  unfold linMoll
  rw [mul_comm, Finset.sum_mul]
  rw [Finset.sum_congr rfl hterm, ← Summable.tsum_finsetSum hsumF]
  refine tsum_congr fun m => ?_
  unfold mollCoeff
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [hF]
  split_ifs <;> simp

end

end RHTower.VerticalAP
