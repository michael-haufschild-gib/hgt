import GaloisForLFunctions.RHTower.OddSectorPoleFreeResonatorPositivity
import GaloisForLFunctions.RHTower.WeilToeplitzGenericProfile
import GaloisForLFunctions.RHTower.EvenSectorPoleFreeLogDensity

/-!
# The log-density ceiling of odd-positive weights at every pole weight

**Theorem** (`odd_log_density_le`).  If `lam` is Weil-positive at some pole weight `β` on the
autocorrelations of odd compactly supported `C²` tests, then for every `ε > 0` and all large `N`,
`Σ_{n ≥ 2, m ≥ 1, nm ≤ N} lam(n)/(nm) ≤ (1/2 + ε)(log N)²`.

Proof.  The Weil–Toeplitz bound holds for every narrow profile
(`weil_multiplicativeToeplitz_bound_of_profile`).  Take the odd profile `g_w'`, the derivative of
the corpus polar profile `g_w = ψ_w'' − ψ_w/4`, `w = 1/(N+1)`.
* Its scaling ratio is bounded: `w² ∫ g_w''² ≤ K' ∫ g_w'²` with
  `K' = (2‖ψ⁽⁴⁾‖² + ‖ψ''‖²/8)/‖ψ⁽³⁾‖²` (`sq_mul_integral_gR''_le`), because
  `∫ g_w'² = w^{−5} ∫ (ψ''' − w²ψ'/4)² ≥ w^{−5} ‖ψ'''‖²`; the cross term is `+(w²/2)‖ψ''‖²`
  by parts.
* The resonator `Σ_{m ≤ N} m^{−1/2} g_w'(· − log m + (log N)/2)` has nonnegative coefficients
  and the odd profile `g_w'`, so odd positivity at any pole weight transfers to it
  (`re_weilFullFunctional_derivTranslateSum_nonneg_of_weilPositiveOddAt`).

Row 1254 of the loop log said the odd sector cannot transfer.  That holds only for even profiles,
which need the weight `1/z²`, negative on the imaginary segment.  An odd profile carries its own
factor `z²`.  The earlier attempts with odd symmetrizations `R(x) − R(−x)` lost the ceiling to
mirror product atoms; the transfer through the odd cosine-shift measure avoids symmetrization.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.OddSector

open ResonatorProfile EvenSector

/-! ## The fourth derivative of the unit bump -/

/-- `ψ⁽⁴⁾`. -/
def resonatorD4 : ℝ → ℝ := deriv d3

theorem contDiff_resonatorD4 (n : ℕ) : ContDiff ℝ n resonatorD4 := (contDiff_d3 (n + 1)).deriv'

theorem resonatorD4_eq_zero {v : ℝ} (hv : 1 / 4 < |v|) : resonatorD4 v = 0 := by
  have hev : d3 =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
    have hopen : IsOpen {x : ℝ | 1 / 4 < |x|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds hv] with x hx
    exact d3_eq_zero hx
  unfold resonatorD4; rw [hev.deriv_eq]; simp

theorem hasCompactSupport_resonatorD4 : HasCompactSupport resonatorD4 :=
  hasCompactSupport_of_vanish fun _ h => resonatorD4_eq_zero h

/-- Integration by parts: `∫ ψ' ψ''' = −∫ (ψ'')²`. -/
theorem integral_d1_mul_d3 : ∫ v, d1 v * d3 v = -∫ v, d2 v * d2 v := by
  exact integral_mul_deriv_eq_deriv_mul_of_integrable (u := d1) (v := d2) (u' := d2) (v' := d3)
    (fun x _ => ((contDiff_d1 1).differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => ((contDiff_d2 1).differentiable (by norm_num) x).hasDerivAt)
    (((contDiff_d1 0).continuous.mul (contDiff_d3 0).continuous).integrable_of_hasCompactSupport
      hasCompactSupport_d1.mul_right)
    (((contDiff_d2 0).continuous.mul (contDiff_d2 0).continuous).integrable_of_hasCompactSupport
      hasCompactSupport_d2.mul_right)
    (((contDiff_d1 0).continuous.mul (contDiff_d2 0).continuous).integrable_of_hasCompactSupport
      hasCompactSupport_d1.mul_right)

theorem integral_d3_sq_pos : 0 < ∫ v, d3 v ^ 2 := by
  have hc : Continuous fun v => d3 v ^ 2 := (contDiff_d3 0).continuous.pow 2
  by_contra hle
  push Not at hle
  have hnn : ∀ v, 0 ≤ d3 v ^ 2 := fun v => sq_nonneg _
  have hint : Integrable fun v => d3 v ^ 2 :=
    hc.integrable_of_hasCompactSupport
      (hasCompactSupport_d3.comp_left (g := fun x : ℝ => x ^ 2) (by simp))
  have hzero : ∫ v, d3 v ^ 2 = 0 := le_antisymm hle (integral_nonneg hnn)
  have hae := (integral_eq_zero_iff_of_nonneg hnn hint).mp hzero
  have hall : ∀ v, d3 v ^ 2 = 0 := by
    intro v
    exact congrFun (hc.ae_eq_iff_eq volume continuous_const |>.mp hae) v
  have hd3 : ∀ v, d3 v = 0 := fun v => pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (hall v)
  have hd2c : ∀ x y, d2 x = d2 y := fun x y =>
    is_const_of_deriv_eq_zero ((contDiff_d2 1).differentiable (by norm_num)) (fun v => hd3 v) x y
  have hd2 : ∀ v, d2 v = 0 := fun v => by rw [hd2c v 1]; exact d2_eq_zero (by norm_num)
  have hd1c : ∀ x y, d1 x = d1 y := fun x y =>
    is_const_of_deriv_eq_zero ((contDiff_d1 1).differentiable (by norm_num)) (fun v => hd2 v) x y
  have hd1 : ∀ v, d1 v = 0 := fun v => by rw [hd1c v 1]; exact d1_eq_zero (by norm_num)
  have hΨc : ∀ x y, Ψ x = Ψ y := fun x y =>
    is_const_of_deriv_eq_zero ((contDiff_Ψ 1).differentiable (by norm_num)) (fun v => hd1 v) x y
  have h1 := hΨc 0 1
  rw [Ψ_zero, Ψ_eq_zero (by norm_num)] at h1
  norm_num at h1

/-! ## The odd profile `g_w'` and its derivative -/

/-- `g_w'' (u) = ψ⁽⁴⁾(u/w)/w⁴ − ψ''(u/w)/(4w²)`. -/
def gR'' (w u : ℝ) : ℝ := resonatorD4 (u / w) / w ^ 4 - d2 (u / w) / (4 * w ^ 2)

theorem hasDerivAt_gR' (w u : ℝ) : HasDerivAt (gR' w) (gR'' w u) u := by
  have h3 := hasDerivAt_comp_div (F := d3) ((contDiff_d3 1).differentiable (by norm_num)) w u
  have h1 := hasDerivAt_comp_div (F := d1) ((contDiff_d1 1).differentiable (by norm_num)) w u
  have h : HasDerivAt (gR' w) _ u := (h3.div_const (w ^ 3)).sub (h1.div_const (4 * w))
  refine h.congr_deriv ?_
  have hd4 : deriv d3 (u / w) = resonatorD4 (u / w) := rfl
  have hd2 : deriv d1 (u / w) = d2 (u / w) := rfl
  rw [hd4, hd2]
  unfold gR''
  by_cases hw : w = 0
  · subst hw; simp
  · field_simp

theorem deriv_gR' (w : ℝ) : deriv (gR' w) = gR'' w := funext fun u => (hasDerivAt_gR' w u).deriv

theorem deriv_gR (w : ℝ) : deriv (gR w) = gR' w := funext fun u => (hasDerivAt_gR w u).deriv

theorem gR'_neg_eq (w u : ℝ) : gR' w (-u) = -gR' w u := by
  have h1 := deriv_comp_neg (gR w) u
  have e : (fun x => gR w (-x)) = gR w := funext fun x => gR_neg w x
  rw [e, deriv_gR] at h1
  linarith

theorem integral_gR'_sq_ge {w : ℝ} (hw : 0 < w) :
    (∫ v, d3 v ^ 2) / w ^ 5 ≤ ∫ u, gR' w u ^ 2 := by
  set ε := w ^ 2 / 4 with hε
  have hpt : ∀ u, gR' w u ^ 2 = (d3 (u / w) - ε * d1 (u / w)) ^ 2 / w ^ 6 := by
    intro u; simp only [gR', hε]; field_simp
  have hc3 := (contDiff_d3 0).continuous
  have hc1 := (contDiff_d1 0).continuous
  have i33 : Integrable fun v => d3 v ^ 2 :=
    integrable_of_cs (hc3.pow 2)
      (hasCompactSupport_d3.comp_left (g := fun x : ℝ => x ^ 2) (by simp))
  have i31 : Integrable fun v => d3 v * d1 v :=
    integrable_of_cs (hc3.mul hc1) hasCompactSupport_d1.mul_left
  have i11 : Integrable fun v => d1 v ^ 2 :=
    integrable_of_cs (hc1.pow 2)
      (hasCompactSupport_d1.comp_left (g := fun x : ℝ => x ^ 2) (by simp))
  have hexp : ∫ v, (d3 v - ε * d1 v) ^ 2 =
      (∫ v, d3 v ^ 2) + 2 * ε * (∫ v, d2 v * d2 v) + ε ^ 2 * ∫ v, d1 v ^ 2 := by
    have e : (fun v => (d3 v - ε * d1 v) ^ 2) =
        fun v => d3 v ^ 2 - 2 * ε * (d3 v * d1 v) + ε ^ 2 * d1 v ^ 2 := by funext v; ring
    have e31 : ∫ v, d3 v * d1 v = -∫ v, d2 v * d2 v := by
      rw [← integral_d1_mul_d3]; congr 1; funext v; ring
    rw [e, integral_add (f := fun v => d3 v ^ 2 - 2 * ε * (d3 v * d1 v))
      (g := fun v => ε ^ 2 * d1 v ^ 2) (i33.sub (i31.const_mul _)) (i11.const_mul _),
      integral_sub (f := fun v => d3 v ^ 2) (g := fun v => 2 * ε * (d3 v * d1 v)) i33
        (i31.const_mul _), integral_const_mul, integral_const_mul, e31]
    ring
  have hnn2 : 0 ≤ ∫ v, d2 v * d2 v := integral_nonneg fun v => mul_self_nonneg _
  have hnn1 : 0 ≤ ∫ v, d1 v ^ 2 := integral_nonneg fun v => sq_nonneg _
  have hεpos : 0 ≤ ε := by positivity
  have hscale : ∫ u, gR' w u ^ 2 = w * (∫ v, (d3 v - ε * d1 v) ^ 2) / w ^ 6 := by
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_div]
    rw [integral_sq_comp_div (fun v => d3 v - ε * d1 v) hw]
  rw [hscale, hexp]
  have hw6 : (0 : ℝ) < w ^ 6 := by positivity
  have hw5 : (0 : ℝ) < w ^ 5 := by positivity
  rw [div_le_div_iff₀ hw5 hw6]
  have h0 : 0 ≤ 2 * ε * (∫ v, d2 v * d2 v) + ε ^ 2 * ∫ v, d1 v ^ 2 := by positivity
  have : w * ((∫ v, d3 v ^ 2) + 2 * ε * (∫ v, d2 v * d2 v) + ε ^ 2 * ∫ v, d1 v ^ 2) * w ^ 5 =
      (∫ v, d3 v ^ 2) * w ^ 6 + (2 * ε * (∫ v, d2 v * d2 v) + ε ^ 2 * ∫ v, d1 v ^ 2) * w ^ 6 := by
    ring
  rw [this]
  nlinarith

theorem integral_gR''_sq_le {w : ℝ} (hw : 0 < w) :
    ∫ u, gR'' w u ^ 2 ≤ 2 * (∫ v, resonatorD4 v ^ 2) / w ^ 7 + (∫ v, d2 v ^ 2) / (8 * w ^ 3) := by
  have hc4 := (contDiff_resonatorD4 0).continuous
  have hc2 := (contDiff_d2 0).continuous
  have i44 : Integrable fun v => resonatorD4 v ^ 2 :=
    integrable_of_cs (hc4.pow 2)
      (hasCompactSupport_resonatorD4.comp_left (g := fun x : ℝ => x ^ 2) (by simp))
  have i22 : Integrable fun v => d2 v ^ 2 :=
    integrable_of_cs (hc2.pow 2)
      (hasCompactSupport_d2.comp_left (g := fun x : ℝ => x ^ 2) (by simp))
  have hle : ∀ u, gR'' w u ^ 2 ≤
      2 / w ^ 8 * resonatorD4 (u / w) ^ 2 + 1 / (8 * w ^ 4) * d2 (u / w) ^ 2 := by
    intro u
    unfold gR''
    have hw4 : (0 : ℝ) < w ^ 4 := by positivity
    set a := resonatorD4 (u / w); set b := d2 (u / w)
    have : (a / w ^ 4 - b / (4 * w ^ 2)) ^ 2 ≤ 2 * (a / w ^ 4) ^ 2 + 2 * (b / (4 * w ^ 2)) ^ 2 := by
      nlinarith [sq_nonneg (a / w ^ 4 + b / (4 * w ^ 2))]
    calc (a / w ^ 4 - b / (4 * w ^ 2)) ^ 2
        ≤ 2 * (a / w ^ 4) ^ 2 + 2 * (b / (4 * w ^ 2)) ^ 2 := this
      _ = 2 / w ^ 8 * a ^ 2 + 1 / (8 * w ^ 4) * b ^ 2 := by field_simp; ring
  have j4 : Integrable fun u => resonatorD4 (u / w) ^ 2 := by
    have := (i44.comp_div (ne_of_gt hw)); simpa using this
  have j2 : Integrable fun u => d2 (u / w) ^ 2 := by
    have := (i22.comp_div (ne_of_gt hw)); simpa using this
  have hcont : Continuous (gR'' w) := by
    unfold gR''
    exact ((hc4.comp (continuous_id.div_const w)).div_const _).sub
      ((hc2.comp (continuous_id.div_const w)).div_const _)
  have hint : Integrable fun u => gR'' w u ^ 2 :=
    integrable_of_cs (hcont.pow 2)
      (hasCompactSupport_of_support_subset_abs (Λ := w / 4) fun u hu => by
        by_contra h; push Not at h
        have hv : 1 / 4 < |u / w| := abs_div_gt hw h
        exact hu (by simp [gR'', resonatorD4_eq_zero hv, d2_eq_zero hv]))
  calc ∫ u, gR'' w u ^ 2
      ≤ ∫ u, (2 / w ^ 8 * resonatorD4 (u / w) ^ 2 + 1 / (8 * w ^ 4) * d2 (u / w) ^ 2) :=
        integral_mono hint ((j4.const_mul _).add (j2.const_mul _)) hle
    _ = 2 / w ^ 8 * (w * ∫ v, resonatorD4 v ^ 2) + 1 / (8 * w ^ 4) * (w * ∫ v, d2 v ^ 2) := by
        rw [integral_add (j4.const_mul _) (j2.const_mul _), integral_const_mul,
          integral_const_mul, integral_sq_comp_div resonatorD4 hw, integral_sq_comp_div d2 hw]
    _ = 2 * (∫ v, resonatorD4 v ^ 2) / w ^ 7 + (∫ v, d2 v ^ 2) / (8 * w ^ 3) := by field_simp

/-- The odd profile constant `K' = (2‖ψ⁽⁴⁾‖² + ‖ψ''‖²/8)/‖ψ⁽³⁾‖²`. -/
def oddProfileRatio : ℝ := (2 * (∫ v, resonatorD4 v ^ 2) + (∫ v, d2 v ^ 2) / 8) / ∫ v, d3 v ^ 2

/-- **Scaling law for the odd profile.**  For `0 < w ≤ 1`: `w² ∫ (g_w'')² ≤ K' ∫ (g_w')²`. -/
theorem sq_mul_integral_gR''_le {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    w ^ 2 * ∫ u, gR'' w u ^ 2 ≤ oddProfileRatio * ∫ u, gR' w u ^ 2 := by
  have hup := integral_gR''_sq_le hw
  have hlo := integral_gR'_sq_ge hw
  have hpos := integral_d3_sq_pos
  have h4 : 0 ≤ ∫ v, resonatorD4 v ^ 2 := integral_nonneg fun v => sq_nonneg _
  have h2 : 0 ≤ ∫ v, d2 v ^ 2 := integral_nonneg fun v => sq_nonneg _
  have hw5 : 0 < w ^ 5 := by positivity
  have step1 : w ^ 2 * ∫ u, gR'' w u ^ 2 ≤
      (2 * (∫ v, resonatorD4 v ^ 2) + (∫ v, d2 v ^ 2) / 8) / w ^ 5 := by
    calc w ^ 2 * ∫ u, gR'' w u ^ 2
        ≤ w ^ 2 * (2 * (∫ v, resonatorD4 v ^ 2) / w ^ 7 + (∫ v, d2 v ^ 2) / (8 * w ^ 3)) :=
          mul_le_mul_of_nonneg_left hup (by positivity)
      _ = 2 * (∫ v, resonatorD4 v ^ 2) / w ^ 5 + ((∫ v, d2 v ^ 2) / 8) / w := by
          field_simp
      _ ≤ (2 * (∫ v, resonatorD4 v ^ 2) + (∫ v, d2 v ^ 2) / 8) / w ^ 5 := by
          rw [add_div]
          have hw51 : w ^ 5 ≤ w := by
            calc w ^ 5 = w * w ^ 4 := by ring
              _ ≤ w * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hw.le hw1) hw.le
              _ = w := mul_one w
          have : ((∫ v, d2 v ^ 2) / 8) / w ≤ ((∫ v, d2 v ^ 2) / 8) / w ^ 5 :=
            div_le_div_of_nonneg_left (by positivity) hw5 hw51
          linarith
  have step2 : (2 * (∫ v, resonatorD4 v ^ 2) + (∫ v, d2 v ^ 2) / 8) / w ^ 5 ≤
      oddProfileRatio * ∫ u, gR' w u ^ 2 := by
    unfold oddProfileRatio
    calc (2 * (∫ v, resonatorD4 v ^ 2) + (∫ v, d2 v ^ 2) / 8) / w ^ 5
        = (2 * (∫ v, resonatorD4 v ^ 2) + (∫ v, d2 v ^ 2) / 8) / (∫ v, d3 v ^ 2) *
            ((∫ v, d3 v ^ 2) / w ^ 5) := by
          field_simp
      _ ≤ (2 * (∫ v, resonatorD4 v ^ 2) + (∫ v, d2 v ^ 2) / 8) / (∫ v, d3 v ^ 2) *
            ∫ u, gR' w u ^ 2 :=
          mul_le_mul_of_nonneg_left hlo (by positivity)
  exact step1.trans step2

/-! ## The odd unit resonator -/

theorem gR'_eq_zero' {w u : ℝ} (hw : 0 < w) (hu : w / 4 < |u|) : gR' w u = 0 :=
  gR'_eq_zero hw hu

theorem profileResonator_unitResonatorCoeff (N : ℕ) (w : ℝ) :
    profileResonator N (unitResonatorCoeff N) (gR' w) =
      fun u =>
        ((∑ m ∈ Finset.Icc 1 N, 1 / Real.sqrt m * deriv (gR w) (u - resPt N m) : ℝ) : ℂ) := by
  funext u
  unfold profileResonator
  rw [Complex.ofReal_sum, deriv_gR]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [unitResonatorCoeff, if_pos (Finset.mem_Icc.mp hm).2, Complex.ofReal_mul]

theorem paperFT_profileResonator_gR'_pole (N : ℕ) (c : ℕ → ℂ) {w : ℝ} (hw : 0 < w) :
    paperFT (profileResonator N c (gR' w)) (I / 2) = 0 ∧
      paperFT (profileResonator N c (gR' w)) (-(I / 2)) = 0 := by
  have hg2 : ContDiff ℝ 2 (gR w) := contDiff_gR w 2
  have hgc : HasCompactSupport (gR w) :=
    (hasCompactSupport_comp_left (g := Complex.ofReal) fun {_} => Complex.ofReal_eq_zero).mp
      (hasCompactSupport_gC hw)
  have hd2 : ContDiff ℝ 2 (gR' w) := contDiff_gR' w 2
  have hdcc : HasCompactSupport fun u => ((gR' w u : ℝ) : ℂ) := by
    rw [← deriv_gR]; exact hgc.deriv.comp_left Complex.ofReal_zero
  have hft : ∀ z, paperFT (profileResonator N c (gR' w)) z =
      (∑ m ∈ Finset.Icc 1 N, c m * cexp (I * z * resPt N m)) *
        oddLift (paperFT fun u => ((gR w u : ℝ) : ℂ)) z := by
    intro z
    have h1 := paperFT_sum_translate (Finset.Icc 1 N) c (resPt N)
      (Complex.continuous_ofReal.comp hd2.continuous) hdcc z
    rw [← paperFT_ofReal_deriv hg2 hgc, deriv_gR]
    exact h1
  obtain ⟨hp1, hp2⟩ := paperFT_gC_pole hw
  have e1 : paperFT (fun u => ((gR w u : ℝ) : ℂ)) (I / 2) = 0 := hp1
  have e2 : paperFT (fun u => ((gR w u : ℝ) : ℂ)) (-(I / 2)) = 0 := hp2
  constructor
  · rw [hft]; simp [oddLift, e1]
  · rw [hft]; simp [oddLift, e2]

/-- **Odd positivity at any pole weight gives the Toeplitz hypothesis on the odd unit
resonator.** -/
theorem integral_weilAtomSymbol_oddUnitResonator_nonneg {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveOddAt β lam) (N : ℕ) :
    0 ≤ ∫ τ : ℝ, ‖paperFT (profileResonator N (unitResonatorCoeff N)
        (gR' (1 / ((N : ℝ) + 1)))) τ‖ ^ 2 *
      weilAtomSymbol lam ⌊Real.exp (2 * (Real.log N / 2 + 1 / ((N : ℝ) + 1) / 4))⌋₊
        (τ / (2 * π)) := by
  have hw : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  obtain ⟨hp1, hp2⟩ := paperFT_profileResonator_gR'_pole N (unitResonatorCoeff N) hw
  have ha : 0 ≤ Real.log N / 2 + 1 / ((N : ℝ) + 1) / 4 := by
    have := Real.log_natCast_nonneg N
    positivity
  have hd : ContDiff ℝ 2 (profileResonator N (unitResonatorCoeff N) (gR' (1 / ((N : ℝ) + 1)))) :=
    contDiff_profileResonator N _ (contDiff_gR' _ 2)
  refine integral_weilAtomSymbol_nonneg_of_polar ha hd
    (tsupport_subset_of_vanish fun u hu => sum_translates_eq_zero
      (h := fun v => ((gR' (1 / ((N : ℝ) + 1)) v : ℝ) : ℂ))
      (fun v hv => by
        show ((gR' (1 / ((N : ℝ) + 1)) v : ℝ) : ℂ) = 0
        rw [gR'_eq_zero hw hv, Complex.ofReal_zero]) hu) hp1 hp2 ?_
  have hgc : HasCompactSupport (gR (1 / ((N : ℝ) + 1))) :=
    (hasCompactSupport_comp_left (g := Complex.ofReal) fun {_} => Complex.ofReal_eq_zero).mp
      (hasCompactSupport_gC hw)
  rw [profileResonator_unitResonatorCoeff]
  exact re_weilFullFunctional_derivTranslateSum_nonneg_of_weilPositiveOddAt h (Finset.Icc 1 N)
    (c := fun m => 1 / Real.sqrt m) (fun m _ => by positivity) (resPt N)
    (contDiff_gR _ 3) hgc (gR_neg _) (paperFT_gC_pole hw).1

/-- **The unit Weil–Toeplitz bound for odd-positive weights.**  For every `N ≥ 1`,
`2 Σ_{n ≥ 2, m ≥ 1, nm ≤ N} lam(n)/(nm) ≤ (log N + C₀') Σ_{m ≤ N} 1/m`. -/
theorem odd_unit_toeplitz_bound {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam) {N : ℕ}
    (hN : 1 ≤ N) :
    2 * ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
        (if n * m ≤ N then lam n / (n * m) else 0) ≤
      (Real.log N + (Real.log 2 + 9 / 2 + oddProfileRatio / 2)) *
        ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m := by
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hw : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  have hw1 : 1 / ((N : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hN1]; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
  have hc : ∀ m, N < m → unitResonatorCoeff N m = 0 := fun m hm => by
    simp [unitResonatorCoeff, not_le.mpr hm]
  have hq0 : 0 < ∫ u, gR' (1 / ((N : ℝ) + 1)) u ^ 2 :=
    lt_of_lt_of_le (div_pos integral_d3_sq_pos (by positivity)) (integral_gR'_sq_ge hw)
  have hK : (1 / ((N : ℝ) + 1)) ^ 2 * ∫ u, deriv (gR' (1 / ((N : ℝ) + 1))) u ^ 2 ≤
      oddProfileRatio * ∫ u, gR' (1 / ((N : ℝ) + 1)) u ^ 2 := by
    rw [deriv_gR']; exact sq_mul_integral_gR''_le hw hw1
  have hb := weil_multiplicativeToeplitz_bound_of_profile hN (unitResonatorCoeff N) hc
    (contDiff_gR' _ 3) (fun u hu => gR'_eq_zero hw hu) hq0 hK
    (integral_weilAtomSymbol_oddUnitResonator_nonneg h N)
  have hlhs : ∀ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
      (∑ m ∈ Finset.Icc 1 N, unitResonatorCoeff N (n * m) * conj (unitResonatorCoeff N m)).re =
      ∑ m ∈ Finset.Icc 1 N, (if n * m ≤ N then lam n / (n * m) else 0) := by
    intro n hn
    have hn1 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.mp hn).1; exact_mod_cast (show 0 < n by omega)
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    by_cases hnm : n * m ≤ N
    · rw [if_pos hnm]
      simp only [unitResonatorCoeff, if_pos hnm, if_pos hmN, Complex.conj_ofReal,
        ← Complex.ofReal_mul, Complex.ofReal_re]
      have hsq : Real.sqrt ((n * m : ℕ) : ℝ) = Real.sqrt n * Real.sqrt m := by
        push_cast; exact Real.sqrt_mul hn1.le _
      rw [hsq]
      have hsm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
      have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn1.le
      have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn1
      have hsm0 : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
      calc lam n / Real.sqrt n * (1 / (Real.sqrt n * Real.sqrt m) * (1 / Real.sqrt m))
          = lam n / ((Real.sqrt n * Real.sqrt n) * (Real.sqrt m * Real.sqrt m)) := by
            field_simp
        _ = lam n / (n * m) := by rw [hsn, hsm]
    · rw [if_neg hnm]
      simp [unitResonatorCoeff, if_neg hnm]
  have hrhs : ∑ m ∈ Finset.Icc 1 N, ‖unitResonatorCoeff N m‖ ^ 2 =
      ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    simp only [unitResonatorCoeff, if_pos hmN, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity), div_pow, one_pow, Real.sq_sqrt hm0.le]
  rw [Finset.sum_congr rfl hlhs, hrhs] at hb
  exact hb

/-- **The odd log-density ceiling at every pole weight.**  Weights that are Weil-positive at some
pole weight `β` on all odd tests satisfy `Σ_{n ≥ 2, m ≥ 1, nm ≤ N} lam(n)/(nm) ≤ (1/2 + ε)(log N)²`
for all large `N`. -/
theorem odd_log_density_le {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
          (if n * m ≤ N then lam n / (n * m) else 0) ≤ (1 / 2 + ε) * Real.log N ^ 2 := by
  set C₀ : ℝ := Real.log 2 + 9 / 2 + oddProfileRatio / 2 with hC₀
  set L₀ : ℝ := 2 * (|C₀| + 1) / ε + |C₀| + 1 with hL₀
  refine ⟨⌈Real.exp L₀⌉₊ + 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : L₀ ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNr]
    have h1 : Real.exp L₀ ≤ ⌈Real.exp L₀⌉₊ := Nat.le_ceil _
    have h2 : (⌈Real.exp L₀⌉₊ : ℝ) ≤ N := by exact_mod_cast (show ⌈Real.exp L₀⌉₊ ≤ N by omega)
    linarith
  have hq0 : 0 ≤ 2 * (|C₀| + 1) / ε := by positivity
  have hL1 : 1 ≤ L₀ := by rw [hL₀]; linarith [abs_nonneg C₀]
  set L := Real.log N with hLdef
  have hχ := odd_unit_toeplitz_bound h hN1
  have hH := sum_Icc_inv_le_one_add_log N
  have hLC : 0 ≤ L + C₀ := by
    have h1 : |C₀| + 1 ≤ L₀ := by rw [hL₀]; linarith
    linarith [neg_abs_le C₀]
  have hstep : 2 * ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
      (if n * m ≤ N then lam n / (n * m) else 0) ≤ (L + C₀) * (1 + L) :=
    hχ.trans (mul_le_mul_of_nonneg_left hH hLC)
  have hquad : (L + C₀) * (1 + L) ≤ (1 + 2 * ε) * L ^ 2 := by
    have hLpos : 1 ≤ L := hL1.trans hlog
    have hdiv : 2 * (|C₀| + 1) / ε ≤ L := by rw [hL₀] at hlog; linarith [abs_nonneg C₀]
    have hbig : 2 * (|C₀| + 1) ≤ L * ε := (div_le_iff₀ hε).mp hdiv
    have hC : C₀ ≤ |C₀| := le_abs_self C₀
    have h1 : (L + C₀) * (1 + L) ≤ L ^ 2 + 2 * (|C₀| + 1) * L := by nlinarith [abs_nonneg C₀]
    have h2 : 2 * (|C₀| + 1) * L ≤ ε * L ^ 2 := by nlinarith
    nlinarith
  linarith

end RHTower.OddSector

end
