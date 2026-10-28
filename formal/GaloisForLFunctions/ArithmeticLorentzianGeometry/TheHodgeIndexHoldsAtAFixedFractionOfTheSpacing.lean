import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheAtomicFormIsMetzlerBelowTheSpacing
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheStabilityLawAtTheSpacingScale

/-!
# The Hodge index holds at a fixed fraction of the spacing

The Euler-gauge atomic intersection form of `ζ` — pole plane `H, V`, pole row
`(∫ g_n e^{−u/2}, ∫ g_n e^{u/2})`, atom block `−M(g_m, g_n)` — has the Hodge index iff Weil's form
is nonnegative on every signed atomic test (`atomicIntersectionGram_isHyperbolic_iff`). This file
proves it at every width `w ≤ c★δ_N`, a fixed fraction of the spacing, uniformly in `N`.

* **The tilted margin** (`atomMargin`, `atomMargin_mul_le_levy_sub`): the row-by-row estimate of the
  stability law at the spacing scale (SpacingScaleHarmonicAnalysis) bounds the Markov form below by
  `‖g‖² Σ_m μ_m x_m²` with the per-atom margin
  `μ_m = 2θ′(0) + log(1/w) − cross_m − (log N + 2(log 4 + 4) − (m/4N) log m)`.
* **The margin grows along the pole** (`one_add_le_atomMargin`): at `w ≤ c★δ_N`, using the tilted
  saving at width `2w` against the archimedean cross row, `μ_m ≥ 1 + (m/8N) log m`. The top atoms,
  which carry the moment `B = ∫ f e^{u/2}`, have margin `≍ log N`.
* **The pole is paid** (`sq_mul_poleMoments_le`): by weighted Cauchy–Schwarz,
  `A² ≤ X ‖g‖₁² Σ 1/(mμ_m)` and `B² ≤ X e^w ‖g‖₁² Σ m/μ_m` with `X = Σ μ_m x_m²`; the sums are at most
  `1 + log N` and `16N²/(1 + log N)` (`mul_one_add_log_le`), so `A²B² ≤ 16e^w(wN)²‖g‖⁴X²`, and
  `2|AB| ≤ ‖g‖²X` at `wN ≤ c★`.
* **Weil positivity at a fixed fraction of the spacing** (`weilQuad_atomicTest_nonneg`): `Q(f) ≥ 0`
  for every real coefficient vector, at every `N`. The same holds for every completely multiplicative
  sign twin (`twin_markov_add_pole_nonneg`).
* **The Lorentzian structure of `ζ` at the spacing scale** (`atomicIntersectionGram_isHyperbolic`,
  `weightedTrickleDown_atomicIntersectionGram`, `hasHyperbolicLinks_atomicIntersectionGram`): for a
  nonnegative nonzero bump the atomic intersection form is a connected Metzler form in the
  trickle-down regime with one positive square, satisfying `(TD_π)`, with hyperbolic links.

This is the programme's central conjecture for `ζ` in the whole stability regime `K ≤ c★`, pole
plane included, uniformly in `N`. A uniform margin cannot pay the pole at a fixed ratio
(`TheUniformMarginPaysThePoleOnlyUpToARootLogarithm`); the tilted margin can, because it grows exactly
along the pole direction `(n^{1/2})`. The statement is twist-blind: the trickle-down regime
`c★ < K` is untouched.
-/

noncomputable section

open MeasureTheory Set Finset Matrix RHTower
open scoped Real

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics

variable {g : ℝ → ℝ} {w : ℝ}

/-! ### Elementary moment bounds -/

/-- **`L¹` against `L²` on `[0, w]`**: `(∫ |g|)² ≤ w ∫ g²` for `g` vanishing off `[0, w]`. -/
theorem sq_integral_abs_le (hg : Continuous g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hw : 0 < w) : (∫ u, |g u|) ^ 2 ≤ w * ∫ u, g u ^ 2 := by
  have e1 : ∫ u, |g u| = ∫ u in Set.Icc 0 w, |g u| :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by simp [hgsupp u hu]).symm
  have e2 : ∫ u, g u ^ 2 = ∫ u in Set.Icc 0 w, g u ^ 2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by simp [hgsupp u hu]).symm
  have hvol : (volume (Set.Icc (0 : ℝ) w)).toReal = w := by
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring
  set I := ∫ u in Set.Icc 0 w, |g u|
  set S := ∫ u in Set.Icc 0 w, g u ^ 2
  set c := I / w
  have i1 : IntegrableOn (fun u => g u ^ 2) (Set.Icc 0 w) := (hg.pow 2).integrableOn_Icc
  have i2 : IntegrableOn (fun u => 2 * c * |g u|) (Set.Icc 0 w) :=
    (continuous_const.mul hg.abs).integrableOn_Icc
  have i3 : IntegrableOn (fun _ : ℝ => c ^ 2) (Set.Icc 0 w) := integrableOn_const (by simp)
  -- `0 ≤ ∫_{[0,w]} (|g| − c)² = S − 2cI + c²w`
  have hnn : 0 ≤ ∫ u in Set.Icc 0 w, (|g u| - c) ^ 2 := setIntegral_nonneg measurableSet_Icc
    fun u _ => sq_nonneg _
  have hexp : ∫ u in Set.Icc 0 w, (|g u| - c) ^ 2 = S - 2 * c * I + c ^ 2 * w := by
    have hpt : ∀ u, (|g u| - c) ^ 2 = g u ^ 2 - 2 * c * |g u| + c ^ 2 := fun u => by
      rw [sub_sq, sq_abs]; ring
    have i12 : IntegrableOn (fun u => g u ^ 2 - 2 * c * |g u|) (Set.Icc 0 w) := i1.sub i2
    simp_rw [hpt]
    rw [integral_add i12 i3, integral_sub i1 i2, integral_const_mul, setIntegral_const,
      smul_eq_mul, Measure.real, hvol]
    ring
  rw [e1, e2]
  rw [hexp] at hnn
  have hc : c * w = I := by simp only [c]; field_simp
  nlinarith

/-- A bump translated to `c`, integrated against `φ` bounded by `M` on `[c, c + w]`. -/
theorem abs_integral_shift_mul_le (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {φ : ℝ → ℝ} (hφ : Continuous φ) {c M : ℝ}
    (hM : ∀ u ∈ Set.Icc c (c + w), |φ u| ≤ M) :
    |∫ u, g (u - c) * φ u| ≤ M * ∫ u, |g u| := by
  have hgcs : HasCompactSupport fun u => g (u - c) := hgc.comp_homeomorph (Homeomorph.subRight c)
  have hgc' : Continuous fun u => g (u - c) := hg.comp (continuous_id.sub continuous_const)
  have i1 : Integrable fun u => |g (u - c) * φ u| :=
    ((hgc'.mul hφ).integrable_of_hasCompactSupport hgcs.mul_right).abs
  have i2 : Integrable fun u => M * |g (u - c)| :=
    (hgc'.integrable_of_hasCompactSupport hgcs).abs.const_mul M
  calc |∫ u, g (u - c) * φ u| ≤ ∫ u, |g (u - c) * φ u| := abs_integral_le_integral_abs
    _ ≤ ∫ u, M * |g (u - c)| := integral_mono i1 i2 fun u => by
        by_cases hu : u - c ∈ Set.Icc 0 w
        · rw [abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hM u ⟨by linarith [hu.1], by linarith [hu.2]⟩)
            (abs_nonneg _)
        · simp [hgsupp _ hu]
    _ = M * ∫ u, |g u| := by
        rw [integral_const_mul, integral_sub_right_eq_self (fun u => |g u|) c]

/-- The moment of an atomic test against `φ` is the sum of the atom moments. -/
theorem integral_atomicTest_mul {φ : ℝ → ℝ} (hφ : Continuous φ) (hg : Continuous g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N : ℕ) (x : ℕ → ℝ) :
    ∫ u, atomicTest N x g u * φ u = ∑ n ∈ Finset.Icc 1 N, x n * ∫ u, g (u - Real.log n) * φ u := by
  simp only [atomicTest, sum_mul]
  rw [integral_finsetSum _ fun n _ => ?_]
  · exact sum_congr rfl fun n _ => by rw [← integral_const_mul]; congr 1; funext u; ring
  · refine ((continuous_const.mul (hg.comp (continuous_id.sub continuous_const))).mul hφ)
      |>.integrable_of_hasCompactSupport ?_
    exact HasCompactSupport.mul_right (HasCompactSupport.mul_left (hasCompactSupport_atom hgsupp n))

theorem exp_half_log_sq {n : ℕ} (hn : 1 ≤ n) : Real.exp (Real.log n / 2) ^ 2 = n := by
  rw [sq, ← Real.exp_add, add_halves, Real.exp_log (by exact_mod_cast hn)]

theorem exp_neg_half_log_sq {n : ℕ} (hn : 1 ≤ n) : Real.exp (-(Real.log n / 2)) ^ 2 = 1 / n := by
  rw [Real.exp_neg, inv_pow, exp_half_log_sq hn, one_div]

/-- The pole term of Weil's form: `2C² − 2S² = 2 (∫ f e^{−u/2}) (∫ f e^{u/2})`. -/
theorem two_mul_cosh_sq_sub_sinh_sq_eq {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2 =
      2 * (∫ u, f u * Real.exp (-(u / 2))) * ∫ u, f u * Real.exp (u / 2) := by
  have hint : ∀ φ : ℝ → ℝ, Continuous φ → Integrable fun u => f u * φ u := fun φ hφ =>
    (hf.mul hφ).integrable_of_hasCompactSupport hfc.mul_right
  have hc := hint (fun u => Real.cosh (u / 2)) (by fun_prop)
  have hs := hint (fun u => Real.sinh (u / 2)) (by fun_prop)
  have e1 : ∫ u, f u * Real.exp (-(u / 2)) = coshHalfMoment f - sinhHalfMoment f := by
    rw [coshHalfMoment, sinhHalfMoment, ← integral_sub hc hs]
    congr 1; funext u; rw [← mul_sub, Real.cosh_sub_sinh]
  have e2 : ∫ u, f u * Real.exp (u / 2) = coshHalfMoment f + sinhHalfMoment f := by
    rw [coshHalfMoment, sinhHalfMoment, ← integral_add hc hs]
    congr 1; funext u; rw [← mul_add, Real.cosh_add_sinh]
  rw [e1, e2]; ring

/-- **Weighted Cauchy–Schwarz**: `(Σ |x_m| a_m)² ≤ (Σ μ_m x_m²)(Σ a_m²/μ_m)` for `μ > 0`. -/
theorem sq_sum_abs_mul_le (s : Finset ℕ) (x a μ : ℕ → ℝ) (hμ : ∀ m ∈ s, 0 < μ m) :
    (∑ m ∈ s, |x m| * a m) ^ 2 ≤ (∑ m ∈ s, x m ^ 2 * μ m) * ∑ m ∈ s, a m ^ 2 / μ m := by
  have h := sum_mul_sq_le_sq_mul_sq s (fun m => |x m| * Real.sqrt (μ m))
    (fun m => a m / Real.sqrt (μ m))
  have e1 : ∑ m ∈ s, |x m| * Real.sqrt (μ m) * (a m / Real.sqrt (μ m)) = ∑ m ∈ s, |x m| * a m :=
    sum_congr rfl fun m hm => by
      have := Real.sqrt_pos.mpr (hμ m hm); field_simp
  have e2 : ∑ m ∈ s, (|x m| * Real.sqrt (μ m)) ^ 2 = ∑ m ∈ s, x m ^ 2 * μ m :=
    sum_congr rfl fun m hm => by rw [mul_pow, sq_abs, Real.sq_sqrt (hμ m hm).le]
  have e3 : ∑ m ∈ s, (a m / Real.sqrt (μ m)) ^ 2 = ∑ m ∈ s, a m ^ 2 / μ m :=
    sum_congr rfl fun m hm => by rw [div_pow, Real.sq_sqrt (hμ m hm).le]
  rw [e1, e2, e3] at h
  exact h

/-! ### The tilted margin -/

/-- The **per-atom margin** of the stability law at the spacing scale. -/
def atomMargin (w : ℝ) (N m : ℕ) : ℝ :=
  2 * gammaHardyPhaseRate 0 +
    (Real.log (1 / w) - 8 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1))) -
      (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m)

/-- **The tilted margin**: for `w ≤ δ_N/2` and weights `y` with `y_m² = x_m²`,
`‖g‖² Σ_m μ_m x_m² ≤ 2θ′(0)‖f_x‖² + levyEnergy f_x − ‖g‖² P_N(y)`. -/
theorem atomMargin_mul_le_levy_sub (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ atomSpacing N / 2) (x y : ℕ → ℝ) (hxy : ∀ m ∈ Finset.Icc 1 N, y m ^ 2 = x m ^ 2) :
    (∫ u, g u ^ 2) * ∑ m ∈ Finset.Icc 1 N, x m ^ 2 * atomMargin w N m ≤
      2 * gammaHardyPhaseRate 0 * (∫ u, atomicTest N x g u ^ 2) +
        levyEnergy (atomicTest N x g) - (∫ u, g u ^ 2) * atomicWeilForm N y := by
  have hδ := atomSpacing_pos hN
  rw [integral_atomicTest_sq hg hgc hgsupp (by linarith) x]
  have hlevy := levyEnergy_atomicTest_ge hg hgc hgsupp hN hw0 hw x
  have hprime : atomicWeilForm N y ≤ ∑ m ∈ Finset.Icc 1 N, x m ^ 2 *
      (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m) :=
    (atomicWeilForm_le_tilted N y).trans (le_of_eq (sum_congr rfl fun m hm => by rw [hxy m hm]))
  set G2 := ∫ u, g u ^ 2
  have hG2 : 0 ≤ G2 := integral_nonneg fun u => sq_nonneg _
  have hexpand : G2 * ∑ m ∈ Finset.Icc 1 N, x m ^ 2 * atomMargin w N m =
      2 * gammaHardyPhaseRate 0 * ((∑ m ∈ Finset.Icc 1 N, x m ^ 2) * G2) +
        G2 * ∑ m ∈ Finset.Icc 1 N, x m ^ 2 *
          (Real.log (1 / w) - 8 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1))) -
        G2 * ∑ m ∈ Finset.Icc 1 N, x m ^ 2 *
          (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m) := by
    simp only [atomMargin, mul_sum, sum_mul, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun m _ => by ring
  have hP := mul_le_mul_of_nonneg_left hprime hG2
  linarith

/-- The **fixed width ratio** `c★ = (c₁/2) e^{−(C + 2|θ′(0)| + 1)}`. -/
def fixedWidthRatio : ℝ :=
  spacingRatio / 2 * Real.exp (-(spacingConstant + 2 * |gammaHardyPhaseRate 0| + 1))

theorem fixedWidthRatio_pos : 0 < fixedWidthRatio := by
  unfold fixedWidthRatio; have := spacingRatio_pos; positivity

theorem fixedWidthRatio_le : fixedWidthRatio ≤ spacingRatio / 2 := by
  unfold fixedWidthRatio
  refine mul_le_of_le_one_right (by have := spacingRatio_pos; positivity)
    (Real.exp_le_one_iff.mpr ?_)
  have : (0 : ℝ) ≤ spacingConstant := by
    unfold spacingConstant; have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  have := abs_nonneg (gammaHardyPhaseRate 0)
  linarith

/-- At `w ≤ c★δ_N`: the atoms are separated, `wN ≤ c★ ≤ 1/64`, and **the margin grows along the
pole**: `μ_m ≥ 1 + (m/8N) log m` for `1 ≤ m ≤ N`. -/
theorem one_add_le_atomMargin {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ fixedWidthRatio * atomSpacing N) :
    w ≤ spacingRatio * atomSpacing N ∧ w ≤ atomSpacing N / 2 ∧ w * N ≤ 1 / 64 ∧ w ≤ 1 ∧
      ∀ m ∈ Finset.Icc 1 N, 1 + (m : ℝ) / (8 * N) * Real.log m ≤ atomMargin w N m := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hδ := atomSpacing_pos hN
  have hδN : atomSpacing N ≤ 1 / N := atomSpacing_le_inv hN
  have hNδ : (N : ℝ) * atomSpacing N ≤ 1 := by rw [le_div_iff₀ hNpos] at hδN; linarith
  have hc := fixedWidthRatio_le
  have hR := spacingRatio_lt_half
  have hR0 := spacingRatio_pos
  have hc0 := fixedWidthRatio_pos
  have hwR : w ≤ spacingRatio * atomSpacing N := hw.trans (by nlinarith)
  have hwN : w * N ≤ fixedWidthRatio := by nlinarith
  have hR64 : spacingRatio ≤ 1 / 32 := by
    unfold spacingRatio
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.one_le_exp (show (0 : ℝ) ≤ 5 / 2 by norm_num)]
  refine ⟨hwR, by nlinarith [atomSpacing_le_one hN], by linarith, by
    nlinarith [atomSpacing_le_one hN], fun m hm => ?_⟩
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  -- the tilted saving at width `2w` pays the cross row with half the saving
  have h2w : 2 * w ≤ spacingRatio / N := by
    rw [le_div_iff₀ hNpos]; nlinarith
  have hcross := crossRow_le_saving hm1 hmN h2w
  -- `log(1/w) − log N = log(1/(wN)) ≥ C + 2|θ| + 1`
  have hlog : Real.log (1 / w) - Real.log N ≥ spacingConstant + 2 * |gammaHardyPhaseRate 0| + 1 := by
    have e : Real.log (1 / w) - Real.log N = Real.log (1 / (w * N)) := by
      rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul hw0.ne' hNpos.ne']; ring
    have hmono : Real.log (1 / fixedWidthRatio) ≤ Real.log (1 / (w * N)) :=
      Real.log_le_log (by positivity) (one_div_le_one_div_of_le (by positivity) hwN)
    have hval : Real.log (1 / fixedWidthRatio) = Real.log (2 / spacingRatio) +
        (spacingConstant + 2 * |gammaHardyPhaseRate 0| + 1) := by
      have hdef : fixedWidthRatio = spacingRatio / 2 *
          Real.exp (-(spacingConstant + 2 * |gammaHardyPhaseRate 0| + 1)) := rfl
      rw [hdef, one_div, Real.log_inv, Real.log_mul (by positivity) (Real.exp_pos _).ne',
        Real.log_exp, Real.log_div (by norm_num) hR0.ne', Real.log_div hR0.ne' (by norm_num)]
      ring
    have h2R : 0 < Real.log (2 / spacingRatio) :=
      Real.log_pos (by rw [lt_div_iff₀ hR0]; linarith)
    linarith
  have hθ := neg_abs_le (gammaHardyPhaseRate 0)
  have e1 : (m : ℝ) / (4 * N) * Real.log m = 2 * ((m : ℝ) / (8 * N) * Real.log m) := by
    field_simp; ring
  have e2 : 8 * Real.exp (5 / 2) * (2 * w) * m * (1 + Real.log (N + 1)) =
      2 * (8 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1))) := by ring
  unfold atomMargin
  unfold spacingConstant at hlog
  rw [e1]
  rw [e2] at hcross
  rw [e1] at hcross
  linarith

/-- `m(1 + log N) ≤ 16N + 2m log m` for `1 ≤ m ≤ N`. -/
theorem mul_one_add_log_le {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    (m : ℝ) * (1 + Real.log N) ≤ 16 * N + 2 * m * Real.log m := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hNm : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogm := Real.log_nonneg hm1
  have hlogN := Real.log_nonneg (hm1.trans hNm)
  by_cases h : 1 + Real.log N ≤ 2 * Real.log m
  · nlinarith
  push Not at h
  -- `m² < eN ≤ 3N` and `(1 + log N)² ≤ 4N`
  have hm2 : (m : ℝ) ^ 2 < 3 * N := by
    have : (m : ℝ) ^ 2 < Real.exp 1 * N := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < m ^ 2), ← Real.exp_log hNpos, ← Real.exp_add,
        Real.exp_lt_exp, Real.log_pow]
      push_cast; linarith
    have := Real.exp_one_lt_d9
    nlinarith
  have hL2 : (1 + Real.log N) ^ 2 ≤ 4 * N := by
    have hs := Real.sqrt_pos.mpr hNpos
    have h1 : Real.log (Real.sqrt N) ≤ Real.sqrt N - 1 := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt hNpos.le] at h1
    have h2 : 1 + Real.log N ≤ 2 * Real.sqrt N := by linarith
    have h3 : (2 * Real.sqrt N) ^ 2 = 4 * N := by rw [mul_pow, Real.sq_sqrt hNpos.le]; ring
    rw [← h3]
    exact pow_le_pow_left₀ (by linarith) h2 2
  have hprod : ((m : ℝ) * (1 + Real.log N)) ^ 2 ≤ (4 * N) ^ 2 := by
    rw [mul_pow]; nlinarith
  have h4 : (m : ℝ) * (1 + Real.log N) ≤ 4 * N :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hprod
  nlinarith

/-! ### The pole is paid -/

/-- **The pole is paid by the tilted margin**: with `X = Σ μ_m x_m²` and margins
`μ_m ≥ 1 + (m/8N) log m`, `(∫ f e^{−u/2})² (∫ f e^{u/2})² ≤ 16 e^w (wN)² ‖g‖⁴ X²`. -/
theorem sq_mul_poleMoments_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w) (x μ : ℕ → ℝ)
    (hμ : ∀ m ∈ Finset.Icc 1 N, 1 + (m : ℝ) / (8 * N) * Real.log m ≤ μ m) :
    ((∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
        ∫ u, atomicTest N x g u * Real.exp (u / 2)) ^ 2 ≤
      16 * Real.exp w * (w * N) ^ 2 * (∫ u, g u ^ 2) ^ 2 *
        (∑ m ∈ Finset.Icc 1 N, x m ^ 2 * μ m) ^ 2 := by
  set A₁ := ∫ u, |g u|
  set G := ∫ u, g u ^ 2
  set X := ∑ m ∈ Finset.Icc 1 N, x m ^ 2 * μ m
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hA₁ : 0 ≤ A₁ := integral_nonneg fun _ => abs_nonneg _
  have hG : 0 ≤ G := integral_nonneg fun _ => sq_nonneg _
  have hμpos : ∀ m ∈ Finset.Icc 1 N, 0 < μ m := fun m hm => by
    have : 0 ≤ (m : ℝ) / (8 * N) * Real.log m :=
      mul_nonneg (by positivity) (Real.log_natCast_nonneg m)
    linarith [hμ m hm]
  have hX : 0 ≤ X := sum_nonneg fun m hm => mul_nonneg (sq_nonneg _) (hμpos m hm).le
  set ea : ℕ → ℝ := fun m => A₁ * Real.exp (-(Real.log m / 2))
  set eb : ℕ → ℝ := fun m => Real.exp (w / 2) * A₁ * Real.exp (Real.log m / 2)
  -- the atom moments
  have hA : |∫ u, atomicTest N x g u * Real.exp (-(u / 2))| ≤
      ∑ m ∈ Finset.Icc 1 N, |x m| * ea m := by
    rw [integral_atomicTest_mul (by fun_prop) hg.continuous hgsupp]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have := abs_integral_shift_mul_le hg.continuous hgc hgsupp
      (φ := fun u => Real.exp (-(u / 2))) (by fun_prop) (c := Real.log n)
      (M := Real.exp (-(Real.log n / 2))) fun u hu => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (by linarith [hu.1])
    simp only [ea]; linarith
  have hB : |∫ u, atomicTest N x g u * Real.exp (u / 2)| ≤ ∑ m ∈ Finset.Icc 1 N, |x m| * eb m := by
    rw [integral_atomicTest_mul (by fun_prop) hg.continuous hgsupp]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have := abs_integral_shift_mul_le hg.continuous hgc hgsupp
      (φ := fun u => Real.exp (u / 2)) (by fun_prop) (c := Real.log n)
      (M := Real.exp (Real.log n / 2) * Real.exp (w / 2)) fun u hu => by
        rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [hu.2])
    simp only [eb]; linarith
  -- the weighted sums
  have hsa : ∑ m ∈ Finset.Icc 1 N, ea m ^ 2 / μ m ≤ A₁ ^ 2 * (1 + Real.log N) := by
    have hharm : ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n ≤ 1 + Real.log N := by
      have h := harmonic_le_one_add_log N
      simp only [_root_.harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
      simpa only [one_div] using h
    calc ∑ m ∈ Finset.Icc 1 N, ea m ^ 2 / μ m ≤ ∑ m ∈ Finset.Icc 1 N, A₁ ^ 2 * (1 / (m : ℝ)) :=
          sum_le_sum fun m hm => by
            have h1 : ea m ^ 2 = A₁ ^ 2 * (1 / (m : ℝ)) := by
              simp only [ea]
              rw [mul_pow, exp_neg_half_log_sq (Finset.mem_Icc.mp hm).1]
            have h2 : 1 ≤ μ m := by
              have : 0 ≤ (m : ℝ) / (8 * N) * Real.log m :=
                mul_nonneg (by positivity) (Real.log_natCast_nonneg m)
              linarith [hμ m hm]
            rw [h1]
            exact div_le_self (by positivity) h2
      _ = A₁ ^ 2 * ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m := by rw [mul_sum]
      _ ≤ A₁ ^ 2 * (1 + Real.log N) := mul_le_mul_of_nonneg_left hharm (sq_nonneg _)
  have hL : 0 < 1 + Real.log N := by linarith [Real.log_natCast_nonneg N]
  have hsb : ∑ m ∈ Finset.Icc 1 N, eb m ^ 2 / μ m ≤
      Real.exp w * A₁ ^ 2 * (16 * N ^ 2 / (1 + Real.log N)) := by
    calc ∑ m ∈ Finset.Icc 1 N, eb m ^ 2 / μ m ≤
          ∑ _m ∈ Finset.Icc 1 N, Real.exp w * A₁ ^ 2 * (16 * N / (1 + Real.log N)) :=
          sum_le_sum fun m hm => by
            obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
            have h1 : eb m ^ 2 = Real.exp w * A₁ ^ 2 * m := by
              simp only [eb]
              rw [mul_pow, mul_pow, exp_half_log_sq hm1, ← Real.exp_nat_mul]
              push_cast; ring_nf
            rw [h1, mul_div_assoc]
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hμm := hμ m hm
            have hμ0 := hμpos m hm
            rw [div_le_div_iff₀ hμ0 hL]
            have := mul_one_add_log_le hm1 hmN
            have e : 16 * (N : ℝ) * (1 + (m : ℝ) / (8 * N) * Real.log m) =
                16 * N + 2 * m * Real.log m := by field_simp; ring
            nlinarith [mul_le_mul_of_nonneg_left hμm (by positivity : (0 : ℝ) ≤ 16 * N)]
      _ = Real.exp w * A₁ ^ 2 * (16 * N ^ 2 / (1 + Real.log N)) := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; field_simp
  -- squares of the moments
  have hA2' : (∫ u, atomicTest N x g u * Real.exp (-(u / 2))) ^ 2 ≤ X * (A₁ ^ 2 * (1 + Real.log N)) := by
    calc _ = |∫ u, atomicTest N x g u * Real.exp (-(u / 2))| ^ 2 := (sq_abs _).symm
      _ ≤ (∑ m ∈ Finset.Icc 1 N, |x m| * ea m) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hA 2
      _ ≤ X * ∑ m ∈ Finset.Icc 1 N, ea m ^ 2 / μ m := sq_sum_abs_mul_le _ x ea μ hμpos
      _ ≤ X * (A₁ ^ 2 * (1 + Real.log N)) := mul_le_mul_of_nonneg_left hsa hX
  have hB2' : (∫ u, atomicTest N x g u * Real.exp (u / 2)) ^ 2 ≤
      X * (Real.exp w * A₁ ^ 2 * (16 * N ^ 2 / (1 + Real.log N))) := by
    calc _ = |∫ u, atomicTest N x g u * Real.exp (u / 2)| ^ 2 := (sq_abs _).symm
      _ ≤ (∑ m ∈ Finset.Icc 1 N, |x m| * eb m) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hB 2
      _ ≤ X * ∑ m ∈ Finset.Icc 1 N, eb m ^ 2 / μ m := sq_sum_abs_mul_le _ x eb μ hμpos
      _ ≤ X * (Real.exp w * A₁ ^ 2 * (16 * N ^ 2 / (1 + Real.log N))) :=
          mul_le_mul_of_nonneg_left hsb hX
  have hL1 := sq_integral_abs_le hg.continuous hgsupp hw0
  have hA4 : A₁ ^ 2 * A₁ ^ 2 ≤ (w * G) * (w * G) := mul_le_mul hL1 hL1 (sq_nonneg _) (by positivity)
  calc ((∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
        ∫ u, atomicTest N x g u * Real.exp (u / 2)) ^ 2
      = (∫ u, atomicTest N x g u * Real.exp (-(u / 2))) ^ 2 *
          (∫ u, atomicTest N x g u * Real.exp (u / 2)) ^ 2 := mul_pow _ _ _
    _ ≤ (X * (A₁ ^ 2 * (1 + Real.log N))) *
          (X * (Real.exp w * A₁ ^ 2 * (16 * N ^ 2 / (1 + Real.log N)))) :=
        mul_le_mul hA2' hB2' (sq_nonneg _) (by positivity)
    _ = 16 * Real.exp w * (N : ℝ) ^ 2 * (A₁ ^ 2 * A₁ ^ 2) * X ^ 2 := by field_simp
    _ ≤ 16 * Real.exp w * (N : ℝ) ^ 2 * ((w * G) * (w * G)) * X ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA4 (by positivity)) (sq_nonneg _)
    _ = 16 * Real.exp w * (w * N) ^ 2 * G ^ 2 * X ^ 2 := by ring

/-- At `w ≤ c★δ_N` the pole costs at most the tilted margin: `2|AB| ≤ ‖g‖² X`. -/
theorem two_mul_abs_poleMoments_le_margin (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ fixedWidthRatio * atomSpacing N) (x : ℕ → ℝ) :
    2 * |(∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
        ∫ u, atomicTest N x g u * Real.exp (u / 2)| ≤
      (∫ u, g u ^ 2) * ∑ m ∈ Finset.Icc 1 N, x m ^ 2 * atomMargin w N m := by
  obtain ⟨-, -, hwN, hw1, hμ⟩ := one_add_le_atomMargin hN hw0 hw
  set P := (∫ u, atomicTest N x g u * Real.exp (-(u / 2))) * ∫ u, atomicTest N x g u * Real.exp (u / 2)
  set G := ∫ u, g u ^ 2
  set X := ∑ m ∈ Finset.Icc 1 N, x m ^ 2 * atomMargin w N m
  have hG : 0 ≤ G := integral_nonneg fun _ => sq_nonneg _
  have hX : 0 ≤ X := sum_nonneg fun m hm => mul_nonneg (sq_nonneg _) (by
    have := hμ m hm
    have : 0 ≤ (m : ℝ) / (8 * N) * Real.log m :=
      mul_nonneg (by positivity) (Real.log_natCast_nonneg m)
    linarith)
  have h := sq_mul_poleMoments_le hg hgc hgsupp hN hw0 x (atomMargin w N) hμ
  have hwN0 : 0 ≤ w * N := by positivity
  have he : Real.exp w ≤ 3 := (Real.exp_le_exp.mpr hw1).trans Real.exp_one_lt_d9.le |>.trans
    (by norm_num)
  have hsmall : 16 * Real.exp w * (w * N) ^ 2 ≤ 1 / 4 := by
    have : (w * N) ^ 2 ≤ (1 / 64) ^ 2 := pow_le_pow_left₀ hwN0 hwN 2
    nlinarith [Real.exp_pos w]
  have h2 : (2 * |P|) ^ 2 ≤ (G * X) ^ 2 := by
    rw [mul_pow, sq_abs]
    nlinarith [mul_nonneg (sq_nonneg G) (sq_nonneg X)]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h2

/-! ### Weil positivity at a fixed fraction of the spacing -/

/-- **Weil positivity at a fixed fraction of the spacing.** For a real `C²` bump supported in
`[0, w]` with `0 < w ≤ c★ δ_N`, Weil's form is nonnegative on every atomic test
`Σ_{n ≤ N} x_n g(· − log n)`, for every real coefficient vector `x` and every `N ≥ 1`. -/
theorem weilQuad_atomicTest_nonneg (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ fixedWidthRatio * atomSpacing N) (x : ℕ → ℝ) : 0 ≤ weilQuad (atomicTest N x g) := by
  obtain ⟨-, hw2, -⟩ := one_add_le_atomMargin hN hw0 hw
  have hwδ : w < atomSpacing N := by linarith [atomSpacing_pos hN]
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  have hM := atomMargin_mul_le_levy_sub hg hgc hgsupp hN hw0 hw2 x x fun _ _ => rfl
  rw [← primeSum_atomicTest hg hgc hgsupp hwδ x] at hM
  have hpole := two_mul_abs_poleMoments_le_margin hg hgc hgsupp hN hw0 hw x
  rw [weilQuad_eq hf hfc, two_mul_cosh_sq_sub_sinh_sq_eq hf.continuous hfc]
  have := neg_abs_le ((∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
    ∫ u, atomicTest N x g u * Real.exp (u / 2))
  nlinarith

/-- **The same for every completely multiplicative sign twin**: `M_ω(f) + 2AB ≥ 0` at `w ≤ c★δ_N`. -/
theorem twin_markov_add_pole_nonneg {ω : ArithmeticFunction ℝ} (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ fixedWidthRatio * atomSpacing N) (x : ℕ → ℝ) :
    0 ≤ archForm (atomicTest N x g) - twistedPrimeSum ω (atomicTest N x g) +
      2 * (∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
        ∫ u, atomicTest N x g u * Real.exp (u / 2) := by
  obtain ⟨-, hw2, -⟩ := one_add_le_atomMargin hN hw0 hw
  have hwδ : w < atomSpacing N := by linarith [atomSpacing_pos hN]
  have hsq : ∀ m ∈ Finset.Icc 1 N, (ω m * x m) ^ 2 = x m ^ 2 := fun m hm => by
    rcases hsign m (Finset.mem_Icc.mp hm).1 with h | h <;> rw [h] <;> ring
  have hM := atomMargin_mul_le_levy_sub hg hgc hgsupp hN hw0 hw2 x _ hsq
  rw [← primeSum_atomicTest hg hgc hgsupp hwδ _,
    ← (twistedPrimeSum_atomicTest hω hsign hg hgc hgsupp hwδ x).1,
    ← archForm_eq_levyEnergy (contDiff_atomicTest hg N x) (hasCompactSupport_atomicTest hgsupp N x)]
    at hM
  have hpole := two_mul_abs_poleMoments_le_margin hg hgc hgsupp hN hw0 hw x
  have := neg_abs_le ((∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
    ∫ u, atomicTest N x g u * Real.exp (u / 2))
  nlinarith

/-! ### The Lorentzian structure of `ζ` at the spacing scale -/

/-- **The Hodge index at a fixed fraction of the spacing**: the Euler-gauge atomic intersection
form of `ζ`, pole plane included, has one positive square at every width `0 < w ≤ c★δ_N`. -/
theorem atomicIntersectionGram_isHyperbolic (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ fixedWidthRatio * atomSpacing N) : IsHyperbolic (atomicIntersectionGram g N) :=
  (atomicIntersectionGram_isHyperbolic_iff hg hgsupp hw0.le N).mpr fun d => by
    rw [finAtomicTest_eq_atomicTest]
    exact weilQuad_atomicTest_nonneg hg hgc hgsupp hN hw0 hw _

/-- **Trickle-down at a fixed fraction of the spacing**: for a nonnegative nonzero bump the atomic
intersection form satisfies the weighted trickle-down inequality, uniformly in `N`. -/
theorem weightedTrickleDown_atomicIntersectionGram (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hg0 : ∀ u, 0 ≤ g u) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {u₀ : ℝ} (hu₀ : 0 < g u₀) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ fixedWidthRatio * atomSpacing N) :
    WeightedTrickleDown (poleWeight (atomPoleRow g N) (-atomicMarkovGram g N))
      (atomicIntersectionGram g N) := by
  obtain ⟨-, hw2, -⟩ := one_add_le_atomMargin hN hw0 hw
  have hwδ : w < atomSpacing N := by linarith [atomSpacing_pos hN]
  refine (weilQuad_finAtomicTest_nonneg_iff_weightedTrickleDown hg hgc hg0 hgsupp hu₀ hw0.le
    hwδ).mp fun d => ?_
  rw [finAtomicTest_eq_atomicTest]
  exact weilQuad_atomicTest_nonneg hg hgc hgsupp hN hw0 hw _

/-- **Hyperbolic links at a fixed fraction of the spacing**: the weighted atomic intersection form
of `ζ`, a connected Metzler form with positive row sums, has hyperbolic links. -/
theorem hasHyperbolicLinks_atomicIntersectionGram (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hg0 : ∀ u, 0 ≤ g u) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {u₀ : ℝ} (hu₀ : 0 < g u₀) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ fixedWidthRatio * atomSpacing N) :
    HasHyperbolicLinks (diagConj (poleWeight (atomPoleRow g N) (-atomicMarkovGram g N))
      (atomicIntersectionGram g N)) := by
  obtain ⟨-, hw2, -⟩ := one_add_le_atomMargin hN hw0 hw
  have hwδ : w < atomSpacing N := by linarith [atomSpacing_pos hN]
  have hB0 := atomPoleRow_zero_pos hg.continuous hgc hg0 hu₀ (N := N)
  have hB1 : ∀ j, 0 ≤ atomPoleRow g N 1 j := fun j => by
    simp only [atomPoleRow, Matrix.of_apply, one_ne_zero, if_false]
    exact integral_nonneg fun u => mul_nonneg (hg0 _) (Real.exp_pos _).le
  obtain ⟨hπ, hQπ⟩ := poleWeight_pos_and_mulVec_pos (atomPoleRow g N) (-atomicMarkovGram g N)
    hB0 hB1
  refine (isHyperbolic_iff_hasHyperbolicLinks (diagConj_isSymm (atomicIntersectionGram_isSymm g N))
    (diagConj_isMetzler hπ (atomicIntersectionGram_isMetzler hg0 hgsupp hwδ)) (fun i => ?_)
    (diagConj_isConnectedSupport hπ
      (poleGram_isConnectedSupport _ _ fun j => (hB0 j).ne'))).mp
    ((isHyperbolic_diagConj_iff fun i => (hπ i).ne').mpr
      (atomicIntersectionGram_isHyperbolic hg hgc hgsupp hN hw0 hw))
  rw [rowSum_diagConj]
  exact mul_pos (hπ i) (hQπ i)

end GaloisForLFunctions.ArithmeticLorentzianGeometry
