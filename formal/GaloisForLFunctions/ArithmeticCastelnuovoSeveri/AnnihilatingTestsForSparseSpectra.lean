import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheTowerDefectCountsTheFrobeniusEigenvalues
import GaloisForLFunctions.RHTower.WeilFullConeHerglotzRightHalfPlane
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity

/-!
# Annihilating tests for sparse spectra

A compactly supported test whose transform vanishes on a prescribed infinite set `A ⊂ ℂ` and at
no prescribed finite set `F` of non-real points exists as soon as `Σ_{a ∈ A} |a|^{-s} < ∞` for some
`s < 1`.

*Ingham bump.* The iterated convolution of the boxes `1_{[−ε_n, ε_n]}/(2ε_n)`,
`ε_n = (n+1)^{-p}` with `p > 1`, converges to a smooth function `φ` supported in
`[−Σε_n, Σε_n]` whose transform is `Φ(z) = Π_n sin(ε_n z)/(ε_n z)`. On the real line
`|Φ(x)| ≤ e^{2 − (|x|/e)^{1/p}}`; off the real line `Φ` does not vanish.

*Annihilator.* With `L_a h = h + (ia)⁻¹ h'`, the transform of `L_{a_{N−1}} ⋯ L_{a_0} φ` is
`Π_{k<N}(1 − z/a_k) Φ(z)`. Since `|Π(1 − x/a_k)| ≤ e^{|x|^s Σ|a_k|^{-s}/s}` on the real line and
`1/p > s`, these tests converge uniformly, inside the support of `φ`, to a `C²` test `g` with
`ĝ = Π_k (1 − z/a_k) · Φ`.
-/

open Complex MeasureTheory Set Filter Topology Finset
open scoped ComplexConjugate Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open Zeta23

/-! ### 1. Boxes and the complex sinc -/

/-- The complex sinc `sin w / w`, equal to `1` at `0`. -/
def sincC (w : ℂ) : ℂ := if w = 0 then 1 else Complex.sin w / w

theorem sincC_zero : sincC 0 = 1 := by simp [sincC]

/-- The normalized box `1_{[−ε, ε]} / (2ε)`. -/
def boxTest (ε : ℝ) : ℝ → ℂ := Set.indicator (Icc (-ε) ε) fun _ => ((2 * ε : ℝ)⁻¹ : ℂ)

theorem boxTest_integrable (ε : ℝ) : Integrable (boxTest ε) :=
  (integrableOn_const (isCompact_Icc.measure_lt_top).ne).integrable_indicator measurableSet_Icc

theorem boxTest_hasCompactSupport (ε : ℝ) : HasCompactSupport (boxTest ε) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -ε) (b := ε)) fun x hx => ?_
  simp [boxTest, Set.indicator_of_notMem hx]

theorem support_boxTest_subset (ε : ℝ) : Function.support (boxTest ε) ⊆ Icc (-ε) ε :=
  Set.support_indicator_subset

/-- **The transform of a box is a sinc**: `paperFT (1_{[−ε,ε]}/(2ε)) z = sin(εz)/(εz)`. -/
theorem paperFT_boxTest {ε : ℝ} (hε : 0 < ε) (z : ℂ) : paperFT (boxTest ε) z = sincC (ε * z) := by
  have hind : paperFT (boxTest ε) z = ((2 * ε : ℝ)⁻¹ : ℂ) * ∫ u in (-ε)..ε, cexp (I * z * u) := by
    simp only [paperFT, boxTest]
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      ← integral_const_mul, ← integral_indicator measurableSet_Icc]
    congr 1
    funext u
    by_cases hu : u ∈ Icc (-ε) ε <;> simp [Set.indicator, hu]
  rw [hind]
  by_cases hz : z = 0
  · subst hz
    have hint : (∫ u in (-ε)..ε, cexp (I * 0 * u)) = ((2 * ε : ℝ) : ℂ) := by
      simp only [mul_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
        Complex.real_smul, mul_one]
      push_cast; ring
    rw [hint, mul_zero, sincC_zero]
    have : ((2 * ε : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
    exact inv_mul_cancel₀ this
  · have hIz : I * z ≠ 0 := mul_ne_zero I_ne_zero hz
    have hεz : (ε : ℂ) * z ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hε.ne') hz
    rw [integral_exp_mul_complex hIz, sincC, if_neg hεz, Complex.sin]
    push_cast
    have hε' : (ε : ℂ) ≠ 0 := ofReal_ne_zero.mpr hε.ne'
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring_nf

/-! ### 2. Bounds for the sinc -/

theorem sincC_ofReal (t : ℝ) : sincC (t : ℂ) = ((if t = 0 then 1 else Real.sin t / t : ℝ) : ℂ) := by
  by_cases ht : t = 0
  · subst ht; simp [sincC]
  · have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht
    simp [sincC, ht, ht', Complex.ofReal_sin]

theorem norm_sincC_ofReal_le_one (t : ℝ) : ‖sincC (t : ℂ)‖ ≤ 1 := by
  rw [sincC_ofReal, Complex.norm_real, Real.norm_eq_abs]
  split_ifs with ht
  · simp
  · rw [abs_div]
    exact div_le_one_of_le₀ (Real.abs_sin_le_abs) (abs_nonneg _)

theorem norm_sincC_ofReal_le_inv (t : ℝ) (ht : t ≠ 0) : ‖sincC (t : ℂ)‖ ≤ |t|⁻¹ := by
  rw [sincC_ofReal, if_neg ht, Complex.norm_real, Real.norm_eq_abs, abs_div, div_eq_mul_inv]
  have := Real.abs_sin_le_one t
  exact mul_le_of_le_one_left (inv_nonneg.mpr (abs_nonneg _)) this

/-- Near the origin `sin w / w` is within `|w|²` of `1`. -/
theorem norm_sincC_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖sincC w - 1‖ ≤ ‖w‖ ^ 2 := by
  by_cases h0 : w = 0
  · subst h0; simp [sincC]
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr h0
  have hb := Complex.sin_bound hw
  have hsin : ‖Complex.sin w - w‖ ≤ ‖w‖ ^ 3 := by
    calc ‖Complex.sin w - w‖ = ‖(Complex.sin w - (w - w ^ 3 / 6)) - w ^ 3 / 6‖ := by ring_nf
      _ ≤ ‖Complex.sin w - (w - w ^ 3 / 6)‖ + ‖w ^ 3 / 6‖ := norm_sub_le _ _
      _ ≤ ‖w‖ ^ 5 / 100 + ‖w‖ ^ 3 / 6 := by
          gcongr
          rw [norm_div, norm_pow]; norm_num
      _ ≤ ‖w‖ ^ 3 := by
          have h5 : ‖w‖ ^ 5 ≤ ‖w‖ ^ 3 := pow_le_pow_of_le_one (norm_nonneg _) hw (by norm_num)
          nlinarith [pow_nonneg (norm_nonneg w) 3]
  rw [sincC, if_neg h0, show Complex.sin w / w - 1 = (Complex.sin w - w) / w by
    field_simp, norm_div]
  rw [div_le_iff₀ hw0]
  calc ‖Complex.sin w - w‖ ≤ ‖w‖ ^ 3 := hsin
    _ = ‖w‖ ^ 2 * ‖w‖ := by ring

/-- The sinc vanishes only on the real line. -/
theorem sincC_ne_zero_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) : sincC w ≠ 0 := by
  have h0 : w ≠ 0 := fun h => hw (by rw [h, Complex.zero_im])
  rw [sincC, if_neg h0]
  refine div_ne_zero ?_ h0
  intro hs
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
  apply hw
  rw [hk]
  simp

/-! ### 3. Iterated convolutions of boxes -/

/-- The box widths `ε_n = (n+1)^{-p}`. -/
def inghamWidth (p : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-p)

theorem inghamWidth_pos (p : ℝ) (n : ℕ) : 0 < inghamWidth p n := by
  unfold inghamWidth; positivity

/-- The partial Ingham bumps `box_0 ⋆ ⋯ ⋆ box_n`. -/
def inghamPartial (p : ℝ) : ℕ → ℝ → ℂ
  | 0 => boxTest (inghamWidth p 0)
  | n + 1 => convolution (inghamPartial p n) (boxTest (inghamWidth p (n + 1)))
      (ContinuousLinearMap.mul ℝ ℂ) volume

/-- The half-width `Σ_{k ≤ n} ε_k` of the support of the `n`-th partial bump. -/
def inghamRadius (p : ℝ) (n : ℕ) : ℝ := ∑ k ∈ range (n + 1), inghamWidth p k

theorem inghamRadius_nonneg (p : ℝ) (n : ℕ) : 0 ≤ inghamRadius p n :=
  Finset.sum_nonneg fun k _ => (inghamWidth_pos p k).le

theorem inghamPartial_integrable_hasCompactSupport (p : ℝ) (n : ℕ) :
    Integrable (inghamPartial p n) ∧ HasCompactSupport (inghamPartial p n) := by
  induction n with
  | zero => exact ⟨boxTest_integrable _, boxTest_hasCompactSupport _⟩
  | succ n ih =>
    exact ⟨ih.1.integrable_convolution _ (boxTest_integrable _),
      ih.2.convolution _ (boxTest_hasCompactSupport _)⟩

theorem support_inghamPartial_subset (p : ℝ) (n : ℕ) :
    Function.support (inghamPartial p n) ⊆ Icc (-inghamRadius p n) (inghamRadius p n) := by
  induction n with
  | zero =>
    show Function.support (boxTest (inghamWidth p 0)) ⊆ _
    simpa [inghamRadius] using support_boxTest_subset (inghamWidth p 0)
  | succ n ih =>
    refine (support_convolution_subset _).trans ?_
    refine (Set.add_subset_add ih (support_boxTest_subset _)).trans ?_
    rw [Set.Icc_add_Icc (by linarith [inghamRadius_nonneg p n]) (by
      linarith [inghamWidth_pos p (n + 1)])]
    have : inghamRadius p (n + 1) = inghamRadius p n + inghamWidth p (n + 1) := by
      simp [inghamRadius, Finset.sum_range_succ]
    rw [this, neg_add]

/-- **The transform of a partial bump is a finite sinc product.** -/
theorem paperFT_inghamPartial (p : ℝ) (n : ℕ) (z : ℂ) :
    paperFT (inghamPartial p n) z = ∏ k ∈ range (n + 1), sincC (inghamWidth p k * z) := by
  induction n with
  | zero => simp [inghamPartial, paperFT_boxTest (inghamWidth_pos p 0)]
  | succ n ih =>
    have h := inghamPartial_integrable_hasCompactSupport p n
    rw [inghamPartial, RHTower.WeilHerglotz.paperFT_convolution h.1 (boxTest_integrable _) h.2
      (boxTest_hasCompactSupport _), ih, paperFT_boxTest (inghamWidth_pos p (n + 1))]
    exact (Finset.prod_range_succ _ (n + 1)).symm

/-! ### 4. The inverse transform -/

/-- The inverse transform `(1/2π) ∫ Ψ(r) e^{−iru} dr`. -/
def invFT (Ψ : ℝ → ℂ) (u : ℝ) : ℂ := 1 / (2 * (π : ℂ)) * ∫ r : ℝ, Ψ r * cexp (-I * r * u)

/-- **Fourier inversion** for a continuous integrable function with integrable transform. -/
theorem eq_invFT_paperFT {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k)
    (hF : Integrable fun r : ℝ => paperFT k r) (u : ℝ) :
    k u = invFT (fun r : ℝ => paperFT k r) u := by
  have hF' : Integrable (FourierTransform.fourier k) := by
    have h := hF.comp_mul_left' (R := -(2 * π)) (neg_ne_zero.mpr (by positivity))
    refine h.congr (Eventually.of_forall fun v => ?_)
    simp only
    rw [EF.paperFT_ofReal_eq_fourier]
    field_simp
  exact EF.paper_inversion hk hki hF' u

theorem norm_invFT_sub_le {Ψ Ψ' : ℝ → ℂ} (h : Integrable Ψ) (h' : Integrable Ψ') (u : ℝ) :
    ‖invFT Ψ u - invFT Ψ' u‖ ≤ (2 * π)⁻¹ * ∫ r, ‖Ψ r - Ψ' r‖ := by
  have hint : ∀ Φ : ℝ → ℂ, Integrable Φ → Integrable fun r : ℝ => Φ r * cexp (-I * r * u) :=
    fun Φ hΦ => hΦ.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun r => by
      rw [Complex.norm_exp]; simp)
  have hsub : invFT Ψ u - invFT Ψ' u =
      1 / (2 * (π : ℂ)) * ∫ r : ℝ, (Ψ r - Ψ' r) * cexp (-I * r * u) := by
    rw [invFT, invFT, ← mul_sub, ← integral_sub (hint Ψ h) (hint Ψ' h')]
    congr 2; funext r; ring
  rw [hsub, norm_mul]
  have h1 : ‖(1 : ℂ) / (2 * (π : ℂ))‖ = (2 * π)⁻¹ := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_two, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]; ring
  rw [h1]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans
    (le_of_eq (integral_congr_ae (Eventually.of_forall fun r => ?_)))) (by positivity)
  simp only [norm_mul, Complex.norm_exp]
  simp

/-- `invFT Ψ` is the Mathlib Fourier transform of `Ψ` at `u/(2π)`, divided by `2π`. -/
theorem invFT_eq_fourier (Ψ : ℝ → ℂ) :
    invFT Ψ = fun u => 1 / (2 * (π : ℂ)) * FourierTransform.fourier Ψ (u / (2 * π)) := by
  funext u
  rw [invFT, Real.fourier_real_eq]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  field_simp

/-- **Smoothness of the inverse transform** from integrable moments. -/
theorem contDiff_invFT {Ψ : ℝ → ℂ} {N : ℕ∞}
    (h : ∀ n : ℕ, (n : ℕ∞) ≤ N → Integrable fun r : ℝ => ‖r‖ ^ n * ‖Ψ r‖) :
    ContDiff ℝ N (invFT Ψ) := by
  rw [invFT_eq_fourier]
  exact contDiff_const.mul ((Real.contDiff_fourier h).comp (contDiff_id.div_const _))

/-! ### 5. The Ingham product -/

theorem inghamWidth_sq (p : ℝ) (k : ℕ) :
    inghamWidth p k ^ 2 = ((((k + 1 : ℕ) : ℝ)) ^ (2 * p))⁻¹ := by
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [inghamWidth, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le,
    show (-p * ((2 : ℕ) : ℝ)) = -(2 * p) by push_cast; ring, Real.rpow_neg hpos.le]
  push_cast; rfl

theorem summable_inghamWidth_sq {p : ℝ} (hp : 1 / 2 < p) :
    Summable fun k : ℕ => inghamWidth p k ^ 2 := by
  simp_rw [inghamWidth_sq]
  exact (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr (by linarith))

theorem summable_inghamWidth {p : ℝ} (hp : 1 < p) : Summable fun k : ℕ => inghamWidth p k := by
  have : ∀ k : ℕ, inghamWidth p k = ((((k + 1 : ℕ) : ℝ)) ^ p)⁻¹ := by
    intro k
    rw [inghamWidth, Real.rpow_neg (by positivity)]
    push_cast; rfl
  simp_rw [this]
  exact (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr hp)

theorem tendsto_inghamWidth {p : ℝ} (hp : 0 < p) :
    Tendsto (inghamWidth p) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop hp).comp
    (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  exact h

theorem summable_norm_sincC_sub_one {p : ℝ} (hp : 1 / 2 < p) (z : ℂ) :
    Summable fun k : ℕ => ‖sincC (inghamWidth p k * z) - 1‖ := by
  refine Summable.of_norm_bounded_eventually (g := fun k => inghamWidth p k ^ 2 * ‖z‖ ^ 2)
    ((summable_inghamWidth_sq hp).mul_right _) ?_
  have hev : ∀ᶠ k in atTop, inghamWidth p k * ‖z‖ ≤ 1 := by
    have := ((tendsto_inghamWidth (by linarith)).mul_const ‖z‖).eventually
      (gt_mem_nhds (show (0 : ℝ) * ‖z‖ < 1 by simp))
    exact this.mono fun k hk => hk.le
  rw [Nat.cofinite_eq_atTop]
  refine hev.mono fun k hk => ?_
  have hw : ‖(inghamWidth p k : ℂ) * z‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inghamWidth_pos p k).le]; exact hk
  rw [norm_norm]
  refine (norm_sincC_sub_one_le hw).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inghamWidth_pos p k).le]; ring

/-- The **Ingham transform** `Φ(z) = Π_k sin(ε_k z)/(ε_k z)`. -/
def inghamFT (p : ℝ) (z : ℂ) : ℂ := ∏' k : ℕ, sincC (inghamWidth p k * z)

theorem multipliable_ingham {p : ℝ} (hp : 1 / 2 < p) (z : ℂ) :
    Multipliable fun k : ℕ => sincC (inghamWidth p k * z) := by
  have h := multipliable_one_add_of_summable (summable_norm_sincC_sub_one hp z)
  simpa using h

theorem tendsto_paperFT_inghamPartial {p : ℝ} (hp : 1 / 2 < p) (z : ℂ) :
    Tendsto (fun n => paperFT (inghamPartial p n) z) atTop (𝓝 (inghamFT p z)) := by
  simp_rw [paperFT_inghamPartial]
  exact (multipliable_ingham hp z).tendsto_prod_tprod_nat.comp (tendsto_add_atTop_nat 1)

/-- **The Ingham transform vanishes nowhere off the real line.** -/
theorem inghamFT_ne_zero {p : ℝ} (hp : 1 / 2 < p) {z : ℂ} (hz : z.im ≠ 0) : inghamFT p z ≠ 0 := by
  have h := tprod_one_add_ne_zero_of_summable (f := fun k : ℕ => sincC (inghamWidth p k * z) - 1)
    (fun k => by
      simp only [add_sub_cancel]
      refine sincC_ne_zero_of_im_ne_zero ?_
      have him : ((inghamWidth p k : ℂ) * z).im = inghamWidth p k * z.im := by
        simp [Complex.mul_im]
      rw [him]
      exact mul_ne_zero (inghamWidth_pos p k).ne' hz)
    (summable_norm_sincC_sub_one hp z)
  simpa [inghamFT] using h

/-! ### 6. The partial bumps are continuous and invert their transforms -/

theorem convolution_boxTest_apply {f : ℝ → ℂ} {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    convolution f (boxTest ε) (ContinuousLinearMap.mul ℝ ℂ) volume x =
      ((2 * ε : ℝ)⁻¹ : ℂ) * ∫ t in (x - ε)..(x + ε), f t := by
  rw [convolution_def, intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc, ← integral_const_mul, ← integral_indicator measurableSet_Icc]
  congr 1
  funext t
  simp only [ContinuousLinearMap.mul_apply', boxTest, Set.indicator]
  by_cases ht : t ∈ Icc (x - ε) (x + ε)
  · have h : x - t ∈ Icc (-ε) ε := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simp only [ht, h, if_true]; ring
  · have h : x - t ∉ Icc (-ε) ε := fun h => ht ⟨by linarith [h.2], by linarith [h.1]⟩
    simp only [ht, h, if_false, mul_zero]

theorem continuous_inghamPartial_succ (p : ℝ) (n : ℕ) : Continuous (inghamPartial p (n + 1)) := by
  have hf := (inghamPartial_integrable_hasCompactSupport p n).1
  have hε := inghamWidth_pos p (n + 1)
  have hII : ∀ a b : ℝ, IntervalIntegrable (inghamPartial p n) volume a b :=
    fun a b => hf.intervalIntegrable
  have heq : inghamPartial p (n + 1) = fun x => ((2 * inghamWidth p (n + 1) : ℝ)⁻¹ : ℂ) *
      ((∫ t in (0 : ℝ)..(x + inghamWidth p (n + 1)), inghamPartial p n t) -
        ∫ t in (0 : ℝ)..(x - inghamWidth p (n + 1)), inghamPartial p n t) := by
    funext x
    show convolution _ _ _ _ x = _
    rw [convolution_boxTest_apply hε, intervalIntegral.integral_interval_sub_left (hII _ _)
      (hII _ _)]
  rw [heq]
  have hprim := intervalIntegral.continuous_primitive hII 0
  exact continuous_const.mul ((hprim.comp (continuous_id.add continuous_const)).sub
    (hprim.comp (continuous_id.sub continuous_const)))

/-- The transform of a continuous integrable function is continuous on the real line. -/
theorem continuous_paperFT_ofReal {k : ℝ → ℂ} (hk : Integrable k) :
    Continuous fun r : ℝ => paperFT k r := by
  simp only [paperFT]
  refine continuous_of_dominated (bound := fun u => ‖k u‖) (fun r => ?_) (fun r => ?_) hk.norm ?_
  · exact hk.aestronglyMeasurable.mul (by fun_prop : Continuous fun u : ℝ =>
      cexp (I * (r : ℂ) * u)).aestronglyMeasurable
  · refine Eventually.of_forall fun u => ?_
    rw [norm_mul, Complex.norm_exp]
    simp
  · exact Eventually.of_forall fun u => by fun_prop

/-- Two sinc factors give quadratic decay: `|sinc(ax) sinc(bx)| ≤ 2/(1 + abx²)`. -/
theorem norm_sincC_mul_sincC_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    ‖sincC ((a : ℂ) * x)‖ * ‖sincC ((b : ℂ) * x)‖ ≤ 2 * (1 + a * b * x ^ 2)⁻¹ := by
  have hpos : 0 < 1 + a * b * x ^ 2 := by positivity
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  by_cases ht : a * b * x ^ 2 ≤ 1
  · have h1 := norm_sincC_ofReal_le_one (a * x)
    have h2 := norm_sincC_ofReal_le_one (b * x)
    have : (1 : ℝ) ≤ 2 * (1 + a * b * x ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ hpos]; linarith
    calc ‖sincC ((a * x : ℝ) : ℂ)‖ * ‖sincC ((b * x : ℝ) : ℂ)‖ ≤ 1 * 1 :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ ≤ _ := by linarith
  · push Not at ht
    have hx : x ≠ 0 := by rintro rfl; simp at ht; linarith
    have hax : a * x ≠ 0 := mul_ne_zero ha.ne' hx
    have hbx : b * x ≠ 0 := mul_ne_zero hb.ne' hx
    have h1 := norm_sincC_ofReal_le_inv (a * x) hax
    have h2 := norm_sincC_ofReal_le_inv (b * x) hbx
    have hprod : |a * x|⁻¹ * |b * x|⁻¹ = (a * b * x ^ 2)⁻¹ := by
      rw [← mul_inv, ← abs_mul, show a * x * (b * x) = a * b * x ^ 2 by ring,
        abs_of_pos (by positivity)]
    calc ‖sincC ((a * x : ℝ) : ℂ)‖ * ‖sincC ((b * x : ℝ) : ℂ)‖ ≤ |a * x|⁻¹ * |b * x|⁻¹ :=
          mul_le_mul h1 h2 (norm_nonneg _) (inv_nonneg.mpr (abs_nonneg _))
      _ = (a * b * x ^ 2)⁻¹ := hprod
      _ ≤ 2 * (1 + a * b * x ^ 2)⁻¹ := by
          rw [show 2 * (1 + a * b * x ^ 2)⁻¹ = ((1 + a * b * x ^ 2) / 2)⁻¹ by field_simp]
          exact inv_anti₀ (by positivity) (by linarith)

/-- The quadratic envelope `2/(1 + ε₀ε₁x²)` of the partial transforms. -/
def inghamEnvelope (p : ℝ) (x : ℝ) : ℝ := 2 * (1 + inghamWidth p 0 * inghamWidth p 1 * x ^ 2)⁻¹

theorem integrable_inghamEnvelope (p : ℝ) : Integrable (inghamEnvelope p) := by
  have hc : 0 < inghamWidth p 0 * inghamWidth p 1 :=
    mul_pos (inghamWidth_pos p 0) (inghamWidth_pos p 1)
  have h := (integrable_inv_one_add_sq.comp_mul_left'
    (R := Real.sqrt (inghamWidth p 0 * inghamWidth p 1)) (Real.sqrt_pos.mpr hc).ne').const_mul 2
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [inghamEnvelope]
  rw [mul_pow, Real.sq_sqrt hc.le]

theorem norm_paperFT_inghamPartial_le (p : ℝ) (n : ℕ) (x : ℝ) :
    ‖paperFT (inghamPartial p (n + 1)) x‖ ≤ inghamEnvelope p x := by
  rw [paperFT_inghamPartial, norm_prod, Finset.prod_range_succ', Finset.prod_range_succ']
  have hrest : ∏ k ∈ range n, ‖sincC ((inghamWidth p (k + 1 + 1) : ℂ) * x)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) fun k _ => by
      rw [← Complex.ofReal_mul]; exact norm_sincC_ofReal_le_one _
  have h01 := norm_sincC_mul_sincC_le (inghamWidth_pos p 0) (inghamWidth_pos p 1) x
  have hnn : 0 ≤ ‖sincC ((inghamWidth p 0 : ℂ) * x)‖ * ‖sincC ((inghamWidth p 1 : ℂ) * x)‖ :=
    by positivity
  calc (∏ k ∈ range n, ‖sincC ((inghamWidth p (k + 1 + 1) : ℂ) * x)‖) *
        ‖sincC ((inghamWidth p (0 + 1) : ℂ) * x)‖ * ‖sincC ((inghamWidth p 0 : ℂ) * x)‖
      = (∏ k ∈ range n, ‖sincC ((inghamWidth p (k + 1 + 1) : ℂ) * x)‖) *
          (‖sincC ((inghamWidth p 0 : ℂ) * x)‖ * ‖sincC ((inghamWidth p 1 : ℂ) * x)‖) := by ring
    _ ≤ 1 * (‖sincC ((inghamWidth p 0 : ℂ) * x)‖ * ‖sincC ((inghamWidth p 1 : ℂ) * x)‖) :=
        mul_le_mul_of_nonneg_right hrest hnn
    _ ≤ inghamEnvelope p x := by rw [one_mul]; exact h01

theorem integrable_paperFT_inghamPartial (p : ℝ) (n : ℕ) :
    Integrable fun r : ℝ => paperFT (inghamPartial p (n + 1)) r :=
  (integrable_inghamEnvelope p).mono'
    (continuous_paperFT_ofReal (inghamPartial_integrable_hasCompactSupport p (n + 1)).1).aestronglyMeasurable
    (Eventually.of_forall (norm_paperFT_inghamPartial_le p n))

/-- **Inversion for the partial bumps.** -/
theorem inghamPartial_eq_invFT (p : ℝ) (n : ℕ) (u : ℝ) :
    inghamPartial p (n + 1) u = invFT (fun r : ℝ => paperFT (inghamPartial p (n + 1)) r) u :=
  eq_invFT_paperFT (continuous_inghamPartial_succ p n)
    (inghamPartial_integrable_hasCompactSupport p (n + 1)).1 (integrable_paperFT_inghamPartial p n) u

/-! ### 7. Stretched-exponential envelopes have all moments -/

/-- `K tˢ` is absorbed by half of `c t^q` up to a constant when `s < q`. -/
theorem exists_mul_rpow_le_half_rpow {K c s q : ℝ} (hs : 0 ≤ s) (hsq : s < q) (hc : 0 < c) :
    ∃ C₁ : ℝ, ∀ t : ℝ, 0 ≤ t → K * t ^ s ≤ c / 2 * t ^ q + C₁ := by
  set K' := max K 0
  set T₀ : ℝ := max 1 ((2 * K' / c) ^ (1 / (q - s)))
  have hT₀ : 1 ≤ T₀ := le_max_left _ _
  refine ⟨K' * T₀ ^ s, fun t ht => ?_⟩
  have hK : K * t ^ s ≤ K' * t ^ s :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht _)
  have hK' : 0 ≤ K' := le_max_right _ _
  by_cases htT : t ≤ T₀
  · have : K' * t ^ s ≤ K' * T₀ ^ s :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht htT hs) hK'
    have : 0 ≤ c / 2 * t ^ q := by positivity
    linarith
  · push Not at htT
    have ht1 : 1 < t := hT₀.trans_lt htT
    have ht0 : 0 < t := by linarith
    have hqs : 0 < q - s := by linarith
    have hsplit : t ^ q = t ^ s * t ^ (q - s) := by
      rw [← Real.rpow_add ht0]; ring_nf
    have hbig : 2 * K' / c ≤ t ^ (q - s) := by
      have h1 : (2 * K' / c) = ((2 * K' / c) ^ (1 / (q - s))) ^ (q - s) := by
        rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hqs.ne', Real.rpow_one]
      rw [h1]
      exact Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans htT.le) hqs.le
    have : K' * t ^ s ≤ c / 2 * t ^ q := by
      rw [hsplit]
      have hts : 0 ≤ t ^ s := Real.rpow_nonneg ht0.le _
      have := mul_le_mul_of_nonneg_left hbig hts
      have hc2 : c / 2 * (t ^ s * (2 * K' / c)) = K' * t ^ s := by field_simp
      nlinarith
    have : 0 ≤ K' * T₀ ^ s := by positivity
    linarith

/-- A stretched-exponential envelope beats every polynomial: `(1 + t²) tⁿ e^{K tˢ − c t^q}` is
bounded on `t ≥ 0` when `0 ≤ s < q`. -/
theorem exists_bound_mul_exp_rpow {K c s q : ℝ} (hs : 0 ≤ s) (hsq : s < q) (hc : 0 < c) (n : ℕ) :
    ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → (1 + t ^ 2) * t ^ n * Real.exp (K * t ^ s - c * t ^ q) ≤ M := by
  obtain ⟨C₁, hC₁⟩ := exists_mul_rpow_le_half_rpow (K := K) hs hsq hc
  have hq : 0 < q := lt_of_le_of_lt hs hsq
  set m : ℕ := ⌈((n : ℝ) + 2) / q⌉₊
  have hm : (n : ℝ) + 2 ≤ q * m := by
    have := Nat.le_ceil (((n : ℝ) + 2) / q)
    rw [div_le_iff₀ hq] at this; linarith
  set C₂ : ℝ := 2 + 2 * (m.factorial : ℝ) / (c / 2) ^ m
  refine ⟨Real.exp C₁ * C₂, fun t ht => ?_⟩
  have hexp : Real.exp (K * t ^ s - c * t ^ q) ≤ Real.exp C₁ * Real.exp (-(c / 2 * t ^ q)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith [hC₁ t ht]
  have hB : (1 + t ^ 2) * t ^ n * Real.exp (-(c / 2 * t ^ q)) ≤ C₂ := by
    have hC₂ : 2 ≤ C₂ := by
      have : 0 ≤ 2 * (m.factorial : ℝ) / (c / 2) ^ m := by positivity
      linarith
    by_cases ht1 : t ≤ 1
    · have h1 : (1 + t ^ 2) * t ^ n ≤ 2 := by
        have : t ^ 2 ≤ 1 := pow_le_one₀ ht ht1
        have : t ^ n ≤ 1 := pow_le_one₀ ht ht1
        nlinarith [pow_nonneg ht n]
      have h2 : Real.exp (-(c / 2 * t ^ q)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; have := Real.rpow_nonneg ht q; nlinarith
      calc (1 + t ^ 2) * t ^ n * Real.exp (-(c / 2 * t ^ q)) ≤ 2 * 1 :=
            mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num)
        _ ≤ C₂ := by linarith
    · push Not at ht1
      have ht0 : 0 < t := by linarith
      set y := c / 2 * t ^ q
      have hy : 0 < y := by positivity
      have hfac := Real.pow_div_factorial_le_exp (x := y) hy.le m
      have hexpy : Real.exp (-y) ≤ (m.factorial : ℝ) / y ^ m := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
        exact hfac
      have hym : y ^ m = (c / 2) ^ m * t ^ (q * m) := by
        rw [mul_pow, ← Real.rpow_natCast (t ^ q), ← Real.rpow_mul ht0.le]
      have hpoly : (1 + t ^ 2) * t ^ n ≤ 2 * t ^ (q * m) := by
        have h1 : (1 + t ^ 2) * t ^ n ≤ 2 * t ^ (n + 2) := by
          have : 1 ≤ t ^ 2 := one_le_pow₀ ht1.le
          rw [pow_add]; nlinarith [pow_nonneg ht0.le n]
        have h2 : t ^ (n + 2) ≤ t ^ (q * m) := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le ht1.le (by push_cast; linarith)
        linarith
      calc (1 + t ^ 2) * t ^ n * Real.exp (-y) ≤ 2 * t ^ (q * m) * ((m.factorial : ℝ) / y ^ m) :=
            mul_le_mul hpoly hexpy (Real.exp_pos _).le (by positivity)
        _ = 2 * (m.factorial : ℝ) / (c / 2) ^ m := by
            rw [hym]
            have : t ^ (q * m) ≠ 0 := (Real.rpow_pos_of_pos ht0 _).ne'
            have : (c / 2) ^ m ≠ 0 := by positivity
            field_simp
        _ ≤ C₂ := by linarith
  calc (1 + t ^ 2) * t ^ n * Real.exp (K * t ^ s - c * t ^ q)
      ≤ (1 + t ^ 2) * t ^ n * (Real.exp C₁ * Real.exp (-(c / 2 * t ^ q))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = Real.exp C₁ * ((1 + t ^ 2) * t ^ n * Real.exp (-(c / 2 * t ^ q))) := by ring
    _ ≤ Real.exp C₁ * C₂ := mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le

/-- **All moments of a stretched-exponentially decaying function are integrable.** -/
theorem integrable_moment_of_le_exp_rpow {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    {K c s q : ℝ} (hs : 0 ≤ s) (hsq : s < q) (hc : 0 < c)
    (hb : ∀ x : ℝ, ‖f x‖ ≤ Real.exp (K * |x| ^ s - c * |x| ^ q)) (n : ℕ) :
    Integrable fun x : ℝ => ‖x‖ ^ n * ‖f x‖ := by
  obtain ⟨M, hM⟩ := exists_bound_mul_exp_rpow (K := K) hs hsq hc n
  refine (integrable_inv_one_add_sq.const_mul M).mono'
    ((continuous_norm.pow n).aestronglyMeasurable.mul hf.norm) (Eventually.of_forall fun x => ?_)
  have h := hM |x| (abs_nonneg x)
  rw [sq_abs] at h
  have hpos : 0 < 1 + x ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (norm_nonneg _),
    Real.norm_eq_abs, le_mul_inv_iff₀ hpos]
  calc |x| ^ n * ‖f x‖ * (1 + x ^ 2) ≤ |x| ^ n * Real.exp (K * |x| ^ s - c * |x| ^ q) * (1 + x ^ 2) := by
        gcongr; exact hb x
    _ = (1 + x ^ 2) * |x| ^ n * Real.exp (K * |x| ^ s - c * |x| ^ q) := by ring
    _ ≤ M := h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
