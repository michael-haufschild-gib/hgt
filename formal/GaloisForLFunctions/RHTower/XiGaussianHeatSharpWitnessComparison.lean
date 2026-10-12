import GaloisForLFunctions.RHTower.XiGaussianHeatSharpWitnessEstimates
import GaloisForLFunctions.RHTower.XiGaussianHeatPoleHyperplaneCriterion

/-!
# Comparing the corrected truncated heat test with the smoothed source on the zeros

**Zero-sum comparison** (`norm_tsum_sq_sub_le`).  If `|F_q − G_q| ≤ D` and `|z_q|² |F_q| ≤ M_F`,
`|z_q|² |G_q| ≤ M_G` at every zero copy, then `|Σ F_q² − Σ G_q²| ≤ D (M_F + M_G) Σ_q |z_q|^{-2}`.

**Integrability on the strip** (`integrable_abs_heatSmooth_mul_exp`).  The heat-smoothed source is
strip-integrable: it is bounded and has Gaussian tails.
-/

open scoped Real
open Complex MeasureTheory Set Polynomial Filter Topology
open GaloisForLFunctions (gaussPolyFun gaussPolyDerivPoly hasDerivAt_gaussPolyFun continuous_gaussPolyFun
  sq_integral_abs_gaussPolyFun_mul_exp_half_le)

namespace RHTower

noncomputable section

/-- **Comparison of zero sums of squares through the second derivative.** -/
theorem norm_tsum_sq_sub_le {F G : XiZeroCopy → ℂ} {D MF MG : ℝ}
    (hD : ∀ q, ‖F q - G q‖ ≤ D) (hF : ∀ q, ‖xiSpectralPoint q‖ ^ 2 * ‖F q‖ ≤ MF)
    (hG : ∀ q, ‖xiSpectralPoint q‖ ^ 2 * ‖G q‖ ≤ MG) :
    Summable (fun q => F q ^ 2) ∧ Summable (fun q => G q ^ 2) ∧
      ‖(∑' q, F q ^ 2) - ∑' q, G q ^ 2‖ ≤
        D * (MF + MG) * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
  have hpos : ∀ q, 0 < ‖xiSpectralPoint q‖ := fun q => norm_pos_iff.2 (xiSpectralPoint_ne_zero q)
  have h1 : ∀ q, 1 ≤ ‖xiSpectralPoint q‖ ^ 2 := fun q => by
    have := oneHundredFifty_lt_norm_xiSpectralPoint_sq q; linarith
  have hS := xiSpectralPoint_inv_sq_summable
  have hFb : ∀ q, ‖F q‖ ≤ MF / ‖xiSpectralPoint q‖ ^ 2 := fun q => by
    rw [le_div_iff₀ (by have := hpos q; positivity), mul_comm]; exact hF q
  have hGb : ∀ q, ‖G q‖ ≤ MG / ‖xiSpectralPoint q‖ ^ 2 := fun q => by
    rw [le_div_iff₀ (by have := hpos q; positivity), mul_comm]; exact hG q
  have hMF : 0 ≤ MF := (mul_nonneg (by positivity) (norm_nonneg _)).trans (hF (Classical.arbitrary _))
  have hMG : 0 ≤ MG := (mul_nonneg (by positivity) (norm_nonneg _)).trans (hG (Classical.arbitrary _))
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD (Classical.arbitrary _))
  have hsq : ∀ (H : XiZeroCopy → ℂ) (M : ℝ), 0 ≤ M → (∀ q, ‖H q‖ ≤ M / ‖xiSpectralPoint q‖ ^ 2) →
      Summable (fun q => H q ^ 2) := fun H M hM hH => by
    refine Summable.of_norm_bounded (hS.mul_left (M ^ 2)) fun q => ?_
    rw [norm_pow]
    have hz := h1 q
    have hz0 : 0 < ‖xiSpectralPoint q‖ ^ 2 := by have := hpos q; positivity
    calc ‖H q‖ ^ 2 ≤ (M / ‖xiSpectralPoint q‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hH q) 2
      _ = M ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring
      _ ≤ M ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) * 1 := by
          gcongr
          rw [div_le_one hz0]; exact hz
      _ = M ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring
  have hFs := hsq F MF hMF hFb
  have hGs := hsq G MG hMG hGb
  refine ⟨hFs, hGs, ?_⟩
  have hterm : ∀ q, ‖F q ^ 2 - G q ^ 2‖ ≤ D * (MF + MG) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) :=
    fun q => by
    rw [show F q ^ 2 - G q ^ 2 = (F q - G q) * (F q + G q) by ring, norm_mul]
    calc ‖F q - G q‖ * ‖F q + G q‖ ≤ D * (MF / ‖xiSpectralPoint q‖ ^ 2 +
          MG / ‖xiSpectralPoint q‖ ^ 2) :=
          mul_le_mul (hD q) ((norm_add_le _ _).trans (add_le_add (hFb q) (hGb q)))
            (norm_nonneg _) hD0
      _ = D * (MF + MG) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring
  rw [← hFs.tsum_sub hGs]
  refine (norm_tsum_le_tsum_norm ((hFs.sub hGs).norm)).trans ?_
  rw [← tsum_mul_left]
  exact (hFs.sub hGs).norm.tsum_le_tsum hterm (hS.mul_left _)

/-- The heat-smoothed source is bounded by the supremum of the source. -/
theorem abs_heatSmooth_le_sup {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} {B : ℝ} (hB : ∀ t, |u t| ≤ B)
    (x : ℝ) :
    |heatSmooth a u x| ≤ B := by
  have hG1 : ∫ y : ℝ, gaussHeatKernel a y = 1 := by
    have h := heatStripTransform_heatKernel ha 0
    unfold heatStripTransform at h
    simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one, zero_pow two_ne_zero,
      zero_div] at h
    rw [integral_complex_ofReal] at h
    exact_mod_cast h
  have hGi : Integrable (fun t : ℝ => gaussHeatKernel a (x - t)) := by
    have : Integrable (fun y : ℝ => gaussHeatKernel a y) := by
      refine ((integrable_exp_neg_mul_sq (b := 1 / (2 * a)) (by positivity)).const_mul
        ((2 * π * a) ^ (-(1 / 2 : ℝ)))).congr (Filter.Eventually.of_forall fun y => ?_)
      simp only [gaussHeatKernel]
      congr 2
      field_simp
    exact this.comp_sub_left x
  rw [heatSmooth]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ t : ℝ, |u t * gaussHeatKernel a (x - t)| ≤ ∫ t : ℝ, B * gaussHeatKernel a (x - t) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (hGi.const_mul B) (Filter.Eventually.of_forall fun t => ?_)
        simp only
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg ha _)]
        exact mul_le_mul_of_nonneg_right (hB t) (heatKernel_nonneg ha _)
    _ = B := by rw [integral_const_mul, integral_sub_left_eq_self, hG1, mul_one]

/-- **The heat-smoothed source is strip-integrable.** -/
theorem integrable_abs_heatSmooth_mul_exp {a A : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16) {u : ℝ → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcpt : HasCompactSupport u)
    (hsupp : ∀ t : ℝ, A < |t| → u t = 0) :
    Integrable (fun x => |heatSmooth a u x| * Real.exp (|x| / 2)) := by
  set X := max 1 (2 * A) with hX
  have hX1 : 1 ≤ X := le_max_left _ _
  have hXA : 2 * A ≤ X := le_max_right _ _
  obtain ⟨htail, -⟩ := integrableOn_tail_heatSmooth hu hcpt hsupp ha ha16 hX1 hXA
  have hcont : Continuous fun x => |heatSmooth a u x| * Real.exp (|x| / 2) :=
    (continuous_abs.comp (continuous_heatSmooth hu hcpt ha)).mul
      (Real.continuous_exp.comp (continuous_abs.div_const 2))
  have hinner : IntegrableOn (fun x => |heatSmooth a u x| * Real.exp (|x| / 2)) (Ioo (-X) X) :=
    hcont.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hunion : heatTailSet X ∪ Ioo (-X) X = univ := by
    rw [← heatTailSet_compl]; exact union_compl_self _
  rw [← integrableOn_univ, ← hunion]
  exact htail.union hinner

/-- The pole value of an even source vanishes with its exponential moment. -/
theorem heatStripTransform_I_half_eq_zero {u : ℝ → ℝ} (heven : ∀ x, u (-x) = u x)
    (hpole : ∫ x, u x * Real.exp (x / 2) = 0) :
    heatStripTransform (fun x => ((u x : ℝ) : ℂ)) (I / 2) = 0 := by
  unfold heatStripTransform
  have h1 : ∀ x : ℝ, ((u x : ℝ) : ℂ) * Complex.exp (I * (I / 2) * x) =
      ((u x * Real.exp (-x / 2) : ℝ) : ℂ) := fun x => by
    push_cast
    congr 2
    ring_nf
    rw [I_sq]
    ring
  simp_rw [h1]
  rw [integral_complex_ofReal, ← integral_neg_eq_self]
  simp only [heven, neg_neg]
  rw [show (fun x : ℝ => u x * Real.exp (x / 2)) = fun x => u x * Real.exp (x / 2) from rfl, hpole,
    Complex.ofReal_zero]

/-- `|e^{-az²/2}| ≤ e^{a/8}` on the strip. -/
theorem norm_cexp_heat_le {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖Complex.exp (-(a : ℂ) * z ^ 2 / 2)‖ ≤ Real.exp (a / 8) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  have hre : (-(a : ℂ) * z ^ 2 / 2).re = -(a * (z.re ^ 2 - z.im ^ 2)) / 2 := by
    simp [pow_two]
  rw [hre]
  have : z.im ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg z.im, sq_abs z.im]
  nlinarith [sq_nonneg z.re]

/-- **Cross terms of the heat Hankel form.**  If `|z|² |e^{-az²/2} P(z²)| ≤ M` on the strip,
then `|H_a(P, 1)|, |H_a(1, P)| ≤ e^{a/8} M Σ_q |z_q|^{-2}`. -/
theorem norm_heatHankel_one_le {a : ℝ} (ha : 0 ≤ a) {P : ℂ[X]} {M : ℝ}
    (hM : ∀ z : ℂ, |z.im| ≤ 1 / 2 →
      ‖z‖ ^ 2 * ‖Complex.exp (-(a : ℂ) * z ^ 2 / 2) * P.eval (z ^ 2)‖ ≤ M) :
    ‖heatHankel a P 1‖ ≤ Real.exp (a / 8) * M * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 ∧
      ‖heatHankel a 1 P‖ ≤ Real.exp (a / 8) * M * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
  have hS := xiSpectralPoint_inv_sq_summable
  have hpos : ∀ q, 0 < ‖xiSpectralPoint q‖ := fun q => norm_pos_iff.2 (xiSpectralPoint_ne_zero q)
  have hz : ∀ q, |(xiSpectralPoint q).im| ≤ 1 / 2 := abs_im_xiSpectralPoint_le_half
  have hzc : ∀ q, |((starRingEnd ℂ) (xiSpectralPoint q)).im| ≤ 1 / 2 := fun q => by
    rw [Complex.conj_im, abs_neg]; exact hz q
  have hsplit : ∀ z : ℂ, Complex.exp (-(a : ℂ) * z ^ 2) =
      Complex.exp (-(a : ℂ) * z ^ 2 / 2) * Complex.exp (-(a : ℂ) * z ^ 2 / 2) := fun z => by
    rw [← Complex.exp_add]; ring_nf
  have hgen : ∀ q, ∀ v : ℂ, ‖v‖ = ‖xiSpectralPoint q‖ → |v.im| ≤ 1 / 2 →
      ‖Complex.exp (-(a : ℂ) * (xiSpectralPoint q) ^ 2 / 2)‖ *
        ‖Complex.exp (-(a : ℂ) * v ^ 2 / 2) * P.eval (v ^ 2)‖ ≤
        Real.exp (a / 8) * M * (1 / ‖xiSpectralPoint q‖ ^ 2) := fun q v hv hvim => by
    have h1 := norm_cexp_heat_le ha (hz q)
    have h2 := hM v hvim
    rw [hv] at h2
    have hq := hpos q
    have h3 : ‖Complex.exp (-(a : ℂ) * v ^ 2 / 2) * P.eval (v ^ 2)‖ ≤
        M / ‖xiSpectralPoint q‖ ^ 2 := by
      rw [le_div_iff₀ (by positivity), mul_comm]; exact h2
    calc ‖Complex.exp (-(a : ℂ) * (xiSpectralPoint q) ^ 2 / 2)‖ *
          ‖Complex.exp (-(a : ℂ) * v ^ 2 / 2) * P.eval (v ^ 2)‖
        ≤ Real.exp (a / 8) * (M / ‖xiSpectralPoint q‖ ^ 2) :=
          mul_le_mul h1 h3 (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by ring
  have hterm1 : ∀ q, ‖heatHankelTermAt a P 1 (xiHeatFrequency q)‖ ≤
      Real.exp (a / 8) * M * (1 / ‖xiSpectralPoint q‖ ^ 2) := fun q => by
    have e : heatHankelTermAt a P 1 (xiHeatFrequency q) =
        Complex.exp (-(a : ℂ) * (xiSpectralPoint q) ^ 2 / 2) *
          (Complex.exp (-(a : ℂ) * (xiSpectralPoint q) ^ 2 / 2) *
            P.eval ((xiSpectralPoint q) ^ 2)) := by
      rw [heatHankelTermAt, eval_one, map_one, mul_one, show xiHeatFrequency q =
        xiSpectralPoint q ^ 2 from rfl, hsplit]
      ring
    rw [e, norm_mul]
    exact hgen q _ rfl (hz q)
  have hterm2 : ∀ q, ‖heatHankelTermAt a 1 P (xiHeatFrequency q)‖ ≤
      Real.exp (a / 8) * M * (1 / ‖xiSpectralPoint q‖ ^ 2) := fun q => by
    set z := xiSpectralPoint q
    have hconj : (starRingEnd ℂ) (Complex.exp (-(a : ℂ) * ((starRingEnd ℂ) z) ^ 2 / 2)) =
        Complex.exp (-(a : ℂ) * z ^ 2 / 2) := by
      rw [← Complex.exp_conj]; congr 1; simp [map_div₀, map_ofNat]
    have e : heatHankelTermAt a 1 P (xiHeatFrequency q) =
        Complex.exp (-(a : ℂ) * z ^ 2 / 2) * (starRingEnd ℂ)
          (Complex.exp (-(a : ℂ) * ((starRingEnd ℂ) z) ^ 2 / 2) *
            P.eval (((starRingEnd ℂ) z) ^ 2)) := by
      rw [heatHankelTermAt, eval_one, mul_one, show xiHeatFrequency q = z ^ 2 from rfl, hsplit,
        map_mul, hconj, map_pow]
      ring
    rw [e, norm_mul, Complex.norm_conj]
    exact hgen q _ (Complex.norm_conj z) (hzc q)
  have hsum := hS.mul_left (Real.exp (a / 8) * M)
  refine ⟨?_, ?_⟩
  · unfold heatHankel
    calc ‖∑' q : XiZeroCopy, heatHankelTermAt a P 1 (xiHeatFrequency q)‖
        ≤ ∑' q : XiZeroCopy, Real.exp (a / 8) * M * (1 / ‖xiSpectralPoint q‖ ^ 2) :=
          tsum_of_norm_bounded hsum.hasSum hterm1
      _ = _ := tsum_mul_left
  · unfold heatHankel
    calc ‖∑' q : XiZeroCopy, heatHankelTermAt a 1 P (xiHeatFrequency q)‖
        ≤ ∑' q : XiZeroCopy, Real.exp (a / 8) * M * (1 / ‖xiSpectralPoint q‖ ^ 2) :=
          tsum_of_norm_bounded hsum.hasSum hterm2
      _ = _ := tsum_mul_left

end

end RHTower
