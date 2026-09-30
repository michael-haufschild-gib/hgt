import GaloisForLFunctions.RHTower.ZetaVerticalMeanSquare
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiUniformMovingLeftLine
import GaloisForLFunctions.HTGeometry.HolomorphicBallMeanSq

/-!
# `ζ` is at most `T^ε` near almost every height

For `0 < ε ≤ 1` and every `δ > 0`, for all large `T`, the heights `t ∈ [T, 2T]` for which some `z`
with `½ ≤ Re z ≤ 2`, `|Im z − t| ≤ 2` has `|ζ(z)| > T^ε` form a set of measure at most `δT`
(`eventually_volume_zetaLargeNear_le`).

The entire function `(z − 1)ζ(z)` satisfies the area mean-value inequality on discs of radius
`r = ε/4`. A disc around a large value near height `t` lies in the box
`[½ − r, 5/2] × [s − 3, s + 4]` of the unit cell `[s, s + 1] ∋ t`. The cells tile `[T, 2T]`, every
height lies in at most seven boxes, and the box integrals are vertical mean squares: on `Re ≥ ½` by
`exists_integral_normSq_zeta_vertical_le`, left of the line by the functional equation
`|ζ(½ − d + iy)| ≤ K y^d |ζ(½ + d + iy)|`. Markov's inequality over the cells bounds the number of
cells carrying a large value by `O(T^{1 − ε})`.
-/

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

/-! ## Boxes, discs and iterated integrals -/

/-- The integral of a continuous function over a box is the iterated integral. -/
theorem setIntegral_reProdIm_eq_iterated {f : ℂ → ℝ} (hf : Continuous f) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ z in Icc a b ×ℂ Icc c d, f z = ∫ x in a..b, ∫ y in c..d, f ((x : ℂ) + (y : ℂ) * I) := by
  let G : ℝ × ℝ → ℝ := fun p => f ((p.1 : ℂ) + (p.2 : ℂ) * I)
  have hGc : Continuous G := hf.comp (by fun_prop)
  have hpre : (Icc a b ×ℂ Icc c d) = measurableEquivRealProd ⁻¹' (Icc a b ×ˢ Icc c d) := by
    ext z
    simp only [Complex.mem_reProdIm, mem_preimage, mem_prod, mem_Icc]
    simp [Complex.measurableEquivRealProd]
  have hG : ∀ z : ℂ, G (measurableEquivRealProd z) = f z := by
    intro z
    simp [G, Complex.measurableEquivRealProd, Complex.re_add_im]
  have hp := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding G (Icc a b ×ˢ Icc c d)
  have hint : Integrable G ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hGc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  calc ∫ z in Icc a b ×ℂ Icc c d, f z
      = ∫ z in measurableEquivRealProd ⁻¹' (Icc a b ×ˢ Icc c d), G (measurableEquivRealProd z) := by
        rw [hpre]; simp only [hG]
    _ = ∫ p in Icc a b ×ˢ Icc c d, G p := hp
    _ = ∫ x in Icc a b, ∫ y in Icc c d, G (x, y) := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod G hint]
    _ = ∫ x in a..b, ∫ y in c..d, f ((x : ℂ) + (y : ℂ) * I) := by
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
        refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
        rw [intervalIntegral.integral_of_le hcd, ← integral_Icc_eq_integral_Ioc]

/-- **Area mean value against a box.** For an entire `F` and a disc of radius `r` around `z`
inside the box `[a, b] × [c, d]`, `π r² |F(z)|² ≤ ∫_a^b ∫_c^d |F(x + iy)|² dy dx`. -/
theorem normSq_mul_area_le_box {F : ℂ → ℂ} (hF : Differentiable ℂ F) {z : ℂ} {r a b c d : ℝ}
    (hr : 0 < r) (ha : a ≤ z.re - r) (hb : z.re + r ≤ b) (hc : c ≤ z.im - r)
    (hd : z.im + r ≤ d) :
    Real.pi * r ^ 2 * ‖F z‖ ^ 2 ≤ ∫ x in a..b, ∫ y in c..d, ‖F ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 := by
  have hcont : Continuous fun w : ℂ => ‖F w‖ ^ 2 := hF.continuous.norm.pow 2
  have hsub : Metric.ball z r ⊆ Icc a b ×ℂ Icc c d := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have h1 := (abs_le.mp ((Complex.abs_re_le_norm (w - z)).trans hw.le))
    have h2 := (abs_le.mp ((Complex.abs_im_le_norm (w - z)).trans hw.le))
    simp only [Complex.sub_re, Complex.sub_im] at h1 h2
    exact Complex.mem_reProdIm.mpr ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hbox : IsCompact (Icc a b ×ℂ Icc c d) := isCompact_Icc.reProdIm isCompact_Icc
  calc Real.pi * r ^ 2 * ‖F z‖ ^ 2 ≤ ∫ w in Metric.ball z r, ‖F w‖ ^ 2 :=
        GaloisForLFunctions.HTGeometry.normSq_value_mul_area_le_integral_ball F hF z hr
    _ ≤ ∫ w in Icc a b ×ℂ Icc c d, ‖F w‖ ^ 2 :=
        setIntegral_mono_set (hcont.continuousOn.integrableOn_compact hbox)
          (Filter.Eventually.of_forall fun w => by positivity) hsub.eventuallyLE
    _ = _ := setIntegral_reProdIm_eq_iterated hcont (by linarith) (by linarith)

/-! ## Vertical mean squares of `(z − 1)ζ(z)` on columns -/

/-- **Reflection across the critical line.** If `|χ(½ − d + iy)| ≤ K max(1, |y|)^d`, then
`|ζ(½ − d + iy)|² ≤ (K Y^d)² |ζ(½ + d + iy)|²` for `1 ≤ y ≤ Y`. -/
theorem normSq_zeta_left_le {K d y Y : ℝ} (hK0 : 0 ≤ K) (hd0 : 0 ≤ d)
    (hχ : ‖zetaChi (((1 / 2 - d : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ K * (max 1 |y|) ^ d)
    (hy : 1 ≤ y) (hyY : y ≤ Y) :
    ‖riemannZeta (((1 / 2 - d : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤
      (K * Y ^ d) ^ 2 * ‖riemannZeta (((1 / 2 + d : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 2 := by
  set s : ℂ := ((1 / 2 - d : ℝ) : ℂ) + (y : ℂ) * I with hs
  have hsim : s.im = y := by simp [hs]
  have hs0 : s ≠ 0 := by intro h; have := congrArg Complex.im h; rw [hsim] at this; simp at this; linarith
  have hs1 : s ≠ 1 := by intro h; have := congrArg Complex.im h; rw [hsim] at this; simp at this; linarith
  have hG : Gammaℝ (1 - s) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by simp [hs]; linarith)
  have hconj : 1 - s = (starRingEnd ℂ) (((1 / 2 + d : ℝ) : ℂ) + (y : ℂ) * I) := by
    apply Complex.ext <;> simp [hs]; ring
  have hmax : max 1 |y| = y := by rw [abs_of_pos (by linarith)]; exact max_eq_right hy
  have hχ' : ‖zetaChi s‖ ≤ K * Y ^ d := by
    refine hχ.trans ?_
    rw [hmax]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hyY hd0) hK0
  rw [zeta_eq_zetaChi_mul hs0 hs1 hG, hconj, riemannZeta_conj, norm_mul, Complex.norm_conj, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hχ' 2) (by positivity)

theorem continuousOn_normSq_zeta_vertical (σ : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun y : ℝ => ‖riemannZeta ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2) (Icc a b) := by
  intro y hy
  have hne : (σ : ℂ) + (y : ℂ) * I ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith [hy.1]
  exact (ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I)
    (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)).norm.pow 2
    |>.continuousWithinAt

theorem one_add_log_cube_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    (1 + Real.log x) ^ 3 ≤ (1 + Real.log y) ^ 3 := by
  have h0 : 0 ≤ 1 + Real.log x := by linarith [Real.log_nonneg hx]
  exact pow_le_pow_left₀ h0 (by linarith [Real.log_le_log (by linarith) hxy]) 3

/-- **Mean square on a vertical span.** From the dyadic mean-square bound, every span
`[Y₁, Y₂] ⊆ [T/2, 4T]` carries `∫ |ζ(σ + iy)|² ≤ 4C T (1 + log 4T)³` for `½ ≤ σ ≤ 3`. -/
theorem integral_normSq_zeta_span_le {C : ℝ} (hC : 0 < C)
    (hA1 : ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 3 →
      ∫ t in T..(2 * T), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ C * T * (1 + Real.log T) ^ 3)
    {T σ Y₁ Y₂ : ℝ} (hT : 4 ≤ T) (hσ : 1 / 2 ≤ σ) (hσ3 : σ ≤ 3) (h1 : T / 2 ≤ Y₁)
    (h12 : Y₁ ≤ Y₂) (h2 : Y₂ ≤ 4 * T) :
    ∫ y in Y₁..Y₂, ‖riemannZeta ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤
      4 * C * T * (1 + Real.log (4 * T)) ^ 3 := by
  set g : ℝ → ℝ := fun y => ‖riemannZeta ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2 with hg
  have hcont : ContinuousOn g (Icc (T / 2) (4 * T)) :=
    continuousOn_normSq_zeta_vertical σ (by linarith)
  have hii : ∀ a b : ℝ, T / 2 ≤ a → a ≤ b → b ≤ 4 * T → IntervalIntegrable g volume a b := by
    intro a b ha hab hb
    refine (hcont.mono ?_).intervalIntegrable
    rw [uIcc_of_le hab]; exact Icc_subset_Icc ha hb
  have hL := one_add_log_cube_mono (x := T / 2) (y := 4 * T) (by linarith) (by linarith)
  have hL1 := one_add_log_cube_mono (x := T) (y := 4 * T) (by linarith) (by linarith)
  have hL2 := one_add_log_cube_mono (x := 2 * T) (y := 4 * T) (by linarith) (by linarith)
  have e1 := hA1 (T / 2) (by linarith) σ hσ hσ3
  have e2 := hA1 T (by linarith) σ hσ hσ3
  have e3 := hA1 (2 * T) (by linarith) σ hσ hσ3
  rw [show 2 * (T / 2) = T by ring] at e1
  rw [show 2 * (2 * T) = 4 * T by ring] at e3
  have hsplit : ∫ y in (T / 2)..(4 * T), g y =
      (∫ y in (T / 2)..T, g y) + (∫ y in T..(2 * T), g y) + ∫ y in (2 * T)..(4 * T), g y := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hii _ _ le_rfl (by linarith) (by linarith))
        (hii _ _ (by linarith) (by linarith) (by linarith)),
      intervalIntegral.integral_add_adjacent_intervals (hii _ _ le_rfl (by linarith) (by linarith))
        (hii _ _ (by linarith) (by linarith) le_rfl)]
  have hmono : ∫ y in Y₁..Y₂, g y ≤ ∫ y in (T / 2)..(4 * T), g y :=
    intervalIntegral.integral_mono_interval h1 h12 h2
      (Filter.Eventually.of_forall fun y => by positivity) (hii _ _ le_rfl (by linarith) le_rfl)
  have hT0 : 0 < T := by linarith
  have hC0 := hC.le
  calc ∫ y in Y₁..Y₂, g y ≤ _ := hmono
    _ = _ := hsplit
    _ ≤ C * (T / 2) * (1 + Real.log (T / 2)) ^ 3 + C * T * (1 + Real.log T) ^ 3
        + C * (2 * T) * (1 + Real.log (2 * T)) ^ 3 := by linarith
    _ ≤ C * (T / 2) * (1 + Real.log (4 * T)) ^ 3 + C * T * (1 + Real.log (4 * T)) ^ 3
        + C * (2 * T) * (1 + Real.log (4 * T)) ^ 3 := by gcongr
    _ ≤ 4 * C * T * (1 + Real.log (4 * T)) ^ 3 := by
        have : 0 ≤ C * T * (1 + Real.log (4 * T)) ^ 3 := by
          have : 0 ≤ 1 + Real.log (4 * T) := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 * T)]
          positivity
        nlinarith

/-- **Column bound for `(z − 1)ζ(z)`.** For `½ − r ≤ x ≤ 5/2` with `r ≤ ¼` and a span
`[Y₁, Y₂] ⊆ [T/2, 4T]`, `∫ |(z − 1)ζ(z)|² dy ≤ (4T + 2)² ((K (4T)^r)² + 1) · 4C T (1 + log 4T)³`
along `z = x + iy`. -/
theorem integral_normSq_zetaEntire_column_le {C K r : ℝ} (hC : 0 < C) (hK0 : 0 ≤ K)
    (hr0 : 0 < r) (hr : r ≤ 1 / 4)
    (hA1 : ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 3 →
      ∫ t in T..(2 * T), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ C * T * (1 + Real.log T) ^ 3)
    (hχ : ∀ d : ℝ, 0 ≤ d → d ≤ 1 / 4 → ∀ t : ℝ,
      ‖zetaChi (((1 / 2 - d : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ K * (max 1 |t|) ^ d)
    {T x Y₁ Y₂ : ℝ} (hT : 4 ≤ T) (hx : 1 / 2 - r ≤ x) (hx' : x ≤ 5 / 2) (h1 : T / 2 ≤ Y₁)
    (h12 : Y₁ ≤ Y₂) (h2 : Y₂ ≤ 4 * T) :
    ∫ y in Y₁..Y₂, ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤
      (4 * T + 2) ^ 2 * ((K * (4 * T) ^ r) ^ 2 + 1) * (4 * C * T * (1 + Real.log (4 * T)) ^ 3) := by
  set B := 4 * C * T * (1 + Real.log (4 * T)) ^ 3 with hB
  set Λ := (K * (4 * T) ^ r) ^ 2 with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hB0 : 0 ≤ B := by
    have : 0 ≤ 1 + Real.log (4 * T) := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 * T)]
    rw [hB]; have := hC.le; positivity
  set σ' : ℝ := max x (1 - x) with hσ'
  have hσ'1 : 1 / 2 ≤ σ' := by
    rcases le_total x (1 / 2) with h | h
    · exact le_trans (by linarith) (le_max_right _ _)
    · exact le_trans h (le_max_left _ _)
  have hσ'3 : σ' ≤ 3 := max_le (by linarith) (by linarith)
  have hspan := integral_normSq_zeta_span_le hC hA1 hT hσ'1 hσ'3 h1 h12 h2
  have hY1 : 2 ≤ Y₁ := by linarith
  -- pointwise comparison
  have hpt : ∀ y ∈ Icc Y₁ Y₂, ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤
      (4 * T + 2) ^ 2 * (Λ + 1) * ‖riemannZeta ((σ' : ℂ) + (y : ℂ) * I)‖ ^ 2 := by
    intro y hy
    have hne : (x : ℂ) + (y : ℂ) * I ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith [hy.1]
    rw [zetaEntire_eq hne, norm_mul, mul_pow]
    have hn1 : ‖(x : ℂ) + (y : ℂ) * I - 1‖ ≤ 4 * T + 2 := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, Complex.one_re, Complex.sub_im, Complex.add_im,
        Complex.mul_im, Complex.one_im]
      have hxa : |x + (y * 0 - 0 * 1) - 1| ≤ 2 := by rw [abs_le]; constructor <;> linarith
      have hya : |0 + (y * 1 + 0 * 0) - 0| ≤ 4 * T := by
        rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
      linarith
    have hn1' : ‖(x : ℂ) + (y : ℂ) * I - 1‖ ^ 2 ≤ (4 * T + 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn1 2
    have hz : ‖riemannZeta ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤
        (Λ + 1) * ‖riemannZeta ((σ' : ℂ) + (y : ℂ) * I)‖ ^ 2 := by
      rcases le_total (1 / 2) x with hxh | hxh
      · have : σ' = x := by rw [hσ']; exact max_eq_left (by linarith)
        rw [this]
        nlinarith [sq_nonneg ‖riemannZeta ((x : ℂ) + (y : ℂ) * I)‖]
      · set d := 1 / 2 - x with hd
        have hd0 : 0 ≤ d := by linarith
        have hdr : d ≤ r := by linarith
        have hσd : σ' = 1 / 2 + d := by rw [hσ']; rw [max_eq_right (by linarith)]; ring
        have hxd : (x : ℂ) = ((1 / 2 - d : ℝ) : ℂ) := by rw [hd]; push_cast; ring
        rw [hxd, hσd]
        have hrefl := normSq_zeta_left_le (Y := 4 * T) hK0 hd0
          (hχ d hd0 (by linarith) y) (by linarith [hy.1]) (by linarith [hy.2])
        have hpow : (K * (4 * T) ^ d) ^ 2 ≤ Λ := by
          rw [hΛ]
          have : (4 * T) ^ d ≤ (4 * T) ^ r :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) hdr
          exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left this hK0) 2
        have h0 := sq_nonneg ‖riemannZeta (((1 / 2 + d : ℝ) : ℂ) + (y : ℂ) * I)‖
        nlinarith
    have hz0 := sq_nonneg ‖riemannZeta ((x : ℂ) + (y : ℂ) * I)‖
    calc ‖(x : ℂ) + (y : ℂ) * I - 1‖ ^ 2 * ‖riemannZeta ((x : ℂ) + (y : ℂ) * I)‖ ^ 2
        ≤ (4 * T + 2) ^ 2 * ((Λ + 1) * ‖riemannZeta ((σ' : ℂ) + (y : ℂ) * I)‖ ^ 2) :=
          mul_le_mul hn1' hz (by positivity) (by positivity)
      _ = _ := by ring
  have hcontE : Continuous fun y : ℝ => ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 :=
    (differentiable_zetaEntire.continuous.comp (by fun_prop)).norm.pow 2
  have hcontZ : ContinuousOn (fun y : ℝ => ‖riemannZeta ((σ' : ℂ) + (y : ℂ) * I)‖ ^ 2)
      (uIcc Y₁ Y₂) := by
    rw [uIcc_of_le h12]; exact continuousOn_normSq_zeta_vertical σ' (by linarith)
  calc ∫ y in Y₁..Y₂, ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2
      ≤ ∫ y in Y₁..Y₂, (4 * T + 2) ^ 2 * (Λ + 1) * ‖riemannZeta ((σ' : ℂ) + (y : ℂ) * I)‖ ^ 2 :=
        intervalIntegral.integral_mono_on h12 (hcontE.intervalIntegrable _ _)
          (hcontZ.intervalIntegrable.const_mul _) hpt
    _ = (4 * T + 2) ^ 2 * (Λ + 1) * ∫ y in Y₁..Y₂, ‖riemannZeta ((σ' : ℂ) + (y : ℂ) * I)‖ ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ (4 * T + 2) ^ 2 * (Λ + 1) * B := by gcongr

/-! ## Unit cells -/

/-- **Sliding windows.** The windows `[s + k − 3, s + k + 4]`, `k < m`, cover every point at most
seven times: `Σ_k ∫_{s+k−3}^{s+k+4} g ≤ 7 ∫_{s−3}^{s+m+4} g` for continuous `g ≥ 0`. -/
theorem sum_integral_sliding_le {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ y, 0 ≤ g y) (s : ℝ)
    (m : ℕ) :
    ∑ k ∈ Finset.range m, ∫ y in (s + k - 3)..(s + k + 4), g y ≤
      7 * ∫ y in (s - 3)..(s + m + 4), g y := by
  have hsplit : ∀ k : ℕ, ∫ y in (s + k - 3)..(s + k + 4), g y =
      ∑ j ∈ Finset.range 7, ∫ y in (s - 3 + j + k)..(s - 3 + j + k + 1), g y := by
    intro k
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := volume)
      (a := fun j : ℕ => s - 3 + j + k) (n := 7) (fun j _ => hg.intervalIntegrable _ _)
    simp only [Nat.cast_ofNat, CharP.cast_eq_zero, add_zero] at h
    rw [show s + k - 3 = s - 3 + k by ring, show s + k + 4 = s - 3 + 7 + k by ring, ← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    push_cast; ring
  have hrow : ∀ j : ℕ, ∑ k ∈ Finset.range m, ∫ y in (s - 3 + j + k)..(s - 3 + j + k + 1), g y =
      ∫ y in (s - 3 + j)..(s - 3 + j + m), g y := by
    intro j
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := volume)
      (a := fun k : ℕ => s - 3 + j + k) (n := m) (fun k _ => hg.intervalIntegrable _ _)
    simp only [CharP.cast_eq_zero, add_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring_nf
  have hmono : ∀ j ∈ Finset.range 7, ∫ y in (s - 3 + j)..(s - 3 + j + m), g y ≤
      ∫ y in (s - 3)..(s + m + 4), g y := by
    intro j hj
    have hj7 : (j : ℝ) ≤ 6 := by
      have := Finset.mem_range.mp hj; exact_mod_cast (by omega : j ≤ 6)
    have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall fun y => hg0 y) (hg.intervalIntegrable _ _)
  calc ∑ k ∈ Finset.range m, ∫ y in (s + k - 3)..(s + k + 4), g y
      = ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range m,
          ∫ y in (s - 3 + j + k)..(s - 3 + j + k + 1), g y := by
        simp_rw [hsplit]; exact Finset.sum_comm
    _ = ∑ j ∈ Finset.range 7, ∫ y in (s - 3 + j)..(s - 3 + j + m), g y :=
        Finset.sum_congr rfl fun j _ => hrow j
    _ ≤ ∑ _j ∈ Finset.range 7, ∫ y in (s - 3)..(s + m + 4), g y := Finset.sum_le_sum hmono
    _ = 7 * ∫ y in (s - 3)..(s + m + 4), g y := by simp

/-- **Cell Markov.** If every bad height `t ∈ [T, 2T]` forces `A ≤ Φ k` for the unit cell
`[T + k, T + k + 1] ∋ t`, the bad heights have measure at most `Σ_{k ≤ ⌈T⌉} Φ k / A`. -/
theorem volume_setOf_le_of_cells {P : ℝ → Prop} {Φ : ℕ → ℝ} {A T : ℝ} (hA : 0 < A)
    (hΦ : ∀ k, 0 ≤ Φ k)
    (hbad : ∀ t ∈ Icc T (2 * T), P t → ∀ k : ℕ, T + k ≤ t → t ≤ T + k + 1 → A ≤ Φ k) :
    volume {t | t ∈ Icc T (2 * T) ∧ P t} ≤
      ENNReal.ofReal ((∑ k ∈ Finset.range (⌈T⌉₊ + 1), Φ k) / A) := by
  set m := ⌈T⌉₊ + 1 with hm
  set Bk := (Finset.range m).filter (fun k => A ≤ Φ k) with hBk
  have hsub : {t | t ∈ Icc T (2 * T) ∧ P t} ⊆ ⋃ k ∈ Bk, Icc (T + k) (T + k + 1) := by
    rintro t ⟨ht, hP⟩
    have h0 : 0 ≤ t - T := by linarith [ht.1]
    set k := ⌊t - T⌋₊ with hk
    have hk1 : (k : ℝ) ≤ t - T := Nat.floor_le h0
    have hk2 : t - T < k + 1 := Nat.lt_floor_add_one _
    have hkm : k < m := by
      have : (k : ℝ) < (⌈T⌉₊ : ℝ) + 1 := by
        have := Nat.le_ceil T; linarith [ht.2]
      rw [hm]; exact_mod_cast this
    refine mem_iUnion₂.mpr ⟨k, ?_, ⟨by linarith, by linarith⟩⟩
    rw [hBk, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr hkm, hbad t ht hP k (by linarith) (by linarith)⟩
  have hcard : (Bk.card : ℝ) * A ≤ ∑ k ∈ Finset.range m, Φ k := by
    calc (Bk.card : ℝ) * A = ∑ _k ∈ Bk, A := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ Bk, Φ k := Finset.sum_le_sum fun k hk => (Finset.mem_filter.mp hk).2
      _ ≤ ∑ k ∈ Finset.range m, Φ k :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ => hΦ k
  calc volume {t | t ∈ Icc T (2 * T) ∧ P t} ≤ volume (⋃ k ∈ Bk, Icc (T + k) (T + k + 1)) :=
        measure_mono hsub
    _ ≤ ∑ k ∈ Bk, volume (Icc (T + k) (T + k + 1)) := measure_biUnion_finset_le _ _
    _ = Bk.card := by
        simp only [Real.volume_Icc, show ∀ k : ℕ, T + k + 1 - (T + k) = 1 from fun k => by ring,
          ENNReal.ofReal_one, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = ENNReal.ofReal Bk.card := (ENNReal.ofReal_natCast _).symm
    _ ≤ ENNReal.ofReal ((∑ k ∈ Finset.range m, Φ k) / A) :=
        ENNReal.ofReal_le_ofReal ((le_div_iff₀ hA).mpr hcard)

/-! ## Large values near typical heights -/

/-- The heights `t ∈ [T, 2T]` near which `ζ` exceeds `M`: some `z` with `½ ≤ Re z ≤ 2` and
`|Im z − t| ≤ 2` has `|ζ(z)| > M`. -/
def zetaLargeNear (T M : ℝ) : Set ℝ :=
  {t | t ∈ Icc T (2 * T) ∧
    ∃ z : ℂ, 1 / 2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im - t| ≤ 2 ∧ M < ‖riemannZeta z‖}

theorem continuous_integral_normSq_zetaEntire_column {c d : ℝ} (hcd : c ≤ d) :
    Continuous fun x : ℝ => ∫ y in c..d, ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 := by
  have e : (fun x : ℝ => ∫ y in c..d, ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2) =
      fun x : ℝ => ∫ y in Icc c d, ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 := by
    funext x; rw [intervalIntegral.integral_of_le hcd, integral_Icc_eq_integral_Ioc]
  rw [e]
  have hc : Continuous fun p : ℝ × ℝ => ‖zetaEntire ((p.1 : ℂ) + (p.2 : ℂ) * I)‖ ^ 2 :=
    (differentiable_zetaEntire.continuous.comp (by fun_prop)).norm.pow 2
  exact continuous_parametric_integral_of_continuous
    (f := fun x y : ℝ => ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2) hc isCompact_Icc

/-- **Large values near typical heights, quantitative.** With `C` from the vertical mean square,
`K` from the `χ`-bound left of the line, `0 < r ≤ ¼`, `T ≥ 6` and `M > 0`, the heights in
`[T, 2T]` near which `|ζ| > M` have measure at most
`21 (4T + 2)² ((K (4T)^r)² + 1) · 4C T (1 + log 4T)³ / (π r² (T/2)² M²)`. -/
theorem volume_zetaLargeNear_le {C K r : ℝ} (hC : 0 < C) (hK0 : 0 ≤ K) (hr0 : 0 < r)
    (hr : r ≤ 1 / 4)
    (hA1 : ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 3 →
      ∫ t in T..(2 * T), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ C * T * (1 + Real.log T) ^ 3)
    (hχ : ∀ d : ℝ, 0 ≤ d → d ≤ 1 / 4 → ∀ t : ℝ,
      ‖zetaChi (((1 / 2 - d : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ K * (max 1 |t|) ^ d)
    {T M : ℝ} (hT : 6 ≤ T) (hM : 0 < M) :
    volume (zetaLargeNear T M) ≤ ENNReal.ofReal (21 * ((4 * T + 2) ^ 2 * ((K * (4 * T) ^ r) ^ 2 + 1)
      * (4 * C * T * (1 + Real.log (4 * T)) ^ 3)) / (Real.pi * r ^ 2 * (T / 2) ^ 2 * M ^ 2)) := by
  set Q := (4 * T + 2) ^ 2 * ((K * (4 * T) ^ r) ^ 2 + 1) * (4 * C * T * (1 + Real.log (4 * T)) ^ 3)
    with hQ
  set A := Real.pi * r ^ 2 * (T / 2) ^ 2 * M ^ 2 with hAdef
  have hA : 0 < A := by rw [hAdef]; have := Real.pi_pos; positivity
  set Φ : ℕ → ℝ := fun k => ∫ x in (1 / 2 - r)..(5 / 2),
    ∫ y in (T + k - 3)..(T + k + 4), ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 with hΦdef
  have hΦ0 : ∀ k, 0 ≤ Φ k := fun k =>
    intervalIntegral.integral_nonneg (by linarith) fun x _ =>
      intervalIntegral.integral_nonneg (by linarith) fun y _ => by positivity
  have hbad : ∀ t ∈ Icc T (2 * T),
      (∃ z : ℂ, 1 / 2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im - t| ≤ 2 ∧ M < ‖riemannZeta z‖) →
      ∀ k : ℕ, T + k ≤ t → t ≤ T + k + 1 → A ≤ Φ k := by
    rintro t ht ⟨z, hz1, hz2, hzt, hzM⟩ k hk1 hk2
    have hzt' := abs_le.mp hzt
    have hmean := normSq_mul_area_le_box differentiable_zetaEntire (z := z) hr0
      (a := 1 / 2 - r) (b := 5 / 2) (c := T + k - 3) (d := T + k + 4)
      (by linarith) (by linarith) (by linarith) (by linarith)
    have hzim : T / 2 ≤ z.im := by linarith [ht.1]
    have hne : z ≠ 1 := by intro h; rw [h] at hzim; simp at hzim; linarith
    have hn1 : T / 2 ≤ ‖z - 1‖ := by
      refine le_trans ?_ (Complex.abs_im_le_norm _)
      rw [Complex.sub_im, Complex.one_im, sub_zero, abs_of_pos (by linarith)]; exact hzim
    have hE : T / 2 * M ≤ ‖zetaEntire z‖ := by
      rw [zetaEntire_eq hne, norm_mul]
      exact mul_le_mul hn1 hzM.le hM.le (norm_nonneg _)
    have hE2 : (T / 2) ^ 2 * M ^ 2 ≤ ‖zetaEntire z‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hE 2
    calc A = Real.pi * r ^ 2 * ((T / 2) ^ 2 * M ^ 2) := by rw [hAdef]; ring
      _ ≤ Real.pi * r ^ 2 * ‖zetaEntire z‖ ^ 2 := by gcongr
      _ ≤ Φ k := hmean
  have hvol := volume_setOf_le_of_cells hA hΦ0 hbad
  refine hvol.trans (ENNReal.ofReal_le_ofReal ?_)
  set m := ⌈T⌉₊ + 1 with hm
  have hm1 : (m : ℝ) ≤ T + 2 := by
    rw [hm]; push_cast; linarith [Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ T)]
  have hsum : ∑ k ∈ Finset.range m, Φ k ≤ 21 * Q := by
    have hswap : ∑ k ∈ Finset.range m, Φ k = ∫ x in (1 / 2 - r)..(5 / 2),
        ∑ k ∈ Finset.range m, ∫ y in (T + k - 3)..(T + k + 4),
          ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 := by
      rw [intervalIntegral.integral_finsetSum]
      intro k _
      exact (continuous_integral_normSq_zetaEntire_column (by linarith)).intervalIntegrable _ _
    rw [hswap]
    have hpt : ∀ x ∈ uIoc (1 / 2 - r) (5 / 2), ‖∑ k ∈ Finset.range m, ∫ y in (T + k - 3)..(T + k + 4),
        ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2‖ ≤ 7 * Q := by
      intro x hx
      rw [uIoc_of_le (by linarith)] at hx
      have hg : Continuous fun y : ℝ => ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 :=
        (differentiable_zetaEntire.continuous.comp (by fun_prop)).norm.pow 2
      have hsl := sum_integral_sliding_le hg (fun y => by positivity) T m
      have hcol := integral_normSq_zetaEntire_column_le hC hK0 hr0 hr hA1 hχ (T := T) (x := x)
        (Y₁ := T - 3) (Y₂ := T + m + 4) (by linarith) hx.1.le hx.2 (by linarith) (by linarith)
        (by linarith)
      have h0 : 0 ≤ ∑ k ∈ Finset.range m, ∫ y in (T + k - 3)..(T + k + 4),
          ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 :=
        Finset.sum_nonneg fun k _ => intervalIntegral.integral_nonneg (by linarith) fun y _ => by
          positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      linarith
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [abs_of_pos (by linarith)] at hn
    have hQ0 : 0 ≤ Q := by
      rw [hQ]
      have : 0 ≤ 1 + Real.log (4 * T) := by
        linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 * T)]
      have := hC.le
      positivity
    calc _ ≤ ‖∫ x in (1 / 2 - r)..(5 / 2), ∑ k ∈ Finset.range m, ∫ y in (T + k - 3)..(T + k + 4),
          ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2‖ := Real.le_norm_self _
      _ ≤ 7 * Q * (5 / 2 - (1 / 2 - r)) := hn
      _ ≤ 21 * Q := by nlinarith
  exact div_le_div_of_nonneg_right hsum hA.le

/-- `(4T)^{ε/4}`, `1 + log 4T` and `T^ε` in terms of `u = (4T)^{ε/12}`. -/
theorem zetaLargeNear_scale_bounds {ε T : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hT : 1 ≤ T) :
    1 ≤ (4 * T) ^ (ε / 12) ∧ (4 * T) ^ (ε / 4) = ((4 * T) ^ (ε / 12)) ^ 3
      ∧ 1 + Real.log (4 * T) ≤ (1 + 12 / ε) * (4 * T) ^ (ε / 12)
      ∧ ((4 * T) ^ (ε / 12)) ^ 12 / 4 ≤ T ^ ε := by
  have h4T : 1 ≤ 4 * T := by linarith
  set u := (4 * T) ^ (ε / 12) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow h4T (by positivity)
  have hpow : ∀ n : ℕ, u ^ n = (4 * T) ^ (ε / 12 * n) := by
    intro n; rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  refine ⟨hu1, by rw [hpow 3]; congr 1; push_cast; ring, ?_, ?_⟩
  · have hl := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ 4 * T) (by positivity : 0 < ε / 12)
    rw [← hu] at hl
    have e : u / (ε / 12) = 12 / ε * u := by field_simp
    rw [e] at hl
    nlinarith
  · have hT' : T ^ ε = (4 * T) ^ ε / (4 : ℝ) ^ ε := by
      rw [← Real.div_rpow (by linarith) (by norm_num)]; congr 1; ring
    have h12 : u ^ 12 = (4 * T) ^ ε := by rw [hpow 12]; congr 1; push_cast; ring
    have h4 : (4 : ℝ) ^ ε ≤ 4 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hε1
    have h40 : 0 < (4 : ℝ) ^ ε := by positivity
    rw [hT', h12]
    exact div_le_div_of_nonneg_left (by positivity) h40 h4

/-- **`ζ` is at most `T^ε` near almost every height.** For `0 < ε ≤ 1` and `δ > 0`, for all
large `T`, the heights `t ∈ [T, 2T]` near which `|ζ| > T^ε` have measure at most `δT`. -/
theorem eventually_volume_zetaLargeNear_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ T in Filter.atTop, volume (zetaLargeNear T (T ^ ε)) ≤ ENNReal.ofReal (δ * T) := by
  obtain ⟨C, hC, hA1⟩ := exists_integral_normSq_zeta_vertical_le
  obtain ⟨K, hK0, hχ⟩ :=
    exists_norm_zetaChi_moving_left_line_le_rpow (d₀ := 1 / 4) (by norm_num) (by norm_num)
  set c₁ := 100 * C * (K ^ 2 + 1) * (1 + 12 / ε) ^ 3 with hc₁
  set c₂ := Real.pi * ε ^ 2 / 1024 with hc₂
  have hc₂0 : 0 < c₂ := by rw [hc₂]; have := Real.pi_pos; positivity
  have hu : Filter.Tendsto (fun T : ℝ => (4 * T) ^ (ε / 12)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by positivity)).comp (Filter.tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [hu.eventually_ge_atTop (21 * c₁ / (c₂ * δ) + 1), Filter.eventually_ge_atTop 6]
    with T hTu hT
  obtain ⟨hu1, hr3, hlog, hM⟩ := zetaLargeNear_scale_bounds hε hε1 (by linarith : (1 : ℝ) ≤ T)
  set u := (4 * T) ^ (ε / 12) with hudef
  have hT0 : 0 < T := by linarith
  have hTε : 0 < T ^ ε := Real.rpow_pos_of_pos hT0 ε
  have hvol := volume_zetaLargeNear_le hC hK0 (by positivity : 0 < ε / 4) (by linarith) hA1
    (fun d hd0 hd t => hχ d hd0 hd t) hT hTε
  refine hvol.trans (ENNReal.ofReal_le_ofReal ?_)
  have hA : 0 < Real.pi * (ε / 4) ^ 2 * (T / 2) ^ 2 * (T ^ ε) ^ 2 := by
    have := Real.pi_pos; positivity
  rw [div_le_iff₀ hA, hr3]
  have hlog0 : 0 ≤ 1 + Real.log (4 * T) := by
    linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 * T)]
  have hK' : (K * u ^ 3) ^ 2 + 1 ≤ (K ^ 2 + 1) * u ^ 6 := by
    have : 1 ≤ u ^ 6 := one_le_pow₀ hu1
    nlinarith [sq_nonneg K]
  have hL : (1 + Real.log (4 * T)) ^ 3 ≤ (1 + 12 / ε) ^ 3 * u ^ 3 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hlog0 hlog 3
  have hQ : (4 * T + 2) ^ 2 * ((K * u ^ 3) ^ 2 + 1) * (4 * C * T * (1 + Real.log (4 * T)) ^ 3)
      ≤ c₁ * T ^ 3 * u ^ 9 := by
    have h1 : (4 * T + 2) ^ 2 ≤ 25 * T ^ 2 := by nlinarith
    calc _ ≤ (25 * T ^ 2) * ((K ^ 2 + 1) * u ^ 6) * (4 * C * T * ((1 + 12 / ε) ^ 3 * u ^ 3)) := by
          gcongr
      _ = c₁ * T ^ 3 * u ^ 9 := by rw [hc₁]; ring
  have hAlow : c₂ * T ^ 2 * u ^ 24 ≤ Real.pi * (ε / 4) ^ 2 * (T / 2) ^ 2 * (T ^ ε) ^ 2 := by
    have hM2 : (u ^ 12 / 4) ^ 2 ≤ (T ^ ε) ^ 2 := pow_le_pow_left₀ (by positivity) hM 2
    calc c₂ * T ^ 2 * u ^ 24 = Real.pi * (ε / 4) ^ 2 * (T / 2) ^ 2 * (u ^ 12 / 4) ^ 2 := by
          rw [hc₂]; ring
      _ ≤ _ := by gcongr
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; have := hC.le; positivity
  have hu15 : 21 * c₁ ≤ δ * c₂ * u ^ 15 := by
    have h1 : u ≤ u ^ 15 := by
      calc u = u ^ 1 := (pow_one u).symm
        _ ≤ u ^ 15 := pow_le_pow_right₀ hu1 (by norm_num)
    have h2 : 21 * c₁ / (c₂ * δ) ≤ u := by linarith
    rw [div_le_iff₀ (by positivity)] at h2
    nlinarith
  calc 21 * ((4 * T + 2) ^ 2 * ((K * u ^ 3) ^ 2 + 1) * (4 * C * T * (1 + Real.log (4 * T)) ^ 3))
      ≤ 21 * (c₁ * T ^ 3 * u ^ 9) := by gcongr
    _ = T ^ 3 * u ^ 9 * (21 * c₁) := by ring
    _ ≤ T ^ 3 * u ^ 9 * (δ * c₂ * u ^ 15) := by gcongr
    _ = δ * T * (c₂ * T ^ 2 * u ^ 24) := by ring
    _ ≤ δ * T * (Real.pi * (ε / 4) ^ 2 * (T / 2) ^ 2 * (T ^ ε) ^ 2) := by gcongr

end RHTower

end
