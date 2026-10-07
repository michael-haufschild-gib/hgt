import GaloisForLFunctions.RHTower.WeilWorkQuantizationRadialGrowth

/-!
# Subpolynomial bounds for the actual canonical radial trace

Producer continuation, horizontal monotonicity and a uniform Gamma ratio
pay every positive power exponent without critical-edge continuity.
This supplies refined contour estimates; it does not assert quantization.
-/

open Complex Set Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace RHTower.WeilSpectral
open WeilHerglotz IntegerMassRigidity FractionalMassRigidity PhaseLockRigidity TruncatedRadial

/-- Retain the actual horizontal displacement in the uniform Gamma estimate. -/
theorem quantization_norm_Gamma_shift {x u y : ℝ} (hx : 1 / 2 ≤ x)
    (hxu : x ≤ u) (hu : u ≤ 3 / 2) (hy : 2 ≤ |y|) :
    ‖Complex.Gammaℝ ((u : ℂ) + y * I)‖ ≤
      Real.exp 3 * (1 + |y|) ^ ((u - x) / 2) * ‖Complex.Gammaℝ ((x : ℂ) + y * I)‖ := by
  have hnorm : ∀ σ : ℝ, ‖Complex.Gammaℝ ((σ : ℂ) + (y : ℂ) * I)‖ =
      Real.pi ^ (-(σ / 2)) * ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + ((|y| / 2 : ℝ) : ℂ) * I)‖ := by
    intro σ
    rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    · congr 1; simp; ring
    · rcases le_total 0 y with h | h
      · rw [abs_of_nonneg h]; congr 1; push_cast; ring_nf
      · rw [abs_of_nonpos h, ← FractionalMassPolynomialTailRigidity.norm_Gamma_conj_line]
        congr 1; push_cast; ring_nf
  rw [hnorm, hnorm]
  set τ : ℝ := |y| / 2 with hτ
  have hτ1 : 1 ≤ τ := by rw [hτ]; linarith
  have hτ0 : 0 < τ := by linarith
  have hd0 : 0 ≤ u / 2 - x / 2 := by linarith
  have hd1 : u / 2 - x / 2 ≤ 1 / 2 := by linarith
  have hsh := norm_Gamma_shift_le_uniform (a := x / 2) (b := u / 2) (τ := τ)
    (by linarith) (by linarith) hτ0
  have hl1 : 1 / 2 * Real.log ((u / 2) ^ 2 + τ ^ 2) ≤ Real.log (1 + |y|) := by
    have h1 : (u / 2) ^ 2 + τ ^ 2 ≤ (1 + |y|) ^ 2 := by rw [hτ]; nlinarith [abs_nonneg y]
    have h2 := Real.log_le_log (by positivity : 0 < (u / 2) ^ 2 + τ ^ 2) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have he1 : 1 / τ ^ 2 + Real.pi / (2 * τ) ≤ 3 := by
    have h1 : 1 / τ ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    have h2 : Real.pi / (2 * τ) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_lt_four]
    linarith
  have hE : (u / 2 - x / 2) * (1 / 2 * Real.log ((u / 2) ^ 2 + τ ^ 2) +
      (1 / τ ^ 2 + Real.pi / (2 * τ))) ≤ (u - x) / 2 * Real.log (1 + |y|) + 3 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hl1 hd0, mul_le_mul_of_nonneg_left he1 hd0]
  have hexp : Real.exp ((u / 2 - x / 2) * (1 / 2 * Real.log ((u / 2) ^ 2 + τ ^ 2) +
      (1 / τ ^ 2 + Real.pi / (2 * τ)))) ≤ Real.exp 3 * (1 + |y|) ^ ((u - x) / 2) := by
    calc _ ≤ Real.exp ((u - x) / 2 * Real.log (1 + |y|) + 3 / 2) := Real.exp_le_exp.mpr hE
      _ = Real.exp (3 / 2) * (1 + |y|) ^ ((u - x) / 2) := by
          rw [Real.exp_add, Real.rpow_def_of_pos (by positivity)]; ring_nf
      _ ≤ Real.exp 3 * (1 + |y|) ^ ((u - x) / 2) := by gcongr; norm_num
  have hpow : Real.pi ^ (-(u / 2)) ≤ Real.pi ^ (-(x / 2)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
  calc _ ≤ Real.pi ^ (-(x / 2)) * (‖Complex.Gamma (((x / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ *
          (Real.exp 3 * (1 + |y|) ^ ((u - x) / 2))) :=
        mul_le_mul hpow (hsh.trans (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)))
          (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Producer continuation agrees with the actual quotient on its interior ball. -/
theorem exists_quantizationProdF_interior_subpolynomial {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ y : ℝ, T₀ ≤ |y| → 2 ≤ |y| → ∀ x : ℝ,
      1 / 2 + δ ≤ x → x ≤ 3 / 2 →
      ‖prodF (quantizationCompletion hW) ((x : ℂ) + y * I)‖ ≤ (|y| + 3) ^ ε := by
  obtain ⟨T₀, hT₀⟩ := exists_producerZeta_subpolynomial_of_weilPositiveFull hW hδ hδ1 hε
  refine ⟨T₀, fun y hy hy2 x hx hx1 => ?_⟩
  obtain ⟨g, hgd, hgL, hgb⟩ := hT₀ y hy
  let B : Set ℂ := ball ((3 : ℂ) + y * I) (5 / 2 - δ / 4)
  have hBre : ∀ s ∈ B, 1 / 2 < s.re := fun s hs => by
    have h := Complex.abs_re_le_norm (s - ((3 : ℂ) + y * I))
    rw [show B = ball ((3 : ℂ) + y * I) (5 / 2 - δ / 4) from rfl, mem_ball, dist_eq_norm] at hs
    simp at h
    linarith [neg_abs_le (s.re - 3)]
  have hB1 : ∀ s ∈ B, s ≠ 1 := fun s hs h1 => by
    rw [h1] at hs
    rw [show B = ball ((3 : ℂ) + y * I) (5 / 2 - δ / 4) from rfl, mem_ball, dist_eq_norm] at hs
    have hsq : ‖(1 : ℂ) - (3 + y * I)‖ ^ 2 = 4 + y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have : 4 ≤ y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
    nlinarith [norm_nonneg ((1 : ℂ) - (3 + y * I))]
  have hF₂d : DifferentiableOn ℂ (prodF (quantizationCompletion hW)) B := fun s hs => by
    have hr := hBre s hs
    exact (differentiableAt_prodF (fun _ hz => hasDerivAt_quantizationCompletion hW hz) hr
      (fun h0 => by rw [h0] at hr; simp at hr; linarith) (hB1 s hs)).differentiableWithinAt
  have hF₁d : DifferentiableOn ℂ (fun s => cexp (g s)) B := fun s hs =>
    ((hgd s hs).differentiableAt (isOpen_ball.mem_nhds hs)).cexp.differentiableWithinAt
  have hcoef : logZetaCoeff (fun n => if 2 ≤ n then lam n else 0) = lamLog lam := by
    funext n; simp only [logZetaCoeff, lamLog]; split_ifs <;> simp
  have hc₀ : (3 : ℂ) + y * I ∈ B := mem_ball_self (by linarith)
  have hev : (fun s => cexp (g s)) =ᶠ[𝓝 ((3 : ℂ) + y * I)] prodF (quantizationCompletion hW) := by
    have hO : IsOpen (B ∩ {s : ℂ | 1 < s.re}) :=
      isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
    refine Filter.eventuallyEq_of_mem (hO.mem_nhds ⟨hc₀, by simp⟩) fun s hs => ?_
    rw [hgL s hs.1 hs.2, hcoef, quantization_prodF_eq_zetaOf hW hs.2]
    rfl
  have hEq := (hF₁d.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
    (hF₂d.analyticOnNhd isOpen_ball) (convex_ball _ _).isPreconnected hc₀ hev
  have hsB : (x : ℂ) + y * I ∈ B := by
    rw [show B = ball ((3 : ℂ) + y * I) (5 / 2 - δ / 4) from rfl, mem_ball, dist_eq_norm]
    have e : (x : ℂ) + y * I - ((3 : ℂ) + y * I) = ((x - 3 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  rw [← hEq hsB]
  exact (hgb x hx (by linarith)).2

/-- Transfer growth across an arbitrarily narrow interior horizontal segment. -/
theorem quantizationProdF_horizontal_bound {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {x u y : ℝ} (hx : 1 / 2 < x) (hxu : x ≤ u) (hu : u ≤ 3 / 2) (hy : 2 ≤ |y|) :
    ‖prodF (quantizationCompletion hW) ((x : ℂ) + y * I)‖ ≤
      4 * Real.exp 3 * (1 + |y|) ^ ((u - x) / 2) *
        ‖prodF (quantizationCompletion hW) ((u : ℂ) + y * I)‖ := by
  set s : ℂ := (x : ℂ) + y * I
  set s' : ℂ := (u : ℂ) + y * I
  have hsy : |y| ≤ ‖s‖ := by simpa [s] using Complex.abs_im_le_norm s
  have hs1y : |y| ≤ ‖s - 1‖ := by simpa [s] using Complex.abs_im_le_norm (s - 1)
  have hs'n : ‖s'‖ ≤ 2 * ‖s‖ := by
    have h := norm_add_le (u : ℂ) ((y : ℂ) * I)
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
      abs_of_pos (by linarith : 0 < u)] at h
    dsimp [s']; linarith
  have hs'1 : ‖s' - 1‖ ≤ 2 * ‖s - 1‖ := by
    have e : s' - 1 = ((u - 1 : ℝ) : ℂ) + y * I := by dsimp [s']; push_cast; ring
    have h := norm_add_le ((u - 1 : ℝ) : ℂ) ((y : ℂ) * I)
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one] at h
    have ha : |u - 1| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [e]; linarith
  have hd (z : ℂ) (hz : 1 / 2 < z.re) (hzy : z.im = y) :
      0 < ‖z‖ * ‖z - 1‖ * ‖Complex.Gammaℝ z‖ := by
    have hy0 : y ≠ 0 := by intro h; rw [h, abs_zero] at hy; norm_num at hy
    have hz0 : z ≠ 0 := by intro h; simp [h] at hzy; exact hy0 hzy.symm
    have hz1 : z - 1 ≠ 0 := by intro h; have := congrArg Complex.im h; simp [hzy] at this; exact hy0 this
    exact mul_pos (mul_pos (norm_pos_iff.mpr hz0) (norm_pos_iff.mpr hz1))
      (norm_pos_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)))
  have hd' := hd s' (by simp [s']; linarith) (by simp [s'])
  have hG' : ‖quantizationCompletion hW s'‖ = ‖prodF (quantizationCompletion hW) s'‖ *
      (‖s'‖ * ‖s' - 1‖ * ‖Complex.Gammaℝ s'‖) := by
    rw [prodF, norm_div, norm_mul, norm_mul, div_mul_cancel₀ _ (ne_of_gt hd')]
  have hΓ := quantization_norm_Gamma_shift hx.le hxu hu hy
  change ‖quantizationCompletion hW s / (s * (s - 1) * Complex.Gammaℝ s)‖ ≤ _
  rw [norm_div, norm_mul, norm_mul, div_le_iff₀ (hd s (by simpa [s] using hx) (by simp [s]))]
  calc ‖quantizationCompletion hW s‖ ≤ ‖quantizationCompletion hW s'‖ :=
        norm_quantizationCompletion_le_of_le hW y hx hxu
    _ = _ := hG'
    _ ≤ ‖prodF (quantizationCompletion hW) s'‖ *
        ((2 * ‖s‖) * (2 * ‖s - 1‖) *
          (Real.exp 3 * (1 + |y|) ^ ((u - x) / 2) * ‖Complex.Gammaℝ s‖)) := by gcongr
    _ = _ := by ring

/-- Arbitrarily small positive power bounds hold uniformly up to the open edge. -/
theorem exists_quantizationProdF_subpolynomial {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, 1 / 2 < x → x ≤ 3 / 2 → 2 ≤ |y| →
      ‖prodF (quantizationCompletion hW) ((x : ℂ) + y * I)‖ ≤ C * (1 + |y|) ^ p := by
  let δ : ℝ := min p (1 / 4)
  have hδ0 : 0 < δ := lt_min hp (by norm_num)
  have hδ1 : δ < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  have hδp : δ ≤ p := min_le_left _ _
  obtain ⟨T₀, hT₀⟩ := exists_quantizationProdF_interior_subpolynomial hW hδ0 hδ1
    (show 0 < p / 2 by linarith)
  obtain ⟨C₀, hC₀, hF₀⟩ := exists_norm_quantizationProdF_le hW
  let T : ℝ := max T₀ 2
  let C₁ : ℝ := 4 * Real.exp 3 * 3 ^ (p / 2)
  let C₂ : ℝ := C₀ * (1 + T) ^ (1 / 2 : ℝ)
  have hT : 2 ≤ T := le_max_right _ _
  have hC₁ : 0 ≤ C₁ := by positivity
  have hC₂ : 0 ≤ C₂ := mul_nonneg hC₀ (Real.rpow_nonneg (by linarith) _)
  refine ⟨max C₁ C₂, hC₁.trans (le_max_left _ _), fun x y hx hx1 hy => ?_⟩
  have hbase : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
  have hpow1 : 1 ≤ (1 + |y|) ^ p := Real.one_le_rpow hbase hp.le
  by_cases hfar : T ≤ |y|
  · let u : ℝ := max x (1 / 2 + δ)
    have hxu : x ≤ u := le_max_left _ _
    have hu : u ≤ 3 / 2 := max_le hx1 (by linarith)
    have hdu : (u - x) / 2 ≤ δ / 2 := by
      have : u ≤ x + δ := max_le (by linarith) (by linarith)
      linarith
    have h1 := quantizationProdF_horizontal_bound hW hx hxu hu hy
    have h2 := hT₀ y ((le_max_left _ _).trans hfar) hy u (le_max_right _ _) hu
    have h3 : (|y| + 3) ^ (p / 2) ≤ 3 ^ (p / 2) * (1 + |y|) ^ (p / 2) := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg y]) (by linarith)
    have h4 : (1 + |y|) ^ ((u - x) / 2) * (1 + |y|) ^ (p / 2) ≤ (1 + |y|) ^ p := by
      rw [← Real.rpow_add (by positivity)]
      exact Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    calc _ ≤ 4 * Real.exp 3 * (1 + |y|) ^ ((u - x) / 2) *
          (3 ^ (p / 2) * (1 + |y|) ^ (p / 2)) :=
            h1.trans (mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity))
      _ = C₁ * ((1 + |y|) ^ ((u - x) / 2) * (1 + |y|) ^ (p / 2)) := by dsimp [C₁]; ring
      _ ≤ C₁ * (1 + |y|) ^ p := mul_le_mul_of_nonneg_left h4 hC₁
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hyT : |y| ≤ T := (lt_of_not_ge hfar).le
    calc _ ≤ C₀ * (1 + |y|) ^ (1 / 2 : ℝ) := hF₀ x y hx hx1 hy
      _ ≤ C₂ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)) hC₀
      _ ≤ max C₁ C₂ * (1 + |y|) ^ p :=
        (le_max_right _ _).trans (le_mul_of_one_le_right (hC₁.trans (le_max_left _ _)) hpow1)

/-- The everywhere-defined actual trace inherits every positive power exponent. -/
theorem exists_quantizationTraceF_subpolynomial {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, ‖quantizationTraceF hW y‖ ≤ C * (1 + |y|) ^ p := by
  obtain ⟨C, hC, hF⟩ := exists_quantizationProdF_subpolynomial hW hp
  obtain ⟨B, hB, hBd⟩ := exists_bound_quantizationTraceF hW (-2) 2
  refine ⟨max C B, hC.trans (le_max_left _ _), fun y => ?_⟩
  by_cases hy : 2 ≤ |y|
  · have h : ‖quantizationTraceF hW y‖ ≤ C * (1 + |y|) ^ p := by
      apply le_of_tendsto (tendsto_quantizationTraceF hW y).norm
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with η hη
      exact hF (1 / 2 + η) y (by linarith [hη.1]) (by linarith [hη.2]) hy
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hy' : |y| ≤ 2 := (lt_of_not_ge hy).le
    have hb := hBd y (by rw [uIcc_of_le (by norm_num)]; exact abs_le.mp hy')
    exact hb.trans ((le_max_right _ _).trans
      (le_mul_of_one_le_right (hC.trans (le_max_left _ _))
        (Real.one_le_rpow (by linarith [abs_nonneg y]) hp.le)))

end RHTower.WeilSpectral
