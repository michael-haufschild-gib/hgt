import GaloisForLFunctions.HTGeometry.MellinRegularStripLinear
import GaloisForLFunctions.RHTower.GammaRCubeChartDerivativeBound
import GaloisForLFunctions.RHTower.GammaRCubeRegularClass

/-!
# The antisymmetric chart space of `Γ_ℝ(s)³`

In the cube-root chart `x = X³/(3√3)`, `(Uf)(X) = 3^{-1/4} X f(X³/(3√3))`, a Mellin symbol `Ψ`
on `0 < Re s < 1` becomes `Φ(w) = 3^{w/2-3/4} Ψ((w+1)/3)` on `-1 < Re w < 2`, and
`Mellin⁻¹_{1/2}Φ = U(Mellin⁻¹_{1/2}Ψ)` (substitution `t = 3τ`).

`antiChartSpace` is the complex vector space of rapidly decaying `F = Mellin⁻¹_{1/2}Φ` with `Φ`
regular and antisymmetric, `Φ(w) = -m̃(w)Φ(1-w)`. Every such `F` has a continuous derivative on
`(0,∞)`, `X²|F|², |F'|² ∈ L¹`, and `∫|F'|² ≤ K²∫X²|F|²`. The charts of the theta test functions
`K₂(yx) - y⁻¹K₂(x/y)` belong to it.
-/

open Complex MeasureTheory Filter Set Topology

noncomputable section

namespace RHTower.DegreeThreeHankel

open GaloisForLFunctions.HTGeometry

/-- The chart point `x = X³/(3√3)`. -/
def chartPoint (X : ℝ) : ℝ := X ^ 3 / (3 * Real.sqrt 3)

/-- The cube-root chart of a function: `(Uf)(X) = 3^{-1/4} X f(X³/(3√3))`. -/
def chartFun (f : ℝ → ℂ) (X : ℝ) : ℂ := (3 : ℂ) ^ (-(1 / 4 : ℂ)) * (X : ℂ) * f (chartPoint X)

theorem norm_three_cpow (z : ℂ) : ‖(3 : ℂ) ^ z‖ = (3 : ℝ) ^ z.re := by
  have := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 3) z
  simpa using this

theorem stripRegular_mellinRegularStrip {Ψ : ℂ → ℂ} (h : StripRegular Ψ) :
    MellinRegularStrip Ψ 0 1 := ⟨h.diff, h.decay⟩

/-- Chart symbols of regular symbols on `0 < Re s < 1` are regular on `-1 < Re w < 2`. -/
theorem mellinRegularStrip_chartSymbol {Ψ : ℂ → ℂ} (h : MellinRegularStrip Ψ 0 1) :
    MellinRegularStrip (chartSymbol Ψ) (-1) 2 := by
  refine ⟨fun w h1 h2 => ?_, fun a b ha hb K => ?_⟩
  · have hre1 : 0 < ((w + 1) / 3).re := by simp; linarith
    have hre2 : ((w + 1) / 3).re < 1 := by simp; linarith
    have hd : DifferentiableAt ℂ (fun w : ℂ => Ψ ((w + 1) / 3)) w :=
      (h.diff _ hre1 hre2).comp w (by fun_prop)
    exact ((differentiableAt_id.div_const 2).sub_const (3 / 4)).const_cpow
      (Or.inl (by norm_num)) |>.mul hd
  · obtain ⟨C, hC⟩ := h.decay ((a + 1) / 3) ((b + 1) / 3) (by linarith) (by linarith) K
    refine ⟨3 * 9 ^ K * C, fun w h1 h2 => ?_⟩
    have hre1 : (a + 1) / 3 ≤ ((w + 1) / 3).re := by simp; linarith
    have hre2 : ((w + 1) / 3).re ≤ (b + 1) / 3 := by simp; linarith
    have hΨ := hC _ hre1 hre2
    have him : ((w + 1) / 3).im = w.im / 3 := by simp
    rw [him] at hΨ
    have hC0 : 0 ≤ C := by
      have h0 := (norm_nonneg _).trans hΨ
      have hD : 0 < (1 + (w.im / 3) ^ 2) ^ K := by positivity
      have := mul_nonneg h0 hD.le
      rwa [div_mul_cancel₀ _ hD.ne'] at this
    have hpow : ‖(3 : ℂ) ^ (w / 2 - 3 / 4)‖ ≤ 3 := by
      rw [norm_three_cpow]
      have : (w / 2 - 3 / 4 : ℂ).re ≤ 1 := by simp; linarith
      calc (3 : ℝ) ^ (w / 2 - 3 / 4 : ℂ).re ≤ (3 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) this
        _ = 3 := Real.rpow_one 3
    have hden : (1 + w.im ^ 2) ^ K ≤ 9 ^ K * (1 + (w.im / 3) ^ 2) ^ K := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by nlinarith [sq_nonneg w.im]) K
    have hq : C / (1 + (w.im / 3) ^ 2) ^ K ≤ 9 ^ K * C / (1 + w.im ^ 2) ^ K := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hden hC0]
    unfold chartSymbol
    rw [norm_mul]
    calc ‖(3 : ℂ) ^ (w / 2 - 3 / 4)‖ * ‖Ψ ((w + 1) / 3)‖
        ≤ 3 * (9 ^ K * C / (1 + w.im ^ 2) ^ K) :=
          mul_le_mul hpow (hΨ.trans hq) (norm_nonneg _) (by norm_num)
      _ = 3 * 9 ^ K * C / (1 + w.im ^ 2) ^ K := by ring

theorem chartPoint_pos {X : ℝ} (hX : 0 < X) : 0 < chartPoint X := by
  unfold chartPoint; positivity

theorem log_chartPoint {X : ℝ} (hX : 0 < X) :
    Real.log (chartPoint X) = 3 * Real.log X - 3 / 2 * Real.log 3 := by
  unfold chartPoint
  have h3 : (0 : ℝ) < Real.sqrt 3 := by positivity
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_mul (by norm_num) h3.ne',
    Real.log_sqrt (by norm_num)]
  push_cast; ring

/-- **The chart identity.** `Mellin⁻¹_{1/2}(chartSymbol Ψ)(X) = 3^{-1/4} X Mellin⁻¹_{1/2} Ψ (X³/(3√3))`. -/
theorem mellinInv_chartSymbol (Ψ : ℂ → ℂ) {X : ℝ} (hX : 0 < X) :
    mellinInv (1 / 2) (chartSymbol Ψ) X = chartFun (mellinInv (1 / 2) Ψ) X := by
  have hx := chartPoint_pos hX
  have hX0 : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hx0 : ((chartPoint X : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have h30 : (3 : ℂ) ≠ 0 := by norm_num
  have hlog3 : Complex.log 3 = ((Real.log 3 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num)]; norm_num
  have hlogX : Complex.log X = ((Real.log X : ℝ) : ℂ) := (Complex.ofReal_log hX.le).symm
  have hlogx : Complex.log (chartPoint X) = ((3 * Real.log X - 3 / 2 * Real.log 3 : ℝ) : ℂ) := by
    rw [← log_chartPoint hX, Complex.ofReal_log hx.le]
  set g : ℝ → ℂ := fun t => (X : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + t * I)) •
    chartSymbol Ψ (((1 / 2 : ℝ) : ℂ) + t * I) with hg
  have hsub := Measure.integral_comp_mul_left g (3 : ℝ)
  have hint : ∫ t : ℝ, g t = 3 * ∫ τ : ℝ, g (3 * τ) := by
    rw [hsub]; simp [abs_of_pos]
  unfold chartFun mellinInv
  rw [show (∫ y : ℝ, (X : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + y * I)) •
      chartSymbol Ψ (((1 / 2 : ℝ) : ℂ) + y * I)) = ∫ t : ℝ, g t from rfl, hint]
  have hpt : ∀ τ : ℝ, 3 * g (3 * τ) = (3 : ℂ) ^ (-(1 / 4 : ℂ)) * (X : ℂ) *
      (((chartPoint X : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + τ * I)) • Ψ (((1 / 2 : ℝ) : ℂ) + τ * I)) := by
    intro τ
    have e1 : (3 : ℂ) = Complex.exp ((Real.log 3 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log (by norm_num)]; norm_num
    have e2 : (X : ℂ) = Complex.exp ((Real.log X : ℝ) : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log hX]
    rw [show (3 : ℂ) * g (3 * τ) = Complex.exp ((Real.log 3 : ℝ) : ℂ) * g (3 * τ) by rw [← e1]]
    rw [show ∀ Y : ℂ, (3 : ℂ) ^ (-(1 / 4 : ℂ)) * (X : ℂ) * Y
        = (3 : ℂ) ^ (-(1 / 4 : ℂ)) * Complex.exp ((Real.log X : ℝ) : ℂ) * Y from
          fun Y => by rw [← e2]]
    simp only [hg, chartSymbol, smul_eq_mul]
    have harg : ((((1 / 2 : ℝ) : ℂ) + ((3 * τ : ℝ) : ℂ) * I) + 1) / 3 = ((1 / 2 : ℝ) : ℂ) + τ * I := by
      push_cast; ring
    rw [harg]
    rw [Complex.cpow_def_of_ne_zero hX0, Complex.cpow_def_of_ne_zero h30,
      Complex.cpow_def_of_ne_zero h30, Complex.cpow_def_of_ne_zero hx0, hlog3, hlogX, hlogx]
    rw [show ∀ a b c : ℂ, Complex.exp a * (Complex.exp b * (Complex.exp c * Ψ (((1 / 2 : ℝ) : ℂ) + τ * I)))
        = Complex.exp (a + b + c) * Ψ (((1 / 2 : ℝ) : ℂ) + τ * I) from fun a b c => by
          rw [Complex.exp_add, Complex.exp_add]; ring]
    rw [show ∀ a b c : ℂ, Complex.exp a * Complex.exp b * (Complex.exp c * Ψ (((1 / 2 : ℝ) : ℂ) + τ * I))
        = Complex.exp (a + b + c) * Ψ (((1 / 2 : ℝ) : ℂ) + τ * I) from fun a b c => by
          rw [Complex.exp_add, Complex.exp_add]; ring]
    congr 2
    push_cast; ring
  rw [show (3 : ℂ) * ∫ τ : ℝ, g (3 * τ) = ∫ τ : ℝ, 3 * g (3 * τ) from (integral_const_mul _ _).symm]
  simp_rw [hpt]
  rw [integral_const_mul]
  simp only [smul_eq_mul, Complex.real_smul]
  ring

/-- Antisymmetric chart functions: `F = Mellin⁻¹_{1/2} Φ` on `(0,∞)` with `Φ` regular on
`-1 < Re w < 2` and `Φ(w) = -m̃(w) Φ(1-w)`. -/
def IsAntiChart (F : ℝ → ℂ) : Prop :=
  ∃ Φ : ℂ → ℂ, MellinRegularStrip Φ (-1) 2 ∧
    (∀ w : ℂ, -1 < w.re → w.re < 2 → Φ w = -chartMultiplier w * Φ (1 - w)) ∧
    ∀ X : ℝ, 0 < X → F X = mellinInv (1 / 2) Φ X

/-- Decay faster than every power at infinity. -/
def RapidDecay (F : ℝ → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X → ‖F X‖ ≤ C * X ^ (-(N : ℝ))

/-- The space of rapidly decaying antisymmetric chart functions. -/
def antiChartSpace : Submodule ℂ (ℝ → ℂ) where
  carrier := {F | IsAntiChart F ∧ RapidDecay F}
  zero_mem' := ⟨⟨fun _ => 0, MellinRegularStrip.zero, fun w _ _ => by simp,
    fun X _ => by simp [mellinInv]⟩, fun N => ⟨0, fun X _ => by simp⟩⟩
  add_mem' := by
    rintro F G ⟨⟨Φ, hΦ, haΦ, hFΦ⟩, hdF⟩ ⟨⟨Γ, hΓ, haΓ, hGΓ⟩, hdG⟩
    refine ⟨⟨fun s => Φ s + Γ s, hΦ.add hΓ, fun w h1 h2 => ?_, fun X hX => ?_⟩, fun N => ?_⟩
    · simp only [haΦ w h1 h2, haΓ w h1 h2]; ring
    · rw [mellinInv_add hΦ hΓ (by norm_num) (by norm_num) hX, Pi.add_apply, hFΦ X hX, hGΓ X hX]
    · obtain ⟨C₁, hC₁⟩ := hdF N
      obtain ⟨C₂, hC₂⟩ := hdG N
      refine ⟨C₁ + C₂, fun X hX => ?_⟩
      calc ‖(F + G) X‖ ≤ ‖F X‖ + ‖G X‖ := norm_add_le _ _
        _ ≤ C₁ * X ^ (-(N : ℝ)) + C₂ * X ^ (-(N : ℝ)) := add_le_add (hC₁ X hX) (hC₂ X hX)
        _ = (C₁ + C₂) * X ^ (-(N : ℝ)) := by ring
  smul_mem' := by
    rintro c F ⟨⟨Φ, hΦ, haΦ, hFΦ⟩, hdF⟩
    refine ⟨⟨fun s => c * Φ s, hΦ.const_mul c, fun w h1 h2 => ?_, fun X hX => ?_⟩, fun N => ?_⟩
    · simp only [haΦ w h1 h2]; ring
    · rw [mellinInv_const_mul, Pi.smul_apply, smul_eq_mul, hFΦ X hX]
    · obtain ⟨C, hC⟩ := hdF N
      refine ⟨‖c‖ * C, fun X hX => ?_⟩
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC X hX) (norm_nonneg c)

/-- **The analytic package of an antisymmetric chart function.** With `F' = X⁻¹Mellin⁻¹(-wΦ)`:
`F' = dF/dX` on `(0,∞)`, `F'` is continuous there, `X²|F|²` and `|F'|²` are integrable, and
`∫|F'|² ≤ K² ∫X²|F|²` whenever `|u m̃(u)| ≤ K` on `Re u = -1/2`. -/
theorem IsAntiChart.analytic {K : ℝ}
    (hK : ∀ t : ℝ, ‖((-1 / 2 : ℂ) + t * I) * chartMultiplier ((-1 / 2 : ℂ) + t * I)‖ ≤ K)
    {F : ℝ → ℂ} (hF : IsAntiChart F) :
    ∃ F' : ℝ → ℂ, (∀ x, 0 < x → HasDerivAt F (F' x) x) ∧ ContinuousOn F' (Ioi 0) ∧
      IntegrableOn (fun x => x ^ 2 * ‖F x‖ ^ 2) (Ioi 0) ∧
      IntegrableOn (fun x => ‖F' x‖ ^ 2) (Ioi 0) ∧
      ∫ x in Ioi 0, ‖F' x‖ ^ 2 ≤ K ^ 2 * ∫ x in Ioi 0, x ^ 2 * ‖F x‖ ^ 2 := by
  obtain ⟨Φ, hΦ, hanti, hFeq⟩ := hF
  have hG : MellinRegularStrip (fun w => -w * Φ w) (-1) 2 := by
    have h := (hΦ.mul_id).const_mul (-1)
    have e : (fun s => -1 * (s * Φ s)) = fun w => -w * Φ w := by funext s; ring
    rwa [e] at h
  refine ⟨fun x => ((x : ℂ))⁻¹ * mellinInv (1 / 2) (fun w => -w * Φ w) x, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have h := hΦ.hasDerivAt_mellinInv (c := 1 / 2) (by norm_num) (by norm_num) (by norm_num) hx
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact hFeq y hy
  · intro x hx
    have hx' : (0 : ℝ) < x := hx
    have h := (hG.hasDerivAt_mellinInv (c := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
      hx').continuousAt
    have hinv : ContinuousAt (fun x : ℝ => ((x : ℂ))⁻¹) x :=
      (Complex.continuous_ofReal.continuousAt).inv₀ (by exact_mod_cast hx'.ne')
    exact (hinv.mul h).continuousWithinAt
  · have h := integrableOn_norm_sq_mellinInv (Ψ := Φ) (σ := 3 / 2)
      (hΦ.integrable_line (c := 3 / 2) (by norm_num) (by norm_num))
      (hΦ.memLp_two_line (c := 3 / 2) (by norm_num) (by norm_num))
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx' : (0 : ℝ) < x := hx
    beta_reduce
    rw [hFeq x hx', hΦ.mellinInv_eq (c₁ := 1 / 2) (c₂ := 3 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hx', show 2 * (3 / 2 : ℝ) - 1 = (2 : ℕ) by norm_num,
      Real.rpow_natCast]
    ring
  · have h := integrableOn_norm_sq_mellinInv (Ψ := fun w => -w * Φ w) (σ := -1 / 2)
      (hG.integrable_line (c := -1 / 2) (by norm_num) (by norm_num))
      (hG.memLp_two_line (c := -1 / 2) (by norm_num) (by norm_num))
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx' : (0 : ℝ) < x := hx
    beta_reduce
    rw [hG.mellinInv_eq (c₁ := -1 / 2) (c₂ := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hx', norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx', mul_pow, show 2 * (-1 / 2 : ℝ) - 1 = -2 by norm_num, Real.rpow_neg hx'.le]
    norm_cast
    ring
  · have h := integral_norm_sq_chartDeriv_le hΦ hanti hK
    have e : ∫ x in Ioi (0 : ℝ), x ^ 2 * ‖F x‖ ^ 2
        = ∫ x in Ioi (0 : ℝ), ‖mellinInv (1 / 2) Φ x‖ ^ 2 * x ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [hFeq x hx]; ring
    rw [e]
    exact h

/-- The chart functions of the theta test functions `K₂(yx) - y⁻¹K₂(x/y)` belong to the
antisymmetric chart space. -/
theorem chartFun_thetaTestFunction_mem {y : ℝ} (hy : 0 < y) :
    chartFun (thetaTestFunction y) ∈ antiChartSpace := by
  refine ⟨⟨chartSymbol (thetaTestSymbol y),
    mellinRegularStrip_chartSymbol (stripRegular_mellinRegularStrip (stripRegular_thetaTestSymbol hy)),
    fun w h1 h2 => chartSymbol_antisymm (thetaTestSymbol_antisymm _ (by simp; linarith)),
    fun X hX => ?_⟩, fun N => ?_⟩
  · rw [mellinInv_chartSymbol _ hX]
    unfold chartFun
    rw [mellinInv_thetaTestSymbol hy (by norm_num) (by norm_num) (chartPoint_pos hX)]
  · set c : ℝ := ((N : ℝ) + 1) / 3 with hc
    have hc0 : 0 < c := by positivity
    obtain ⟨C, hC⟩ := exists_norm_gammaRPowKernel_le 2 hc0
    have hC0 : 0 ≤ C := by
      have := (norm_nonneg _).trans (hC 1 one_pos)
      simpa using this
    set D : ℝ := ‖(3 : ℂ) ^ (-(1 / 4 : ℂ))‖ * C * (y ^ (-c) + y⁻¹ * y⁻¹ ^ (-c)) *
      (3 * Real.sqrt 3) ^ c with hD
    refine ⟨D, fun X hX => ?_⟩
    have hX0 : 0 < X := by linarith
    have hx := chartPoint_pos hX0
    have hth : ‖thetaTestFunction y (chartPoint X)‖
        ≤ C * (y ^ (-c) + y⁻¹ * y⁻¹ ^ (-c)) * chartPoint X ^ (-c) := by
      unfold thetaTestFunction
      have h1 := hC (y * chartPoint X) (mul_pos hy hx)
      have h2 := hC (y⁻¹ * chartPoint X) (mul_pos (inv_pos.mpr hy) hx)
      rw [Real.mul_rpow hy.le hx.le] at h1
      rw [Real.mul_rpow (inv_pos.mpr hy).le hx.le] at h2
      calc ‖gammaRPowKernel 2 (y * chartPoint X) - ((y⁻¹ : ℝ) : ℂ) * gammaRPowKernel 2 (y⁻¹ * chartPoint X)‖
          ≤ ‖gammaRPowKernel 2 (y * chartPoint X)‖ + y⁻¹ * ‖gammaRPowKernel 2 (y⁻¹ * chartPoint X)‖ := by
            refine (norm_sub_le _ _).trans (le_of_eq ?_)
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy)]
        _ ≤ C * (y ^ (-c) * chartPoint X ^ (-c)) + y⁻¹ * (C * (y⁻¹ ^ (-c) * chartPoint X ^ (-c))) :=
            add_le_add h1 (mul_le_mul_of_nonneg_left h2 (inv_pos.mpr hy).le)
        _ = _ := by ring
    have hpt : chartPoint X ^ (-c) = (3 * Real.sqrt 3) ^ c * X ^ (-(3 * c)) := by
      unfold chartPoint
      rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul hX0.le, Real.rpow_neg (by positivity), div_eq_mul_inv, inv_inv]
      push_cast; ring_nf
    have hexp : X * X ^ (-(3 * c)) = X ^ (-(N : ℝ)) := by
      rw [show X * X ^ (-(3 * c)) = X ^ (1 : ℝ) * X ^ (-(3 * c)) by rw [Real.rpow_one],
        ← Real.rpow_add hX0]
      congr 1; rw [hc]; ring
    unfold chartFun
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX0]
    calc ‖(3 : ℂ) ^ (-(1 / 4 : ℂ))‖ * X * ‖thetaTestFunction y (chartPoint X)‖
        ≤ ‖(3 : ℂ) ^ (-(1 / 4 : ℂ))‖ * X *
            (C * (y ^ (-c) + y⁻¹ * y⁻¹ ^ (-c)) * chartPoint X ^ (-c)) :=
          mul_le_mul_of_nonneg_left hth (by positivity)
      _ = D * (X * X ^ (-(3 * c))) := by rw [hpt, hD]; ring
      _ = D * X ^ (-(N : ℝ)) := by rw [hexp]

end RHTower.DegreeThreeHankel
