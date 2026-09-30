import GaloisForLFunctions.RHTower.ZetaNotchCrudeTail
import GaloisForLFunctions.RHTower.WeilNullPotentialSpectralPairing

/-!
# The `|ζ|²`-notch test function

On the critical line `Ξ(t)² = ((¼+t²)/2)² Γℝ(½+it) Γℝ(½−it) |ζ(½+it)|²`
(`XiC_sq_mul_gammaWeightInv`), because `ξ(s) = s(s−1)/2 · Γℝ(s) ζ(s)`, `ξ(½+it) = ξ(½−it)` and
`s(s−1) = −(¼+t²)`. The reciprocal weight `w(t)^{−1} = (2/(¼+t²))² Γℝ(½+it)^{−1} Γℝ(½−it)^{−1}` is
smooth (`1/Γℝ` is entire) and positive (`Γℝ(s̄) = conj Γℝ(s)`).

For a smooth weight `Q` the test function `G = ω Q w^{−1}` is smooth with compact support and
`Ξ² G = ω Q |ζ(½+it)|²`. On the frequency line `g(ξ) = G(2πξ)` this gives
(`fourier_riemannXi_sq_mul_notchTest`)

`𝓕(Ξ² g)(y) = (1/2π) ∫ ω(t) Q(t) |ζ(½+it)|² e^{−iyt} dt`,

and `𝓕g` decays faster than every power (`exists_norm_fourier_mul_pow_le`).
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry
open FourierTransform
open scoped ComplexConjugate

namespace RHTower.ZetaNotch

/-! ## `Ξ²` on the critical line -/

theorem xi_eq_half_mul_gammaR_zeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hre : 0 < s.re) :
    xi s = s * (s - 1) / 2 * (Complex.Gammaℝ s * riemannZeta s) := by
  have hG := Complex.Gammaℝ_ne_zero_of_re_pos hre
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  rw [riemannZeta_def_of_ne_zero hs0, xi, completedRiemannZeta_eq]
  field_simp
  ring

theorem linePt_re (t : ℝ) : (linePt t).re = 1 / 2 := by
  unfold linePt
  simp

theorem linePt_ne_zero (t : ℝ) : linePt t ≠ 0 := fun h => by
  have := linePt_re t
  rw [h, Complex.zero_re] at this
  norm_num at this

theorem linePt_ne_one (t : ℝ) : linePt t ≠ 1 := fun h => by
  have := linePt_re t
  rw [h, Complex.one_re] at this
  norm_num at this

theorem gammaR_linePt_ne_zero (t : ℝ) : Complex.Gammaℝ (linePt t) ≠ 0 :=
  Complex.Gammaℝ_ne_zero_of_re_pos (by rw [linePt_re]; norm_num)

theorem linePt_mul_sub_one (t : ℝ) : linePt t * (linePt t - 1) = -((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
  unfold linePt
  push_cast
  linear_combination (t : ℂ) ^ 2 * Complex.I_sq

theorem XiC_ofReal_eq (t : ℝ) : XiC (t : ℂ) = xi (linePt t) := by
  unfold XiC linePt
  push_cast
  ring_nf

/-- The reciprocal Gamma weight `(2/(¼+t²))² Γℝ(½+it)^{−1} Γℝ(½−it)^{−1}`. -/
def gammaWeightInv (t : ℝ) : ℂ :=
  ((2 / (1 / 4 + t ^ 2) : ℝ) : ℂ) ^ 2 * ((Complex.Gammaℝ (linePt t))⁻¹ * (Complex.Gammaℝ (linePt (-t)))⁻¹)

theorem xiSq_gammaWeight_algebra {c G₁ G₂ z₁ z₂ : ℂ} (hc : c ≠ 0) (h₁ : G₁ ≠ 0) (h₂ : G₂ ≠ 0) :
    -c / 2 * (G₁ * z₁) * (-c / 2 * (G₂ * z₂)) * ((2 / c) ^ 2 * (G₁⁻¹ * G₂⁻¹)) = z₁ * z₂ := by
  field_simp

/-- **`Ξ(t)² w(t)^{−1} = |ζ(½+it)|²`.** -/
theorem XiC_sq_mul_gammaWeightInv (t : ℝ) : XiC (t : ℂ) ^ 2 * gammaWeightInv t = zetaSq t := by
  have hre : ∀ τ : ℝ, 0 < (linePt τ).re := fun τ => by rw [linePt_re]; norm_num
  have e1 : XiC (t : ℂ) = linePt t * (linePt t - 1) / 2 *
      (Complex.Gammaℝ (linePt t) * riemannZeta (linePt t)) := by
    rw [XiC_ofReal_eq, xi_eq_half_mul_gammaR_zeta (linePt_ne_zero t) (linePt_ne_one t) (hre t)]
  have e2 : XiC (t : ℂ) = linePt (-t) * (linePt (-t) - 1) / 2 *
      (Complex.Gammaℝ (linePt (-t)) * riemannZeta (linePt (-t))) := by
    rw [← XiC_even, ← Complex.ofReal_neg, XiC_ofReal_eq,
      xi_eq_half_mul_gammaR_zeta (linePt_ne_zero _) (linePt_ne_one _) (hre _)]
  have hq : (1 / 4 + t ^ 2 : ℝ) ≠ 0 := by positivity
  have hG1 := gammaR_linePt_ne_zero t
  have hG2 := gammaR_linePt_ne_zero (-t)
  rw [sq]
  nth_rewrite 1 [e1]
  rw [e2]
  rw [linePt_mul_sub_one t, linePt_mul_sub_one (-t), neg_sq]
  unfold gammaWeightInv zetaSq
  have hq' : ((1 / 4 + t ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq
  rw [show ((2 / (1 / 4 + t ^ 2) : ℝ) : ℂ) = 2 / ((1 / 4 + t ^ 2 : ℝ) : ℂ) by push_cast; ring]
  exact xiSq_gammaWeight_algebra hq' hG1 hG2

theorem gammaR_conj (s : ℂ) : Complex.Gammaℝ (conj s) = conj (Complex.Gammaℝ s) := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul]
  have hπ : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_pos.ne
  congr 1
  · rw [show -conj s / 2 = conj (-s / 2) by rw [map_div₀, map_neg, map_ofNat],
      Complex.cpow_conj _ _ hπ, Complex.conj_ofReal]
  · rw [← Complex.Gamma_conj, map_div₀, map_ofNat]

theorem linePt_neg_eq_conj' (t : ℝ) : linePt (-t) = conj (linePt t) := by
  unfold linePt
  apply Complex.ext <;> simp

/-- The reciprocal weight is real and positive. -/
theorem gammaWeightInv_eq_ofReal (t : ℝ) :
    gammaWeightInv t = (((2 / (1 / 4 + t ^ 2)) ^ 2 / Complex.normSq (Complex.Gammaℝ (linePt t)) : ℝ) : ℂ) := by
  unfold gammaWeightInv
  rw [linePt_neg_eq_conj', gammaR_conj, ← mul_inv, Complex.mul_conj]
  push_cast
  ring

theorem gammaWeightInv_real_pos (t : ℝ) :
    0 < (2 / (1 / 4 + t ^ 2)) ^ 2 / Complex.normSq (Complex.Gammaℝ (linePt t)) := by
  have := Complex.normSq_pos.mpr (gammaR_linePt_ne_zero t)
  positivity

theorem contDiff_gammaWeightInv (n : ℕ∞) : ContDiff ℝ n gammaWeightInv := by
  have hline : ∀ σ : ℝ, ContDiff ℝ n (fun t : ℝ => linePt (σ * t)) := by
    intro σ
    unfold linePt
    exact contDiff_const.add ((Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul contDiff_id)).mul contDiff_const)
  have hG : ∀ σ : ℝ, ContDiff ℝ n (fun t : ℝ => (Complex.Gammaℝ (linePt (σ * t)))⁻¹) := fun σ =>
    (Complex.differentiable_Gammaℝ_inv.contDiff.restrict_scalars ℝ).comp (hline σ)
  have hq : ContDiff ℝ n (fun t : ℝ => ((2 / (1 / 4 + t ^ 2) : ℝ) : ℂ) ^ 2) := by
    refine (Complex.ofRealCLM.contDiff.comp ?_).pow 2
    exact contDiff_const.div (contDiff_const.add (contDiff_id.pow 2)) fun t => by positivity
  have h := hq.mul ((hG 1).mul (hG (-1)))
  have e : gammaWeightInv = fun t : ℝ => ((2 / (1 / 4 + t ^ 2) : ℝ) : ℂ) ^ 2 *
      ((Complex.Gammaℝ (linePt (1 * t)))⁻¹ * (Complex.Gammaℝ (linePt (-1 * t)))⁻¹) := by
    funext t
    simp only [gammaWeightInv, one_mul, neg_one_mul]
  rw [e]
  exact h

/-! ## Polynomial decay of the transform of a smooth compactly supported function -/

/-- If `f` is `C^J` with compact support, `‖𝓕f(v)‖ (1 + |v|)^J` is bounded. -/
theorem exists_norm_fourier_mul_pow_le {f : ℝ → ℂ} {J : ℕ} (hf : ContDiff ℝ J f)
    (hsupp : HasCompactSupport f) : ∃ C : ℝ, ∀ v : ℝ, ‖𝓕 f v‖ * (1 + |v|) ^ J ≤ C := by
  set I₀ : ℝ := ∫ t, ‖f t‖ with hI₀
  set IJ : ℝ := ∫ t, ‖iteratedDeriv J f t‖ with hIJ
  have hI₀0 : 0 ≤ I₀ := integral_nonneg fun t => norm_nonneg _
  have hIJ0 : 0 ≤ IJ := integral_nonneg fun t => norm_nonneg _
  refine ⟨2 ^ J * (I₀ + IJ / (2 * Real.pi) ^ J), fun v => ?_⟩
  have hq : 0 ≤ IJ / (2 * Real.pi) ^ J := by positivity
  rcases le_or_gt |v| 1 with hv | hv
  · have h1 := RHTower.WeilExcess.norm_fourier_le_integral_norm f v
    have h2 : (1 + |v|) ^ J ≤ 2 ^ J := pow_le_pow_left₀ (by positivity) (by linarith) J
    calc ‖𝓕 f v‖ * (1 + |v|) ^ J ≤ I₀ * 2 ^ J :=
          mul_le_mul h1 h2 (by positivity) hI₀0
      _ ≤ 2 ^ J * (I₀ + IJ / (2 * Real.pi) ^ J) := by nlinarith [pow_pos (two_pos (α := ℝ)) J]
  · have hv0 : v ≠ 0 := fun h => by rw [h, abs_zero] at hv; linarith
    have h1 := norm_fourier_le_of_iteratedDeriv J hf
      (fun n hn => integrable_iteratedDeriv_of_hasCompactSupport hf hsupp hn) hv0
    have h2 : (1 + |v|) ^ J ≤ (2 * |v|) ^ J := pow_le_pow_left₀ (by positivity) (by linarith) J
    have hden : 0 < (2 * Real.pi * |v|) ^ J := by positivity
    calc ‖𝓕 f v‖ * (1 + |v|) ^ J ≤ IJ / (2 * Real.pi * |v|) ^ J * (2 * |v|) ^ J :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 ^ J * (IJ / (2 * Real.pi) ^ J) := by
          rw [mul_pow, mul_pow, mul_pow]
          field_simp
      _ ≤ 2 ^ J * (I₀ + IJ / (2 * Real.pi) ^ J) := by
          have : 0 ≤ (2 : ℝ) ^ J * I₀ := by positivity
          nlinarith

/-! ## The test function -/

/-- The notch test function `G(t) = ω(t) Q(t) w(t)^{−1}`. -/
def notchTest (L : ℝ) (Q : ℝ → ℂ) (t : ℝ) : ℂ := notchWindow L t * Q t * gammaWeightInv t

/-- The test function on the frequency line, `g(ξ) = G(2πξ)`. -/
def notchTestFreq (L : ℝ) (Q : ℝ → ℂ) (ξ : ℝ) : ℂ := notchTest L Q (2 * Real.pi * ξ)

variable {L : ℝ} {Q : ℝ → ℂ}

theorem contDiff_notchTestFreq {n : ℕ} (hQ : ContDiff ℝ n Q) : ContDiff ℝ n (notchTestFreq L Q) := by
  have hG : ContDiff ℝ n (notchTest L Q) :=
    (((contDiff_notchWindow L).of_le (WithTop.coe_le_coe.mpr le_top)).mul hQ).mul
      (contDiff_gammaWeightInv n)
  exact hG.comp (contDiff_const.mul contDiff_id)

theorem notchTestFreq_eq_zero (hL : 0 < L) {ξ : ℝ}
    (hξ : ξ ∉ Icc (L / 2 / (2 * Real.pi)) (5 * L / 2 / (2 * Real.pi))) :
    notchTestFreq L Q ξ = 0 := by
  unfold notchTestFreq notchTest
  have hπ : 0 < 2 * Real.pi := by positivity
  rw [notchWindow_eq_zero hL, zero_mul, zero_mul]
  intro h
  apply hξ
  constructor
  · rw [div_le_iff₀ hπ]; linarith [h.1]
  · rw [le_div_iff₀ hπ]; linarith [h.2]

theorem hasCompactSupport_notchTestFreq (hL : 0 < L) : HasCompactSupport (notchTestFreq L Q) :=
  HasCompactSupport.intro isCompact_Icc fun _ hξ => notchTestFreq_eq_zero hL hξ

theorem riemannXi_sq_mul_notchTestFreq (ξ : ℝ) :
    RHTower.WeilExcess.riemannXi ξ ^ 2 * notchTestFreq L Q ξ =
      notchWindow L (2 * Real.pi * ξ) * Q (2 * Real.pi * ξ) * zetaSq (2 * Real.pi * ξ) := by
  rw [RHTower.WeilExcess.riemannXi_eq_XiC,
    show (2 * Real.pi * ξ : ℂ) = ((2 * Real.pi * ξ : ℝ) : ℂ) by push_cast; ring]
  unfold notchTestFreq notchTest
  rw [← XiC_sq_mul_gammaWeightInv]
  ring

/-- **The transform of `Ξ² g` is the `Q`-weighted twisted moment.** -/
theorem fourier_riemannXi_sq_mul_notchTestFreq (y : ℝ) :
    𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * notchTestFreq L Q ξ) y =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t, notchWindow L t * Q t * zetaSq t * Complex.exp (-(y * t) * I) := by
  rw [RHTower.WeilExcess.fourier_eq_integral]
  set f : ℝ → ℂ := fun t => notchWindow L t * Q t * zetaSq t * Complex.exp (-(y * t) * I) with hf
  have e : (fun ξ : ℝ => Complex.exp (-(2 * Real.pi * ξ * y : ℝ) * I) *
      (RHTower.WeilExcess.riemannXi ξ ^ 2 * notchTestFreq L Q ξ)) =
      fun ξ : ℝ => f (2 * Real.pi * ξ) := by
    funext ξ
    rw [riemannXi_sq_mul_notchTestFreq, hf]
    simp only
    rw [show -((2 * Real.pi * ξ * y : ℝ) : ℂ) * I = -((y : ℂ) * ((2 * Real.pi * ξ : ℝ) : ℂ)) * I by
      push_cast; ring]
    ring
  rw [e, Measure.integral_comp_mul_left f (2 * Real.pi), Complex.real_smul]
  congr 1
  rw [abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹), one_div]

theorem notchTestFreq_div_two_pi (t : ℝ) :
    notchTestFreq L Q (t / (2 * Real.pi)) = notchTest L Q t := by
  unfold notchTestFreq
  congr 1
  field_simp

/-- With a real nonnegative weight the test function is real and nonnegative. -/
theorem notchTest_ofReal_eq {q : ℝ → ℝ} (t : ℝ) :
    notchTest L (fun t => (q t : ℂ)) t = ((blockWindow L (2 * L) (L / 2) t * q t *
      ((2 / (1 / 4 + t ^ 2)) ^ 2 / Complex.normSq (Complex.Gammaℝ (linePt t))) : ℝ) : ℂ) := by
  unfold notchTest notchWindow blockWindowC
  rw [gammaWeightInv_eq_ofReal]
  push_cast
  ring

theorem notchTest_re_nonneg {q : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t) (t : ℝ) :
    0 ≤ (notchTest L (fun t => (q t : ℂ)) t).re := by
  rw [notchTest_ofReal_eq, Complex.ofReal_re]
  exact mul_nonneg (mul_nonneg (blockWindow_nonneg _ _ _ _) (hq t))
    (gammaWeightInv_real_pos t).le

end RHTower.ZetaNotch
