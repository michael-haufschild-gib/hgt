import GaloisForLFunctions.RHTower.RiemannKernelStripThetaBounds
import GaloisForLFunctions.RHTower.RiemannKernelStripPlancherel
import GaloisForLFunctions.RHTower.XiSecondOrderLaguerrePolyaPreimage
import GaloisForLFunctions.HTGeometry.PoincareTilingVanishing

/-!
# LP-maximality of Ξ in degree two

**Theorem** (`not_exists_laguerrePolya_secondOrder_preimage_XiC`). For `a₁, a₂ > 0` there is no
Laguerre–Pólya function `ψ` with `(1 − D/a₁)(1 − D/a₂)ψ = Ξ`.

Proof. Such a `ψ` makes `Ξ` Laguerre–Pólya, so RH holds. Littlewood's short windows and
first-order interlacing then put a zero of `ψ₀ = ψ|_ℝ` in every window `[t, t+h]` at large height,
for every `h > 0` (`Littlewood.riemannHypothesis_and_kernelPsi_zeros_of_secondOrder_preimage`).
Here `ψ₀(x) = ∫Φ(u)m(u)e^{ixu}du` with `m(u) = 1/((1−iu/a₁)(1−iu/a₂))`.

For `0 < c < π/4` put `g = e^{cx}ψ₀` and `G(u) = Φ(u+ic)m(u+ic)`. Plancherel gives
`∫|g|² = 2π∫|G|²` and `∫|g′|² = 2π∫u²|G|²`. On the line `Im = c` Riemann's kernel is a theta
series near the real axis, and Parseval over periods makes `|Φ(u+ic)|²` flat at height
`(cos 2c)^{-9/2}`:
* `∫|G|² ≥ L(cos 2c)^{-9/2}` (`exists_integral_norm_sq_shiftedProfile_ge`);
* `∫u²|G|² ≤ C(cos 2c)^{-9/2}`, since `u²|m|² ≲ 1/(1+u²)` in degree two
  (`integral_sq_mul_norm_sq_shiftedProfile_le`).

Poincaré on tiles of length `h` gives `∫|g|² ≤ H + h²∫|g′|²` (`integral_norm_sq_le_of_zero_tiles`),
with a head `H` independent of `c`. Choosing `h² C ≤ L/2` and letting `c → π/4` is a contradiction
(`false_of_kernelPsi_zeros`).

The same argument fails in degree one: there `u²|m|²` tends to a positive constant, which is not
integrable against a flat spectrum of width `log(1/cos 2c)`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform
open Zeta23

noncomputable section

namespace RHTower.KernelStrip

/-! ## The Lorentz pair on the strip -/

theorem norm_one_sub_I_mul_div_ge {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 ≤ z.im) :
    1 ≤ ‖1 - I * z / a‖ ∧ |z.re| / a ≤ ‖1 - I * z / a‖ := by
  have hre : (1 - I * z / a).re = 1 + z.im / a := by
    simp [Complex.div_re, Complex.mul_re, Complex.normSq_ofReal]; field_simp; ring
  have him : (1 - I * z / a).im = -(z.re / a) := by
    simp [Complex.div_im, Complex.mul_im, Complex.normSq_ofReal]; field_simp
  constructor
  · have := Complex.abs_re_le_norm (1 - I * z / a)
    rw [hre] at this
    have h0 : 0 ≤ z.im / a := div_nonneg hz ha.le
    rw [abs_of_nonneg (by linarith)] at this
    linarith
  · have := Complex.abs_im_le_norm (1 - I * z / a)
    rw [him, abs_neg, abs_div, abs_of_pos ha] at this
    exact this

theorem lorentzPair_ne {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 ≤ z.im) : 1 - I * z / a ≠ 0 := by
  intro h
  have := (norm_one_sub_I_mul_div_ge ha hz).1
  rw [h, norm_zero] at this
  linarith

theorem norm_lorentzPair_le_one {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖lorentzPair a₁ a₂ z‖ ≤ 1 := by
  rw [lorentzPair, norm_div, norm_one, norm_mul]
  have := (norm_one_sub_I_mul_div_ge h₁ hz).1
  have := (norm_one_sub_I_mul_div_ge h₂ hz).1
  rw [div_le_one (by positivity)]
  nlinarith

theorem differentiableAt_lorentzPair {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) {z : ℂ}
    (hz : 0 ≤ z.im) : DifferentiableAt ℂ (lorentzPair a₁ a₂) z := by
  unfold lorentzPair
  refine (differentiableAt_const _).div ?_ (mul_ne_zero (lorentzPair_ne h₁ hz) (lorentzPair_ne h₂ hz))
  fun_prop

/-- `u²|m(u+ic)|² ≤ 2(1 + (a₁a₂)²)/(1 + u²)` on the line `Im = c ≥ 0`. -/
theorem sq_mul_norm_sq_lorentzPair_le {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) {c : ℝ} (hc : 0 ≤ c)
    (u : ℝ) :
    u ^ 2 * ‖lorentzPair a₁ a₂ ((u : ℂ) + c * I)‖ ^ 2 ≤ 2 * (1 + (a₁ * a₂) ^ 2) / (1 + u ^ 2) := by
  set z : ℂ := (u : ℂ) + c * I
  have hz : 0 ≤ z.im := by simp [z, hc]
  have hzr : z.re = u := by simp [z]
  obtain ⟨g1, g1'⟩ := norm_one_sub_I_mul_div_ge h₁ hz
  obtain ⟨g2, g2'⟩ := norm_one_sub_I_mul_div_ge h₂ hz
  rw [hzr] at g1' g2'
  set n₁ := ‖1 - I * z / a₁‖
  set n₂ := ‖1 - I * z / a₂‖
  have hm : ‖lorentzPair a₁ a₂ z‖ = 1 / (n₁ * n₂) := by
    rw [lorentzPair, norm_div, norm_one, norm_mul]
  rw [hm]
  have hn : 0 < n₁ * n₂ := by positivity
  have hu1 : 0 < 1 + u ^ 2 := by positivity
  rw [div_pow, one_pow, ← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) hu1]
  rcases le_total (u ^ 2) 1 with h | h
  · nlinarith [mul_le_mul g1 g2 zero_le_one (by linarith), sq_nonneg (a₁ * a₂)]
  · have hab : |u| / a₁ * (|u| / a₂) ≤ n₁ * n₂ :=
      mul_le_mul g1' g2' (by positivity) (by linarith)
    have hab' : u ^ 2 ≤ a₁ * a₂ * (n₁ * n₂) := by
      have : |u| / a₁ * (|u| / a₂) = u ^ 2 / (a₁ * a₂) := by
        rw [div_mul_div_comm, ← sq_abs u, sq]
      rw [this, div_le_iff₀ (by positivity)] at hab
      linarith
    nlinarith [sq_nonneg (n₁ * n₂), mul_le_mul hab' hab' (by positivity) (by positivity)]


theorem sum_inv_one_add_sq_le (N : ℕ) :
    ∑ j ∈ Finset.range N, 1 / (1 + (j : ℝ) ^ 2) ≤ 4 - 4 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have key : 1 / (1 + (N : ℝ) ^ 2) ≤ 4 / ((N : ℝ) + 1) - 4 / ((N : ℝ) + 1 + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith [sq_nonneg ((N : ℝ) - 1 / 2)]
    push_cast at key ⊢
    linarith

theorem norm_lorentzPair_line_ge {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) {c u R : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hu : |u| ≤ R) :
    1 / ((1 + (R + 1) / a₁) * (1 + (R + 1) / a₂)) ≤ ‖lorentzPair a₁ a₂ ((u : ℂ) + c * I)‖ := by
  have hz : 0 ≤ ((u : ℂ) + c * I).im := by simp [hc0]
  have hnorm : ∀ {a : ℝ}, 0 < a → ‖1 - I * ((u : ℂ) + c * I) / a‖ ≤ 1 + (R + 1) / a := by
    intro a ha
    calc ‖1 - I * ((u : ℂ) + c * I) / a‖ ≤ ‖(1 : ℂ)‖ + ‖I * ((u : ℂ) + c * I) / a‖ := norm_sub_le _ _
      _ = 1 + ‖(u : ℂ) + c * I‖ / a := by
          rw [norm_one, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos ha]
      _ ≤ 1 + (R + 1) / a := by
          gcongr
          calc ‖(u : ℂ) + c * I‖ ≤ ‖(u : ℂ)‖ + ‖(c : ℂ) * I‖ := norm_add_le _ _
            _ = |u| + c := by
                rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
                  Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc0]
            _ ≤ R + 1 := by linarith
  rw [lorentzPair, norm_div, norm_one, norm_mul]
  have n1 := hnorm h₁
  have n2 := hnorm h₂
  have p1 := (norm_one_sub_I_mul_div_ge h₁ hz).1
  have p2 := (norm_one_sub_I_mul_div_ge h₂ hz).1
  apply one_div_le_one_div_of_le (mul_pos (by linarith) (by linarith))
  exact mul_le_mul n1 n2 (by linarith) (by linarith)

variable {a₁ a₂ : ℝ}

theorem lorentzPair_hm (h₁ : 0 < a₁) (h₂ : 0 < a₂) (c : ℝ) :
    ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c → DifferentiableAt ℂ (lorentzPair a₁ a₂) z :=
  fun _ hz _ => differentiableAt_lorentzPair h₁ h₂ hz

theorem lorentzPair_hmb (h₁ : 0 < a₁) (h₂ : 0 < a₂) (c : ℝ) :
    ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c → ‖lorentzPair a₁ a₂ z‖ ≤ 1 :=
  fun _ hz _ => norm_lorentzPair_le_one h₁ h₂ hz

/-- **Whole-line upper bound** for the derivative energy:
`∫u²|G(u)|²du ≤ 16(1 + (a₁a₂)²) C (cos 2c)^{-4}/√(cos 2c)`. -/
theorem integral_sq_mul_norm_sq_shiftedProfile_le (h₁ : 0 < a₁) (h₂ : 0 < a₂) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c < π / 4) (hs : 1 / 2 ≤ Real.sin (2 * c)) :
    ∫ u : ℝ, u ^ 2 * ‖shiftedProfile (lorentzPair a₁ a₂) c u‖ ^ 2 ≤
      16 * (1 + (a₁ * a₂) ^ 2) * kernelWindowConst * (Real.cos (2 * c))⁻¹ ^ 4 *
        (1 / Real.sqrt (Real.cos (2 * c))) := by
  obtain ⟨-, -, -, h4⟩ := shiftedProfile_integrability hc0 hc (lorentzPair_hm h₁ h₂ c)
    (lorentzPair_hmb h₁ h₂ c)
  set F : ℝ → ℝ := fun u => u ^ 2 * ‖shiftedProfile (lorentzPair a₁ a₂) c u‖ ^ 2 with hF_def
  have hFint : Integrable F := by
    have := h4.integrable_norm_pow (p := 2) (by norm_num)
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only [hF_def, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs]
  set W : ℝ := kernelWindowConst * (Real.cos (2 * c))⁻¹ ^ 4 * (1 / Real.sqrt (Real.cos (2 * c)))
    with hW_def
  set P : ℝ := 2 * (1 + (a₁ * a₂) ^ 2) with hP_def
  have hP : 0 ≤ P := by positivity
  have hW : 0 ≤ W := by
    have hk : 0 ≤ kernelWindowConst := by
      unfold kernelWindowConst
      have := thetaWindowConst_nonneg 4; have := thetaWindowConst_nonneg 2; positivity
    have : 0 < Real.cos (2 * c) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
    positivity
  have hGc := continuous_shiftedProfile hc0 hc (lorentzPair_hm h₁ h₂ c)
  have hFc : Continuous F := by
    simp only [hF_def]; fun_prop
  have hPhic : Continuous fun u : ℝ => ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 :=
    (continuous_kernelC_line hc0 hc).norm.pow 2
  -- one window, either side
  have hwin : ∀ (j : ℕ) (σ : ℝ), (σ = 1 ∨ σ = -1) →
      ∫ u in (j : ℝ)..j + 1, F (σ * u) ≤ P / (1 + (j : ℝ) ^ 2) * W := by
    intro j σ hσ
    have hσ2 : σ ^ 2 = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
    have hjj : (j : ℝ) ≤ j + 1 := by linarith
    have hpt : ∀ u ∈ Icc (j : ℝ) (j + 1), F (σ * u) ≤
        P / (1 + (j : ℝ) ^ 2) * ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 := by
      intro u hu
      have hu0 : 0 ≤ u := le_trans (Nat.cast_nonneg j) hu.1
      have hnorm : ‖kernelC (((σ * u : ℝ) : ℂ) + c * I)‖ = ‖kernelC ((u : ℂ) + c * I)‖ := by
        rcases hσ with h | h
        · rw [h, one_mul]
        · rw [h, neg_one_mul]; exact norm_kernelC_neg_line hc0 hc u
      have hwt := sq_mul_norm_sq_lorentzPair_le h₁ h₂ hc0 (σ * u)
      have hsq : (σ * u) ^ 2 = u ^ 2 := by rw [mul_pow, hσ2, one_mul]
      rw [hsq] at hwt
      have hjle : P / (1 + u ^ 2) ≤ P / (1 + (j : ℝ) ^ 2) :=
        div_le_div_of_nonneg_left hP (by positivity) (by nlinarith [hu.1])
      simp only [hF_def, shiftedProfile, norm_mul, mul_pow, hnorm]
      have hK := sq_nonneg ‖kernelC ((u : ℂ) + c * I)‖
      calc σ ^ 2 * u ^ 2 * (‖kernelC ((u : ℂ) + c * I)‖ ^ 2 *
            ‖lorentzPair a₁ a₂ (((σ * u : ℝ) : ℂ) + c * I)‖ ^ 2)
          = (u ^ 2 * ‖lorentzPair a₁ a₂ (((σ * u : ℝ) : ℂ) + c * I)‖ ^ 2) *
              ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 := by rw [hσ2]; ring
        _ ≤ P / (1 + u ^ 2) * ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hwt hK
        _ ≤ P / (1 + (j : ℝ) ^ 2) * ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hjle hK
    calc ∫ u in (j : ℝ)..j + 1, F (σ * u)
        ≤ ∫ u in (j : ℝ)..j + 1, P / (1 + (j : ℝ) ^ 2) * ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 :=
          intervalIntegral.integral_mono_on hjj
            ((hFc.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
            ((hPhic.const_mul _).intervalIntegrable _ _) hpt
      _ = P / (1 + (j : ℝ) ^ 2) * ∫ u in (j : ℝ)..j + 1, ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ P / (1 + (j : ℝ) ^ 2) * W := by
          gcongr
          exact integral_norm_sq_kernelC_line_le hc0 hc hs (Nat.cast_nonneg j)
  have hhalf : ∀ (N : ℕ) (σ : ℝ), (σ = 1 ∨ σ = -1) →
      ∫ u in (0 : ℝ)..N, F (σ * u) ≤ 4 * P * W := by
    intro N σ hσ
    have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun j : ℕ => (j : ℝ))
      (f := fun u => F (σ * u)) (μ := volume) (n := N)
      (fun j _ => (hFc.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at hsum
    rw [← hsum]
    calc ∑ j ∈ Finset.range N, ∫ u in (j : ℝ)..j + 1, F (σ * u)
        ≤ ∑ j ∈ Finset.range N, P / (1 + (j : ℝ) ^ 2) * W :=
          Finset.sum_le_sum fun j _ => hwin j σ hσ
      _ = P * W * ∑ j ∈ Finset.range N, 1 / (1 + (j : ℝ) ^ 2) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      _ ≤ P * W * 4 := by
          gcongr
          exact (sum_inv_one_add_sq_le N).trans (by
            have : (0 : ℝ) ≤ 4 / (N + 1) := by positivity
            linarith)
      _ = 4 * P * W := by ring
  have hN : ∀ N : ℕ, ∫ u in -(N : ℝ)..N, F u ≤ 8 * P * W := by
    intro N
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hFc.intervalIntegrable (μ := volume) (-(N : ℝ)) 0)
      (hFc.intervalIntegrable (μ := volume) 0 N)
    rw [← hsplit]
    have hneg : ∫ u in -(N : ℝ)..0, F u = ∫ u in (0 : ℝ)..N, F ((-1) * u) := by
      have := intervalIntegral.integral_comp_neg (a := 0) (b := (N : ℝ)) F
      simp only [neg_zero] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun u _ => ?_
      simp only [neg_one_mul]
    have hpos : ∫ u in (0 : ℝ)..N, F u = ∫ u in (0 : ℝ)..N, F (1 * u) := by
      simp only [one_mul]
    rw [hneg, hpos]
    have := hhalf N (-1) (Or.inr rfl)
    have := hhalf N 1 (Or.inl rfl)
    linarith
  have hlim := MeasureTheory.intervalIntegral_tendsto_integral hFint
    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop) tendsto_natCast_atTop_atTop
  have hle : ∫ u, F u ≤ 8 * P * W := le_of_tendsto' hlim fun N => hN N
  calc ∫ u, F u ≤ 8 * P * W := hle
    _ = 16 * (1 + (a₁ * a₂) ^ 2) * kernelWindowConst * (Real.cos (2 * c))⁻¹ ^ 4 *
          (1 / Real.sqrt (Real.cos (2 * c))) := by rw [hP_def, hW_def]; ring

/-! ## Paper transforms: continuity and square integrability -/

theorem continuous_paperFT_of_integrable {h : ℝ → ℂ} (h1 : Integrable h) :
    Continuous fun x : ℝ => paperFT h x := by
  have hfun : (fun x : ℝ => paperFT h x) = fun x => 𝓕 h (x / (-(2 * π))) := by
    funext x; rw [paperFT_ofReal_eq_fourier, neg_div, ← div_neg]
  rw [hfun]
  exact (GaloisForLFunctions.RHTower.continuous_fourier_of_integrable h1).comp
    (continuous_id.div_const _)

theorem integrable_norm_sq_paperFT {h : ℝ → ℂ} (h1 : Integrable h) (h2 : MemLp h 2) :
    Integrable fun x : ℝ => ‖paperFT h x‖ ^ 2 := by
  have hfun : (fun x : ℝ => ‖paperFT h x‖ ^ 2) =
      fun x => (fun ξ : ℝ => ‖𝓕 h ξ‖ ^ 2) (x / (-(2 * π))) := by
    funext x; rw [paperFT_ofReal_eq_fourier, neg_div, ← div_neg]
  rw [hfun]
  exact (GaloisForLFunctions.RHTower.integrable_norm_sq_fourier h1 h2).comp_div
    (by have := Real.pi_pos; linarith)

/-! ## Whole-line lower bound -/

theorem exists_integral_norm_sq_shiftedProfile_ge (h₁ : 0 < a₁) (h₂ : 0 < a₂) :
    ∃ L : ℝ, 0 < L ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ c : ℝ, 0 ≤ c → c < π / 4 →
      1 / 2 ≤ Real.sin (2 * c) → Real.cos (2 * c) ≤ κ₀ →
      L * (Real.cos (2 * c))⁻¹ ^ 4 * (1 / Real.sqrt (Real.cos (2 * c))) ≤
        ∫ u : ℝ, ‖shiftedProfile (lorentzPair a₁ a₂) c u‖ ^ 2 := by
  obtain ⟨U₀, hU₀, c₀, hc₀, κ₀, hκ₀, H⟩ := exists_integral_norm_sq_kernelC_line_ge
  set μ : ℝ := 1 / ((1 + (U₀ + 1 + 1) / a₁) * (1 + (U₀ + 1 + 1) / a₂)) with hμ_def
  have hμ : 0 < μ := by rw [hμ_def]; positivity
  refine ⟨μ ^ 2 * c₀, by positivity, κ₀, hκ₀, fun c hc0 hc hs hκ => ?_⟩
  have hc1 : c ≤ 1 := by have := Real.pi_lt_four; linarith
  obtain ⟨-, h2, -, -⟩ := shiftedProfile_integrability hc0 hc (lorentzPair_hm h₁ h₂ c)
    (lorentzPair_hmb h₁ h₂ c)
  have hint := h2.integrable_norm_pow (p := 2) (by norm_num)
  have hUU : U₀ ≤ U₀ + 1 := by linarith
  have hPhic : Continuous fun u : ℝ => ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 :=
    (continuous_kernelC_line hc0 hc).norm.pow 2
  have hset : ∫ u in U₀..U₀ + 1, ‖shiftedProfile (lorentzPair a₁ a₂) c u‖ ^ 2 ≤
      ∫ u : ℝ, ‖shiftedProfile (lorentzPair a₁ a₂) c u‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hUU]
    exact setIntegral_le_integral hint (Eventually.of_forall fun _ => by positivity)
  have hpt : ∀ u ∈ Icc U₀ (U₀ + 1), μ ^ 2 * ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 ≤
      ‖shiftedProfile (lorentzPair a₁ a₂) c u‖ ^ 2 := by
    intro u hu
    have hu' : |u| ≤ U₀ + 1 := by rw [abs_of_nonneg (by linarith [hu.1])]; exact hu.2
    have hm := norm_lorentzPair_line_ge h₁ h₂ hc0 hc1 hu'
    rw [← hμ_def] at hm
    simp only [shiftedProfile, norm_mul, mul_pow]
    have hK := sq_nonneg ‖kernelC ((u : ℂ) + c * I)‖
    have : μ ^ 2 ≤ ‖lorentzPair a₁ a₂ ((u : ℂ) + c * I)‖ ^ 2 := pow_le_pow_left₀ hμ.le hm 2
    nlinarith
  have hGc := continuous_shiftedProfile hc0 hc (lorentzPair_hm h₁ h₂ c)
  have hwin : μ ^ 2 * ∫ u in U₀..U₀ + 1, ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 ≤
      ∫ u in U₀..U₀ + 1, ‖shiftedProfile (lorentzPair a₁ a₂) c u‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hUU ((hPhic.const_mul _).intervalIntegrable _ _)
      ((hGc.norm.pow 2).intervalIntegrable _ _) hpt
  have hH := H c hc0 hc hs hκ
  calc μ ^ 2 * c₀ * (Real.cos (2 * c))⁻¹ ^ 4 * (1 / Real.sqrt (Real.cos (2 * c)))
      = μ ^ 2 * (c₀ * (Real.cos (2 * c))⁻¹ ^ 4 * (1 / Real.sqrt (Real.cos (2 * c)))) := by ring
    _ ≤ μ ^ 2 * ∫ u in U₀..U₀ + 1, ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 := by gcongr
    _ ≤ _ := hwin
    _ ≤ _ := hset

/-! ## Zeros in every window force a small mean square -/

theorem sq_norm_eq_re_sq_add_im_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- **Tiling with a head.** If `g` vanishes in every window `[t, t+h]`, `t ≥ X₁`, and its mass on
`(−∞, X₁]` is at most `H`, then `∫|g|² ≤ H + h²∫|g′|²`. -/
theorem integral_norm_sq_le_of_zero_tiles {g g' : ℝ → ℂ} {h X₁ H : ℝ} (hh : 0 < h)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg'c : Continuous g')
    (hgint : Integrable fun x => ‖g x‖ ^ 2) (hg'int : Integrable fun x => ‖g' x‖ ^ 2)
    (hzero : ∀ t ≥ X₁, ∃ x ∈ Icc t (t + h), g x = 0)
    (hhead : ∀ M : ℝ, 0 ≤ M → ∫ x in X₁ - M..X₁, ‖g x‖ ^ 2 ≤ H) :
    ∫ x, ‖g x‖ ^ 2 ≤ H + h ^ 2 * ∫ x, ‖g' x‖ ^ 2 := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  have hre : ∀ x, HasDerivAt (fun x => (g x).re) (g' x).re x := fun x =>
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hg x))
  have him : ∀ x, HasDerivAt (fun x => (g x).im) (g' x).im x := fun x =>
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hg x))
  have hrec : Continuous fun x => (g' x).re := Complex.continuous_re.comp hg'c
  have himc : Continuous fun x => (g' x).im := Complex.continuous_im.comp hg'c
  have htile : ∀ N : ℕ, ∫ x in X₁..X₁ + N * h, ‖g x‖ ^ 2 ≤
      h ^ 2 * ∫ x in X₁..X₁ + N * h, ‖g' x‖ ^ 2 := by
    intro N
    have hz : ∀ (part : ℂ → ℝ), (∀ z : ℂ, z = 0 → part z = 0) →
        ∀ j : ℕ, j < N → ∃ x ∈ Icc (X₁ + j * h) (X₁ + (j + 1) * h), part (g x) = 0 := by
      intro part hpart j _
      obtain ⟨x, hx, hx0⟩ := hzero (X₁ + j * h) (by nlinarith [Nat.cast_nonneg (α := ℝ) j])
      exact ⟨x, ⟨hx.1, by nlinarith [hx.2]⟩, hpart _ hx0⟩
    have t1 := GaloisForLFunctions.HTGeometry.integral_sq_le_of_tiling (s := fun x => (g x).re)
      (s' := fun x => (g' x).re) hh.le N (fun x _ => hre x) hrec.continuousOn
      (hz Complex.re (fun z hz => by rw [hz]; rfl))
    have t2 := GaloisForLFunctions.HTGeometry.integral_sq_le_of_tiling (s := fun x => (g x).im)
      (s' := fun x => (g' x).im) hh.le N (fun x _ => him x) himc.continuousOn
      (hz Complex.im (fun z hz => by rw [hz]; rfl))
    have hI := fun (f : ℝ → ℝ) (hf : Continuous f) => hf.intervalIntegrable (μ := volume) X₁ (X₁ + N * h)
    have e1 : ∫ x in X₁..X₁ + N * h, ‖g x‖ ^ 2 =
        (∫ x in X₁..X₁ + N * h, (g x).re ^ 2) + ∫ x in X₁..X₁ + N * h, (g x).im ^ 2 := by
      rw [← intervalIntegral.integral_add (hI (fun x => (g x).re ^ 2)
        ((Complex.continuous_re.comp hgc).pow 2)) (hI (fun x => (g x).im ^ 2)
        ((Complex.continuous_im.comp hgc).pow 2))]
      exact intervalIntegral.integral_congr fun x _ => sq_norm_eq_re_sq_add_im_sq _
    have e2 : ∫ x in X₁..X₁ + N * h, ‖g' x‖ ^ 2 =
        (∫ x in X₁..X₁ + N * h, (g' x).re ^ 2) + ∫ x in X₁..X₁ + N * h, (g' x).im ^ 2 := by
      rw [← intervalIntegral.integral_add (hI (fun x => (g' x).re ^ 2) (hrec.pow 2))
        (hI (fun x => (g' x).im ^ 2) (himc.pow 2))]
      exact intervalIntegral.integral_congr fun x _ => sq_norm_eq_re_sq_add_im_sq _
    rw [e1, e2]
    linarith
  have hwhole : ∀ N : ℕ, ∫ x in X₁..X₁ + N * h, ‖g' x‖ ^ 2 ≤ ∫ x, ‖g' x‖ ^ 2 := by
    intro N
    rw [intervalIntegral.integral_of_le (by nlinarith [Nat.cast_nonneg (α := ℝ) N])]
    exact setIntegral_le_integral hg'int (Eventually.of_forall fun _ => by positivity)
  have hN : ∀ N : ℕ, ∫ x in X₁ - N..X₁ + N * h, ‖g x‖ ^ 2 ≤ H + h ^ 2 * ∫ x, ‖g' x‖ ^ 2 := by
    intro N
    have hc2 : Continuous fun x => ‖g x‖ ^ 2 := hgc.norm.pow 2
    rw [← intervalIntegral.integral_add_adjacent_intervals (hc2.intervalIntegrable _ X₁)
      (hc2.intervalIntegrable X₁ _)]
    have h1 := hhead N (Nat.cast_nonneg N)
    have h2 := htile N
    have h3 := mul_le_mul_of_nonneg_left (hwhole N) (sq_nonneg h)
    linarith
  have hbot : Tendsto (fun N : ℕ => X₁ - N) atTop atBot := by
    refine tendsto_atTop_atBot.2 fun b => ?_
    obtain ⟨N, hN⟩ := exists_nat_ge (X₁ - b)
    exact ⟨N, fun a ha => by have : (N : ℝ) ≤ a := Nat.cast_le.2 ha; linarith⟩
  have htop : Tendsto (fun N : ℕ => X₁ + N * h) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ?_
    obtain ⟨N, hN⟩ := exists_nat_ge ((b - X₁) / h)
    refine ⟨N, fun a ha => ?_⟩
    have : (N : ℝ) ≤ a := Nat.cast_le.2 ha
    rw [div_le_iff₀ hh] at hN
    nlinarith
  have hlim := MeasureTheory.intervalIntegral_tendsto_integral hgint hbot htop
  exact le_of_tendsto' hlim hN

/-! ## The contradiction -/

/-- **Zeros at every scale are impossible.** Let `a₁, a₂ > 0` and
`ψ₀(x) = ∫Φ(u)e^{ixu}du/((1−iu/a₁)(1−iu/a₂))`, the solution of `(1 − D/a₁)(1 − D/a₂)ψ₀ = Ξ`
that decays at both ends. Then `ψ₀` cannot vanish in every window `[t, t+h]`, `t ≥ X(h)`, for
every `h > 0`.

With `g = e^{cx}ψ₀`, Plancherel turns `∫|g|²` and `∫|g′|²` into `2π∫|G|²` and `2π∫u²|G|²`, where
`G(u) = Φ(u+ic)m(u+ic)`. The flat theta bounds give `∫|G|² ≥ L(cos 2c)^{-9/2}` and
`∫u²|G|² ≤ C(cos 2c)^{-9/2}`. Poincaré on tiles of length `h` gives `∫|g|² ≤ H + h²∫|g′|²`, where
the head `H` does not depend on `c`. Taking `h` small and then `c → π/4` contradicts these. -/
theorem false_of_kernelPsi_zeros (h₁ : 0 < a₁) (h₂ : 0 < a₂)
    (hz : ∀ h : ℝ, 0 < h → ∃ X : ℝ, ∀ t ≥ X, ∃ x ∈ Icc t (t + h),
      kernelPsi (lorentzPair a₁ a₂) x = 0) : False := by
  have hpi := Real.pi_pos
  obtain ⟨L, hL, κ₀, hκ₀, hlow⟩ := exists_integral_norm_sq_shiftedProfile_ge h₁ h₂
  set Cup : ℝ := 16 * (1 + (a₁ * a₂) ^ 2) * kernelWindowConst with hCup_def
  have hCup : 0 ≤ Cup := by
    have := thetaWindowConst_nonneg 4; have := thetaWindowConst_nonneg 2
    rw [hCup_def]; unfold kernelWindowConst; positivity
  set h₀ : ℝ := Real.sqrt (L / (2 * (Cup + 1))) with hh₀_def
  have hh₀ : 0 < h₀ := Real.sqrt_pos.mpr (by positivity)
  have hh₀sq : h₀ ^ 2 * Cup ≤ L / 2 := by
    rw [hh₀_def, Real.sq_sqrt (by positivity), div_mul_eq_mul_div,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨X, hX⟩ := hz h₀ hh₀
  set X₁ : ℝ := max X 0 with hX₁_def
  have hX₁0 : 0 ≤ X₁ := le_max_right _ _
  have hm0 := lorentzPair_hm h₁ h₂ 0
  have hmb0 := lorentzPair_hmb h₁ h₂ 0
  obtain ⟨g01, g02, -, -⟩ := shiftedProfile_integrability (c := 0) le_rfl (by positivity) hm0 hmb0
  have hψint : Integrable fun x => ‖kernelPsi (lorentzPair a₁ a₂) x‖ ^ 2 := by
    refine (integrable_norm_sq_paperFT g01 g02).congr (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [← exp_mul_kernelPsi_eq le_rfl (by positivity) hm0 hmb0 x]
    simp
  set H : ℝ := Real.exp (π / 2 * X₁) * ∫ x, ‖kernelPsi (lorentzPair a₁ a₂) x‖ ^ 2 with hH_def
  have hH : 0 ≤ H := by
    have : 0 ≤ ∫ x, ‖kernelPsi (lorentzPair a₁ a₂) x‖ ^ 2 := integral_nonneg fun _ => by positivity
    positivity
  set κ : ℝ := min (min κ₀ (1 / 2)) (π * L / (2 * (H + 1))) with hκ_def
  have hκpos : 0 < κ := by rw [hκ_def]; positivity
  have hκκ₀ : κ ≤ κ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hκhalf : κ ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hκH : κ ≤ π * L / (2 * (H + 1)) := min_le_right _ _
  set c : ℝ := Real.arccos κ / 2 with hc_def
  have h2c : 2 * c = Real.arccos κ := by rw [hc_def]; ring
  have hcos : Real.cos (2 * c) = κ := by
    rw [h2c]; exact Real.cos_arccos (by linarith) (by linarith)
  have hc0 : 0 ≤ c := by rw [hc_def]; exact div_nonneg (Real.arccos_nonneg κ) (by norm_num)
  have hc : c < π / 4 := by
    have := Real.arccos_lt_pi_div_two.mpr hκpos
    rw [hc_def]; linarith
  have hs : 1 / 2 ≤ Real.sin (2 * c) := by
    rw [h2c, Real.sin_arccos]
    rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hm := lorentzPair_hm h₁ h₂ c
  have hmb := lorentzPair_hmb h₁ h₂ c
  obtain ⟨G1, G2, G3, G4⟩ := shiftedProfile_integrability hc0 hc hm hmb
  set Q : ℝ := κ⁻¹ ^ 4 * (1 / Real.sqrt κ) with hQ_def
  have hLow : L * Q ≤ ∫ u, ‖shiftedProfile (lorentzPair a₁ a₂) c u‖ ^ 2 := by
    have := hlow c hc0 hc hs (by rw [hcos]; exact hκκ₀)
    rw [hcos] at this; rw [hQ_def, ← mul_assoc]; exact this
  have hUp : ∫ u : ℝ, u ^ 2 * ‖shiftedProfile (lorentzPair a₁ a₂) c u‖ ^ 2 ≤ Cup * Q := by
    have := integral_sq_mul_norm_sq_shiftedProfile_le h₁ h₂ hc0 hc hs
    rw [hcos] at this; rw [hQ_def, hCup_def]; linarith
  -- the function `g = e^{cx}ψ₀` and its derivative
  set g : ℝ → ℂ := fun x => (Real.exp (c * x) : ℂ) * kernelPsi (lorentzPair a₁ a₂) x with hg_def
  set g' : ℝ → ℂ := fun x => paperFT (fun u : ℝ => I * u * shiftedProfile (lorentzPair a₁ a₂) c u) x with hg'_def
  have hgd : ∀ x, HasDerivAt g (g' x) x := hasDerivAt_exp_mul_kernelPsi hc0 hc hm hmb
  have hg'c : Continuous g' := continuous_paperFT_of_integrable G3
  have hgeq : ∀ x, g x = paperFT (shiftedProfile (lorentzPair a₁ a₂) c) x := exp_mul_kernelPsi_eq hc0 hc hm hmb
  have hgint : Integrable fun x => ‖g x‖ ^ 2 := by
    refine (integrable_norm_sq_paperFT G1 G2).congr (Eventually.of_forall fun x => ?_)
    simp only [hgeq]
  have hg'int : Integrable fun x => ‖g' x‖ ^ 2 := integrable_norm_sq_paperFT G3 G4
  have hzero : ∀ t ≥ X₁, ∃ x ∈ Icc t (t + h₀), g x = 0 := by
    intro t ht
    obtain ⟨x, hx, hx0⟩ := hX t (le_trans (le_max_left _ _) ht)
    exact ⟨x, hx, by simp only [hg_def, hx0, mul_zero]⟩
  have hhead : ∀ M : ℝ, 0 ≤ M → ∫ x in X₁ - M..X₁, ‖g x‖ ^ 2 ≤ H := by
    intro M hM
    have hle : X₁ - M ≤ X₁ := by linarith
    have hψc : Continuous fun x => kernelPsi (lorentzPair a₁ a₂) x := by
      have := continuous_paperFT_of_integrable g01
      refine this.congr fun x => ?_
      rw [← exp_mul_kernelPsi_eq le_rfl (by positivity) hm0 hmb0 x]; simp
    have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hgd x).continuousAt
    calc ∫ x in X₁ - M..X₁, ‖g x‖ ^ 2
        ≤ ∫ x in X₁ - M..X₁, Real.exp (π / 2 * X₁) * ‖kernelPsi (lorentzPair a₁ a₂) x‖ ^ 2 := by
          refine intervalIntegral.integral_mono_on hle ((hgc.norm.pow 2).intervalIntegrable _ _)
            (((hψc.norm.pow 2).const_mul _).intervalIntegrable _ _) fun x hx => ?_
          simp only [hg_def, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _), mul_pow]
          have he : Real.exp (c * x) ^ 2 ≤ Real.exp (π / 2 * X₁) := by
            rw [← Real.exp_nat_mul]
            apply Real.exp_le_exp.mpr
            have e1 : c * x ≤ c * X₁ := mul_le_mul_of_nonneg_left hx.2 hc0
            have e2 : c * X₁ ≤ π / 4 * X₁ := mul_le_mul_of_nonneg_right hc.le hX₁0
            push_cast
            linarith
          exact mul_le_mul_of_nonneg_right he (by positivity)
      _ = Real.exp (π / 2 * X₁) * ∫ x in X₁ - M..X₁, ‖kernelPsi (lorentzPair a₁ a₂) x‖ ^ 2 :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ H := by
          rw [hH_def]
          gcongr
          rw [intervalIntegral.integral_of_le hle]
          exact setIntegral_le_integral hψint (Eventually.of_forall fun _ => by positivity)
  have htile := integral_norm_sq_le_of_zero_tiles hh₀ hgd hg'c hgint hg'int hzero hhead
  have hPl : ∫ x, ‖g x‖ ^ 2 = 2 * π * ∫ u, ‖shiftedProfile (lorentzPair a₁ a₂) c u‖ ^ 2 :=
    integral_norm_sq_exp_mul_kernelPsi hc0 hc hm hmb
  have hPd : ∫ x, ‖g' x‖ ^ 2 = 2 * π * ∫ u : ℝ, u ^ 2 * ‖shiftedProfile (lorentzPair a₁ a₂) c u‖ ^ 2 := by
    rw [← integral_norm_sq_deriv_exp_mul_kernelPsi hc0 hc hm hmb]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hd : deriv (fun x : ℝ => (Real.exp (c * x) : ℂ) *
        kernelPsi (lorentzPair a₁ a₂) x) x = g' x := (hgd x).deriv
    simp only [hd]
  rw [hPl, hPd] at htile
  have hQpos : κ⁻¹ ≤ Q := by
    have hk1 : 1 ≤ κ⁻¹ := one_le_inv_iff₀.mpr ⟨hκpos, by linarith⟩
    have h1 : κ⁻¹ ≤ κ⁻¹ ^ 4 := by
      calc κ⁻¹ = κ⁻¹ ^ 1 := (pow_one _).symm
        _ ≤ κ⁻¹ ^ 4 := pow_le_pow_right₀ hk1 (by norm_num)
    have h2 : 1 ≤ 1 / Real.sqrt κ := by
      rw [le_div_iff₀ (Real.sqrt_pos.mpr hκpos), one_mul]
      calc Real.sqrt κ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
        _ = 1 := Real.sqrt_one
    rw [hQ_def]
    calc κ⁻¹ = κ⁻¹ * 1 := (mul_one _).symm
      _ ≤ κ⁻¹ ^ 4 * (1 / Real.sqrt κ) := mul_le_mul h1 h2 zero_le_one (by positivity)
  have hbig : 2 * (H + 1) ≤ π * L * κ⁻¹ := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (H + 1))).1 hκH
    rw [← div_eq_mul_inv, le_div_iff₀ hκpos]; linarith
  have hQ0 : 0 ≤ Q := by rw [hQ_def]; positivity
  have hGsq : 0 ≤ ∫ u : ℝ, u ^ 2 * ‖shiftedProfile (lorentzPair a₁ a₂) c u‖ ^ 2 :=
    integral_nonneg fun _ => by positivity
  have key : 2 * π * (L * Q) ≤ H + 2 * π * (L / 2 * Q) := by
    calc 2 * π * (L * Q) ≤ 2 * π * ∫ u, ‖shiftedProfile (lorentzPair a₁ a₂) c u‖ ^ 2 := by gcongr
      _ ≤ H + h₀ ^ 2 * (2 * π * ∫ u : ℝ, u ^ 2 * ‖shiftedProfile (lorentzPair a₁ a₂) c u‖ ^ 2) := htile
      _ ≤ H + h₀ ^ 2 * (2 * π * (Cup * Q)) := by gcongr
      _ = H + 2 * π * ((h₀ ^ 2 * Cup) * Q) := by ring
      _ ≤ H + 2 * π * (L / 2 * Q) := by gcongr
  have e4 : π * L * κ⁻¹ ≤ π * L * Q := mul_le_mul_of_nonneg_left hQpos (by positivity)
  linarith [key, e4, hbig]


/-- **LP-maximality of Ξ in degree two (same-sign zeros).** For `a₁, a₂ > 0` there is no
Laguerre–Pólya `ψ` with `(1 − D/a₁)(1 − D/a₂)ψ = Ξ`.

If there were, `Ξ` would be Laguerre–Pólya, hence RH. Littlewood's short windows then put zeros of
`ψ` in every window of length `h`, at all large heights, for every `h > 0`
(`Littlewood.riemannHypothesis_and_kernelPsi_zeros_of_secondOrder_preimage`). That contradicts the
flat theta bounds (`false_of_kernelPsi_zeros`). -/
theorem not_exists_laguerrePolya_secondOrder_preimage_XiC {a₁ a₂ : ℝ} (h₁ : 0 < a₁)
    (h₂ : 0 < a₂) :
    ¬ ∃ ψ : ℂ → ℂ, GaloisForLFunctions.HTGeometry.LaguerrePolya ψ ∧
      ∀ z, ψ z - ((1 / a₁ + 1 / a₂ : ℝ) : ℂ) * deriv ψ z +
        deriv (deriv ψ) z / ((a₁ * a₂ : ℝ) : ℂ) = XiC z := by
  rintro ⟨ψ, hψ, hode⟩
  obtain ⟨-, hz⟩ := Littlewood.riemannHypothesis_and_kernelPsi_zeros_of_secondOrder_preimage
    h₁.ne' h₂.ne' hψ hode
  exact false_of_kernelPsi_zeros h₁ h₂ fun h hh => by
    obtain ⟨X, hX⟩ := hz h hh
    exact ⟨X, fun t ht => hX t ht⟩

end RHTower.KernelStrip
