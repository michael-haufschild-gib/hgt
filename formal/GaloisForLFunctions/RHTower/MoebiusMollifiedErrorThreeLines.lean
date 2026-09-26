import GaloisForLFunctions.RHTower.MoebiusMollifiedCriticalMoment
import GaloisForLFunctions.RHTower.SelbergNearLineWindowBounds

/-!
# L² three lines for the Möbius-mollified error

Put `E_X = ζ M_X − 1` and `F(z) = exp((z − iτ)²/H²) · ((z−1)/z) E_X(z)` (`mobWindowField`), holomorphic
on `Re z > 0` and bounded on `1/2 ≤ Re z ≤ 3`. On the right edge `Re z = 3` every window carries at
most `S_R = e²(2/X)² √(πH²/2)` (the coefficients of `E_X` start beyond `X`). On the critical line the
whole-line mass of `|F|²` is at most

`S_L = e² (2 CS + 4N) + e² C² X² (2(1+|τ|)² + 2H²) e^{−R₀²/(2H²)} √(2πH²)`,

where `CS` bounds `∫_{−N}^{N} |ζ M_X|²` (fourth moments of `ζ` and `M_X`), and the second term is the
Gaussian tail beyond `|t| > N`, `N − |τ| ≥ R₀`. The L² three-lines lemma
(`integral_normSq_le_of_three_lines`) then gives, for `1/2 < σ ≤ 1` and windows within `H/8` of `τ`,

`∫_{T₁}^{T₂} |E_X(σ+it)|² ≤ 4 S_L^{1−λ} S_R^λ`, `λ = (σ − 1/2)/(5/2)`
(`exists_integral_normSq_mobMollifiedError_le_threeLines`).
-/

noncomputable section

open Complex MeasureTheory Set

namespace RHTower

/-- The Gaussian-windowed pole-cleared Möbius error. -/
def mobWindowField (X : ℕ) (H τ : ℝ) (z : ℂ) : ℂ := nearLineGauss H τ z * mobField X z

theorem differentiableOn_mobWindowField (X : ℕ) (H τ : ℝ) :
    DifferentiableOn ℂ (mobWindowField X H τ) {z | 0 < z.re} :=
  (differentiable_nearLineGauss H τ).differentiableOn.mul (differentiableOn_mobField X)

theorem continuous_mobWindowField_line (X : ℕ) (H τ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Continuous fun u : ℝ => mobWindowField X H τ ((σ : ℂ) + (u : ℂ) * I) := by
  have hc : ContinuousOn (mobWindowField X H τ) {z : ℂ | 0 < z.re} :=
    (differentiableOn_mobWindowField X H τ).continuousOn
  refine hc.comp_continuous (by fun_prop) fun u => ?_
  show 0 < ((σ : ℂ) + (u : ℂ) * I).re
  simpa using hσ

/-- The Gaussian mass of any window. -/
theorem intervalIntegral_exp_neg_mul_sq_le {a b : ℝ} (hab : a ≤ b) {c : ℝ} (hc : 0 < c) (τ : ℝ) :
    ∫ t in a..b, Real.exp (-c * (t - τ) ^ 2) ≤ Real.sqrt (Real.pi / c) := by
  have hint : Integrable (fun t : ℝ => Real.exp (-c * (t - τ) ^ 2)) :=
    (integrable_exp_neg_mul_sq hc).comp_sub_right τ
  rw [intervalIntegral.integral_of_le hab]
  refine (setIntegral_le_integral hint
    (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)).trans (le_of_eq ?_)
  rw [integral_sub_right_eq_self (fun t => Real.exp (-c * t ^ 2)) τ, integral_gaussian]

/-- **Right edge.** -/
theorem integral_mobWindowField_three_le {X : ℕ} (hX : 1 ≤ X) {H : ℝ} (hH : 3 ≤ H) (τ : ℝ)
    {A B : ℝ} (hAB : A ≤ B) (y : ℝ) :
    ∫ t in A..B, ‖mobWindowField X H τ (((3 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤
      Real.exp 1 ^ 2 * (2 / X) ^ 2 * Real.sqrt (Real.pi / (2 / H ^ 2)) := by
  have hH0 : 0 < H := by linarith
  have hpt : ∀ t : ℝ, ‖mobWindowField X H τ (((3 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤
      Real.exp 1 ^ 2 * (2 / X) ^ 2 * Real.exp (-(2 / H ^ 2) * (t - (τ - y)) ^ 2) := by
    intro t
    set z : ℂ := ((3 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I with hz
    have hre : z.re = 3 := by simp [hz]
    have him : z.im = y + t := by simp [hz]
    have hG := norm_nearLineGauss_le (τ := τ) hH (z := z) (by rw [hre]; norm_num)
    have hf : ‖mobField X z‖ ≤ 2 / X := by
      have := norm_mobField_three_le hX (y + t)
      rwa [show ((3 : ℝ) : ℂ) = (3 : ℂ) by norm_num] at hz ⊢
    unfold mobWindowField
    rw [norm_mul, mul_pow]
    have hG2 : ‖nearLineGauss H τ z‖ ^ 2 ≤
        Real.exp 1 ^ 2 * Real.exp (-(2 / H ^ 2) * (t - (τ - y)) ^ 2) := by
      have h := pow_le_pow_left₀ (norm_nonneg _) hG 2
      refine h.trans (le_of_eq ?_)
      rw [mul_pow, ← Real.exp_nat_mul, him]
      congr 2
      push_cast
      ring
    have hf2 : ‖mobField X z‖ ^ 2 ≤ (2 / X) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hf 2
    calc ‖nearLineGauss H τ z‖ ^ 2 * ‖mobField X z‖ ^ 2
        ≤ (Real.exp 1 ^ 2 * Real.exp (-(2 / H ^ 2) * (t - (τ - y)) ^ 2)) * (2 / X) ^ 2 :=
          mul_le_mul hG2 hf2 (by positivity) (by positivity)
      _ = _ := by ring
  have hcont : Continuous fun t : ℝ =>
      ‖mobWindowField X H τ (((3 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 := by
    have h := continuous_mobWindowField_line X H τ (σ := 3) (by norm_num)
    exact (h.comp (continuous_const.add continuous_id)).norm.pow 2
  calc ∫ t in A..B, ‖mobWindowField X H τ (((3 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2
      ≤ ∫ t in A..B, Real.exp 1 ^ 2 * (2 / X) ^ 2 *
          Real.exp (-(2 / H ^ 2) * (t - (τ - y)) ^ 2) :=
        intervalIntegral.integral_mono_on hAB (hcont.intervalIntegrable _ _)
          ((continuous_const.mul (by fun_prop)).intervalIntegrable _ _) fun t _ => hpt t
    _ = Real.exp 1 ^ 2 * (2 / X) ^ 2 *
          ∫ t in A..B, Real.exp (-(2 / H ^ 2) * (t - (τ - y)) ^ 2) :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (intervalIntegral_exp_neg_mul_sq_le hAB (by positivity) (τ - y)) (by positivity)

/-- `(1+|t|)² e^{−2x²/H²} ≤ (2(1+|τ|)² + 2H²) e^{−x²/H²}`, `x = t − τ`. -/
theorem one_add_abs_sq_mul_exp_le {H : ℝ} (hH : 0 < H) (t τ : ℝ) :
    (1 + |t|) ^ 2 * Real.exp (-(2 * (t - τ) ^ 2 / H ^ 2)) ≤
      (2 * (1 + |τ|) ^ 2 + 2 * H ^ 2) * Real.exp (-((t - τ) ^ 2 / H ^ 2)) := by
  set x : ℝ := t - τ with hx
  have ht : |t| ≤ |τ| + |x| := by
    have := abs_add (τ) x
    rwa [show τ + x = t by rw [hx]; ring] at this
  have h1 : (1 + |t|) ^ 2 ≤ 2 * (1 + |τ|) ^ 2 + 2 * x ^ 2 := by
    have h0 : 0 ≤ 1 + |t| := by positivity
    have : (1 + |t|) ^ 2 ≤ ((1 + |τ|) + |x|) ^ 2 := pow_le_pow_left₀ h0 (by linarith) 2
    nlinarith [sq_nonneg ((1 + |τ|) - |x|), sq_abs x]
  have hsplit : Real.exp (-(2 * x ^ 2 / H ^ 2)) =
      Real.exp (-(x ^ 2 / H ^ 2)) * Real.exp (-(x ^ 2 / H ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE1 : Real.exp (-(x ^ 2 / H ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ x ^ 2 / H ^ 2 := by positivity
    linarith)
  have hx2 := sq_mul_exp_neg_sq_div_le (x := x) hH
  have hE0 : 0 ≤ Real.exp (-(x ^ 2 / H ^ 2)) := (Real.exp_pos _).le
  calc (1 + |t|) ^ 2 * Real.exp (-(2 * x ^ 2 / H ^ 2))
      ≤ (2 * (1 + |τ|) ^ 2 + 2 * x ^ 2) * Real.exp (-(2 * x ^ 2 / H ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 2 * (1 + |τ|) ^ 2 * Real.exp (-(x ^ 2 / H ^ 2)) * Real.exp (-(x ^ 2 / H ^ 2)) +
          2 * (x ^ 2 * Real.exp (-(x ^ 2 / H ^ 2))) * Real.exp (-(x ^ 2 / H ^ 2)) := by
        rw [hsplit]; ring
    _ ≤ 2 * (1 + |τ|) ^ 2 * 1 * Real.exp (-(x ^ 2 / H ^ 2)) +
          2 * H ^ 2 * Real.exp (-(x ^ 2 / H ^ 2)) := by
        gcongr
    _ = (2 * (1 + |τ|) ^ 2 + 2 * H ^ 2) * Real.exp (-(x ^ 2 / H ^ 2)) := by ring

/-- **Left edge.** The whole critical line carries at most `S_L` of `|F|²`. -/
theorem integral_mobWindowField_half_whole_le {C D : ℝ} (hC : 0 < C)
    (hgrowth : ∀ X : ℕ, 1 ≤ X → ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 →
      ‖mobField X z‖ ≤ C * X * (1 + |z.im|))
    {X N : ℕ} (hX : 1 ≤ X) {H τ R₀ CS : ℝ} (hH : 3 ≤ H) (hR₀ : 0 ≤ R₀)
    (hNR : R₀ ≤ N - |τ|)
    (hCS : ∫ t in (-(N : ℝ))..(N : ℝ), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly mobCoeff (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ CS) :
    Integrable (fun t : ℝ => ‖mobWindowField X H τ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ∧
    ∫ t : ℝ, ‖mobWindowField X H τ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      Real.exp 1 ^ 2 * (2 * CS + 4 * N) +
        Real.exp 1 ^ 2 * C ^ 2 * (X : ℝ) ^ 2 * (2 * (1 + |τ|) ^ 2 + 2 * H ^ 2) *
          Real.exp (-(R₀ ^ 2 / (2 * H ^ 2))) * Real.sqrt (Real.pi / (1 / (2 * H ^ 2))) := by
  have hH0 : 0 < H := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set g : ℝ → ℝ := fun t => ‖mobWindowField X H τ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 with hg
  have hgc : Continuous g := (continuous_mobWindowField_line X H τ (σ := 1 / 2)
    (by norm_num)).norm.pow 2
  have hg0 : ∀ t, 0 ≤ g t := fun t => by simp only [hg]; positivity
  set K : ℝ := Real.exp 1 ^ 2 * C ^ 2 * (X : ℝ) ^ 2 * (2 * (1 + |τ|) ^ 2 + 2 * H ^ 2) with hK
  have hK0 : 0 ≤ K := by simp only [hK]; positivity
  -- the Gaussian envelope
  have hG : ∀ t : ℝ, ‖nearLineGauss H τ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      Real.exp 1 ^ 2 * Real.exp (-(2 * (t - τ) ^ 2 / H ^ 2)) := by
    intro t
    have h := norm_nearLineGauss_le (τ := τ) hH (z := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
      (by simp; norm_num)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    refine h2.trans (le_of_eq ?_)
    have him : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).im = t := by simp
    rw [him, mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have henv : ∀ t : ℝ, g t ≤ K * Real.exp (-((t - τ) ^ 2 / H ^ 2)) := by
    intro t
    have hf := hgrowth X hX (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) (by simp; norm_num)
      (by simp; norm_num)
    have him : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).im = t := by simp
    rw [him] at hf
    have hf2 : ‖mobField X (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        C ^ 2 * (X : ℝ) ^ 2 * (1 + |t|) ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hf 2
      nlinarith [this]
    have hkey := one_add_abs_sq_mul_exp_le hH0 t τ
    simp only [hg, mobWindowField, norm_mul, mul_pow]
    calc ‖nearLineGauss H τ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 *
          ‖mobField X (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2
        ≤ (Real.exp 1 ^ 2 * Real.exp (-(2 * (t - τ) ^ 2 / H ^ 2))) *
            (C ^ 2 * (X : ℝ) ^ 2 * (1 + |t|) ^ 2) :=
          mul_le_mul (hG t) hf2 (by positivity) (by positivity)
      _ = Real.exp 1 ^ 2 * C ^ 2 * (X : ℝ) ^ 2 *
            ((1 + |t|) ^ 2 * Real.exp (-(2 * (t - τ) ^ 2 / H ^ 2))) := by ring
      _ ≤ Real.exp 1 ^ 2 * C ^ 2 * (X : ℝ) ^ 2 *
            ((2 * (1 + |τ|) ^ 2 + 2 * H ^ 2) * Real.exp (-((t - τ) ^ 2 / H ^ 2))) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = K * Real.exp (-((t - τ) ^ 2 / H ^ 2)) := by simp only [hK]; ring
  have hgauss1 : Integrable (fun t : ℝ => Real.exp (-((t - τ) ^ 2 / H ^ 2))) := by
    have h := (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1 / H ^ 2)).comp_sub_right τ
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only
    congr 1
    ring
  have hgint : Integrable g := by
    refine (hgauss1.const_mul K).mono' hgc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 t)]
    exact henv t
  refine ⟨hgint, ?_⟩
  -- split at `[−N, N]`
  rw [← integral_add_compl (measurableSet_Icc (a := -(N : ℝ)) (b := N)) hgint]
  have hin : ∫ t in Icc (-(N : ℝ)) N, g t ≤ Real.exp 1 ^ 2 * (2 * CS + 4 * N) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    have hs : ∀ n ∈ Finset.Icc 1 X, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
    have hZMc : Continuous fun t : ℝ => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly mobCoeff (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
      (continuous_riemannZeta_critical.mul
        ((differentiable_edPoly mobCoeff hs).continuous.comp (by fun_prop))).norm.pow 2
    have hpt : ∀ t : ℝ, g t ≤ Real.exp 1 ^ 2 *
        (2 * ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly mobCoeff (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 + 2) := by
      intro t
      set z : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I with hz
      have hre : z.re = 1 / 2 := by simp [hz]
      have hz0 : z ≠ 0 := fun h => by rw [h] at hre; norm_num at hre
      have hz1 : z ≠ 1 := fun h => by rw [h] at hre; norm_num at hre
      have hq := norm_sub_one_div_le_one (z := z) (by rw [hre])
      have hE : ‖mobMollifiedError X z‖ ≤
          ‖riemannZeta z * edPoly mobCoeff (Finset.Icc 1 X) z‖ + 1 := by
        unfold mobMollifiedError
        have := norm_sub_le (riemannZeta z * edPoly mobCoeff (Finset.Icc 1 X) z) 1
        rwa [norm_one] at this
      have hF : ‖mobField X z‖ ≤ ‖riemannZeta z * edPoly mobCoeff (Finset.Icc 1 X) z‖ + 1 := by
        rw [mobField_eq hz0 hz1, norm_mul]
        calc ‖(z - 1) / z‖ * ‖mobMollifiedError X z‖ ≤ 1 * ‖mobMollifiedError X z‖ :=
              mul_le_mul_of_nonneg_right hq (norm_nonneg _)
          _ ≤ _ := by rw [one_mul]; exact hE
      have hF2 : ‖mobField X z‖ ^ 2 ≤
          2 * ‖riemannZeta z * edPoly mobCoeff (Finset.Icc 1 X) z‖ ^ 2 + 2 := by
        have h0 := norm_nonneg (mobField X z)
        have h1 := norm_nonneg (riemannZeta z * edPoly mobCoeff (Finset.Icc 1 X) z)
        nlinarith [sq_nonneg (‖riemannZeta z * edPoly mobCoeff (Finset.Icc 1 X) z‖ - 1)]
      have hGe : ‖nearLineGauss H τ z‖ ^ 2 ≤ Real.exp 1 ^ 2 := by
        refine (hG t).trans ?_
        have : Real.exp (-(2 * (t - τ) ^ 2 / H ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by
          have : 0 ≤ 2 * (t - τ) ^ 2 / H ^ 2 := by positivity
          linarith)
        have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ Real.exp 1 ^ 2)
        linarith
      simp only [hg, mobWindowField, norm_mul, mul_pow]
      rw [← hz]
      exact mul_le_mul hGe hF2 (by positivity) (by positivity)
    calc ∫ t in (-(N : ℝ))..(N : ℝ), g t
        ≤ ∫ t in (-(N : ℝ))..(N : ℝ), Real.exp 1 ^ 2 *
            (2 * ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
              edPoly mobCoeff (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 + 2) :=
          intervalIntegral.integral_mono_on (by linarith) (hgc.intervalIntegrable _ _)
            ((continuous_const.mul ((continuous_const.mul hZMc).add continuous_const)).intervalIntegrable
              _ _) fun t _ => hpt t
      _ = Real.exp 1 ^ 2 * (2 * ∫ t in (-(N : ℝ))..(N : ℝ),
            ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
              edPoly mobCoeff (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 + 4 * N) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
            ((continuous_const.mul hZMc).intervalIntegrable _ _) intervalIntegrable_const,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
          ring
      _ ≤ Real.exp 1 ^ 2 * (2 * CS + 4 * N) := by gcongr
  have hout : ∫ t in (Icc (-(N : ℝ)) N)ᶜ, g t ≤
      K * Real.exp (-(R₀ ^ 2 / (2 * H ^ 2))) * Real.sqrt (Real.pi / (1 / (2 * H ^ 2))) := by
    set P : ℝ → ℝ := fun t => K * Real.exp (-(R₀ ^ 2 / (2 * H ^ 2))) *
      Real.exp (-(1 / (2 * H ^ 2)) * (t - τ) ^ 2) with hP
    have hPint : Integrable P :=
      ((integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1 / (2 * H ^ 2))).comp_sub_right
        τ).const_mul _
    have hptout : ∀ t ∈ (Icc (-(N : ℝ)) N)ᶜ, g t ≤ P t := by
      intro t ht
      have htN : (N : ℝ) < |t| := by
        simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at ht
        rcases ht with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact h
      have hx : R₀ ≤ |t - τ| := by
        have := abs_sub_abs_le_abs_sub t τ
        linarith
      have hx2 : R₀ ^ 2 ≤ (t - τ) ^ 2 := by
        rw [← sq_abs (t - τ)]; exact pow_le_pow_left₀ hR₀ hx 2
      refine (henv t).trans ?_
      simp only [hP]
      rw [mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK0
      have key : -((t - τ) ^ 2 / H ^ 2) = -(R₀ ^ 2 / (2 * H ^ 2)) +
          -(1 / (2 * H ^ 2)) * (t - τ) ^ 2 - ((t - τ) ^ 2 - R₀ ^ 2) / (2 * H ^ 2) := by
        field_simp; ring
      have : 0 ≤ ((t - τ) ^ 2 - R₀ ^ 2) / (2 * H ^ 2) := div_nonneg (by linarith) (by positivity)
      linarith
    calc ∫ t in (Icc (-(N : ℝ)) N)ᶜ, g t ≤ ∫ t in (Icc (-(N : ℝ)) N)ᶜ, P t :=
          setIntegral_mono_on hgint.integrableOn hPint.integrableOn measurableSet_Icc.compl hptout
      _ ≤ ∫ t, P t := setIntegral_le_integral hPint (Filter.Eventually.of_forall fun t => by
          simp only [hP]; positivity)
      _ = K * Real.exp (-(R₀ ^ 2 / (2 * H ^ 2))) * Real.sqrt (Real.pi / (1 / (2 * H ^ 2))) := by
          simp only [hP]
          rw [integral_const_mul, integral_sub_right_eq_self
            (fun t => Real.exp (-(1 / (2 * H ^ 2)) * t ^ 2)) τ, integral_gaussian]
  calc (∫ t in Icc (-(N : ℝ)) N, g t) + ∫ t in (Icc (-(N : ℝ)) N)ᶜ, g t
      ≤ Real.exp 1 ^ 2 * (2 * CS + 4 * N) +
          K * Real.exp (-(R₀ ^ 2 / (2 * H ^ 2))) * Real.sqrt (Real.pi / (1 / (2 * H ^ 2))) :=
        add_le_add hin hout
    _ = _ := by simp only [hK]

/-- **Uniform bound on the closed strip.** -/
theorem norm_mobWindowField_le_strip {C : ℝ} (hC : 0 < C)
    (hgrowth : ∀ X : ℕ, 1 ≤ X → ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 →
      ‖mobField X z‖ ≤ C * X * (1 + |z.im|))
    {X : ℕ} (hX : 1 ≤ X) {H : ℝ} (hH : 3 ≤ H) (τ : ℝ) {z : ℂ} (hz : 1 / 2 ≤ z.re)
    (hz' : z.re ≤ 3) :
    ‖mobWindowField X H τ z‖ ≤ Real.exp 1 * (C * X * (1 + |τ| + H)) := by
  have hH0 : 0 < H := by linarith
  have hG := norm_nearLineGauss_le (τ := τ) hH (z := z) (abs_le.mpr ⟨by linarith, hz'⟩)
  have hf := hgrowth X hX z (by linarith) hz'
  set x : ℝ := z.im - τ with hx
  have hkey : (1 + |z.im|) * Real.exp (-(x ^ 2 / H ^ 2)) ≤ 1 + |τ| + H := by
    have h1 : |z.im| ≤ |τ| + |x| := by
      have := abs_add τ x
      rwa [show τ + x = z.im by rw [hx]; ring] at this
    have h2 := mul_exp_neg_sq_div_le (x := |x|) (abs_nonneg x) hH0
    rw [sq_abs] at h2
    have hE1 : Real.exp (-(x ^ 2 / H ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : 0 ≤ x ^ 2 / H ^ 2 := by positivity
      linarith)
    have hE0 : 0 ≤ Real.exp (-(x ^ 2 / H ^ 2)) := (Real.exp_pos _).le
    calc (1 + |z.im|) * Real.exp (-(x ^ 2 / H ^ 2))
        ≤ (1 + |τ| + |x|) * Real.exp (-(x ^ 2 / H ^ 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) hE0
      _ = (1 + |τ|) * Real.exp (-(x ^ 2 / H ^ 2)) + |x| * Real.exp (-(x ^ 2 / H ^ 2)) := by ring
      _ ≤ (1 + |τ|) * 1 + H := by
          gcongr
      _ = 1 + |τ| + H := by ring
  unfold mobWindowField
  rw [norm_mul]
  calc ‖nearLineGauss H τ z‖ * ‖mobField X z‖
      ≤ (Real.exp 1 * Real.exp (-(x ^ 2 / H ^ 2))) * (C * X * (1 + |z.im|)) :=
        mul_le_mul hG hf (norm_nonneg _) (by positivity)
    _ = Real.exp 1 * (C * X * ((1 + |z.im|) * Real.exp (-(x ^ 2 / H ^ 2)))) := by ring
    _ ≤ Real.exp 1 * (C * X * (1 + |τ| + H)) := by
        gcongr

/-- **The centre.** Within `H/8` of `τ`, `|E_X|² ≤ 4 |F|²` on `1/2 ≤ Re ≤ 1`, `|Im| ≥ 1`. -/
theorem normSq_mobMollifiedError_le_four_mul {X : ℕ} {H τ σ t : ℝ} (hH : 0 < H)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (ht : 1 ≤ |t|) (hτ : |t - τ| ≤ H / 8) :
    ‖mobMollifiedError X ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      4 * ‖mobWindowField X H τ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hE := norm_mobMollifiedError_sq_le_two_mul (X := X) (z := (σ : ℂ) + (t : ℂ) * I)
    (by simpa using hσ) (by simpa using hσ1) (by simpa using ht)
  have hG : (1 / 2 : ℝ) ≤ ‖nearLineGauss H τ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    rw [norm_nearLineGauss, ← Real.exp_nat_mul]
    have hx2 : (t - τ) ^ 2 ≤ H ^ 2 / 64 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hτ 2
      rw [sq_abs] at this
      nlinarith
    have hexp : -(1 / 32 : ℝ) ≤ ((2 : ℕ) : ℝ) * ((σ ^ 2 - (t - τ) ^ 2) / H ^ 2) := by
      have hH2 : 0 < H ^ 2 := by positivity
      have : (t - τ) ^ 2 / H ^ 2 ≤ 1 / 64 := by
        rw [div_le_iff₀ hH2]; linarith
      have : 0 ≤ σ ^ 2 / H ^ 2 := by positivity
      rw [sub_div]
      push_cast
      linarith
    have h1 : Real.exp (-(1 / 32 : ℝ)) ≥ 1 / 2 := by
      have := Real.add_one_le_exp (-(1 / 32 : ℝ))
      linarith
    linarith [Real.exp_le_exp.mpr hexp]
  unfold mobWindowField
  rw [norm_mul, mul_pow]
  have hF0 := sq_nonneg ‖mobField X ((σ : ℂ) + (t : ℂ) * I)‖
  nlinarith

/-- **L² three lines for the Möbius-mollified error.** -/
theorem exists_integral_normSq_mobMollifiedError_le_threeLines :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ {X N : ℕ}, 1 ≤ X → 4 ≤ N →
      ∀ {H τ R₀ σ T₁ T₂ : ℝ}, 3 ≤ H → 0 ≤ R₀ → R₀ ≤ N - |τ| → 1 / 2 < σ → σ ≤ 1 →
        1 ≤ T₁ → T₁ ≤ T₂ → (∀ t ∈ Icc T₁ T₂, |t - τ| ≤ H / 8) →
        ∫ t in T₁..T₂, ‖mobMollifiedError X ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          4 * ((Real.exp 1 ^ 2 * (2 * Real.sqrt
              ((2 * N + 8 * ((X * X : ℕ) : ℝ) * (1 + Real.log ((X * X : ℕ) : ℝ))) *
                (1 + Real.log ((X * X : ℕ) : ℝ)) ^ 4 * (D * N * (1 + Real.log N) ^ 4)) + 4 * N) +
              Real.exp 1 ^ 2 * C ^ 2 * (X : ℝ) ^ 2 * (2 * (1 + |τ|) ^ 2 + 2 * H ^ 2) *
                Real.exp (-(R₀ ^ 2 / (2 * H ^ 2))) *
                  Real.sqrt (Real.pi / (1 / (2 * H ^ 2)))) ^ (1 - (σ - 1 / 2) / (3 - 1 / 2)) *
            (Real.exp 1 ^ 2 * (2 / X) ^ 2 * Real.sqrt (Real.pi / (2 / H ^ 2))) ^
              ((σ - 1 / 2) / (3 - 1 / 2))) := by
  obtain ⟨C, hC, hgrowth⟩ := exists_norm_mobField_le
  obtain ⟨D, hD, hmom⟩ := exists_integral_normSq_zeta_mul_edPoly_mob_critical_le
  refine ⟨C, D, hC, hD, fun {X N} hX hN {H τ R₀ σ T₁ T₂} hH hR₀ hNR hσ hσ1 hT₁ hT hwin => ?_⟩
  have hH0 : 0 < H := by linarith
  set F := mobWindowField X H τ with hFdef
  set CS : ℝ := Real.sqrt ((2 * N + 8 * ((X * X : ℕ) : ℝ) * (1 + Real.log ((X * X : ℕ) : ℝ))) *
    (1 + Real.log ((X * X : ℕ) : ℝ)) ^ 4 * (D * N * (1 + Real.log N) ^ 4)) with hCS
  obtain ⟨hgint, hwhole⟩ := integral_mobWindowField_half_whole_le hC hgrowth hX hH hR₀ hNR
    (hmom hX hN)
  rw [← hCS] at hwhole
  set SL : ℝ := Real.exp 1 ^ 2 * (2 * CS + 4 * N) +
    Real.exp 1 ^ 2 * C ^ 2 * (X : ℝ) ^ 2 * (2 * (1 + |τ|) ^ 2 + 2 * H ^ 2) *
      Real.exp (-(R₀ ^ 2 / (2 * H ^ 2))) * Real.sqrt (Real.pi / (1 / (2 * H ^ 2))) with hSL
  set SR : ℝ := Real.exp 1 ^ 2 * (2 / X) ^ 2 * Real.sqrt (Real.pi / (2 / H ^ 2)) with hSR
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hSL0 : 0 < SL := by
    have : 0 ≤ CS := Real.sqrt_nonneg _
    have h2 : 0 < Real.exp 1 ^ 2 * (2 * CS + 4 * N) := by positivity
    have h3 : 0 ≤ Real.exp 1 ^ 2 * C ^ 2 * (X : ℝ) ^ 2 * (2 * (1 + |τ|) ^ 2 + 2 * H ^ 2) *
      Real.exp (-(R₀ ^ 2 / (2 * H ^ 2))) * Real.sqrt (Real.pi / (1 / (2 * H ^ 2))) := by positivity
    linarith
  have hSR0 : 0 < SR := by
    have : 0 < Real.sqrt (Real.pi / (2 / H ^ 2)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  -- the three-lines lemma
  have hdiff : DiffContOnCl ℂ F (Complex.HadamardThreeLines.verticalStrip (1 / 2) 3) := by
    apply DifferentiableOn.diffContOnCl
    rw [GaloisForLFunctions.HTGeometry.closure_verticalStrip (by norm_num)]
    refine (differentiableOn_mobWindowField X H τ).mono fun z hz => ?_
    have : z.re ∈ Icc (1 / 2 : ℝ) 3 := hz
    show 0 < z.re
    linarith [this.1]
  have hbound : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip (1 / 2) 3,
      ‖F z‖ ≤ Real.exp 1 * (C * X * (1 + |τ| + H)) := by
    intro z hz
    have : z.re ∈ Icc (1 / 2 : ℝ) 3 := hz
    exact norm_mobWindowField_le_strip hC hgrowth hX hH τ this.1 this.2
  have hL : ∀ y : ℝ, ∫ t in T₁..T₂, ‖F (((1 / 2 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤ SL := by
    intro y
    have hshift := intervalIntegral.integral_comp_add_left
      (fun t : ℝ => ‖F (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) y (a := T₁) (b := T₂)
    simp only at hshift
    rw [hshift, intervalIntegral.integral_of_le (by linarith)]
    refine (setIntegral_le_integral hgint (Filter.Eventually.of_forall fun t => by positivity)).trans
      hwhole
  have hR : ∀ y : ℝ, ∫ t in T₁..T₂, ‖F (((3 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤ SR :=
    fun y => integral_mobWindowField_three_le hX hH τ hT y
  have h3 := GaloisForLFunctions.HTGeometry.integral_normSq_le_of_three_lines (F := F)
    (l := 1 / 2) (u := 3) (σ := σ) (A := T₁) (B := T₂) (by norm_num) hσ.le (by linarith) hT
    hdiff hbound hSL0 hSR0 (by exact_mod_cast hL) (by exact_mod_cast hR)
  -- the centre
  have hcentre : ∫ t in T₁..T₂, ‖mobMollifiedError X ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      4 * ∫ t in T₁..T₂, ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    have hFc : Continuous fun t : ℝ => ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
      (continuous_mobWindowField_line X H τ (σ := σ) (by linarith)).norm.pow 2
    have hEc : ContinuousOn (fun t : ℝ => ‖mobMollifiedError X ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
        (Icc T₁ T₂) := by
      have hs : ∀ n ∈ Finset.Icc 1 X, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
      intro t ht
      have hne : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
        intro h
        have := congrArg Complex.im h
        simp at this
        linarith [ht.1]
      have hc : ContinuousAt (fun t : ℝ => mobMollifiedError X ((σ : ℂ) + (t : ℂ) * I)) t := by
        unfold mobMollifiedError
        exact ((ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I)
          (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)).mul
          (((differentiable_edPoly mobCoeff hs).continuous.comp (by fun_prop)).continuousAt)).sub
          continuousAt_const
      exact (hc.norm.pow 2).continuousWithinAt
    refine intervalIntegral.integral_mono_on hT (hEc.intervalIntegrable_of_Icc hT)
      ((continuous_const.mul hFc).intervalIntegrable _ _) fun t ht => ?_
    have ht1 : 1 ≤ |t| := by rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.1]
    exact normSq_mobMollifiedError_le_four_mul hH0 hσ.le hσ1 ht1 (hwin t ht)
  refine hcentre.trans ?_
  have h3' : ∫ t in T₁..T₂, ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      SL ^ (1 - (σ - 1 / 2) / (3 - 1 / 2)) * SR ^ ((σ - 1 / 2) / (3 - 1 / 2)) := h3
  linarith

end RHTower
