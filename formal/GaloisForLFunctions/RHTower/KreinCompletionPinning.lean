import GaloisForLFunctions.RHTower.ModulatedRiemannRadicalTest


/-!
# Positive completions of the level-`L` Weil form are pinned to the zeros

A positive measure `ν` on the ordinate line is dominated by the level-`L` Hodge form of `ζ` if
`∫ |f̂|² dν ≤ |W(f,f)|` for every Hodge-class test at level `L`.  Every positive Krein completion
of the level-`L` Weil form is such a measure.  Under RH the zero-counting measure of `ζ` is one; in
general the extension problem is indeterminate.

**Theorem** (`zeta_krein_completion_pinned_off_zeros`).  For all large `L`, every dominated `ν`
satisfies `ν([τ₀ - δ/2, τ₀ + δ/2]) ≤ K e^{12L} e^{-π e^{2L-1/2}}` whenever `τ₀ ≥ 5` is at distance
`≥ δ` from every zero ordinate and `π(τ₀ + 1/2) + 6C log(τ₀+1)/δ ≤ π e^{2L-1/2}`.

So below height `≈ e^{2L-1/2}` every positive completion lives, up to super-exponentially small
mass, on the zero ordinates of `ζ`.  This is a Christoffel-function bound.  Test `ν` against the
modulated radical test `f_{L,τ₀}`: its Weil energy is `O(ε_L²)`, while `|f̂| ≳ |Ξ(τ₀)|` on the
window, and `|Ξ(τ₀)|` is bounded below by the critical-line estimate away from the zeros.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal
open Bottcher Zeta23

namespace RHTower

noncomputable section

/-- A positive measure `ν` on the ordinate line is *dominated by the level-`L` Hodge form* if
`∫ |f̂|² dν ≤ |W(f, f)|` for every Hodge-class test `f` at level `L` (`C²`, supported in `[-L, L]`,
`f̂(±i/2) = 0`).  Every positive Krein completion of the level-`L` Weil form qualifies. -/
def DominatedByHodgeForm (L : ℝ) (ν : Measure ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-L) L → paperFT f (I / 2) = 0 →
    paperFT f (-(I / 2)) = 0 →
    ∫⁻ τ, ENNReal.ofReal (‖paperFT f τ‖ ^ 2) ∂ν ≤ ENNReal.ofReal ‖zetaZeroConfig.W f f‖

/-- The lower envelope of `|Ξ|` on `[τ₀ - δ/2, τ₀ + δ/2]`. -/
def xiWindowFloor (τ₀ δ : ℝ) : ℝ :=
  xiLineConst * (τ₀ - 1 / 2) ^ 2 * Real.exp (-(Real.pi * (τ₀ + 1 / 2) / 2)) *
    Real.exp (-(3 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ))

theorem norm_riemannPhiTransform_window_ge {τ₀ δ τ : ℝ} (hτ₀ : 5 ≤ τ₀) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, δ ≤ |ρ.im - τ₀|)
    (hτ : τ ∈ Icc (τ₀ - δ / 2) (τ₀ + δ / 2)) :
    xiWindowFloor τ₀ δ ≤ ‖riemannPhiTransform (1 / 2 + I * τ)‖ := by
  have hτ4 : 4 ≤ τ := by linarith [hτ.1]
  have hfar : ∀ ρ ∈ zetaZeroConfig.carrier, δ / 2 ≤ |ρ.im - τ| := by
    intro ρ hρ
    have h1 := hsep ρ hρ
    have h2 : |τ - τ₀| ≤ δ / 2 := abs_le.mpr ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have := abs_sub_abs_le_abs_sub (ρ.im - τ₀) (τ - τ₀)
    have e : ρ.im - τ₀ - (τ - τ₀) = ρ.im - τ := by ring
    rw [e] at this
    linarith [abs_sub_comm (ρ.im - τ₀) (τ - τ₀)]
  have h := norm_riemannPhiTransform_line_ge hτ4 (by linarith : (0 : ℝ) < δ / 2)
    (by linarith) hfar
  refine le_trans ?_ h
  have hC := logDerivZetaConstant_nonneg
  have hc := xiLineConst_pos
  unfold xiWindowFloor
  have hsq : (τ₀ - 1 / 2) ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith [hτ.1]) 2
  have he1 : Real.exp (-(Real.pi * (τ₀ + 1 / 2) / 2)) ≤ Real.exp (-(Real.pi * τ / 2)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hτ.2])
  have hlog : Real.log τ ≤ Real.log (τ₀ + 1) :=
    Real.log_le_log (by linarith) (by linarith [hτ.2])
  have he2 : Real.exp (-(3 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ)) ≤
      Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log τ / (δ / 2))) := by
    apply Real.exp_le_exp.mpr
    rw [show 3 / 2 * logDerivZetaConstant * Real.log τ / (δ / 2) =
      3 * logDerivZetaConstant * Real.log τ / δ by field_simp]
    have : 3 * logDerivZetaConstant * Real.log τ / δ ≤
        3 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ := by
      apply div_le_div_of_nonneg_right _ hδ.le
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    linarith
  have h0a : 0 ≤ xiLineConst * (τ₀ - 1 / 2) ^ 2 := by positivity
  calc xiLineConst * (τ₀ - 1 / 2) ^ 2 * Real.exp (-(Real.pi * (τ₀ + 1 / 2) / 2)) *
        Real.exp (-(3 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ))
      ≤ xiLineConst * τ ^ 2 * Real.exp (-(Real.pi * τ / 2)) *
          Real.exp (-(3 / 2 * logDerivZetaConstant * Real.log τ / (δ / 2))) := by
        gcongr

/-- **Christoffel bound (raw form).**  If `ν` is dominated by the level-`L` Hodge form, `τ₀ ≥ 5`,
every zero ordinate is at distance `≥ δ` from `τ₀`, and `2 ε_L ≤ m_Ξ` (the window floor of `|Ξ|`),
then `ν([τ₀ - δ/2, τ₀ + δ/2]) ≤ ‖W(f,f)‖ / ℓ²` for the modulated radical test `f` at `ω = τ₀`,
where `ℓ = (m_Ξ/2)(τ₀ - 1/2)² cos(1/8) ∫κ`. -/
theorem measure_window_le_of_dominated {L : ℝ} {ν : Measure ℝ} (hν : DominatedByHodgeForm L ν)
    {τ₀ δ : ℝ} (hτ₀ : 5 ≤ τ₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, δ ≤ |ρ.im - τ₀|)
    (hbig : 2 * (∫ u : ℝ, ‖riemannPhiTail L u‖ * Real.exp (1 / 2 * |u|)) ≤ xiWindowFloor τ₀ δ) :
    ν (Icc (τ₀ - δ / 2) (τ₀ + δ / 2)) ≤
      ENNReal.ofReal (‖zetaZeroConfig.W (modRadicalTest L τ₀) (modRadicalTest L τ₀)‖ /
        ((xiWindowFloor τ₀ δ / 2) * (τ₀ - 1 / 2) ^ 2 *
          (Real.cos (1 / 8) * (∫ u, weilBump u))) ^ 2) := by
  set ε := ∫ u : ℝ, ‖riemannPhiTail L u‖ * Real.exp (1 / 2 * |u|) with hε
  set m := xiWindowFloor τ₀ δ with hm
  set I₀ := Icc (τ₀ - δ / 2) (τ₀ + δ / 2) with hI₀
  set c := Real.cos (1 / 8) * (∫ u, weilBump u) with hc
  have hIκ : 0 < ∫ u, weilBump u := weilBump.integral_pos
  have hcos : 0 < Real.cos (1 / 8) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  have hc0 : 0 < c := mul_pos hcos hIκ
  have hm0 : 0 < m := by
    rw [hm]; unfold xiWindowFloor
    have := xiLineConst_pos
    have : 0 < τ₀ - 1 / 2 := by linarith
    positivity
  set ℓ := (m / 2) * (τ₀ - 1 / 2) ^ 2 * c with hℓ
  have hτ₀' : 0 < τ₀ - 1 / 2 := by linarith
  have hℓ0 : 0 < ℓ := by rw [hℓ]; positivity
  -- pointwise lower bound on the window
  have hpt : ∀ τ ∈ I₀, ℓ ≤ ‖paperFT (modRadicalTest L τ₀) (τ : ℂ)‖ := by
    intro τ hτ
    have hτω : |τ - τ₀| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hlow := norm_paperFT_modRadicalTest_real_ge L τ₀ hτω
    have hXi := norm_riemannPhiTransform_window_ge hτ₀ hδ hδ1 hsep hτ
    rw [← hε] at hlow
    have hsq : (τ₀ - 1 / 2) ^ 2 ≤ τ ^ 2 + 1 / 4 := by
      have : (τ₀ - 1 / 2) ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith [hτ.1]) 2
      linarith
    have hdiff : m / 2 ≤ ‖riemannPhiTransform (1 / 2 + I * τ)‖ - ε := by linarith
    calc ℓ = (m / 2) * ((τ₀ - 1 / 2) ^ 2 * c) := by rw [hℓ]; ring
      _ ≤ (‖riemannPhiTransform (1 / 2 + I * τ)‖ - ε) * ((τ ^ 2 + 1 / 4) * c) := by
          apply mul_le_mul hdiff (mul_le_mul_of_nonneg_right hsq hc0.le) (by positivity)
            (by linarith)
      _ ≤ ‖paperFT (modRadicalTest L τ₀) (τ : ℂ)‖ := hlow
  -- the domination inequality applied to the modulated test
  have hdom := hν (modRadicalTest L τ₀) (contDiff_modRadicalTest L τ₀) (tsupport_modRadicalTest L τ₀)
    (paperFT_modRadicalTest_half_I L τ₀) (paperFT_modRadicalTest_neg_half_I L τ₀)
  have hind : ∫⁻ τ, I₀.indicator (fun _ => ENNReal.ofReal (ℓ ^ 2)) τ ∂ν ≤
      ∫⁻ τ, ENNReal.ofReal (‖paperFT (modRadicalTest L τ₀) τ‖ ^ 2) ∂ν := by
    refine lintegral_mono fun τ => ?_
    by_cases hτ : τ ∈ I₀
    · rw [indicator_of_mem hτ]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hℓ0.le (hpt τ hτ) 2)
    · rw [indicator_of_notMem hτ]; exact bot_le
  rw [lintegral_indicator_const measurableSet_Icc] at hind
  have hkey : ENNReal.ofReal (ℓ ^ 2) * ν I₀ ≤
      ENNReal.ofReal ‖zetaZeroConfig.W (modRadicalTest L τ₀) (modRadicalTest L τ₀)‖ :=
    hind.trans hdom
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  rw [ENNReal.ofReal_div_of_pos hℓ2]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hℓ2).ne')
    (Or.inl ENNReal.ofReal_ne_top)]
  rw [mul_comm]; exact hkey


/-! ## The pinning law -/

local notation "Mθ" => jacobiThetaTailConstant

/-- `E₀ = 40 Mθ e^π/(6π - 6)`, the tail constant of Riemann's kernel. -/
def phiTailConst : ℝ := 40 * Mθ * Real.exp Real.pi / (6 * Real.pi - 6)

theorem phiTailConst_nonneg : 0 ≤ phiTailConst := by
  unfold phiTailConst
  have hM := jacobiThetaTailConstant_nonneg
  have : 0 < 6 * Real.pi - 6 := by nlinarith [Real.pi_gt_three]
  positivity

/-- For `L ≥ 1`: `ε_L ≤ E₀ e^{6L} e^{-π e^{2L-1/2}}`. -/
theorem phiTail_eps_le {L : ℝ} (hL : 1 ≤ L) :
    ∫ u : ℝ, ‖riemannPhiTail L u‖ * Real.exp (1 / 2 * |u|) ≤
      phiTailConst * Real.exp (6 * L) * Real.exp (-Real.pi * Real.exp (2 * L - 1 / 2)) := by
  have h := integral_norm_riemannPhiTail_mul_exp_le (b := 1 / 2) hL (by norm_num)
  refine h.trans ?_
  rw [show 2 * (L - 1 / 4) = 2 * L - 1 / 2 by ring]
  have h6 : Real.exp (6 * (L - 1 / 4)) ≤ Real.exp (6 * L) := Real.exp_le_exp.mpr (by linarith)
  have hE := phiTailConst_nonneg
  unfold phiTailConst at hE ⊢
  gcongr

/-- The quadratic-beats-linear step: for `L ≥ 6 + B`, `B ≥ 0`,
`6L + B ≤ (π/2) e^{2L-1/2}`. -/
theorem linear_le_half_pi_exp {L B : ℝ} (hB : 0 ≤ B) (hL : 6 + B ≤ L) :
    6 * L + B ≤ Real.pi / 2 * Real.exp (2 * L - 1 / 2) := by
  have hL1 : 1 ≤ L := by linarith
  have h1 : Real.exp (2 * L - 1 / 2) = Real.exp L * Real.exp (L - 1 / 2) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : 1 + L + L ^ 2 / 2 ≤ Real.exp L := by
    have := Real.sum_le_exp_of_nonneg (x := L) (by linarith) 3
    simp [Finset.sum_range_succ, Nat.factorial] at this
    nlinarith
  have h3 : 1 ≤ Real.exp (L - 1 / 2) := Real.one_le_exp (by linarith)
  have h4 : 1 + L + L ^ 2 / 2 ≤ Real.exp (2 * L - 1 / 2) := by
    rw [h1]; nlinarith [Real.exp_pos L]
  have hpi : 3 ≤ Real.pi := Real.pi_gt_three.le
  have h5 : 3 / 2 * (1 + L + L ^ 2 / 2) ≤ Real.pi / 2 * Real.exp (2 * L - 1 / 2) := by
    have := mul_le_mul (by linarith : (3 / 2 : ℝ) ≤ Real.pi / 2) h4 (by positivity)
      (by positivity)
    linarith
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ L - 6 - B) (by linarith : (0:ℝ) ≤ L),
    mul_nonneg hB (by linarith : (0:ℝ) ≤ L - 4 / 3)]

theorem pinning_poly_le {τ₀ : ℝ} (hτ₀ : 5 ≤ τ₀) :
    (1 + τ₀) ^ 4 * Real.log (τ₀ + 3) ≤ 4 * (τ₀ - 1 / 2) ^ 8 := by
  set x := τ₀ - 1 / 2 with hx
  have hx45 : (9 / 2 : ℝ) ≤ x := by rw [hx]; linarith
  have hx0 : 0 ≤ x := by linarith
  have hlog : Real.log (τ₀ + 3) ≤ τ₀ + 3 := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < τ₀ + 3); linarith
  have hlog0 : 0 ≤ Real.log (τ₀ + 3) := Real.log_nonneg (by linarith)
  have h1 : (1 + τ₀) ^ 4 ≤ 4 * x ^ 4 := by
    have hle : 1 + τ₀ ≤ (4 / 3) * x := by rw [hx]; linarith
    have h' : (1 + τ₀) ^ 4 ≤ ((4 / 3) * x) ^ 4 := pow_le_pow_left₀ (by linarith) hle 4
    have e : ((4 / 3 : ℝ) * x) ^ 4 = (256 / 81) * x ^ 4 := by ring
    have hx4 : 0 ≤ x ^ 4 := by positivity
    linarith
  have h2 : τ₀ + 3 ≤ x ^ 4 := by
    have hx3 : 2 ≤ x ^ 3 := by
      have : (9 / 2 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx45 3
      norm_num at this; linarith
    have : x ^ 4 = x * x ^ 3 := by ring
    rw [this]
    have : 2 * x ≤ x * x ^ 3 := by nlinarith
    rw [hx] at this ⊢; linarith
  calc (1 + τ₀) ^ 4 * Real.log (τ₀ + 3) ≤ (4 * x ^ 4) * (τ₀ + 3) :=
        mul_le_mul h1 hlog hlog0 (by positivity)
    _ ≤ (4 * x ^ 4) * x ^ 4 := by gcongr
    _ = 4 * x ^ 8 := by ring

/-- The window floor beats twice the tail once `L ≥ 6 + B`. -/
theorem two_eps_le_window_floor {L B τ₀ δ : ℝ} (hB : Real.log (8 * phiTailConst /
      (81 * xiLineConst) + 1) ≤ B) (hB0 : 0 ≤ B) (hL : 6 + B ≤ L) (hτ₀ : 5 ≤ τ₀)
    (hH : Real.pi * (τ₀ + 1 / 2) + 6 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ ≤
      Real.pi * Real.exp (2 * L - 1 / 2)) :
    2 * (∫ u : ℝ, ‖riemannPhiTail L u‖ * Real.exp (1 / 2 * |u|)) ≤ xiWindowFloor τ₀ δ := by
  set E₀ := phiTailConst
  have hE₀0 : 0 ≤ E₀ := phiTailConst_nonneg
  set cΞ := xiLineConst
  have hcΞ0 : 0 < cΞ := xiLineConst_pos
  set T := Real.exp (2 * L - 1 / 2) with hT
  have hL1 : 1 ≤ L := by linarith
  have hεle := phiTail_eps_le hL1
  rw [← hT] at hεle
  set S := Real.pi * (τ₀ + 1 / 2) + 6 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ with hS
  have hmS : xiWindowFloor τ₀ δ = cΞ * (τ₀ - 1 / 2) ^ 2 * Real.exp (-(S / 2)) := by
    unfold xiWindowFloor
    rw [mul_assoc, ← Real.exp_add]
    congr 2; rw [hS]; ring
  have hm_low : cΞ * (81 / 4) * Real.exp (-(Real.pi * T / 2)) ≤ xiWindowFloor τ₀ δ := by
    rw [hmS]
    have hsq : (81 / 4 : ℝ) ≤ (τ₀ - 1 / 2) ^ 2 := by nlinarith
    have hexpS : Real.exp (-(Real.pi * T / 2)) ≤ Real.exp (-(S / 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    gcongr
  have hlin := linear_le_half_pi_exp hB0 hL
  have hexpB : 8 * E₀ / (81 * cΞ) + 1 ≤ Real.exp B := by
    calc 8 * E₀ / (81 * cΞ) + 1 = Real.exp (Real.log (8 * E₀ / (81 * cΞ) + 1)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp B := Real.exp_le_exp.mpr hB
  have h1 : 8 * E₀ / (81 * cΞ) * Real.exp (6 * L) ≤ Real.exp (Real.pi * T / 2) := by
    calc 8 * E₀ / (81 * cΞ) * Real.exp (6 * L) ≤ Real.exp B * Real.exp (6 * L) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = Real.exp (6 * L + B) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (Real.pi * T / 2) := Real.exp_le_exp.mpr (by rw [hT]; linarith)
  have h1' : 8 * E₀ * Real.exp (6 * L) ≤ 81 * cΞ * Real.exp (Real.pi * T / 2) := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 81 * cΞ)
    rw [← mul_assoc, mul_div_cancel₀ _ (by positivity)] at this
    linarith
  set X := Real.exp (-(Real.pi * T / 2)) with hX
  have hX0 : 0 < X := Real.exp_pos _
  have hinv : Real.exp (Real.pi * T / 2) * X = 1 := by rw [hX, ← Real.exp_add]; simp
  have hsplit : Real.exp (-Real.pi * T) = X * X := by
    rw [hX, ← Real.exp_add]; ring_nf
  have hA : 2 * E₀ * Real.exp (6 * L) * X ≤ cΞ * (81 / 4) := by
    have := mul_le_mul_of_nonneg_right h1' (by positivity : (0:ℝ) ≤ X / 4)
    calc 2 * E₀ * Real.exp (6 * L) * X = (8 * E₀ * Real.exp (6 * L)) * (X / 4) := by ring
      _ ≤ (81 * cΞ * Real.exp (Real.pi * T / 2)) * (X / 4) := this
      _ = cΞ * (81 / 4) * (Real.exp (Real.pi * T / 2) * X) := by ring
      _ = cΞ * (81 / 4) := by rw [hinv]; ring
  have h2 : 2 * (E₀ * Real.exp (6 * L) * Real.exp (-Real.pi * T)) ≤ cΞ * (81 / 4) * X := by
    rw [hsplit]
    calc 2 * (E₀ * Real.exp (6 * L) * (X * X)) = (2 * E₀ * Real.exp (6 * L) * X) * X := by ring
      _ ≤ cΞ * (81 / 4) * X := mul_le_mul_of_nonneg_right hA hX0.le
  linarith [mul_le_mul_of_nonneg_left hεle (by norm_num : (0:ℝ) ≤ 2)]

/-- The numeric form of the Christoffel ratio. -/
theorem pinning_ratio_le {L τ₀ δ A₀ ε Wv : ℝ} (hA₀ : 1 ≤ A₀) (hτ₀ : 5 ≤ τ₀)
    (hH : Real.pi * (τ₀ + 1 / 2) + 6 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ ≤
      Real.pi * Real.exp (2 * L - 1 / 2))
    (hε0 : 0 ≤ ε)
    (hεle : ε ≤ phiTailConst * Real.exp (6 * L) * Real.exp (-Real.pi * Real.exp (2 * L - 1 / 2)))
    (hW : Wv ≤ ε ^ 2 * bumpDecayConst ^ 2 * (1 + τ₀) ^ 4 * (24 * A₀ * Real.log (τ₀ + 3))) :
    Wv / ((xiWindowFloor τ₀ δ / 2) * (τ₀ - 1 / 2) ^ 2 *
        (Real.cos (1 / 8) * (∫ u, weilBump u))) ^ 2 ≤
      (384 * (phiTailConst ^ 2 * bumpDecayConst ^ 2 * A₀) /
        (xiLineConst ^ 2 * (Real.cos (1 / 8) * (∫ u, weilBump u)) ^ 2)) *
        Real.exp (12 * L) * Real.exp (-Real.pi * Real.exp (2 * L - 1 / 2)) := by
  set E₀ := phiTailConst
  have hE₀0 : 0 ≤ E₀ := phiTailConst_nonneg
  set Cκ := bumpDecayConst
  have hCκ0 : 0 ≤ Cκ := bumpDecayConst_nonneg
  set cΞ := xiLineConst
  have hcΞ0 : 0 < cΞ := xiLineConst_pos
  have hIκ : 0 < ∫ u, weilBump u := weilBump.integral_pos
  have hcos : 0 < Real.cos (1 / 8) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  set c := Real.cos (1 / 8) * (∫ u, weilBump u) with hc
  have hc0 : 0 < c := mul_pos hcos hIκ
  set T := Real.exp (2 * L - 1 / 2) with hT
  set S := Real.pi * (τ₀ + 1 / 2) + 6 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ with hS
  have hτpos : 0 < τ₀ - 1 / 2 := by linarith
  have hmS : xiWindowFloor τ₀ δ = cΞ * (τ₀ - 1 / 2) ^ 2 * Real.exp (-(S / 2)) := by
    unfold xiWindowFloor
    rw [mul_assoc, ← Real.exp_add]
    congr 2; rw [hS]; ring
  set m := xiWindowFloor τ₀ δ with hm
  have hm2 : cΞ ^ 2 * (τ₀ - 1 / 2) ^ 4 * Real.exp (-(Real.pi * T)) ≤ m ^ 2 := by
    rw [hmS]
    have e : (cΞ * (τ₀ - 1 / 2) ^ 2 * Real.exp (-(S / 2))) ^ 2 =
        cΞ ^ 2 * (τ₀ - 1 / 2) ^ 4 * Real.exp (-S) := by
      rw [mul_pow, mul_pow, ← pow_mul, ← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e]
    have : Real.exp (-(Real.pi * T)) ≤ Real.exp (-S) := Real.exp_le_exp.mpr (by linarith)
    gcongr
  set ℓ := (m / 2) * (τ₀ - 1 / 2) ^ 2 * c with hℓ
  have hℓ2 : ℓ ^ 2 = m ^ 2 * (τ₀ - 1 / 2) ^ 4 * c ^ 2 / 4 := by rw [hℓ]; ring
  have hpoly := pinning_poly_le hτ₀
  have hε2 : ε ^ 2 ≤ E₀ ^ 2 * Real.exp (12 * L) * (Real.exp (-(Real.pi * T)) *
      Real.exp (-(Real.pi * T))) := by
    have := pow_le_pow_left₀ hε0 hεle 2
    calc ε ^ 2 ≤ (E₀ * Real.exp (6 * L) * Real.exp (-Real.pi * T)) ^ 2 := this
      _ = E₀ ^ 2 * Real.exp (12 * L) * (Real.exp (-(Real.pi * T)) *
            Real.exp (-(Real.pi * T))) := by
          rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
          push_cast
          rw [show -Real.pi * T = -(Real.pi * T) by ring]
          ring_nf
  have hWnum : Wv ≤ E₀ ^ 2 * Real.exp (12 * L) * (Real.exp (-(Real.pi * T)) *
      Real.exp (-(Real.pi * T))) * Cκ ^ 2 * (24 * A₀) * (4 * (τ₀ - 1 / 2) ^ 8) := by
    refine hW.trans ?_
    have hA0 : 0 ≤ 24 * A₀ := by linarith
    have hlog0 : 0 ≤ Real.log (τ₀ + 3) := Real.log_nonneg (by linarith)
    have hP0 : 0 ≤ (1 + τ₀) ^ 4 * Real.log (τ₀ + 3) := by positivity
    have hQ0 : 0 ≤ Cκ ^ 2 * (24 * A₀) := by positivity
    calc ε ^ 2 * Cκ ^ 2 * (1 + τ₀) ^ 4 * (24 * A₀ * Real.log (τ₀ + 3))
        = ε ^ 2 * (Cκ ^ 2 * (24 * A₀)) * ((1 + τ₀) ^ 4 * Real.log (τ₀ + 3)) := by ring
      _ ≤ (E₀ ^ 2 * Real.exp (12 * L) * (Real.exp (-(Real.pi * T)) *
            Real.exp (-(Real.pi * T)))) * (Cκ ^ 2 * (24 * A₀)) * (4 * (τ₀ - 1 / 2) ^ 8) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hε2 hQ0) hpoly hP0
          have : 0 ≤ E₀ ^ 2 * Real.exp (12 * L) * (Real.exp (-(Real.pi * T)) *
            Real.exp (-(Real.pi * T))) := by positivity
          positivity
      _ = (E₀ ^ 2 * Real.exp (12 * L) * (Real.exp (-(Real.pi * T)) *
            Real.exp (-(Real.pi * T)))) * Cκ ^ 2 * (24 * A₀) * (4 * (τ₀ - 1 / 2) ^ 8) := by ring
  set Y := Real.exp (-(Real.pi * T)) with hY
  have hY0 : 0 < Y := Real.exp_pos _
  have hden : cΞ ^ 2 * (τ₀ - 1 / 2) ^ 4 * Y * (τ₀ - 1 / 2) ^ 4 * c ^ 2 / 4 ≤ ℓ ^ 2 := by
    rw [hℓ2]
    have := mul_le_mul_of_nonneg_right hm2 (by positivity : (0:ℝ) ≤ (τ₀ - 1 / 2) ^ 4 * c ^ 2 / 4)
    calc cΞ ^ 2 * (τ₀ - 1 / 2) ^ 4 * Y * (τ₀ - 1 / 2) ^ 4 * c ^ 2 / 4
        = cΞ ^ 2 * (τ₀ - 1 / 2) ^ 4 * Y * ((τ₀ - 1 / 2) ^ 4 * c ^ 2 / 4) := by ring
      _ ≤ m ^ 2 * ((τ₀ - 1 / 2) ^ 4 * c ^ 2 / 4) := this
      _ = m ^ 2 * (τ₀ - 1 / 2) ^ 4 * c ^ 2 / 4 := by ring
  have hdenpos : 0 < cΞ ^ 2 * (τ₀ - 1 / 2) ^ 4 * Y * (τ₀ - 1 / 2) ^ 4 * c ^ 2 / 4 := by
    positivity
  have hWv0 : 0 ≤ E₀ ^ 2 * Real.exp (12 * L) * (Y * Y) * Cκ ^ 2 * (24 * A₀) *
      (4 * (τ₀ - 1 / 2) ^ 8) := by
    have : 0 ≤ 24 * A₀ := by linarith
    positivity
  calc Wv / ℓ ^ 2
      ≤ (E₀ ^ 2 * Real.exp (12 * L) * (Y * Y) * Cκ ^ 2 * (24 * A₀) * (4 * (τ₀ - 1 / 2) ^ 8)) /
          (cΞ ^ 2 * (τ₀ - 1 / 2) ^ 4 * Y * (τ₀ - 1 / 2) ^ 4 * c ^ 2 / 4) := by
        rcases le_or_gt Wv 0 with hWn | hWp
        · have : Wv / ℓ ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hWn (by positivity)
          exact this.trans (div_nonneg hWv0 hdenpos.le)
        · exact div_le_div₀ hWv0 hWnum hdenpos hden
    _ = 384 * (E₀ ^ 2 * Cκ ^ 2 * A₀) / (cΞ ^ 2 * c ^ 2) * Real.exp (12 * L) * Y := by
        set x := τ₀ - 1 / 2 with hx
        have hx0 : x ≠ 0 := hτpos.ne'
        have hY0' : Y ≠ 0 := hY0.ne'
        have hc0' : c ≠ 0 := hc0.ne'
        have hcΞ' : cΞ ≠ 0 := hcΞ0.ne'
        field_simp
        ring
    _ = 384 * (E₀ ^ 2 * Cκ ^ 2 * A₀) / (cΞ ^ 2 * c ^ 2) * Real.exp (12 * L) *
          Real.exp (-Real.pi * T) := by
        rw [hY]; ring_nf

/-- **Krein pinning law (away from the zeros).**  There are constants `K > 0` and `L₀` such that
for every `L ≥ L₀` and every positive measure `ν` dominated by the level-`L` Hodge form of `ζ`
(in particular every positive Krein completion of the level-`L` Weil form): if `τ₀ ≥ 5` is at
distance `≥ δ` (`0 < δ ≤ 1`) from every zero ordinate and
`π(τ₀ + 1/2) + 6C log(τ₀+1)/δ ≤ π e^{2L-1/2}`, then
`ν([τ₀ - δ/2, τ₀ + δ/2]) ≤ K e^{12L} e^{-π e^{2L-1/2}}`.

Below height `≈ e^{2L-1/2}`, a positive completion carries only super-exponentially small mass away
from the zero ordinates of `ζ`.  The proof tests `ν` against the modulated radical test at
`ω = τ₀`. -/
theorem zeta_krein_completion_pinned_off_zeros :
    ∃ K L₀ : ℝ, 0 < K ∧ ∀ L : ℝ, L₀ ≤ L → ∀ ν : Measure ℝ, DominatedByHodgeForm L ν →
      ∀ τ₀ δ : ℝ, 5 ≤ τ₀ → 0 < δ → δ ≤ 1 →
        (∀ ρ ∈ zetaZeroConfig.carrier, δ ≤ |ρ.im - τ₀|) →
        Real.pi * (τ₀ + 1 / 2) + 6 * logDerivZetaConstant * Real.log (τ₀ + 1) / δ ≤
          Real.pi * Real.exp (2 * L - 1 / 2) →
        ν (Icc (τ₀ - δ / 2) (τ₀ + δ / 2)) ≤
          ENNReal.ofReal (K * Real.exp (12 * L) *
            Real.exp (-Real.pi * Real.exp (2 * L - 1 / 2))) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  have hE₀0 : 0 ≤ phiTailConst := phiTailConst_nonneg
  have hcΞ0 : 0 < xiLineConst := xiLineConst_pos
  have hIκ : 0 < ∫ u, weilBump u := weilBump.integral_pos
  have hcos : 0 < Real.cos (1 / 8) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  set K := 384 * (phiTailConst ^ 2 * bumpDecayConst ^ 2 * A₀) /
    (xiLineConst ^ 2 * (Real.cos (1 / 8) * (∫ u, weilBump u)) ^ 2) + 1 with hK
  have hK0 : 0 < K := by
    rw [hK]
    have := bumpDecayConst_nonneg
    positivity
  set B := max 0 (Real.log (8 * phiTailConst / (81 * xiLineConst) + 1)) with hB
  have hB0 : 0 ≤ B := le_max_left _ _
  have hBlog : Real.log (8 * phiTailConst / (81 * xiLineConst) + 1) ≤ B := le_max_right _ _
  refine ⟨K, 6 + B, hK0, fun L hL ν hν τ₀ δ hτ₀ hδ hδ1 hsep hH => ?_⟩
  have hL1 : 1 ≤ L := by linarith
  have hbig := two_eps_le_window_floor hBlog hB0 hL hτ₀ hH
  have hraw := measure_window_le_of_dominated hν hτ₀ hδ hδ1 hsep hbig
  refine le_trans hraw (ENNReal.ofReal_le_ofReal ?_)
  have hW := norm_W_modRadicalTest_le hA₀ hloc L τ₀
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ τ₀)] at hW
  have hε0 : 0 ≤ ∫ u : ℝ, ‖riemannPhiTail L u‖ * Real.exp (1 / 2 * |u|) :=
    integral_nonneg fun _ => by positivity
  have hratio := pinning_ratio_le hA₀ hτ₀ hH hε0 (phiTail_eps_le hL1) hW
  refine hratio.trans ?_
  have hE : 0 ≤ Real.exp (12 * L) * Real.exp (-Real.pi * Real.exp (2 * L - 1 / 2)) := by
    positivity
  calc 384 * (phiTailConst ^ 2 * bumpDecayConst ^ 2 * A₀) /
          (xiLineConst ^ 2 * (Real.cos (1 / 8) * (∫ u, weilBump u)) ^ 2) *
        Real.exp (12 * L) * Real.exp (-Real.pi * Real.exp (2 * L - 1 / 2))
      = (384 * (phiTailConst ^ 2 * bumpDecayConst ^ 2 * A₀) /
          (xiLineConst ^ 2 * (Real.cos (1 / 8) * (∫ u, weilBump u)) ^ 2)) *
        (Real.exp (12 * L) * Real.exp (-Real.pi * Real.exp (2 * L - 1 / 2))) := by ring
    _ ≤ K * (Real.exp (12 * L) * Real.exp (-Real.pi * Real.exp (2 * L - 1 / 2))) := by
        gcongr; rw [hK]; linarith
    _ = K * Real.exp (12 * L) * Real.exp (-Real.pi * Real.exp (2 * L - 1 / 2)) := by ring

end

end RHTower
