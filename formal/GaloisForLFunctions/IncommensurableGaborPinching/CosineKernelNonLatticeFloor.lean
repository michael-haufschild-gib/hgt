import GaloisForLFunctions.IncommensurableGaborPinching.DisjointPairSchurSlack
import GaloisForLFunctions.RHTower.WindowTransformSamplingParseval
import Zeta23.ThmD.ParamsD
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Non-lattice floor and finite-grid approximation for the Montgomery–Taylor cosine kernel

For the untapered Montgomery–Taylor cosine profile `v*_λ(v) = cos(√2 λ v)` on `[-1/2, 1/2]`,
the normalized Fourier correlation kernel at scaled ordinate spacing `Δ = (L / 2π) (γ_x − γ_y)` is

`K_λ(Δ) = (∫_{-1/2}^{1/2} cos(√2 λ v) cos(2π Δ v) dv) / (∫_{-1/2}^{1/2} cos(√2 λ v) dv)`.

Unlike the boxcar sinc kernel `sin(π Δ) / (π Δ)` whose zeros lie on the additive lattice `ℤ \ {0}`,
the zeros of `K_λ` for `λ ∈ [999/1000, 1]` lie inside two narrow intervals
`I₁ = (26/25, 43/40)` and `I₂ = (503/250, 256/125)` on `[0, 3]` whose sumsets miss `I₁ ∪ I₂`:
`2 · (26/25) > 256/125` and `26/25 + 503/250 > 3`. Consequently:

1. `1 / 250 ≤ |K_λ(Δ)|` for every `Δ ∈ [0, 3] \ (I₁ ∪ I₂)` (`one_div_250_le_abs_mtKernel`);
2. Every ordered triple `γ₁ < γ₂ < γ₃` of scaled span `α (γ₃ − γ₁) ≤ 3` contains a pair with
   `1 / 250 ≤ |K_λ|` (`exists_pair_mtKernel_ge_of_triple`);
3. Uniformly over all bulk pairs `x, y ∈ S₁` with ordinates in `[T + √T, 2T − √T]`, the concrete
   finite-grid overlap `pairGridOverlap Z (P.atD T) T x y` converges to `K_λ((L / 2π)(γ_x − γ_y))`
   as `T → ∞` (`eventually_pairGridOverlap_atD_close`).
-/

noncomputable section

open Real MeasureTheory Filter Topology Finset
open scoped BigOperators

namespace GaloisForLFunctions.IncommensurableGaborPinching

/-! ## Section 1. The untapered cosine kernel and its closed form -/

/-- Numerator `∫_{-1/2}^{1/2} cos(√2 λ v) cos(2π Δ v) dv` of the Montgomery–Taylor kernel. -/
def mtKernelNum (lam Δ : ℝ) : ℝ :=
  ∫ v in (-(1 : ℝ) / 2)..(1 / 2), Zeta23.ThmD.vStar lam v * Real.cos (2 * Real.pi * Δ * v)

/-- Normalized untapered correlation kernel `mtKernelNum lam Δ / aStar lam`. -/
def mtKernel (lam Δ : ℝ) : ℝ :=
  mtKernelNum lam Δ / Zeta23.ThmD.aStar lam

/-- First root-exclusion interval `(26/25, 43/40) = (1.040, 1.075)` on `[0, 3]`. -/
def mtExcl₁ : Set ℝ := Set.Ioo (26 / 25) (43 / 40)

/-- Second root-exclusion interval `(503/250, 256/125) = (2.012, 2.048)` on `[0, 3]`. -/
def mtExcl₂ : Set ℝ := Set.Ioo (503 / 250) (256 / 125)

lemma mtKernelNum_neg (lam Δ : ℝ) : mtKernelNum lam (-Δ) = mtKernelNum lam Δ := by
  unfold mtKernelNum
  refine intervalIntegral.integral_congr fun v _ => ?_
  rw [show 2 * Real.pi * (-Δ) * v = -(2 * Real.pi * Δ * v) by ring, Real.cos_neg]

lemma mtKernel_neg (lam Δ : ℝ) : mtKernel lam (-Δ) = mtKernel lam Δ := by
  unfold mtKernel
  rw [mtKernelNum_neg]

lemma mtKernel_abs (lam Δ : ℝ) : mtKernel lam |Δ| = mtKernel lam Δ := by
  rcases le_or_gt 0 Δ with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, mtKernel_neg]

lemma vStar_bounds_on_unit {lam v : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hv : v ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) :
    1 / 2 ≤ Zeta23.ThmD.vStar lam v ∧ Zeta23.ThmD.vStar lam v ≤ 1 := by
  unfold Zeta23.ThmD.vStar
  refine ⟨?_, Real.cos_le_one _⟩
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hv_sq : v ^ 2 ≤ 1 / 4 := by nlinarith [hv.1, hv.2]
  have hlam_sq : lam ^ 2 ≤ 1 := by nlinarith
  have harg_sq : (Real.sqrt 2 * lam * v) ^ 2 ≤ 1 / 2 := by
    calc (Real.sqrt 2 * lam * v) ^ 2 = 2 * lam ^ 2 * v ^ 2 := by
          rw [mul_pow, mul_pow, hs2]
      _ ≤ 2 * 1 * (1 / 4) := by nlinarith [sq_nonneg lam, sq_nonneg v]
      _ = 1 / 2 := by norm_num
  have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.sqrt 2 * lam * v)
  linarith

lemma aStar_bounds {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    1 / 2 ≤ Zeta23.ThmD.aStar lam ∧ Zeta23.ThmD.aStar lam ≤ 1 := by
  unfold Zeta23.ThmD.aStar
  have hle : (-(1 : ℝ) / 2) ≤ 1 / 2 := by norm_num
  have hint : IntervalIntegrable (Zeta23.ThmD.vStar lam) volume (-(1 : ℝ) / 2) (1 / 2) :=
    (by unfold Zeta23.ThmD.vStar; fun_prop : Continuous (Zeta23.ThmD.vStar lam)).intervalIntegrable _ _
  constructor
  · have hlow : ∫ _ in (-(1 : ℝ) / 2)..(1 / 2), (1 / 2 : ℝ)
        ≤ ∫ v in (-(1 : ℝ) / 2)..(1 / 2), Zeta23.ThmD.vStar lam v :=
      intervalIntegral.integral_mono_on hle intervalIntegrable_const hint fun v hv =>
        (vStar_bounds_on_unit h0 h1 hv).1
    rw [intervalIntegral.integral_const, smul_eq_mul] at hlow
    linarith
  · have hhi : ∫ v in (-(1 : ℝ) / 2)..(1 / 2), Zeta23.ThmD.vStar lam v
        ≤ ∫ _ in (-(1 : ℝ) / 2)..(1 / 2), (1 : ℝ) :=
      intervalIntegral.integral_mono_on hle hint intervalIntegrable_const fun v hv =>
        (vStar_bounds_on_unit h0 h1 hv).2
    rw [intervalIntegral.integral_const, smul_eq_mul] at hhi
    linarith

lemma abs_mtKernelNum_le_aStar {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (Δ : ℝ) :
    |mtKernelNum lam Δ| ≤ Zeta23.ThmD.aStar lam := by
  unfold mtKernelNum Zeta23.ThmD.aStar
  have hle : (-(1 : ℝ) / 2) ≤ 1 / 2 := by norm_num
  rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle]
  refine (abs_integral_le_integral_abs).trans ?_
  apply MeasureTheory.setIntegral_mono_on
  · exact (by unfold Zeta23.ThmD.vStar; fun_prop :
      Continuous fun v => |Zeta23.ThmD.vStar lam v * Real.cos (2 * Real.pi * Δ * v)|).integrableOn_Ioc
  · exact (by unfold Zeta23.ThmD.vStar; fun_prop :
      Continuous (Zeta23.ThmD.vStar lam)).integrableOn_Ioc
  · exact measurableSet_Ioc
  · intro v hv
    have hv' : v ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) := Set.Ioc_subset_Icc_self hv
    have hv0 : 0 ≤ Zeta23.ThmD.vStar lam v := by linarith [(vStar_bounds_on_unit h0 h1 hv').1]
    rw [abs_mul, abs_of_nonneg hv0]
    exact mul_le_of_le_one_right hv0 (Real.abs_cos_le_one _)

lemma abs_mtKernelNum_le_abs_mtKernel {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (Δ : ℝ) :
    |mtKernelNum lam Δ| ≤ |mtKernel lam Δ| := by
  obtain ⟨ha_lo, ha_hi⟩ := aStar_bounds h0 h1
  have ha_pos : 0 < Zeta23.ThmD.aStar lam := by linarith
  unfold mtKernel
  rw [abs_div, abs_of_pos ha_pos, le_div_iff₀ ha_pos]
  exact mul_le_of_le_one_right (abs_nonneg _) ha_hi

private lemma integral_cos_two_mul {t : ℝ} (ht : t ≠ 0) :
    ∫ v in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (2 * t * v) = Real.sin t / t := by
  have hd : ∀ v ∈ Set.uIcc (-(1 : ℝ) / 2) (1 / 2),
      HasDerivAt (fun v => Real.sin (2 * t * v) / (2 * t)) (Real.cos (2 * t * v)) v := by
    intro v _
    have h1 : HasDerivAt (fun v => 2 * t * v) (2 * t * 1) v := (hasDerivAt_id' v).const_mul (2 * t)
    exact (h1.sin.div_const (2 * t)).congr_deriv (by field_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun v => Real.cos (2 * t * v)).intervalIntegrable _ _)]
  have e1 : 2 * t * (1 / 2) = t := by ring
  have e2 : 2 * t * (-(1 : ℝ) / 2) = -t := by ring
  rw [e1, e2, Real.sin_neg]
  field_simp
  ring

/-- Exact closed form of the untapered cosine kernel numerator for `Δ ≥ 2/5`, `0 ≤ λ ≤ 1`. -/
lemma mtKernelNum_closed_form {lam Δ : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (hΔ : 2 / 5 ≤ Δ) :
    ((Real.pi * Δ) ^ 2 - (Zeta23.ThmD.theta lam) ^ 2) * mtKernelNum lam Δ
      = (Real.pi * Δ) * Real.cos (Zeta23.ThmD.theta lam) * Real.sin (Real.pi * Δ)
        - Zeta23.ThmD.theta lam * Real.sin (Zeta23.ThmD.theta lam) * Real.cos (Real.pi * Δ) := by
  set a := Zeta23.ThmD.theta lam
  set x := Real.pi * Δ
  have ha0 : 0 ≤ a := Zeta23.ThmD.theta_nonneg h0
  have ha_sq : a ^ 2 ≤ 1 / 2 := Zeta23.ThmD.theta_sq_le h0 h1
  have ha_lt : a < 1 := by nlinarith
  have hx_gt : 6 / 5 < x := by
    simp only [x]
    nlinarith [Real.pi_gt_three]
  have hxm : x - a ≠ 0 := by linarith
  have hxp : x + a ≠ 0 := by linarith
  have harg : ∀ v : ℝ, Real.sqrt 2 * lam * v = 2 * a * v := fun v => by
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs0 : (0 : ℝ) < Real.sqrt 2 := by positivity
    simp only [a, Zeta23.ThmD.theta]
    field_simp
    ring_nf
    rw [hs2]
    ring
  have hprod : ∀ v : ℝ, Zeta23.ThmD.vStar lam v * Real.cos (2 * Real.pi * Δ * v)
      = (Real.cos (2 * (x - a) * v) + Real.cos (2 * (x + a) * v)) / 2 := fun v => by
    unfold Zeta23.ThmD.vStar
    rw [harg v, show 2 * Real.pi * Δ * v = 2 * x * v by simp only [x]; ring]
    have hsub := Real.cos_sub (2 * x * v) (2 * a * v)
    have hadd := Real.cos_add (2 * x * v) (2 * a * v)
    rw [show 2 * x * v - 2 * a * v = 2 * (x - a) * v by ring] at hsub
    rw [show 2 * x * v + 2 * a * v = 2 * (x + a) * v by ring] at hadd
    linarith
  have hint_eq : mtKernelNum lam Δ
      = (Real.sin (x - a) / (x - a) + Real.sin (x + a) / (x + a)) / 2 := by
    unfold mtKernelNum
    have hc : ∫ v in (-(1 : ℝ) / 2)..(1 / 2),
        Zeta23.ThmD.vStar lam v * Real.cos (2 * Real.pi * Δ * v)
        = ∫ v in (-(1 : ℝ) / 2)..(1 / 2),
            (Real.cos (2 * (x - a) * v) + Real.cos (2 * (x + a) * v)) / 2 :=
      intervalIntegral.integral_congr fun v _ => hprod v
    rw [hc, intervalIntegral.integral_div,
      intervalIntegral.integral_add
        ((by fun_prop : Continuous fun v => Real.cos (2 * (x - a) * v)).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun v => Real.cos (2 * (x + a) * v)).intervalIntegrable _ _),
      integral_cos_two_mul hxm, integral_cos_two_mul hxp]
  rw [hint_eq]
  have h1' : (x ^ 2 - a ^ 2) * ((Real.sin (x - a) / (x - a) + Real.sin (x + a) / (x + a)) / 2)
      = ((x + a) * Real.sin (x - a) + (x - a) * Real.sin (x + a)) / 2 := by
    have hfac : x ^ 2 - a ^ 2 = (x - a) * (x + a) := by ring
    rw [hfac]
    field_simp
  rw [h1', Real.sin_sub, Real.sin_add]
  ring

/-! ## Section 2. Elementary enclosures and the 11-subinterval non-lattice floor -/

private lemma cos_le_quartic {t : ℝ} (ht : 0 ≤ t) :
    Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
  set g : ℝ → ℝ := fun s => 1 - s ^ 2 / 2 + s ^ 4 / 24 - Real.cos s
  have hderiv : ∀ s : ℝ, HasDerivAt g (-s + s ^ 3 / 6 + Real.sin s) s := fun s => by
    have h2 : HasDerivAt (fun u : ℝ => u ^ 2 / 2) ((2 * s ^ 1) / 2) s :=
      (hasDerivAt_pow 2 s).div_const 2
    have h4 : HasDerivAt (fun u : ℝ => u ^ 4 / 24) ((4 * s ^ 3) / 24) s :=
      (hasDerivAt_pow 4 s).div_const 24
    have hc : HasDerivAt Real.cos (-Real.sin s) s := Real.hasDerivAt_cos s
    exact ((((hasDerivAt_const s (1 : ℝ)).sub h2).add h4).sub hc).congr_deriv (by ring)
  have hmono : MonotoneOn g (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by unfold g; fun_prop)
      (fun s _ => (hderiv s).differentiableAt.differentiableWithinAt) ?_
    intro s hs
    rw [interior_Ici] at hs
    rw [(hderiv s).deriv]
    linarith [Real.sin_gt_sub_cube hs]
  have h0 : g 0 ≤ g t := hmono Set.self_mem_Ici ht ht
  simp only [g] at h0
  norm_num at h0
  linarith

private lemma theta_trig_enclosures {lam : ℝ} (hlo : 999 / 1000 ≤ lam) (hhi : lam ≤ 1) :
    3 / 4 ≤ Real.cos (Zeta23.ThmD.theta lam) ∧
    Real.cos (Zeta23.ThmD.theta lam) ≤ 77 / 100 ∧
    9 / 20 ≤ Zeta23.ThmD.theta lam * Real.sin (Zeta23.ThmD.theta lam) ∧
    Zeta23.ThmD.theta lam * Real.sin (Zeta23.ThmD.theta lam) ≤ 47 / 100 := by
  set a := Zeta23.ThmD.theta lam
  have hlam0 : 0 < lam := by linarith
  have ha_pos : 0 < a := Zeta23.ThmD.theta_pos hlam0
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ha_sq_eq : a ^ 2 = lam ^ 2 / 2 := by
    simp only [a, Zeta23.ThmD.theta, div_pow, hs2]
  have ha_sq_lo : 499 / 1000 ≤ a ^ 2 := by
    rw [ha_sq_eq]
    have h1 : (999 / 1000 : ℝ) ^ 2 ≤ lam ^ 2 := pow_le_pow_left₀ (by norm_num) hlo 2
    linarith
  have ha_sq_hi : a ^ 2 ≤ 1 / 2 := Zeta23.ThmD.theta_sq_le hlam0.le hhi
  have ha_4_hi : a ^ 4 ≤ 1 / 4 := by
    have : a ^ 4 = (a ^ 2) ^ 2 := by ring
    rw [this]; nlinarith
  have hc_lo : 3 / 4 ≤ Real.cos a := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := a)]
  have hc_hi : Real.cos a ≤ 77 / 100 := by
    linarith [cos_le_quartic ha_pos.le]
  have hp_lo : 9 / 20 ≤ a * Real.sin a := by
    have hsin := Real.sin_gt_sub_cube ha_pos
    have hmul : a * (a - a ^ 3 / 6) ≤ a * Real.sin a :=
      mul_le_mul_of_nonneg_left hsin.le ha_pos.le
    have hexp : a * (a - a ^ 3 / 6) = a ^ 2 - a ^ 4 / 6 := by ring
    linarith
  have hp_hi : a * Real.sin a ≤ 47 / 100 := by
    have hhalf_pos : 0 ≤ a / 2 := by linarith
    have hsin2 : Real.sin a = 2 * Real.sin (a / 2) * Real.cos (a / 2) := by
      conv_lhs => rw [show a = 2 * (a / 2) by ring]
      exact Real.sin_two_mul (a / 2)
    have hsin_nn : 0 ≤ Real.sin (a / 2) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi hhalf_pos
      have ha1 : a < 1 := by nlinarith
      linarith [Real.pi_gt_three]
    have hcos_nn : 0 ≤ Real.cos (a / 2) := by
      have : 1 - (a / 2) ^ 2 / 2 ≤ Real.cos (a / 2) := Real.one_sub_sq_div_two_le_cos
      nlinarith
    have hsin_ub : Real.sin (a / 2) ≤ a / 2 := Real.sin_le hhalf_pos
    have hcos_ub : Real.cos (a / 2) ≤ 1 - a ^ 2 / 8 + a ^ 4 / 384 := by
      have hq := cos_le_quartic hhalf_pos
      linarith [show (a / 2) ^ 2 / 2 = a ^ 2 / 8 by ring,
        show (a / 2) ^ 4 / 24 = a ^ 4 / 384 by ring]
    have hprod : 2 * a * Real.sin (a / 2) * Real.cos (a / 2)
        ≤ a ^ 2 * (1 - a ^ 2 / 8 + a ^ 4 / 384) := by
      have h1 : 2 * a * Real.sin (a / 2) ≤ a ^ 2 := by nlinarith
      calc 2 * a * Real.sin (a / 2) * Real.cos (a / 2)
          ≤ a ^ 2 * Real.cos (a / 2) := mul_le_mul_of_nonneg_right h1 hcos_nn
        _ ≤ a ^ 2 * (1 - a ^ 2 / 8 + a ^ 4 / 384) :=
            mul_le_mul_of_nonneg_left hcos_ub (sq_nonneg a)
    have heq : a * Real.sin a = 2 * a * Real.sin (a / 2) * Real.cos (a / 2) := by
      rw [hsin2]; ring
    have h6 : a ^ 6 ≤ 1 / 8 := by
      have : a ^ 6 = a ^ 2 * a ^ 4 := by ring
      rw [this]; nlinarith
    have h4_lo : (499 / 1000 : ℝ) ^ 2 ≤ a ^ 4 := by
      have : a ^ 4 = (a ^ 2) ^ 2 := by ring
      rw [this]; exact pow_le_pow_left₀ (by norm_num) ha_sq_lo 2
    rw [heq]
    linarith [show a ^ 2 * (1 - a ^ 2 / 8 + a ^ 4 / 384) = a ^ 2 - a ^ 4 / 8 + a ^ 6 / 384 by ring]
  exact ⟨hc_lo, hc_hi, hp_lo, hp_hi⟩

/-- Subinterval S1 (`Δ ∈ [0, 2/5]`): direct integrand lower bound `mtKernelNum lam Δ ≥ 1/10`. -/
private lemma mtKernelNum_ge_sub1 {lam Δ : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ 2 / 5) :
    1 / 250 ≤ |mtKernelNum lam Δ| := by
  have hle : (-(1 : ℝ) / 2) ≤ 1 / 2 := by norm_num
  have hlow : ∫ _ in (-(1 : ℝ) / 2)..(1 / 2), (1 / 10 : ℝ) ≤ mtKernelNum lam Δ := by
    unfold mtKernelNum
    apply intervalIntegral.integral_mono_on hle intervalIntegrable_const
      ((by unfold Zeta23.ThmD.vStar; fun_prop :
        Continuous fun v => Zeta23.ThmD.vStar lam v * Real.cos (2 * Real.pi * Δ * v)).intervalIntegrable _ _)
    intro v hv
    have hv_lo : 1 / 2 ≤ Zeta23.ThmD.vStar lam v := (vStar_bounds_on_unit h0 h1 hv).1
    have harg_abs : |2 * Real.pi * Δ * v| ≤ 126 / 100 := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos Real.pi_pos, abs_of_nonneg hΔ0]
      have hv_abs : |v| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hv.1], hv.2⟩
      have hpi := Real.pi_lt_d4
      have h1 : 2 * Real.pi * Δ ≤ 2 * 3.1416 * (2 / 5) := by nlinarith
      nlinarith [abs_nonneg v]
    have harg_sq : (2 * Real.pi * Δ * v) ^ 2 ≤ (126 / 100) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) harg_abs 2
    have hcos : 1 / 5 ≤ Real.cos (2 * Real.pi * Δ * v) := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * Δ * v)]
    nlinarith
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlow
  have hpos : 1 / 10 ≤ mtKernelNum lam Δ := by linarith
  exact le_trans (by norm_num : (1 / 250 : ℝ) ≤ 1 / 10) (hpos.trans (le_abs_self _))

/-- Subinterval S2 (`Δ ∈ [2/5, 1/2]`). -/
private lemma kernel_num_floor_S2 {c p Δ : ℝ}
    (hc_lo : 3 / 4 ≤ c) (_hc_hi : c ≤ 77 / 100)
    (_hp_lo : 9 / 20 ≤ p) (hp_hi : p ≤ 47 / 100)
    (hΔ_lo : 2 / 5 ≤ Δ) (hΔ_hi : Δ ≤ 1 / 2) :
    (Real.pi * Δ) ^ 2 / 250
      ≤ |(Real.pi * Δ) * c * Real.sin (Real.pi * Δ) - p * Real.cos (Real.pi * Δ)| := by
  set x := Real.pi * Δ
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have hx_lo : 1256 / 1000 < x := by simp only [x]; nlinarith
  have hx_pi2 : x ≤ Real.pi / 2 := by simp only [x]; nlinarith
  have hx_hi : x < 158 / 100 := by linarith
  have hsin_mono : Real.sin (1256 / 1000) ≤ Real.sin x :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hx_pi2 hx_lo.le
  have hsin_lo : 92 / 100 < Real.sin x := by
    have hcube := Real.sin_gt_sub_cube (show (0 : ℝ) < 1256 / 1000 by norm_num)
    linarith
  have hcos_eq : Real.cos x = Real.sin (Real.pi / 2 - x) := by
    rw [Real.sin_sub, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  have hcos_nn : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hx_pi2⟩
  have hcos_hi : Real.cos x < 315 / 1000 := by
    rw [hcos_eq]
    have hle := Real.sin_le (show 0 ≤ Real.pi / 2 - x by linarith)
    linarith
  have hx_sq : x ^ 2 ≤ (158 / 100) ^ 2 := by nlinarith
  have hxc : (1256 / 1000) * (3 / 4) ≤ x * c := by nlinarith
  have hxcs : (1256 / 1000) * (3 / 4) * (92 / 100) ≤ x * c * Real.sin x :=
    mul_le_mul hxc hsin_lo.le (by norm_num) (by nlinarith)
  have hf_lo : 71 / 100 ≤ x * c * Real.sin x - p * Real.cos x := by nlinarith
  calc x ^ 2 / 250 ≤ 71 / 100 := by linarith
    _ ≤ x * c * Real.sin x - p * Real.cos x := hf_lo
    _ ≤ |x * c * Real.sin x - p * Real.cos x| := le_abs_self _

/-- Subinterval S3 (`Δ ∈ [1/2, 1]`). -/
private lemma kernel_num_floor_S3 {c p Δ : ℝ}
    (hc_lo : 3 / 4 ≤ c) (hp_lo : 9 / 20 ≤ p)
    (hΔ_lo : 1 / 2 ≤ Δ) (hΔ_hi : Δ ≤ 1) :
    (Real.pi * Δ) ^ 2 / 250
      ≤ |(Real.pi * Δ) * c * Real.sin (Real.pi * Δ) - p * Real.cos (Real.pi * Δ)| := by
  set x := Real.pi * Δ
  set t := Real.pi - x
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have ht0 : 0 ≤ t := by simp only [t, x]; nlinarith
  have ht_hi : t ≤ Real.pi / 2 := by simp only [t, x]; nlinarith
  have hx_lo : 157 / 100 < x := by simp only [x]; nlinarith
  have hx_hi : x < 315 / 100 := by simp only [x]; nlinarith
  have hsin_eq : Real.sin x = Real.sin t := by
    have : x = Real.pi - t := by simp only [t]; ring
    rw [this, Real.sin_sub, Real.sin_pi, Real.cos_pi]; ring
  have hcos_eq : Real.cos x = -Real.cos t := by
    have : x = Real.pi - t := by simp only [t]; ring
    rw [this, Real.cos_sub, Real.sin_pi, Real.cos_pi]; ring
  have hsin_nn : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith)
  have hcos_nn : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith, ht_hi⟩
  have hf_eq : x * c * Real.sin x - p * Real.cos x = x * c * Real.sin t + p * Real.cos t := by
    rw [hsin_eq, hcos_eq]; ring
  have hx_sq : x ^ 2 / 250 ≤ 4 / 100 := by nlinarith
  have hf_ge : 4 / 100 ≤ x * c * Real.sin t + p * Real.cos t := by
    rcases le_or_gt t (Real.pi / 4) with ht4 | ht4
    · have ht_sq : t ^ 2 ≤ (79 / 100) ^ 2 := by nlinarith
      have hcos_lo : 68 / 100 ≤ Real.cos t := by
        linarith [Real.one_sub_sq_div_two_le_cos (x := t)]
      have h1 : 0 ≤ x * c * Real.sin t := by positivity
      nlinarith
    · have hsin_lo : 1 / 2 ≤ Real.sin t := by
        have hj := Real.mul_le_sin ht0 ht_hi
        calc (1 / 2 : ℝ) = 2 / Real.pi * (Real.pi / 4) := by field_simp; ring
          _ ≤ 2 / Real.pi * t := mul_le_mul_of_nonneg_left ht4.le (by positivity)
          _ ≤ Real.sin t := hj
      have h2 : 0 ≤ p * Real.cos t := by positivity
      have hxc : (157 / 100) * (3 / 4) ≤ x * c := by nlinarith
      nlinarith
  calc x ^ 2 / 250 ≤ 4 / 100 := hx_sq
    _ ≤ x * c * Real.sin x - p * Real.cos x := by rw [hf_eq]; exact hf_ge
    _ ≤ |x * c * Real.sin x - p * Real.cos x| := le_abs_self _

/-- Subinterval S4 (`Δ ∈ [1, 26/25]`). -/
private lemma kernel_num_floor_S4 {c p Δ : ℝ}
    (hc_lo : 3 / 4 ≤ c) (hc_hi : c ≤ 77 / 100)
    (hp_lo : 9 / 20 ≤ p)
    (hΔ_lo : 1 ≤ Δ) (hΔ_hi : Δ ≤ 26 / 25) :
    (Real.pi * Δ) ^ 2 / 250
      ≤ |(Real.pi * Δ) * c * Real.sin (Real.pi * Δ) - p * Real.cos (Real.pi * Δ)| := by
  set x := Real.pi * Δ
  set t := x - Real.pi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have ht0 : 0 ≤ t := by simp only [t, x]; nlinarith
  have ht_hi : t < 1257 / 10000 := by simp only [t, x]; nlinarith
  have hx0 : 0 < x := by simp only [x]; nlinarith
  have hx_hi : x < 3268 / 1000 := by simp only [x]; nlinarith
  have hsin_eq : Real.sin x = -Real.sin t := by
    have : x = Real.pi + t := by simp only [t]; ring
    rw [this, Real.sin_add, Real.sin_pi, Real.cos_pi]; ring
  have hcos_eq : Real.cos x = -Real.cos t := by
    have : x = Real.pi + t := by simp only [t]; ring
    rw [this, Real.cos_add, Real.sin_pi, Real.cos_pi]; ring
  have hsin_nn : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith)
  have hsin_ub : Real.sin t < 1257 / 10000 := (Real.sin_le ht0).trans_lt ht_hi
  have ht_sq : t ^ 2 ≤ (1257 / 10000) ^ 2 := by nlinarith
  have hcos_lo : 992 / 1000 ≤ Real.cos t := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  have hf_eq : x * c * Real.sin x - p * Real.cos x = p * Real.cos t - x * c * Real.sin t := by
    rw [hsin_eq, hcos_eq]; ring
  have hx_sq : x ^ 2 / 250 ≤ 12 / 100 := by nlinarith
  have hsub_hi : x * c * Real.sin t ≤ (3268 / 1000) * (77 / 100) * (1257 / 10000) := by
    have hxc : x * c ≤ (3268 / 1000) * (77 / 100) := by nlinarith
    exact mul_le_mul hxc hsin_ub.le hsin_nn (by norm_num)
  have hf_lo : 12 / 100 ≤ p * Real.cos t - x * c * Real.sin t := by nlinarith
  calc x ^ 2 / 250 ≤ 12 / 100 := hx_sq
    _ ≤ x * c * Real.sin x - p * Real.cos x := by rw [hf_eq]; exact hf_lo
    _ ≤ |x * c * Real.sin x - p * Real.cos x| := le_abs_self _

/-- Subinterval S5 (`Δ ∈ [43/40, 5/4]`). -/
private lemma kernel_num_floor_S5 {c p Δ : ℝ}
    (hc_lo : 3 / 4 ≤ c)
    (_hp_lo : 9 / 20 ≤ p) (hp_hi : p ≤ 47 / 100)
    (hΔ_lo : 43 / 40 ≤ Δ) (hΔ_hi : Δ ≤ 5 / 4) :
    (Real.pi * Δ) ^ 2 / 250
      ≤ |(Real.pi * Δ) * c * Real.sin (Real.pi * Δ) - p * Real.cos (Real.pi * Δ)| := by
  set x := Real.pi * Δ
  set t := x - Real.pi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have ht_lo : 2356 / 10000 < t := by simp only [t, x]; nlinarith
  have ht_pi2 : t ≤ Real.pi / 2 := by simp only [t, x]; nlinarith
  have hx_lo : 3377 / 1000 < x := by simp only [x]; nlinarith
  have hx_hi : x < 3927 / 1000 := by simp only [x]; nlinarith
  have hsin_eq : Real.sin x = -Real.sin t := by
    have : x = Real.pi + t := by simp only [t]; ring
    rw [this, Real.sin_add, Real.sin_pi, Real.cos_pi]; ring
  have hcos_eq : Real.cos x = -Real.cos t := by
    have : x = Real.pi + t := by simp only [t]; ring
    rw [this, Real.cos_add, Real.sin_pi, Real.cos_pi]; ring
  have hsin_lo : 2334 / 10000 < Real.sin t := by
    have hm := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) ht_pi2 ht_lo.le
    have hc3 := Real.sin_gt_sub_cube (show (0 : ℝ) < 2356 / 10000 by norm_num)
    linarith
  have hcos_nn : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith, ht_pi2⟩
  have hcos_hi : Real.cos t < 973 / 1000 := by
    have hm := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num) (by linarith) ht_lo.le
    have hq := cos_le_quartic (show (0 : ℝ) ≤ 2356 / 10000 by norm_num)
    linarith
  have hf_eq : -(x * c * Real.sin x - p * Real.cos x) = x * c * Real.sin t - p * Real.cos t := by
    rw [hsin_eq, hcos_eq]; ring
  have hx_sq : x ^ 2 / 250 ≤ 13 / 100 := by nlinarith
  have hadd_lo : (3377 / 1000) * (3 / 4) * (2334 / 10000) ≤ x * c * Real.sin t := by
    have hxc : (3377 / 1000) * (3 / 4) ≤ x * c := by nlinarith
    exact mul_le_mul hxc hsin_lo.le (by norm_num) (by nlinarith)
  have hf_lo : 13 / 100 ≤ x * c * Real.sin t - p * Real.cos t := by nlinarith
  calc x ^ 2 / 250 ≤ 13 / 100 := hx_sq
    _ ≤ -(x * c * Real.sin x - p * Real.cos x) := by rw [hf_eq]; exact hf_lo
    _ ≤ |x * c * Real.sin x - p * Real.cos x| := neg_le_abs _

/-- Subinterval S6 (`Δ ∈ [5/4, 3/2]`). -/
private lemma kernel_num_floor_S6 {c p Δ : ℝ}
    (hc_lo : 3 / 4 ≤ c)
    (_hp_lo : 9 / 20 ≤ p) (hp_hi : p ≤ 47 / 100)
    (hΔ_lo : 5 / 4 ≤ Δ) (hΔ_hi : Δ ≤ 3 / 2) :
    (Real.pi * Δ) ^ 2 / 250
      ≤ |(Real.pi * Δ) * c * Real.sin (Real.pi * Δ) - p * Real.cos (Real.pi * Δ)| := by
  set x := Real.pi * Δ
  set t := x - Real.pi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have ht_lo : Real.pi / 4 ≤ t := by simp only [t, x]; nlinarith
  have ht_hi : t ≤ Real.pi / 2 := by simp only [t, x]; nlinarith
  have hx_lo : 392 / 100 < x := by simp only [x]; nlinarith
  have hx_hi : x < 472 / 100 := by simp only [x]; nlinarith
  have hsin_eq : Real.sin x = -Real.sin t := by
    have : x = Real.pi + t := by simp only [t]; ring
    rw [this, Real.sin_add, Real.sin_pi, Real.cos_pi]; ring
  have hcos_eq : Real.cos x = -Real.cos t := by
    have : x = Real.pi + t := by simp only [t]; ring
    rw [this, Real.cos_add, Real.sin_pi, Real.cos_pi]; ring
  have hsin_lo : 1 / 2 ≤ Real.sin t := by
    calc (1 / 2 : ℝ) = 2 / Real.pi * (Real.pi / 4) := by field_simp; ring
      _ ≤ 2 / Real.pi * t := mul_le_mul_of_nonneg_left ht_lo (by positivity)
      _ ≤ Real.sin t := Real.mul_le_sin (by linarith) ht_hi
  have hcos_nn : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith, ht_hi⟩
  have hcos_hi : Real.cos t ≤ 1 := Real.cos_le_one t
  have hf_eq : -(x * c * Real.sin x - p * Real.cos x) = x * c * Real.sin t - p * Real.cos t := by
    rw [hsin_eq, hcos_eq]; ring
  have hx_sq : x ^ 2 / 250 ≤ 1 := by nlinarith
  have hf_lo : 1 ≤ x * c * Real.sin t - p * Real.cos t := by
    have hxc : (392 / 100) * (3 / 4) ≤ x * c := by nlinarith
    have hxcs : (392 / 100) * (3 / 4) * (1 / 2) ≤ x * c * Real.sin t :=
      mul_le_mul hxc hsin_lo (by norm_num) (by nlinarith)
    nlinarith
  calc x ^ 2 / 250 ≤ 1 := hx_sq
    _ ≤ -(x * c * Real.sin x - p * Real.cos x) := by rw [hf_eq]; exact hf_lo
    _ ≤ |x * c * Real.sin x - p * Real.cos x| := neg_le_abs _

/-- Subinterval S7 (`Δ ∈ [3/2, 2]`). -/
private lemma kernel_num_floor_S7 {c p Δ : ℝ}
    (hc_lo : 3 / 4 ≤ c) (hp_lo : 9 / 20 ≤ p)
    (hΔ_lo : 3 / 2 ≤ Δ) (hΔ_hi : Δ ≤ 2) :
    (Real.pi * Δ) ^ 2 / 250
      ≤ |(Real.pi * Δ) * c * Real.sin (Real.pi * Δ) - p * Real.cos (Real.pi * Δ)| := by
  set x := Real.pi * Δ
  set t := 2 * Real.pi - x
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have ht0 : 0 ≤ t := by simp only [t, x]; nlinarith
  have ht_hi : t ≤ Real.pi / 2 := by simp only [t, x]; nlinarith
  have hx_lo : 471 / 100 < x := by simp only [x]; nlinarith
  have hx_hi : x < 629 / 100 := by simp only [x]; nlinarith
  have hsin_eq : Real.sin x = -Real.sin t := by
    have : x = 2 * Real.pi - t := by simp only [t]; ring
    rw [this, Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi]; ring
  have hcos_eq : Real.cos x = Real.cos t := by
    have : x = 2 * Real.pi - t := by simp only [t]; ring
    rw [this, Real.cos_sub, Real.sin_two_pi, Real.cos_two_pi]; ring
  have hsin_nn : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith)
  have hcos_nn : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith, ht_hi⟩
  have hf_eq : -(x * c * Real.sin x - p * Real.cos x) = x * c * Real.sin t + p * Real.cos t := by
    rw [hsin_eq, hcos_eq]; ring
  have hx_sq : x ^ 2 / 250 ≤ 16 / 100 := by nlinarith
  have hf_ge : 16 / 100 ≤ x * c * Real.sin t + p * Real.cos t := by
    rcases le_or_gt t (Real.pi / 4) with ht4 | ht4
    · have ht_sq : t ^ 2 ≤ (79 / 100) ^ 2 := by nlinarith
      have hcos_lo : 68 / 100 ≤ Real.cos t := by
        linarith [Real.one_sub_sq_div_two_le_cos (x := t)]
      have h1 : 0 ≤ x * c * Real.sin t := by positivity
      nlinarith
    · have hsin_lo : 1 / 2 ≤ Real.sin t := by
        calc (1 / 2 : ℝ) = 2 / Real.pi * (Real.pi / 4) := by field_simp; ring
          _ ≤ 2 / Real.pi * t := mul_le_mul_of_nonneg_left ht4.le (by positivity)
          _ ≤ Real.sin t := Real.mul_le_sin ht0 ht_hi
      have h2 : 0 ≤ p * Real.cos t := by positivity
      have hxc : (471 / 100) * (3 / 4) ≤ x * c := by nlinarith
      nlinarith
  calc x ^ 2 / 250 ≤ 16 / 100 := hx_sq
    _ ≤ -(x * c * Real.sin x - p * Real.cos x) := by rw [hf_eq]; exact hf_ge
    _ ≤ |x * c * Real.sin x - p * Real.cos x| := neg_le_abs _

/-- Subinterval S8 (`Δ ∈ [2, 503/250]`). -/
private lemma kernel_num_floor_S8 {c p Δ : ℝ}
    (hc_lo : 3 / 4 ≤ c) (hc_hi : c ≤ 77 / 100)
    (hp_lo : 9 / 20 ≤ p)
    (hΔ_lo : 2 ≤ Δ) (hΔ_hi : Δ ≤ 503 / 250) :
    (Real.pi * Δ) ^ 2 / 250
      ≤ |(Real.pi * Δ) * c * Real.sin (Real.pi * Δ) - p * Real.cos (Real.pi * Δ)| := by
  set x := Real.pi * Δ
  set t := x - 2 * Real.pi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have ht0 : 0 ≤ t := by simp only [t, x]; nlinarith
  have ht_hi : t < 377 / 10000 := by simp only [t, x]; nlinarith
  have hx0 : 0 < x := by simp only [x]; nlinarith
  have hx_hi : x < 6321 / 1000 := by simp only [x]; nlinarith
  have hsin_eq : Real.sin x = Real.sin t := by
    have : x = 2 * Real.pi + t := by simp only [t]; ring
    rw [this, Real.sin_add, Real.sin_two_pi, Real.cos_two_pi]; ring
  have hcos_eq : Real.cos x = Real.cos t := by
    have : x = 2 * Real.pi + t := by simp only [t]; ring
    rw [this, Real.cos_add, Real.sin_two_pi, Real.cos_two_pi]; ring
  have hsin_nn : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith)
  have hsin_ub : Real.sin t < 377 / 10000 := (Real.sin_le ht0).trans_lt ht_hi
  have ht_sq : t ^ 2 ≤ (377 / 10000) ^ 2 := by nlinarith
  have hcos_lo : 9992 / 10000 ≤ Real.cos t := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  have hf_eq : -(x * c * Real.sin x - p * Real.cos x) = p * Real.cos t - x * c * Real.sin t := by
    rw [hsin_eq, hcos_eq]; ring
  have hx_sq : x ^ 2 / 250 ≤ 26 / 100 := by nlinarith
  have hsub_hi : x * c * Real.sin t ≤ (6321 / 1000) * (77 / 100) * (377 / 10000) := by
    have hxc : x * c ≤ (6321 / 1000) * (77 / 100) := by nlinarith
    exact mul_le_mul hxc hsin_ub.le hsin_nn (by norm_num)
  have hf_lo : 26 / 100 ≤ p * Real.cos t - x * c * Real.sin t := by nlinarith
  calc x ^ 2 / 250 ≤ 26 / 100 := hx_sq
    _ ≤ -(x * c * Real.sin x - p * Real.cos x) := by rw [hf_eq]; exact hf_lo
    _ ≤ |x * c * Real.sin x - p * Real.cos x| := neg_le_abs _

/-- Subinterval S9 (`Δ ∈ [256/125, 43/20]`). -/
private lemma kernel_num_floor_S9 {c p Δ : ℝ}
    (hc_lo : 3 / 4 ≤ c)
    (_hp_lo : 9 / 20 ≤ p) (hp_hi : p ≤ 47 / 100)
    (hΔ_lo : 256 / 125 ≤ Δ) (hΔ_hi : Δ ≤ 43 / 20) :
    (Real.pi * Δ) ^ 2 / 250
      ≤ |(Real.pi * Δ) * c * Real.sin (Real.pi * Δ) - p * Real.cos (Real.pi * Δ)| := by
  set x := Real.pi * Δ
  set t := x - 2 * Real.pi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have ht_lo : 1507 / 10000 < t := by simp only [t, x]; nlinarith
  have ht_pi2 : t ≤ Real.pi / 2 := by simp only [t, x]; nlinarith
  have hx_lo : 6433 / 1000 < x := by simp only [x]; nlinarith
  have hx_hi : x < 6755 / 1000 := by simp only [x]; nlinarith
  have hsin_eq : Real.sin x = Real.sin t := by
    have : x = 2 * Real.pi + t := by simp only [t]; ring
    rw [this, Real.sin_add, Real.sin_two_pi, Real.cos_two_pi]; ring
  have hcos_eq : Real.cos x = Real.cos t := by
    have : x = 2 * Real.pi + t := by simp only [t]; ring
    rw [this, Real.cos_add, Real.sin_two_pi, Real.cos_two_pi]; ring
  have hsin_lo : 1501 / 10000 < Real.sin t := by
    have hm := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) ht_pi2 ht_lo.le
    have hc3 := Real.sin_gt_sub_cube (show (0 : ℝ) < 1507 / 10000 by norm_num)
    linarith
  have hcos_nn : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith, ht_pi2⟩
  have hcos_hi : Real.cos t < 9887 / 10000 := by
    have hm := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num) (by linarith) ht_lo.le
    have hq := cos_le_quartic (show (0 : ℝ) ≤ 1507 / 10000 by norm_num)
    linarith
  have hf_eq : x * c * Real.sin x - p * Real.cos x = x * c * Real.sin t - p * Real.cos t := by
    rw [hsin_eq, hcos_eq]
  have hx_sq : x ^ 2 / 250 ≤ 25 / 100 := by nlinarith
  have hadd_lo : (6433 / 1000) * (3 / 4) * (1501 / 10000) ≤ x * c * Real.sin t := by
    have hxc : (6433 / 1000) * (3 / 4) ≤ x * c := by nlinarith
    exact mul_le_mul hxc hsin_lo.le (by norm_num) (by nlinarith)
  have hf_lo : 25 / 100 ≤ x * c * Real.sin t - p * Real.cos t := by nlinarith
  calc x ^ 2 / 250 ≤ 25 / 100 := hx_sq
    _ ≤ x * c * Real.sin x - p * Real.cos x := by rw [hf_eq]; exact hf_lo
    _ ≤ |x * c * Real.sin x - p * Real.cos x| := le_abs_self _

/-- Subinterval S10 (`Δ ∈ [43/20, 5/2]`). -/
private lemma kernel_num_floor_S10 {c p Δ : ℝ}
    (hc_lo : 3 / 4 ≤ c)
    (_hp_lo : 9 / 20 ≤ p) (hp_hi : p ≤ 47 / 100)
    (hΔ_lo : 43 / 20 ≤ Δ) (hΔ_hi : Δ ≤ 5 / 2) :
    (Real.pi * Δ) ^ 2 / 250
      ≤ |(Real.pi * Δ) * c * Real.sin (Real.pi * Δ) - p * Real.cos (Real.pi * Δ)| := by
  set x := Real.pi * Δ
  set t := x - 2 * Real.pi
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have ht_lo : 3 / 20 * Real.pi ≤ t := by simp only [t, x]; nlinarith
  have ht_hi : t ≤ Real.pi / 2 := by simp only [t, x]; nlinarith
  have hx_lo : 675 / 100 < x := by simp only [x]; nlinarith
  have hx_hi : x < 786 / 100 := by simp only [x]; nlinarith
  have hsin_eq : Real.sin x = Real.sin t := by
    have : x = 2 * Real.pi + t := by simp only [t]; ring
    rw [this, Real.sin_add, Real.sin_two_pi, Real.cos_two_pi]; ring
  have hcos_eq : Real.cos x = Real.cos t := by
    have : x = 2 * Real.pi + t := by simp only [t]; ring
    rw [this, Real.cos_add, Real.sin_two_pi, Real.cos_two_pi]; ring
  have hsin_lo : 3 / 10 ≤ Real.sin t := by
    calc (3 / 10 : ℝ) = 2 / Real.pi * (3 / 20 * Real.pi) := by field_simp; ring
      _ ≤ 2 / Real.pi * t := mul_le_mul_of_nonneg_left ht_lo (by positivity)
      _ ≤ Real.sin t := Real.mul_le_sin (by linarith) ht_hi
  have hcos_nn : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith, ht_hi⟩
  have hcos_hi : Real.cos t ≤ 1 := Real.cos_le_one t
  have hf_eq : x * c * Real.sin x - p * Real.cos x = x * c * Real.sin t - p * Real.cos t := by
    rw [hsin_eq, hcos_eq]
  have hx_sq : x ^ 2 / 250 ≤ 1 := by nlinarith
  have hf_lo : 1 ≤ x * c * Real.sin t - p * Real.cos t := by
    have hxc : (675 / 100) * (3 / 4) ≤ x * c := by nlinarith
    have hxcs : (675 / 100) * (3 / 4) * (3 / 10) ≤ x * c * Real.sin t :=
      mul_le_mul hxc hsin_lo (by norm_num) (by nlinarith)
    nlinarith
  calc x ^ 2 / 250 ≤ 1 := hx_sq
    _ ≤ x * c * Real.sin x - p * Real.cos x := by rw [hf_eq]; exact hf_lo
    _ ≤ |x * c * Real.sin x - p * Real.cos x| := le_abs_self _

/-- Subinterval S11 (`Δ ∈ [5/2, 3]`). -/
private lemma kernel_num_floor_S11 {c p Δ : ℝ}
    (hc_lo : 3 / 4 ≤ c) (hp_lo : 9 / 20 ≤ p)
    (hΔ_lo : 5 / 2 ≤ Δ) (hΔ_hi : Δ ≤ 3) :
    (Real.pi * Δ) ^ 2 / 250
      ≤ |(Real.pi * Δ) * c * Real.sin (Real.pi * Δ) - p * Real.cos (Real.pi * Δ)| := by
  set x := Real.pi * Δ
  set t := 3 * Real.pi - x
  have hpi_lo := Real.pi_gt_d4
  have hpi_hi := Real.pi_lt_d4
  have ht0 : 0 ≤ t := by simp only [t, x]; nlinarith
  have ht_hi : t ≤ Real.pi / 2 := by simp only [t, x]; nlinarith
  have hx_lo : 785 / 100 < x := by simp only [x]; nlinarith
  have hx_hi : x < 9425 / 1000 := by simp only [x]; nlinarith
  have hsin_eq : Real.sin x = Real.sin t := by
    have : x = 2 * Real.pi + (Real.pi - t) := by simp only [t]; ring
    rw [this, Real.sin_add, Real.sin_two_pi, Real.cos_two_pi, Real.sin_sub, Real.sin_pi,
      Real.cos_pi]; ring
  have hcos_eq : Real.cos x = -Real.cos t := by
    have : x = 2 * Real.pi + (Real.pi - t) := by simp only [t]; ring
    rw [this, Real.cos_add, Real.sin_two_pi, Real.cos_two_pi, Real.cos_sub, Real.sin_pi,
      Real.cos_pi]; ring
  have hsin_nn : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith)
  have hcos_nn : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith, ht_hi⟩
  have hf_eq : x * c * Real.sin x - p * Real.cos x = x * c * Real.sin t + p * Real.cos t := by
    rw [hsin_eq, hcos_eq]; ring
  have hx_sq : x ^ 2 / 250 ≤ 36 / 100 := by nlinarith
  have hf_ge : 36 / 100 ≤ x * c * Real.sin t + p * Real.cos t := by
    rcases le_or_gt t (1 / 5) with ht5 | ht5
    · have ht_sq : t ^ 2 ≤ (1 / 5) ^ 2 := by nlinarith
      have hcos_lo : 49 / 50 ≤ Real.cos t := by
        linarith [Real.one_sub_sq_div_two_le_cos (x := t)]
      have h1 : 0 ≤ x * c * Real.sin t := by positivity
      nlinarith
    · have hsin_lo : 127 / 1000 ≤ Real.sin t := by
        have hj := Real.mul_le_sin ht0 ht_hi
        have h2pi : 127 / 200 ≤ 2 / Real.pi := by
          rw [le_div_iff₀ Real.pi_pos]
          linarith
        calc (127 / 1000 : ℝ) = (127 / 200) * (1 / 5) := by norm_num
          _ ≤ (2 / Real.pi) * t := mul_le_mul h2pi ht5.le (by norm_num) (by positivity)
          _ ≤ Real.sin t := hj
      have h2 : 0 ≤ p * Real.cos t := by positivity
      have hxc : (785 / 100) * (3 / 4) ≤ x * c := by nlinarith
      have hxcs : (785 / 100) * (3 / 4) * (127 / 1000) ≤ x * c * Real.sin t :=
        mul_le_mul hxc hsin_lo (by norm_num) (by nlinarith)
      nlinarith
  calc x ^ 2 / 250 ≤ 36 / 100 := hx_sq
    _ ≤ x * c * Real.sin x - p * Real.cos x := by rw [hf_eq]; exact hf_ge
    _ ≤ |x * c * Real.sin x - p * Real.cos x| := le_abs_self _

/-- **Pointwise non-lattice floor of `mtKernel`.**
For `λ ∈ [999/1000, 1]` and `Δ ∈ [0, 3] \ (mtExcl₁ ∪ mtExcl₂)`, `1 / 250 ≤ |mtKernel lam Δ|`. -/
theorem one_div_250_le_abs_mtKernel {lam Δ : ℝ}
    (hlo : 999 / 1000 ≤ lam) (hhi : lam ≤ 1)
    (hΔ0 : 0 ≤ Δ) (hΔ3 : Δ ≤ 3)
    (hn1 : Δ ∉ mtExcl₁) (hn2 : Δ ∉ mtExcl₂) :
    1 / 250 ≤ |mtKernel lam Δ| := by
  have hlam0 : 0 ≤ lam := by linarith
  refine le_trans ?_ (abs_mtKernelNum_le_abs_mtKernel hlam0 hhi Δ)
  rcases le_or_gt Δ (2 / 5) with hS1 | hge
  · exact mtKernelNum_ge_sub1 hlam0 hhi hΔ0 hS1
  · obtain ⟨hc_lo, hc_hi, hp_lo, hp_hi⟩ := theta_trig_enclosures hlo hhi
    have hclosed := mtKernelNum_closed_form hlam0 hhi hge.le
    set a := Zeta23.ThmD.theta lam
    set x := Real.pi * Δ
    have ha_sq : a ^ 2 ≤ 1 / 2 := Zeta23.ThmD.theta_sq_le hlam0 hhi
    have hx_gt : 6 / 5 < x := by simp only [x]; nlinarith [Real.pi_gt_three]
    have hxa_pos : 0 < x ^ 2 - a ^ 2 := by nlinarith
    have hxa_le : x ^ 2 - a ^ 2 ≤ x ^ 2 := by nlinarith [sq_nonneg a]
    have hnum_floor : x ^ 2 / 250
        ≤ |x * Real.cos a * Real.sin x - (a * Real.sin a) * Real.cos x| := by
      rw [mtExcl₁, Set.mem_Ioo, not_and_or, not_lt, not_lt] at hn1
      rw [mtExcl₂, Set.mem_Ioo, not_and_or, not_lt, not_lt] at hn2
      rcases le_or_gt Δ (1 / 2) with h2 | h2
      · exact kernel_num_floor_S2 hc_lo hc_hi hp_lo hp_hi hge.le h2
      rcases le_or_gt Δ 1 with h3 | h3
      · exact kernel_num_floor_S3 hc_lo hp_lo h2.le h3
      rcases hn1 with h4 | h4'
      · exact kernel_num_floor_S4 hc_lo hc_hi hp_lo h3.le h4
      rcases le_or_gt Δ (5 / 4) with h5 | h5
      · exact kernel_num_floor_S5 hc_lo hp_lo hp_hi h4' h5
      rcases le_or_gt Δ (3 / 2) with h6 | h6
      · exact kernel_num_floor_S6 hc_lo hp_lo hp_hi h5.le h6
      rcases le_or_gt Δ 2 with h7 | h7
      · exact kernel_num_floor_S7 hc_lo hp_lo h6.le h7
      rcases hn2 with h8 | h8'
      · exact kernel_num_floor_S8 hc_lo hc_hi hp_lo h7.le h8
      rcases le_or_gt Δ (43 / 20) with h9 | h9
      · exact kernel_num_floor_S9 hc_lo hp_lo hp_hi h8' h9
      rcases le_or_gt Δ (5 / 2) with h10 | h10
      · exact kernel_num_floor_S10 hc_lo hp_lo hp_hi h9.le h10
      · exact kernel_num_floor_S11 hc_lo hp_lo h10.le hΔ3
    have habs_closed : (x ^ 2 - a ^ 2) * |mtKernelNum lam Δ|
        = |x * Real.cos a * Real.sin x - (a * Real.sin a) * Real.cos x| := by
      calc (x ^ 2 - a ^ 2) * |mtKernelNum lam Δ|
          = |(x ^ 2 - a ^ 2) * mtKernelNum lam Δ| := by
            rw [abs_mul, abs_of_pos hxa_pos]
        _ = _ := by rw [hclosed]
    have hmul_le : (x ^ 2 - a ^ 2) * (1 / 250) ≤ (x ^ 2 - a ^ 2) * |mtKernelNum lam Δ| := by
      calc (x ^ 2 - a ^ 2) * (1 / 250) ≤ x ^ 2 / 250 := by linarith
        _ ≤ |x * Real.cos a * Real.sin x - (a * Real.sin a) * Real.cos x| := hnum_floor
        _ = (x ^ 2 - a ^ 2) * |mtKernelNum lam Δ| := habs_closed.symm
    exact le_of_mul_le_mul_left hmul_le hxa_pos

/-- **Triple sumset disjointness.**
For any ordered triple `γ₁ < γ₂ < γ₃` and scale `α > 0` with `α (γ₃ − γ₁) ≤ 3`, at least one of the
three pairs in `{γ₁, γ₂, γ₃}` has `1 / 250 ≤ |mtKernel lam (α * (v - u))|`. -/
theorem exists_pair_mtKernel_ge_of_triple {lam α γ₁ γ₂ γ₃ : ℝ}
    (hlo : 999 / 1000 ≤ lam) (hhi : lam ≤ 1)
    (hα : 0 < α) (h12 : γ₁ < γ₂) (h23 : γ₂ < γ₃)
    (hspan : α * (γ₃ - γ₁) ≤ 3) :
    ∃ u v : ℝ, u ∈ ({γ₁, γ₂, γ₃} : Set ℝ) ∧ v ∈ ({γ₁, γ₂, γ₃} : Set ℝ) ∧ u ≠ v ∧
      1 / 250 ≤ |mtKernel lam (α * (v - u))| := by
  set Δ₁ := α * (γ₂ - γ₁)
  set Δ₂ := α * (γ₃ - γ₂)
  have hΔ₁_pos : 0 < Δ₁ := mul_pos hα (sub_pos.mpr h12)
  have hΔ₂_pos : 0 < Δ₂ := mul_pos hα (sub_pos.mpr h23)
  have hsum_eq : Δ₁ + Δ₂ = α * (γ₃ - γ₁) := by simp only [Δ₁, Δ₂]; ring
  have hΔ₁_le : Δ₁ ≤ 3 := by linarith
  have hΔ₂_le : Δ₂ ≤ 3 := by linarith
  by_cases h1 : Δ₁ ∉ mtExcl₁ ∧ Δ₁ ∉ mtExcl₂
  · refine ⟨γ₁, γ₂, by simp, by simp, h12.ne, ?_⟩
    exact one_div_250_le_abs_mtKernel hlo hhi hΔ₁_pos.le hΔ₁_le h1.1 h1.2
  · by_cases h2 : Δ₂ ∉ mtExcl₁ ∧ Δ₂ ∉ mtExcl₂
    · refine ⟨γ₂, γ₃, by simp, by simp, h23.ne, ?_⟩
      exact one_div_250_le_abs_mtKernel hlo hhi hΔ₂_pos.le hΔ₂_le h2.1 h2.2
    · -- Both `Δ₁` and `Δ₂` lie in `mtExcl₁ ∪ mtExcl₂`; their sum `Δ₁ + Δ₂` cannot!
      have h1_mem : Δ₁ ∈ mtExcl₁ ∨ Δ₁ ∈ mtExcl₂ := by tauto
      have h2_mem : Δ₂ ∈ mtExcl₁ ∨ Δ₂ ∈ mtExcl₂ := by tauto
      have h12_not1 : Δ₁ + Δ₂ ∉ mtExcl₁ := by
        intro hm
        rw [mtExcl₁, Set.mem_Ioo] at hm
        rcases h1_mem with h1a | h1b <;> rcases h2_mem with h2a | h2b
        · rw [mtExcl₁, Set.mem_Ioo] at h1a h2a; linarith
        · rw [mtExcl₁, Set.mem_Ioo] at h1a; rw [mtExcl₂, Set.mem_Ioo] at h2b; linarith
        · rw [mtExcl₂, Set.mem_Ioo] at h1b; rw [mtExcl₁, Set.mem_Ioo] at h2a; linarith
        · rw [mtExcl₂, Set.mem_Ioo] at h1b h2b; linarith
      have h12_not2 : Δ₁ + Δ₂ ∉ mtExcl₂ := by
        intro hm
        rw [mtExcl₂, Set.mem_Ioo] at hm
        rcases h1_mem with h1a | h1b <;> rcases h2_mem with h2a | h2b
        · rw [mtExcl₁, Set.mem_Ioo] at h1a h2a; linarith
        · rw [mtExcl₁, Set.mem_Ioo] at h1a; rw [mtExcl₂, Set.mem_Ioo] at h2b; linarith
        · rw [mtExcl₂, Set.mem_Ioo] at h1b; rw [mtExcl₁, Set.mem_Ioo] at h2a; linarith
        · rw [mtExcl₂, Set.mem_Ioo] at h1b h2b; linarith
      refine ⟨γ₁, γ₃, by simp, by simp, (h12.trans h23).ne, ?_⟩
      rw [← hsum_eq]
      exact one_div_250_le_abs_mtKernel hlo hhi (by linarith) (by linarith) h12_not1 h12_not2

/-! ## Section 3. Uniform bulk finite-grid overlap approximation -/

private lemma admWindow_deriv_eq_zero {φ : ℝ → ℝ} {L w c : ℝ}
    (hW : Zeta23.AdmWindow φ L w c) {u : ℝ} (hu : L / 2 ≤ |u|) :
    deriv φ u = 0 := by
  have hmin : IsLocalMin φ u :=
    Filter.Eventually.of_forall fun x => by rw [hW.support u hu]; exact hW.nonneg x
  exact hmin.deriv_eq_zero

private lemma admWindow_abs_deriv_le {φ : ℝ → ℝ} {L w c : ℝ}
    (hW : Zeta23.AdmWindow φ L w c) (u : ℝ) :
    |deriv φ u| ≤ c / w := by
  rcases le_or_gt (L / 2) |u| with hu | hu
  · rw [admWindow_deriv_eq_zero hW hu, abs_zero]
    exact div_nonneg hW.c_nonneg hW.w_pos.le
  · have habs := abs_lt.mp hu
    have hle : -(L / 2) ≤ u := by linarith
    have hd1 : ContDiff ℝ 1 (deriv φ) := hW.contDiff.deriv'
    have hdiff : ∀ x, DifferentiableAt ℝ (deriv φ) x := fun x =>
      hd1.differentiable one_ne_zero x
    have hcont2 : Continuous (deriv (deriv φ)) := hd1.continuous_deriv le_rfl
    have hcs2 : HasCompactSupport (deriv (deriv φ)) := by
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -(L / 2)) (b := L / 2)) ?_
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hmem
      apply hx
      have hopen : IsOpen {y : ℝ | L / 2 < |y|} := continuous_abs.isOpen_preimage _ isOpen_Ioi
      have hgt : L / 2 < |x| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
        rcases hmem with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have heq : deriv φ =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [hopen.mem_nhds hgt] with y hy
        exact admWindow_deriv_eq_zero hW hy.le
      rw [heq.deriv_eq, deriv_const]
    have hint2 : Integrable (fun t => |deriv (deriv φ) t|) :=
      (hcont2.integrable_of_hasCompactSupport hcs2).abs
    have hzero : deriv φ (-(L / 2)) = 0 :=
      admWindow_deriv_eq_zero hW (by rw [abs_neg, abs_of_pos (by linarith [hW.L_pos])])
    have hftc : ∫ t in (-(L / 2))..u, deriv (deriv φ) t = deriv φ u - deriv φ (-(L / 2)) :=
      intervalIntegral.integral_deriv_eq_sub (fun x _ => hdiff x)
        (hcont2.intervalIntegrable _ _)
    rw [hzero, sub_zero] at hftc
    rw [← hftc, intervalIntegral.integral_of_le hle]
    calc |∫ t in Set.Ioc (-(L / 2)) u, deriv (deriv φ) t|
        ≤ ∫ t in Set.Ioc (-(L / 2)) u, |deriv (deriv φ) t| := abs_integral_le_integral_abs
      _ ≤ ∫ t, |deriv (deriv φ) t| :=
          setIntegral_le_integral hint2 (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      _ ≤ c / w := hW.l1_deriv2

private lemma admWindow_grid_tail_sq_le {φ : ℝ → ℝ} {L w c : ℝ}
    (hW : Zeta23.AdmWindow φ L w c) {T γ : ℝ} (hT : 0 < T)
    (t : Finset ℤ)
    (hfar : ∀ k ∈ t, (T / 4) ≤ (γ - (T + k * (2 * Real.pi / L))) ^ 2) :
    ∑ k ∈ t, (Zeta23.AdmWindow.vHatR φ (γ - (T + k * (2 * Real.pi / L)))) ^ 2
      ≤ 4 * L ^ 2 * (c / w) ^ 2 / T := by
  set f : ℝ → ℂ := fun u => Complex.ofReal (φ u)
  set ψ : ℝ → ℂ := fun u => Complex.ofReal (deriv φ u)
  have hf_cd1 : ContDiff ℝ 1 f := hW.vC_contDiff.of_le (by norm_num)
  have hderiv_f : deriv f = ψ := by
    funext u
    exact (((hW.contDiff.differentiable (by norm_num) u).hasDerivAt).ofReal_comp).deriv
  have hψ_cont : Continuous ψ :=
    Complex.continuous_ofReal.comp (hW.contDiff.continuous_deriv (by norm_num))
  have hψ_supp : ∀ u, L / 2 ≤ |u| → ψ u = 0 := fun u hu => by
    simp only [ψ, admWindow_deriv_eq_zero hW hu, Complex.ofReal_zero]
  have hparseval := RHTower.sum_norm_sq_paperFT_grid_le hW.L_pos hψ_cont hψ_supp γ T t
  have hpt : ∀ k ∈ t,
      (T / 4) * (Zeta23.AdmWindow.vHatR φ (γ - (T + k * (2 * Real.pi / L)))) ^ 2
        ≤ ‖Zeta23.paperFT ψ ((γ - (T + k * (2 * Real.pi / L)) : ℝ) : ℂ)‖ ^ 2 := by
    intro k hk
    set r : ℝ := γ - (T + k * (2 * Real.pi / L))
    have hft := Zeta23.paperFT_deriv hf_cd1 hW.vC_hasCompactSupport (r : ℂ)
    rw [hderiv_f] at hft
    have hnorm : ‖Zeta23.paperFT ψ (r : ℂ)‖ ^ 2 = r ^ 2 * ‖Zeta23.paperFT f (r : ℂ)‖ ^ 2 := by
      rw [hft, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, mul_pow, sq_abs]
    have hvhat : (Zeta23.AdmWindow.vHatR φ r) ^ 2 ≤ ‖Zeta23.paperFT f (r : ℂ)‖ ^ 2 := by
      have := Complex.abs_re_le_norm (Zeta23.paperFT f (r : ℂ))
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    rw [hnorm]
    calc (T / 4) * (Zeta23.AdmWindow.vHatR φ r) ^ 2
        ≤ r ^ 2 * (Zeta23.AdmWindow.vHatR φ r) ^ 2 :=
          mul_le_mul_of_nonneg_right (hfar k hk) (sq_nonneg _)
      _ ≤ r ^ 2 * ‖Zeta23.paperFT f (r : ℂ)‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hvhat (sq_nonneg _)
  have hint_le : ∫ u in (-(L / 2))..(L / 2), ‖ψ u‖ ^ 2 ≤ L * (c / w) ^ 2 := by
    have hle : -(L / 2) ≤ L / 2 := by linarith [hW.L_pos]
    have hmono : ∫ u in (-(L / 2))..(L / 2), ‖ψ u‖ ^ 2
        ≤ ∫ _ in (-(L / 2))..(L / 2), (c / w) ^ 2 := by
      apply intervalIntegral.integral_mono_on hle
        ((hψ_cont.norm.pow 2).intervalIntegrable _ _) intervalIntegrable_const
      intro u _
      simp only [ψ, Complex.norm_real, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (admWindow_abs_deriv_le hW u) 2
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    linarith
  have hsum_le : (T / 4) * ∑ k ∈ t,
      (Zeta23.AdmWindow.vHatR φ (γ - (T + k * (2 * Real.pi / L)))) ^ 2
      ≤ L ^ 2 * (c / w) ^ 2 := by
    rw [Finset.mul_sum]
    calc ∑ k ∈ t, (T / 4) * (Zeta23.AdmWindow.vHatR φ (γ - (T + k * (2 * Real.pi / L)))) ^ 2
        ≤ ∑ k ∈ t, ‖Zeta23.paperFT ψ ((γ - (T + k * (2 * Real.pi / L)) : ℝ) : ℂ)‖ ^ 2 :=
          Finset.sum_le_sum hpt
      _ ≤ L * ∫ u in (-(L / 2))..(L / 2), ‖ψ u‖ ^ 2 := hparseval
      _ ≤ L * (L * (c / w) ^ 2) := mul_le_mul_of_nonneg_left hint_le hW.L_pos.le
      _ = L ^ 2 * (c / w) ^ 2 := by ring
  rw [le_div_iff₀ hT]
  linarith

private lemma VPhiR_phiD_close {ϱ : ℝ → ℝ} (hϱ : Zeta23.TaperProfile ϱ)
    {lam L w : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) (r : ℝ) :
    |L⁻¹ * Zeta23.AdmWindow.VPhiR (Zeta23.ThmD.phiD ϱ lam L w) r
      - mtKernelNum lam (L / (2 * Real.pi) * r)| ≤ 2 * w / L := by
  have hL : 0 < L := by linarith
  have hw0 : 0 < w := by linarith
  have hwL2 : 2 * w ≤ L := by linarith
  set φ := Zeta23.ThmD.phiD ϱ lam L w
  have hW := Zeta23.ThmD.admWindow_phiD hϱ h0 h1 hw hwL
  -- Express `VPhiR φ r` as `∫ u, φ u ^ 2 * cos (r * u)`
  have hVPhiR : Zeta23.AdmWindow.VPhiR φ r = ∫ u : ℝ, φ u ^ 2 * Real.cos (r * u) := by
    unfold Zeta23.AdmWindow.VPhiR Zeta23.AdmWindow.VPhi Zeta23.paperFT
    have hint_c : Integrable (fun u : ℝ => ((φ u ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) :=
      (hW.vSqC_continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
        (hW.vSqC_hasCompactSupport.mul_right)
    rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hint_c]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Complex.reCLM_apply]
    rw [show Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  -- Express `mtKernelNum` as `L⁻¹ * ∫ u, sharpW lam L u * cos (r * u)`
  have hsharp : mtKernelNum lam (L / (2 * Real.pi) * r)
      = L⁻¹ * ∫ u : ℝ, Zeta23.ThmD.sharpW lam L u * Real.cos (r * u) := by
    have hind : (fun u : ℝ => Zeta23.ThmD.sharpW lam L u * Real.cos (r * u))
        = (Set.Icc (-(L / 2)) (L / 2)).indicator
            (fun u => Zeta23.ThmD.vStar lam (u / L) * Real.cos (r * u)) := by
      funext u
      unfold Zeta23.ThmD.sharpW
      by_cases hu : u ∈ Set.Icc (-(L / 2)) (L / 2)
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul]
    rw [hind, MeasureTheory.integral_indicator measurableSet_Icc,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -(L / 2) ≤ L / 2)]
    have hcomp := intervalIntegral.integral_comp_div
      (f := fun v => Zeta23.ThmD.vStar lam v * Real.cos (r * L * v))
      (a := -(L / 2)) (b := L / 2) hL.ne'
    have hcongr : ∫ x in (-(L / 2))..(L / 2), Zeta23.ThmD.vStar lam (x / L) * Real.cos (r * x)
        = ∫ x in (-(L / 2))..(L / 2), Zeta23.ThmD.vStar lam (x / L) * Real.cos (r * L * (x / L)) :=
      intervalIntegral.integral_congr fun x _ => by
        congr 2; field_simp
    rw [hcongr, hcomp, smul_eq_mul,
      show -(L / 2) / L = -(1 : ℝ) / 2 by field_simp,
      show (L / 2) / L = (1 : ℝ) / 2 by field_simp,
      ← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul]
    unfold mtKernelNum
    refine intervalIntegral.integral_congr fun v _ => ?_
    congr 2
    field_simp
  rw [hVPhiR, hsharp, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hL)]
  have hint_φ : Integrable (fun u : ℝ => φ u ^ 2 * Real.cos (r * u)) :=
    (hW.sq_continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hW.sq_hasCompactSupport.mul_right)
  have hint_k : Integrable (fun u : ℝ => Zeta23.ThmD.sharpW lam L u * Real.cos (r * u)) := by
    have hk : Integrable (Zeta23.ThmD.sharpW lam L) := by
      unfold Zeta23.ThmD.sharpW
      exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
        (((by unfold Zeta23.ThmD.vStar; fun_prop :
          Continuous fun u : ℝ => Zeta23.ThmD.vStar lam (u / L)).continuousOn).integrableOn_compact
          isCompact_Icc)
    exact (hk.bdd_mul (c := 1) (by fun_prop : Continuous fun u => Real.cos (r * u)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)).congr
      (Filter.Eventually.of_forall fun u => mul_comm _ _)
  have hint_diff : Integrable (fun u : ℝ => |φ u ^ 2 - Zeta23.ThmD.sharpW lam L u|) := by
    have hk : Integrable (Zeta23.ThmD.sharpW lam L) := by
      unfold Zeta23.ThmD.sharpW
      exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
        (((by unfold Zeta23.ThmD.vStar; fun_prop :
          Continuous fun u : ℝ => Zeta23.ThmD.vStar lam (u / L)).continuousOn).integrableOn_compact
          isCompact_Icc)
    exact ((hW.integrable_pow two_pos).sub hk).abs
  rw [← MeasureTheory.integral_sub hint_φ hint_k]
  have hdiff_le : |(∫ u : ℝ, (φ u ^ 2 * Real.cos (r * u) - Zeta23.ThmD.sharpW lam L u * Real.cos (r * u)))|
      ≤ 2 * w := by
    calc |(∫ u : ℝ, (φ u ^ 2 * Real.cos (r * u) - Zeta23.ThmD.sharpW lam L u * Real.cos (r * u)))|
        ≤ ∫ u : ℝ, |φ u ^ 2 * Real.cos (r * u) - Zeta23.ThmD.sharpW lam L u * Real.cos (r * u)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ u : ℝ, |φ u ^ 2 - Zeta23.ThmD.sharpW lam L u| := by
          apply MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun _ => abs_nonneg _) hint_diff
            (Filter.Eventually.of_forall fun u => ?_)
          dsimp only
          rw [← sub_mul, abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
      _ ≤ 2 * w := Zeta23.ThmD.integral_abs_phiDsq_sub_sharp hϱ h0 h1 hw0 hwL2
  rw [div_eq_mul_inv, mul_comm (2 * w)]
  exact mul_le_mul_of_nonneg_left hdiff_le (inv_nonneg.mpr hL.le)

/-- **Uniform bulk finite-grid overlap approximation.**
Eventually in `T`, for every pair `x, y ∈ ZI Z T` with bulk ordinates in `[T + √T, 2T − √T]`,
`pairGridOverlap Z (P.atD T) T x y` is within `1 / 500` of
`mtKernel P.lam (P.L T / (2 * π) * |(x : ℂ).im - (y : ℂ).im|)`. -/
theorem eventually_pairGridOverlap_atD_close (Z : Zeta23.ZeroConfig)
    {P : Zeta23.Params} (hP : P.Valid) :
    ∀ᶠ T in atTop, ∀ x y : Zeta23.ZeroSide.ZI Z T,
      T + Real.sqrt T ≤ (x : ℂ).im → (x : ℂ).im ≤ 2 * T - Real.sqrt T →
      T + Real.sqrt T ≤ (y : ℂ).im → (y : ℂ).im ≤ 2 * T - Real.sqrt T →
      |pairGridOverlap Z (P.atD T) T x y
        - mtKernel P.lam (P.L T / (2 * Real.pi) * |(x : ℂ).im - (y : ℂ).im|)| ≤ 1 / 500 := by
  have hLtop : Tendsto P.L atTop atTop :=
    Zeta23.Assembly.tendsto_L_atTop P hP.lam_pos
  set c := Zeta23.ThmD.cDT P.ϱ P.lam
  filter_upwards [eventually_ge_atTop (16 : ℝ),
    eventually_ge_atTop (32000 * (c / P.w) ^ 2 + 1),
    hLtop.eventually_ge_atTop (max (8 * P.w) (96000 * P.w + 2 * Real.pi))]
    with T hT16 hT_tail hL_big x y hx_lo hx_hi hy_lo hy_hi
  have hT_pos : 0 < T := by linarith
  have h8w : 8 * P.w ≤ P.L T := le_trans (le_max_left _ _) hL_big
  have h96 : 96000 * P.w + 2 * Real.pi ≤ P.L T := le_trans (le_max_right _ _) hL_big
  have hL_pos : 0 < P.L T := by linarith [hP.one_le_w]
  have hsqrt4 : 4 ≤ Real.sqrt T := by
    rw [show (4 : ℝ) = Real.sqrt 16 by norm_num]
    exact Real.sqrt_le_sqrt hT16
  have hhgrid : 2 * Real.pi / P.L T ≤ Real.sqrt T / 2 := by
    have h1 : 2 * Real.pi ≤ P.L T := by linarith [hP.one_le_w]
    have h2 : 2 * Real.pi / P.L T ≤ 1 := (div_le_one hL_pos).mpr h1
    linarith
  set φ := P.phiD T
  set L := P.L T
  have hW : Zeta23.AdmWindow φ L P.w c := Zeta23.ThmD.admWindow_params hP h8w
  -- Identify `(P.atD T).phiHatR` and `(P.atD T).a`
  have hphi_eq : (P.atD T).phi T = φ := Zeta23.Params.atD_phi_valid T hP
  have hphiHatR_eq : ∀ r : ℝ, (P.atD T).phiHatR T r = Zeta23.AdmWindow.vHatR φ r := fun r => by
    unfold Zeta23.Params.phiHatR Zeta23.Params.phiHat Zeta23.AdmWindow.vHatR Zeta23.AdmWindow.vHat
    rw [hphi_eq]
  have ha_eq : (P.atD T).a T = L⁻¹ * ∫ u, φ u ^ 2 := by
    rw [Zeta23.Params.atD_a T hP]; rfl
  set aD := (P.atD T).a T
  obtain ⟨haStar_lo, haStar_hi⟩ := aStar_bounds hP.lam_pos.le hP.lam_le_one
  have haD_close : |aD - Zeta23.ThmD.aStar P.lam| ≤ 4 * P.w / L := by
    rw [ha_eq]
    exact Zeta23.ThmD.aD_close hP.taper hP.lam_pos hP.lam_le_one hP.one_le_w h8w
  have hwL_small : 4 * P.w / L ≤ 1 / 4 := by
    rw [div_le_iff₀ hL_pos]; linarith [Real.pi_pos]
  have haD_lo : 1 / 4 ≤ aD := by linarith [(abs_le.mp haD_close).1]
  have haD_pos : 0 < aD := by linarith
  -- Step 1: Grid-tail bound outside `s = image (Fin d → ℤ)`
  set d := P.d T
  set s : Finset ℤ := Finset.univ.image (fun k : Fin d => ((k : ℕ) : ℤ))
  have hinj : Function.Injective (fun k : Fin d => ((k : ℕ) : ℤ)) := by
    intro a b h; simp only [Nat.cast_inj] at h; exact Fin.ext h
  have hfar_of_bulk : ∀ γ : ℝ, T + Real.sqrt T ≤ γ → γ ≤ 2 * T - Real.sqrt T →
      ∀ k : ℤ, k ∉ s → T / 4 ≤ (γ - (T + k * (2 * Real.pi / L))) ^ 2 := by
    intro γ hγ_lo hγ_hi k hk_not
    have hk_cases : k < 0 ∨ (d : ℤ) ≤ k := by
      by_contra h
      rw [not_or, not_lt, not_le] at h
      apply hk_not
      rw [Finset.mem_image]
      refine ⟨⟨k.toNat, ?_⟩, Finset.mem_univ _, ?_⟩
      · have hk_nn : 0 ≤ k := h.1
        have hlt : k < (d : ℤ) := h.2
        omega
      · simp [Int.toNat_of_nonneg h.1]
    have hstep_pos : 0 < 2 * Real.pi / L := by positivity
    have hdiff_ge : Real.sqrt T / 2 ≤ |γ - (T + k * (2 * Real.pi / L))| := by
      rcases hk_cases with hk_neg | hk_ge
      · have hk_le : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk_neg
        have hkmul : (k : ℝ) * (2 * Real.pi / L) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) hstep_pos.le
        have : Real.sqrt T / 2 ≤ γ - (T + k * (2 * Real.pi / L)) := by linarith [Real.sqrt_nonneg T]
        exact this.trans (le_abs_self _)
      · have hk_ge_r : (d : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge
        have hd_gt : L * T / (2 * Real.pi) - 1 < (d : ℝ) :=
          Nat.sub_one_lt_floor (L * T / (2 * Real.pi))
        have htau_gt : 2 * T - 2 * Real.pi / L < T + (k : ℝ) * (2 * Real.pi / L) := by
          have h1 : (L * T / (2 * Real.pi) - 1) * (2 * Real.pi / L)
              < (k : ℝ) * (2 * Real.pi / L) :=
            mul_lt_mul_of_pos_right (hd_gt.trans_le hk_ge_r) hstep_pos
          have h2 : (L * T / (2 * Real.pi) - 1) * (2 * Real.pi / L) = T - 2 * Real.pi / L := by
            field_simp
          linarith
        have : Real.sqrt T / 2 ≤ -(γ - (T + k * (2 * Real.pi / L))) := by linarith
        exact this.trans (neg_le_abs _)
    have hsq := pow_le_pow_left₀ (by positivity) hdiff_ge 2
    rw [sq_abs, div_pow, Real.sq_sqrt hT_pos.le] at hsq
    linarith
  set γx := (x : ℂ).im
  set γy := (y : ℂ).im
  set g : ℤ → ℝ := fun k =>
    Zeta23.AdmWindow.vHatR φ (γx - (T + k * (2 * Real.pi / L)))
      * Zeta23.AdmWindow.vHatR φ (γy - (T + k * (2 * Real.pi / L)))
  have hhasSum : HasSum g (L * Zeta23.AdmWindow.VPhiR φ (γx - γy)) :=
    hW.hasSum_vHatR_mul T γx γy
  have htail_fin : ∀ u : Finset ℤ, s ⊆ u →
      |(∑ k ∈ u, g k) - ∑ k ∈ s, g k| ≤ 4 * L ^ 2 * (c / P.w) ^ 2 / T := by
    intro u hsu
    rw [← Finset.sum_sdiff hsu, add_sub_cancel_right]
    set t := u \ s
    have ht_not : ∀ k ∈ t, k ∉ s := fun k hk => (Finset.mem_sdiff.mp hk).2
    have htx := admWindow_grid_tail_sq_le hW hT_pos t
      (fun k hk => hfar_of_bulk γx hx_lo hx_hi k (ht_not k hk))
    have hty := admWindow_grid_tail_sq_le hW hT_pos t
      (fun k hk => hfar_of_bulk γy hy_lo hy_hi k (ht_not k hk))
    have hcs : |∑ k ∈ t, g k|
        ≤ (∑ k ∈ t, (Zeta23.AdmWindow.vHatR φ (γx - (T + k * (2 * Real.pi / L)))) ^ 2
            + ∑ k ∈ t, (Zeta23.AdmWindow.vHatR φ (γy - (T + k * (2 * Real.pi / L)))) ^ 2) / 2 := by
      calc |∑ k ∈ t, g k| ≤ ∑ k ∈ t, |g k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ t, ((Zeta23.AdmWindow.vHatR φ (γx - (T + k * (2 * Real.pi / L)))) ^ 2
              + (Zeta23.AdmWindow.vHatR φ (γy - (T + k * (2 * Real.pi / L)))) ^ 2) / 2 := by
            refine Finset.sum_le_sum fun k _ => ?_
            simp only [g, abs_mul]
            have ha := abs_nonneg (Zeta23.AdmWindow.vHatR φ (γx - (T + k * (2 * Real.pi / L))))
            have hb := abs_nonneg (Zeta23.AdmWindow.vHatR φ (γy - (T + k * (2 * Real.pi / L))))
            nlinarith [sq_nonneg (|Zeta23.AdmWindow.vHatR φ (γx - (T + k * (2 * Real.pi / L)))|
              - |Zeta23.AdmWindow.vHatR φ (γy - (T + k * (2 * Real.pi / L)))|),
              sq_abs (Zeta23.AdmWindow.vHatR φ (γx - (T + k * (2 * Real.pi / L)))),
              sq_abs (Zeta23.AdmWindow.vHatR φ (γy - (T + k * (2 * Real.pi / L))))]
        _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]
    linarith
  have hhasSum_tendsto : Tendsto (fun u : Finset ℤ => |(∑ k ∈ u, g k) - ∑ k ∈ s, g k|) atTop
      (𝓝 |(L * Zeta23.AdmWindow.VPhiR φ (γx - γy)) - ∑ k ∈ s, g k|) :=
    (hhasSum.sub_const (∑ k ∈ s, g k)).abs
  have htail_full : |(L * Zeta23.AdmWindow.VPhiR φ (γx - γy)) - ∑ k ∈ s, g k|
      ≤ 4 * L ^ 2 * (c / P.w) ^ 2 / T :=
    le_of_tendsto hhasSum_tendsto
      ((eventually_ge_atTop s).mono fun u hu => htail_fin u hu)
  -- Identify `pairGridOverlap` with `(aD * L ^ 2)⁻¹ * ∑ k ∈ s, g k`
  have hoverlap_eq : pairGridOverlap Z (P.atD T) T x y = (aD * L ^ 2)⁻¹ * ∑ k ∈ s, g k := by
    unfold pairGridOverlap
    simp only [Zeta23.Params.atD_L, Zeta23.Params.atD_d, Zeta23.Params.atD_tau]
    congr 1
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hphiHatR_eq, hphiHatR_eq]
    rfl
  set Ifull := L⁻¹ * Zeta23.AdmWindow.VPhiR φ (γx - γy) / aD
  have hstep1 : |pairGridOverlap Z (P.atD T) T x y - Ifull|
      ≤ 4 * (c / P.w) ^ 2 / (aD * T) := by
    rw [hoverlap_eq]
    have heq : (aD * L ^ 2)⁻¹ * (∑ k ∈ s, g k) - Ifull
        = -((aD * L ^ 2)⁻¹ * ((L * Zeta23.AdmWindow.VPhiR φ (γx - γy)) - ∑ k ∈ s, g k)) := by
      simp only [Ifull]
      field_simp
      ring
    rw [heq, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < (aD * L ^ 2)⁻¹)]
    calc (aD * L ^ 2)⁻¹ * |(L * Zeta23.AdmWindow.VPhiR φ (γx - γy)) - ∑ k ∈ s, g k|
        ≤ (aD * L ^ 2)⁻¹ * (4 * L ^ 2 * (c / P.w) ^ 2 / T) :=
          mul_le_mul_of_nonneg_left htail_full (by positivity)
      _ = 4 * (c / P.w) ^ 2 / (aD * T) := by field_simp
  -- Step 2: Taper comparison between `Ifull` and `mtKernel`
  set Δ := L / (2 * Real.pi) * (γx - γy)
  have hV_close : |L⁻¹ * Zeta23.AdmWindow.VPhiR φ (γx - γy) - mtKernelNum P.lam Δ|
      ≤ 2 * P.w / L :=
    VPhiR_phiD_close hP.taper hP.lam_pos hP.lam_le_one hP.one_le_w h8w (γx - γy)
  have hN_le : |mtKernelNum P.lam Δ| ≤ Zeta23.ThmD.aStar P.lam :=
    abs_mtKernelNum_le_aStar hP.lam_pos.le hP.lam_le_one Δ
  have haStar_pos : 0 < Zeta23.ThmD.aStar P.lam := by linarith
  have hstep2 : |Ifull - mtKernel P.lam Δ| ≤ 6 * P.w / (aD * L) := by
    simp only [Ifull, mtKernel]
    have hfrac : L⁻¹ * Zeta23.AdmWindow.VPhiR φ (γx - γy) / aD
        - mtKernelNum P.lam Δ / Zeta23.ThmD.aStar P.lam
        = ((L⁻¹ * Zeta23.AdmWindow.VPhiR φ (γx - γy) - mtKernelNum P.lam Δ)
              * Zeta23.ThmD.aStar P.lam
            + mtKernelNum P.lam Δ * (Zeta23.ThmD.aStar P.lam - aD))
          / (aD * Zeta23.ThmD.aStar P.lam) := by
      field_simp
      ring
    rw [hfrac, abs_div, abs_of_pos (mul_pos haD_pos haStar_pos),
      div_le_div_iff₀ (mul_pos haD_pos haStar_pos) (mul_pos haD_pos hL_pos)]
    have htri := abs_add_le
      ((L⁻¹ * Zeta23.AdmWindow.VPhiR φ (γx - γy) - mtKernelNum P.lam Δ) * Zeta23.ThmD.aStar P.lam)
      (mtKernelNum P.lam Δ * (Zeta23.ThmD.aStar P.lam - aD))
    rw [abs_mul, abs_mul, abs_of_pos haStar_pos, abs_sub_comm (Zeta23.ThmD.aStar P.lam) aD] at htri
    have h1 : |L⁻¹ * Zeta23.AdmWindow.VPhiR φ (γx - γy) - mtKernelNum P.lam Δ|
        * Zeta23.ThmD.aStar P.lam ≤ (2 * P.w / L) * Zeta23.ThmD.aStar P.lam :=
      mul_le_mul_of_nonneg_right hV_close haStar_pos.le
    have h2 : |mtKernelNum P.lam Δ| * |aD - Zeta23.ThmD.aStar P.lam|
        ≤ Zeta23.ThmD.aStar P.lam * (4 * P.w / L) :=
      mul_le_mul hN_le haD_close (abs_nonneg _) haStar_pos.le
    have hsum : (2 * P.w / L) * Zeta23.ThmD.aStar P.lam + Zeta23.ThmD.aStar P.lam * (4 * P.w / L)
        = (6 * P.w / L) * Zeta23.ThmD.aStar P.lam := by ring
    have hnum_le : |(L⁻¹ * Zeta23.AdmWindow.VPhiR φ (γx - γy) - mtKernelNum P.lam Δ)
          * Zeta23.ThmD.aStar P.lam + mtKernelNum P.lam Δ * (Zeta23.ThmD.aStar P.lam - aD)|
        ≤ (6 * P.w / L) * Zeta23.ThmD.aStar P.lam := by linarith
    calc |(L⁻¹ * Zeta23.AdmWindow.VPhiR φ (γx - γy) - mtKernelNum P.lam Δ)
            * Zeta23.ThmD.aStar P.lam + mtKernelNum P.lam Δ * (Zeta23.ThmD.aStar P.lam - aD)|
          * (aD * L)
        ≤ ((6 * P.w / L) * Zeta23.ThmD.aStar P.lam) * (aD * L) :=
          mul_le_mul_of_nonneg_right hnum_le (by positivity)
      _ = 6 * P.w * (aD * Zeta23.ThmD.aStar P.lam) := by field_simp
  -- Combine Step 1 and Step 2 and use evenness `mtKernel P.lam |Δ| = mtKernel P.lam Δ`
  have hK_abs : mtKernel P.lam (L / (2 * Real.pi) * |γx - γy|) = mtKernel P.lam Δ := by
    have : L / (2 * Real.pi) * |γx - γy| = |Δ| := by
      simp only [Δ]
      rw [abs_mul, abs_of_pos (by positivity : 0 < L / (2 * Real.pi))]
    rw [this, mtKernel_abs]
  rw [hK_abs]
  have hsmall1 : 4 * (c / P.w) ^ 2 / (aD * T) ≤ 1 / 1000 := by
    rw [div_le_iff₀ (mul_pos haD_pos hT_pos)]
    have : 1 / 4 * T ≤ aD * T := mul_le_mul_of_nonneg_right haD_lo hT_pos.le
    linarith
  have hsmall2 : 6 * P.w / (aD * L) ≤ 1 / 1000 := by
    rw [div_le_iff₀ (mul_pos haD_pos hL_pos)]
    have : 1 / 4 * L ≤ aD * L := mul_le_mul_of_nonneg_right haD_lo hL_pos.le
    linarith [Real.pi_pos]
  calc |pairGridOverlap Z (P.atD T) T x y - mtKernel P.lam Δ|
      ≤ |pairGridOverlap Z (P.atD T) T x y - Ifull| + |Ifull - mtKernel P.lam Δ| :=
        abs_sub_le _ _ _
    _ ≤ 1 / 1000 + 1 / 1000 := add_le_add (hstep1.trans hsmall1) (hstep2.trans hsmall2)
    _ = 1 / 500 := by norm_num

end GaloisForLFunctions.IncommensurableGaborPinching
