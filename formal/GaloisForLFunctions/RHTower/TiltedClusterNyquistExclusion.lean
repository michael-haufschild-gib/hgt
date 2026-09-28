import GaloisForLFunctions.RHTower.TiltedRiemannKernel
import GaloisForLFunctions.RHTower.WeilNyquistInertia

/-!
# Landau-sharp cluster exclusion by tilted radical kernels

`HodgeClusterNyquistExclusion` excludes clustered off-line zeros of `ζ` below `≈ 2e^{2X}`,
`X = a - 3/8`, under the level-`a` Hodge index. This file raises the constant to the Landau value
`2π`.

**Theorem** (`hodgeIndex_tilted_cluster_horizon`). For every tilt `0 ≤ θ < π/4`, the level-`a`
Hodge index excludes every zero `β₀ + it₀` with `β₀ > ½` such that

`π cos(2θ) e^{2X} > (π/4 - θ) t₀ + O(N(log N + log 1/δ₀) + log t₀ + N X)`.

With `θ = π/4 - ε` the horizon is `(π sin(2ε)/ε) e^{2X}`, which increases to `2π e^{2X}` as
`ε → 0`: the height where the zero density `(1/2π) log(t/2π)` reaches the Nyquist rate of tests
supported in `[-a, a]`. At `θ = 0` the horizon is `4 e^{2X}`.

Two changes to the cluster test of `HodgeClusterNyquistExclusion` give this.

* **Tilted kernel.** Riemann's kernel `Φ` is replaced by its horizontal slice `Φ_θ(u) = Φ(u + iθ)`
  (`TiltedRiemannKernel`), with `Φ̂_θ(z) = e^{zθ} Ξ(z)` on the whole plane
  (`paperFT_tiltedPhi_eq`). Dividing by the node divisor gives `K̂_θ = e^{zθ} K̂` (`Kθ_spec`). The
  untilted interpolant `Q` is kept, so at a node the test's transform is `e^{γθ}(±i)` up to the
  tail, and the node block is `≤ -(3/8) e^{2θ(t₀ - 3/4)}` (`re_tilted_node_pair_le`,
  `re_neg_cexp_two_mul_le`). The cost of the tilt is the slower decay
  `e^{-π cos(2θ) e^{2|u|}}` of `Φ_θ` (`expTail_tiltedPhi_le`).
* **Quadratic remainder.** At a zero outside the cluster the test's transform is `-QP` times the
  transform of the discarded tail `(1 - χ)K_θ`. That tail is `C²` with second derivative
  supported where `χ ≠ 1`, so its transform decays like `(1 + |t|)^{-2}` with a tail-sized
  constant (`norm_paperFT_tailK_decay`). Both factors of every off-cluster summand are then
  tail-sized, and the positive remainder is `(5/4) S_Z B²` (`re_W_le_nodes_add_decay`); the norm
  of the test never enters.

Balancing `e^{θ t₀}` against `e^{π t₀/4} e^{-π cos(2θ) e^{2X}}` gives the horizon
(`tilted_cluster_inequality`, `hodgeIndex_excludes_tilted_cluster`).
-/

open Complex MeasureTheory Filter Topology Set GaloisForLFunctions
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

local notation "Φ" => riemannPhiKernel

/-! ## The tilted kernel as a divisible radical kernel -/

theorem cos_two_mul_pos_of_tilt {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) :
    0 < Real.cos (2 * θ) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ⟩

/-- An explicit radius beyond which `(11/2 + c) |u| ≤ π cos(2θ) e^{2|u|}` and
`1 ≤ π cos(2θ) e^{2|u|}`. -/
theorem rate_dominates {c₂ k x : ℝ} (hc₂ : 0 < c₂) (_hk : 0 ≤ k)
    (hx : k / (2 * π * c₂) + 1 / (2 * π * c₂) + 1 ≤ x) :
    k * x ≤ π * c₂ * Real.exp (2 * x) ∧ 1 ≤ π * c₂ * Real.exp (2 * x) := by
  have hpc : 0 < π * c₂ := mul_pos Real.pi_pos hc₂
  have hx0 : 0 ≤ x := by
    have : 0 ≤ k / (2 * π * c₂) := by positivity
    have : 0 ≤ 1 / (2 * π * c₂) := by positivity
    linarith
  have he : 2 * x ^ 2 ≤ Real.exp (2 * x) := by
    have h := Real.add_one_le_exp (2 * x)
    have h2 : (2 * x) ^ 2 / 2 + 2 * x + 1 ≤ Real.exp (2 * x) := by
      have := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * x)
      linarith
    nlinarith
  have he1 : 2 * x ≤ Real.exp (2 * x) := by
    have := Real.add_one_le_exp (2 * x); linarith
  constructor
  · have h1 : k / (2 * π * c₂) ≤ x := by
      have : 0 ≤ 1 / (2 * π * c₂) := by positivity
      linarith
    have h2 : k ≤ 2 * π * c₂ * x := by
      rwa [div_le_iff₀ (by positivity), mul_comm] at h1
    have h3 : k * x ≤ 2 * π * c₂ * x * x := mul_le_mul_of_nonneg_right h2 hx0
    have h4 : π * c₂ * (2 * x ^ 2) ≤ π * c₂ * Real.exp (2 * x) :=
      mul_le_mul_of_nonneg_left he hpc.le
    nlinarith
  · have h1 : 1 / (2 * π * c₂) ≤ x := by
      have : 0 ≤ k / (2 * π * c₂) := by positivity
      linarith
    have h2 : 1 ≤ 2 * π * c₂ * x := by
      rwa [div_le_iff₀ (by positivity), mul_comm] at h1
    have h4 : π * c₂ * (2 * x) ≤ π * c₂ * Real.exp (2 * x) :=
      mul_le_mul_of_nonneg_left he1 hpc.le
    nlinarith

/-- The tilted kernel decays super-exponentially. -/
theorem superExpDecay_tiltedPhi {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) :
    SuperExpDecay (tiltedPhi θ) := by
  have hθ4 : |θ| < π / 4 := by rw [abs_of_nonneg hθ0]; linarith
  refine ⟨continuous_tiltedPhi hθ4, fun c => ?_⟩
  set c₂ := Real.cos (2 * θ) with hc₂def
  have hc₂ := cos_two_mul_pos_of_tilt hθ0 hθ
  obtain ⟨C, hC, hb⟩ := exists_norm_tiltedPhi_le hθ0 hθ
  set k : ℝ := 11 / 2 + |c| with hk
  have hk0 : 0 ≤ k := by positivity
  set U : ℝ := k / (2 * π * c₂) + 1 / (2 * π * c₂) + 1 with hU
  have hM := tiltedPhiTailConst_nonneg
  set D : ℝ := tiltedPhiTailConst + C * Real.exp ((|c| + 1) * U) with hD
  have hpt : ∀ u : ℝ, ‖tiltedPhi θ u‖ * Real.exp (c * |u|) ≤ D * Real.exp (-|u|) := by
    intro u
    have hcu : c * |u| ≤ |c| * |u| := mul_le_mul_of_nonneg_right (le_abs_self c) (abs_nonneg u)
    by_cases hu : U ≤ |u|
    · obtain ⟨h1, h2⟩ := rate_dominates hc₂ hk0 hu
      have hr := norm_tiltedPhi_le_of_rate hθ0 hθ h2
      have hexp : 9 / 2 * |u| + (-(π * c₂ * Real.exp (2 * |u|))) + c * |u| ≤ -|u| := by
        have : k * |u| = 11 / 2 * |u| + |c| * |u| := by rw [hk]; ring
        linarith
      calc ‖tiltedPhi θ u‖ * Real.exp (c * |u|)
          ≤ tiltedPhiTailConst * Real.exp (9 / 2 * |u|) *
              Real.exp (-(π * c₂ * Real.exp (2 * |u|))) * Real.exp (c * |u|) :=
            mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
        _ = tiltedPhiTailConst * Real.exp (9 / 2 * |u| + (-(π * c₂ * Real.exp (2 * |u|))) +
              c * |u|) := by rw [Real.exp_add, Real.exp_add]; ring
        _ ≤ tiltedPhiTailConst * Real.exp (-|u|) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hM
        _ ≤ D * Real.exp (-|u|) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            rw [hD]; have : 0 ≤ C * Real.exp ((|c| + 1) * U) := by positivity
            linarith
    · push Not at hu
      have h1 := hb u
      have hU0 : 0 ≤ U := by
        have : 0 ≤ k / (2 * π * c₂) := by positivity
        have : 0 ≤ 1 / (2 * π * c₂) := by positivity
        linarith
      have hexp : c * |u| ≤ (|c| + 1) * U - |u| + (-|u|) + |u| := by
        have : |c| * |u| ≤ |c| * U := mul_le_mul_of_nonneg_left hu.le (abs_nonneg c)
        nlinarith [abs_nonneg u]
      calc ‖tiltedPhi θ u‖ * Real.exp (c * |u|) ≤ C * Real.exp (-|u|) * Real.exp (c * |u|) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = C * Real.exp (c * |u|) * Real.exp (-|u|) := by ring
        _ ≤ C * Real.exp ((|c| + 1) * U) * Real.exp (-|u|) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            apply mul_le_mul_of_nonneg_left _ hC
            apply Real.exp_le_exp.mpr
            have : |c| * |u| ≤ |c| * U := mul_le_mul_of_nonneg_left hu.le (abs_nonneg c)
            nlinarith [abs_nonneg u]
        _ ≤ D * Real.exp (-|u|) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            rw [hD]; linarith
  have hint : Integrable (fun u : ℝ => D * Real.exp (-|u|)) :=
    integrable_exp_neg_abs.const_mul D
  refine hint.mono' ?_ (Eventually.of_forall fun u => ?_)
  · exact ((continuous_tiltedPhi hθ4).norm.mul (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt u

/-- **The tilted transform on the whole plane.** `Φ̂_θ(z) = e^{zθ} Ξ(z)` for every `z`. -/
theorem paperFT_tiltedPhi_eq {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) (z : ℂ) :
    paperFT (tiltedPhi θ) z = cexp (z * θ) * riemannXiHat z := by
  have hF : Differentiable ℂ (paperFT (tiltedPhi θ)) :=
    (superExpDecay_tiltedPhi hθ0 hθ).differentiable_paperFT
  have hG : Differentiable ℂ (fun z : ℂ => cexp (z * θ) * riemannXiHat z) := by
    have hX : Differentiable ℂ riemannXiHat :=
      superExpDecay_riemannPhiKernel.differentiable_paperFT
    exact (by fun_prop : Differentiable ℂ fun z : ℂ => cexp (z * θ)).mul hX
  have hev : paperFT (tiltedPhi θ) =ᶠ[𝓝 0] fun z : ℂ => cexp (z * θ) * riemannXiHat z := by
    have hball : Metric.ball (0 : ℂ) (1 / 2) ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ (by norm_num)
    filter_upwards [hball] with w hw
    have hw' : |w.im| ≤ 1 / 2 := by
      have h1 : ‖w‖ < 1 / 2 := by simpa using hw
      exact (Complex.abs_im_le_norm w).trans h1.le
    rw [paperFT_tiltedPhi hθ0 hθ hw']
    unfold riemannXiHat
    rw [paperFT_riemannPhiKernel]
  have h := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (fun w _ => hF.analyticAt w) (fun w _ => hG.analyticAt w) isPreconnected_univ
    (mem_univ (0 : ℂ)) hev
  exact h (mem_univ z)

/-- The node divisor of `Ξ` is also a divisor datum for the tilted kernel. -/
theorem divisorData_nodeList_tilted {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) (t₀ X y₀ : ℝ) :
    DivisorData (nodeList t₀ X y₀) (tiltedPhi θ) := by
  obtain ⟨h1, h2, h3⟩ := divisorData_nodeList t₀ X y₀
  refine ⟨h1, h2, fun p hp => ?_⟩
  obtain ⟨u, hu, hu0, hloc⟩ := h3 p hp
  refine ⟨fun z => cexp (z * θ) * u z, (by fun_prop : Continuous fun z : ℂ => cexp (z * θ))
    |>.continuousAt.mul hu, mul_ne_zero (Complex.exp_ne_zero _) hu0, ?_⟩
  have heq : paperFT (tiltedPhi θ) = fun z => cexp (z * θ) * riemannXiHat z :=
    funext (paperFT_tiltedPhi_eq hθ0 hθ)
  rw [heq]
  have hloc' : riemannXiHat =ᶠ[𝓝 p.1] fun z => (z - p.1) ^ p.2 * u z := hloc
  filter_upwards [hloc'] with z hz
  rw [hz]; ring

/-! ## Weighted tails of the tilted kernel -/

theorem linear_sub_rate_le {k c₂ U v : ℝ} (hc₂ : 0 ≤ c₂)
    (hU : k ≤ 2 * π * c₂ * Real.exp (2 * U)) (hv : U ≤ v) :
    k * v - π * c₂ * Real.exp (2 * v) ≤ k * U - π * c₂ * Real.exp (2 * U) := by
  have hexp : Real.exp (2 * U) * (1 + 2 * (v - U)) ≤ Real.exp (2 * v) := by
    have h := Real.add_one_le_exp (2 * (v - U))
    have e : Real.exp (2 * v) = Real.exp (2 * U) * Real.exp (2 * (v - U)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have hpc : 0 ≤ π * c₂ := mul_nonneg Real.pi_pos.le hc₂
  have h1 : π * c₂ * (Real.exp (2 * U) * (1 + 2 * (v - U))) ≤ π * c₂ * Real.exp (2 * v) :=
    mul_le_mul_of_nonneg_left hexp hpc
  have h2 : k * (v - U) ≤ 2 * π * c₂ * Real.exp (2 * U) * (v - U) :=
    mul_le_mul_of_nonneg_right hU (by linarith)
  nlinarith

/-- **Weighted tail of the tilted kernel.** For `c ≥ 0` and
`c + 11/2 ≤ 2π cos(2θ) e^{2X}`:
`∫_{|u| ≥ X} ‖Φ_θ‖ e^{c|u|} ≤ 2M e^{(c + 11/2) X} e^{-π cos(2θ) e^{2X}}`. -/
theorem expTail_tiltedPhi_le {θ c X : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) (hc : 0 ≤ c)
    (hrate : c + 11 / 2 ≤ 2 * π * Real.cos (2 * θ) * Real.exp (2 * X)) :
    expTail (tiltedPhi θ) c X ≤
      2 * tiltedPhiTailConst * Real.exp ((c + 11 / 2) * X) *
        Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * X))) := by
  obtain ⟨c₂, hc₂def⟩ : ∃ x, x = Real.cos (2 * θ) := ⟨_, rfl⟩
  rw [← hc₂def] at hrate ⊢
  have hc₂ : 0 ≤ c₂ := by rw [hc₂def]; exact (cos_two_mul_pos_of_tilt hθ0 hθ).le
  have hM := tiltedPhiTailConst_nonneg
  obtain ⟨K, hK⟩ : ∃ x, x = tiltedPhiTailConst * Real.exp ((c + 11 / 2) * X) *
    Real.exp (-(π * c₂ * Real.exp (2 * X))) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hpt : ∀ u : ℝ, {u : ℝ | X ≤ |u|}.indicator
      (fun u => ‖tiltedPhi θ u‖ * Real.exp (c * |u|)) u ≤ K * Real.exp (-|u|) := by
    intro u
    simp only [indicator, mem_setOf_eq]
    split_ifs with hu
    · have hXu : 1 ≤ π * c₂ * Real.exp (2 * |u|) := by
        have : Real.exp (2 * X) ≤ Real.exp (2 * |u|) := Real.exp_le_exp.mpr (by linarith)
        nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg Real.pi_pos.le hc₂)]
      have hb := norm_tiltedPhi_le_of_rate hθ0 hθ (u := u) (by rw [← hc₂def]; exact hXu)
      rw [← hc₂def] at hb
      have hmono := linear_sub_rate_le (k := c + 11 / 2) hc₂ hrate hu
      have e : Real.exp (9 / 2 * |u|) * Real.exp (-(π * c₂ * Real.exp (2 * |u|))) *
          Real.exp (c * |u|) = Real.exp ((c + 11 / 2) * |u| - π * c₂ * Real.exp (2 * |u|)) *
          Real.exp (-|u|) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      have e2 : Real.exp ((c + 11 / 2) * X - π * c₂ * Real.exp (2 * X)) =
          Real.exp ((c + 11 / 2) * X) * Real.exp (-(π * c₂ * Real.exp (2 * X))) := by
        rw [← Real.exp_add]; ring_nf
      calc ‖tiltedPhi θ u‖ * Real.exp (c * |u|)
          ≤ tiltedPhiTailConst * Real.exp (9 / 2 * |u|) *
              Real.exp (-(π * c₂ * Real.exp (2 * |u|))) * Real.exp (c * |u|) :=
            mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
        _ = tiltedPhiTailConst * (Real.exp (9 / 2 * |u|) *
              Real.exp (-(π * c₂ * Real.exp (2 * |u|))) * Real.exp (c * |u|)) := by ring
        _ = tiltedPhiTailConst * (Real.exp ((c + 11 / 2) * |u| - π * c₂ * Real.exp (2 * |u|)) *
              Real.exp (-|u|)) := by rw [e]
        _ ≤ tiltedPhiTailConst * (Real.exp ((c + 11 / 2) * X - π * c₂ * Real.exp (2 * X)) *
              Real.exp (-|u|)) := by gcongr
        _ = K * Real.exp (-|u|) := by rw [e2, hK]; ring
    · positivity
  have hint : Integrable (fun u : ℝ => K * Real.exp (-|u|)) :=
    integrable_exp_neg_abs.const_mul K
  unfold expTail
  refine (integral_mono_of_nonneg (Eventually.of_forall fun u => ?_) hint
    (Eventually.of_forall hpt)).trans (le_of_eq ?_)
  · simp only [indicator]; split_ifs <;> positivity
  · rw [integral_const_mul, integral_exp_neg_abs, hK]; ring


/-! ## Tails of sums and scalar multiples -/

theorem expTail_add_le {f g : ℝ → ℂ} (hf : SuperExpDecay f) (hg : SuperExpDecay g) (c X : ℝ) :
    expTail (fun u => f u + g u) c X ≤ expTail f c X + expTail g c X := by
  unfold expTail
  rw [← integral_add (hf.integrable_tail c X) (hg.integrable_tail c X)]
  refine integral_mono_of_nonneg (Eventually.of_forall fun u => ?_)
    ((hf.integrable_tail c X).add (hg.integrable_tail c X)) (Eventually.of_forall fun u => ?_)
  · simp only [indicator]; split_ifs <;> positivity
  · simp only [indicator]
    split_ifs
    · have := norm_add_le (f u) (g u)
      have he := (Real.exp_pos (c * |u|)).le
      nlinarith
    · simp

theorem expTail_const_mul (a : ℂ) (f : ℝ → ℂ) (c X : ℝ) :
    expTail (fun u => a * f u) c X = ‖a‖ * expTail f c X := by
  unfold expTail
  rw [← integral_const_mul]
  congr 1; funext u
  simp only [indicator]
  split_ifs
  · rw [norm_mul]; ring
  · simp


/-! ## Decay of the transform of a discarded tail -/

local notation "shw" => OffLinePairData.sh

theorem norm_paperFT_le_halfWeight {F : ℝ → ℂ} (hF : SuperExpDecay F) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) : ‖paperFT F z‖ ≤ ∫ u, ‖F u‖ * Real.exp (1 / 2 * |u|) := by
  unfold paperFT
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => norm_nonneg _) (hF.2 (1 / 2))
    (Eventually.of_forall fun u => ?_))
  show ‖F u * cexp (I * z * u)‖ ≤ ‖F u‖ * Real.exp (1 / 2 * |u|)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_exp hz u) (norm_nonneg _)

theorem plateau₁_eq_zero {b w x : ℝ} (hw : 0 < w) (hx : |x| < b - w) : plateau₁ b w x = 0 := by
  have h1 : 1 < (x + b) / w := by rw [lt_div_iff₀ hw]; have := neg_abs_le x; linarith
  have h2 : 1 < (b - x) / w := by rw [lt_div_iff₀ hw]; have := le_abs_self x; linarith
  unfold plateau₁
  rw [deriv_smoothTransition_eq_zero (Or.inr h1), deriv_smoothTransition_eq_zero (Or.inr h2)]
  simp

theorem plateau₂_eq_zero {b w x : ℝ} (hw : 0 < w) (hx : |x| < b - w) : plateau₂ b w x = 0 := by
  have h1 : 1 < (x + b) / w := by rw [lt_div_iff₀ hw]; have := neg_abs_le x; linarith
  have h2 : 1 < (b - x) / w := by rw [lt_div_iff₀ hw]; have := le_abs_self x; linarith
  unfold plateau₂
  rw [deriv_smoothTransition_eq_zero (Or.inr h1), deriv_smoothTransition_eq_zero (Or.inr h2),
    deriv2_smoothTransition_eq_zero (Or.inr h1), deriv2_smoothTransition_eq_zero (Or.inr h2)]
  simp

/-- **Decay of the discarded tail.** Let `h` decay super-exponentially with two derivatives
`k₁, k₂` of the same kind, and let `|plateau₁|, |plateau₂| ≤ Kp`. Then on `|Im z| ≤ ½` the tail
`(1 - χ_b) h` has `(1 + |Re z|)² |tail^(z)| ≤ 2((1 + Kp) T_h + 2Kp T_{k₁} + T_{k₂})`, with `T_f` the
weighted tail `∫_{|u| ≥ b - 1/8} ‖f‖ e^{|u|/2}`. -/
theorem norm_paperFT_tailK_decay {h k₁ k₂ : ℝ → ℂ} (hh : SuperExpDecay h)
    (hk₁ : SuperExpDecay k₁) (hk₂ : SuperExpDecay k₂) (hd1 : ∀ x, HasDerivAt h (k₁ x) x)
    (hd2 : ∀ x, HasDerivAt k₁ (k₂ x) x) {Kp : ℝ} (hKp0 : 0 ≤ Kp)
    (hKp : ∀ b x : ℝ, |plateau₁ b shw x| ≤ Kp ∧ |plateau₂ b shw x| ≤ Kp) (b : ℝ) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    (1 + |z.re|) ^ 2 * ‖paperFT (tailK b h) z‖ ≤
      2 * ((1 + Kp) * expTail h (1 / 2) (b - shw) + 2 * Kp * expTail k₁ (1 / 2) (b - shw) +
        expTail k₂ (1 / 2) (b - shw)) := by
  set X := b - shw with hXdef
  set P : ℝ → ℂ := fun x => ((plateau b shw x : ℝ) : ℂ) with hP
  set P₁ : ℝ → ℂ := fun x => ((plateau₁ b shw x : ℝ) : ℂ) with hP₁
  set P₂ : ℝ → ℂ := fun x => ((plateau₂ b shw x : ℝ) : ℂ) with hP₂
  have hw : shw ≠ 0 := OffLinePairData.sh_pos.ne'
  have dP : ∀ x, HasDerivAt P (P₁ x) x := fun x => (hasDerivAt_plateau hw x).ofReal_comp
  have dP₁ : ∀ x, HasDerivAt P₁ (P₂ x) x := fun x => (hasDerivAt_plateau₁ hw x).ofReal_comp
  have cP₁ : Continuous P₁ := by
    simp only [hP₁]; exact Complex.continuous_ofReal.comp (continuous_plateau₁ b shw)
  have cP₂ : Continuous P₂ := by
    simp only [hP₂]; exact Complex.continuous_ofReal.comp (continuous_plateau₂ b shw)
  have bP₁ : ∀ u, ‖P₁ u‖ ≤ Kp := fun u => by
    simp only [hP₁, Complex.norm_real, Real.norm_eq_abs]; exact (hKp b u).1
  have bP₂ : ∀ u, ‖P₂ u‖ ≤ Kp := fun u => by
    simp only [hP₂, Complex.norm_real, Real.norm_eq_abs]; exact (hKp b u).2
  have b1P : ∀ u, ‖1 - P u‖ ≤ 1 := fun u => OffLinePairData.norm_one_sub_plateau_le b u
  set t0 : ℝ → ℂ := tailK b h with ht0
  set t1 : ℝ → ℂ := fun x => -(P₁ x * h x) + (1 - P x) * k₁ x with ht1
  set t2 : ℝ → ℂ := fun x => -(P₂ x * h x) - 2 * (P₁ x * k₁ x) + (1 - P x) * k₂ x with ht2
  have d0 : ∀ x, HasDerivAt t0 (t1 x) x := by
    intro x
    have h1 := ((hasDerivAt_const x (1 : ℂ)).sub (dP x)).mul (hd1 x)
    have hfun : ((fun _ : ℝ => (1 : ℂ)) - P) * h = t0 := by
      funext y; simp only [Pi.mul_apply, Pi.sub_apply, ht0, tailK, hP]
    rw [hfun] at h1
    refine h1.congr_deriv ?_
    simp only [ht1, Pi.sub_apply]; ring
  have d1 : ∀ x, HasDerivAt t1 (t2 x) x := by
    intro x
    have h1 := ((dP₁ x).mul (hd1 x)).neg.add (((hasDerivAt_const x (1 : ℂ)).sub (dP x)).mul (hd2 x))
    have hfun : -(P₁ * h) + ((fun _ : ℝ => (1 : ℂ)) - P) * k₁ = t1 := by
      funext y; simp only [Pi.add_apply, Pi.neg_apply, Pi.mul_apply, Pi.sub_apply, ht1]
    rw [hfun] at h1
    refine h1.congr_deriv ?_
    simp only [ht2, Pi.sub_apply]; ring
  have s0 : SuperExpDecay t0 := superExpDecay_tailK hh b
  have s1 : SuperExpDecay t1 := by
    have a1 := (hh.mul_bounded cP₁ bP₁).const_mul (-1)
    have a2 := hk₁.mul_bounded (continuous_const.sub (OffLinePairData.continuous_plateauC b)) b1P
    have := a1.add a2
    convert this using 1; funext x; simp only [ht1, Pi.add_apply, Pi.sub_apply, hP]; ring
  have s2 : SuperExpDecay t2 := by
    have a1 := (hh.mul_bounded cP₂ bP₂).const_mul (-1)
    have a2 := (hk₁.mul_bounded cP₁ bP₁).const_mul (-2)
    have a3 := hk₂.mul_bounded (continuous_const.sub (OffLinePairData.continuous_plateauC b)) b1P
    have := (a1.add a2).add a3
    convert this using 1; funext x; simp only [ht2, Pi.add_apply, Pi.sub_apply, hP]; ring
  have f1 := paperFT_deriv_of_superExpDecay s0 s1 d0 z
  have f2 := paperFT_deriv_of_superExpDecay s1 s2 d1 z
  have hsq : ‖z‖ ^ 2 * ‖paperFT t0 z‖ = ‖paperFT t2 z‖ := by
    rw [f2, f1, norm_mul, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul]; ring
  -- the second derivative lives on the tail region
  have hvan : ∀ u : ℝ, |u| < X → t2 u = 0 := by
    intro u hu
    have e0 : plateau b shw u = 1 := plateau_eq_one OffLinePairData.sh_pos hu.le
    have e1 : plateau₁ b shw u = 0 := plateau₁_eq_zero OffLinePairData.sh_pos hu
    have e2 : plateau₂ b shw u = 0 := plateau₂_eq_zero OffLinePairData.sh_pos hu
    simp only [ht2, hP, hP₁, hP₂, e0, e1, e2]; simp
  set I0 := fun u : ℝ => {u : ℝ | X ≤ |u|}.indicator
    (fun u => ‖h u‖ * Real.exp (1 / 2 * |u|)) u with hI0
  set I1 := fun u : ℝ => {u : ℝ | X ≤ |u|}.indicator
    (fun u => ‖k₁ u‖ * Real.exp (1 / 2 * |u|)) u with hI1
  set I2 := fun u : ℝ => {u : ℝ | X ≤ |u|}.indicator
    (fun u => ‖k₂ u‖ * Real.exp (1 / 2 * |u|)) u with hI2
  have iI0 : Integrable I0 := hh.integrable_tail _ _
  have iI1 : Integrable I1 := hk₁.integrable_tail _ _
  have iI2 : Integrable I2 := hk₂.integrable_tail _ _
  have hpt : ∀ u, ‖t2 u‖ * Real.exp (1 / 2 * |u|) ≤ Kp * I0 u + 2 * Kp * I1 u + I2 u := by
    intro u
    by_cases hu : X ≤ |u|
    · simp only [hI0, hI1, hI2, indicator, mem_setOf_eq, if_pos hu]
      have he := (Real.exp_pos (1 / 2 * |u|)).le
      have n1 : ‖t2 u‖ ≤ Kp * ‖h u‖ + 2 * Kp * ‖k₁ u‖ + ‖k₂ u‖ := by
        simp only [ht2]
        calc ‖-(P₂ u * h u) - 2 * (P₁ u * k₁ u) + (1 - P u) * k₂ u‖
            ≤ ‖-(P₂ u * h u)‖ + ‖2 * (P₁ u * k₁ u)‖ + ‖(1 - P u) * k₂ u‖ := by
              refine (norm_add_le _ _).trans ?_
              gcongr
              exact norm_sub_le _ _
          _ ≤ Kp * ‖h u‖ + 2 * Kp * ‖k₁ u‖ + 1 * ‖k₂ u‖ := by
              have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
              rw [norm_neg, norm_mul, norm_mul, norm_mul, norm_mul, h2n]
              have e1 := mul_le_mul_of_nonneg_right (bP₂ u) (norm_nonneg (h u))
              have e2 := mul_le_mul_of_nonneg_right (bP₁ u) (norm_nonneg (k₁ u))
              have e3 := mul_le_mul_of_nonneg_right (b1P u) (norm_nonneg (k₂ u))
              linarith
          _ = Kp * ‖h u‖ + 2 * Kp * ‖k₁ u‖ + ‖k₂ u‖ := by ring
      calc ‖t2 u‖ * Real.exp (1 / 2 * |u|)
          ≤ (Kp * ‖h u‖ + 2 * Kp * ‖k₁ u‖ + ‖k₂ u‖) * Real.exp (1 / 2 * |u|) :=
            mul_le_mul_of_nonneg_right n1 he
        _ = _ := by ring
    · push Not at hu
      rw [hvan u hu, norm_zero, zero_mul]
      have a0 : 0 ≤ I0 u := by simp only [hI0, indicator]; split_ifs <;> positivity
      have a1 : 0 ≤ I1 u := by simp only [hI1, indicator]; split_ifs <;> positivity
      have a2 : 0 ≤ I2 u := by simp only [hI2, indicator]; split_ifs <;> positivity
      positivity
  have hint2 : ∫ u, ‖t2 u‖ * Real.exp (1 / 2 * |u|) ≤
      Kp * expTail h (1 / 2) X + 2 * Kp * expTail k₁ (1 / 2) X + expTail k₂ (1 / 2) X := by
    have iS : Integrable (fun u => Kp * I0 u + 2 * Kp * I1 u + I2 u) :=
      ((iI0.const_mul Kp).add (iI1.const_mul (2 * Kp))).add iI2
    calc ∫ u, ‖t2 u‖ * Real.exp (1 / 2 * |u|) ≤ ∫ u, (Kp * I0 u + 2 * Kp * I1 u + I2 u) :=
          integral_mono_of_nonneg (Eventually.of_forall fun u => by positivity) iS
            (Eventually.of_forall hpt)
      _ = Kp * expTail h (1 / 2) X + 2 * Kp * expTail k₁ (1 / 2) X + expTail k₂ (1 / 2) X := by
          have i2 : Integrable (fun u => Kp * I0 u) := iI0.const_mul Kp
          have i3 : Integrable (fun u => 2 * Kp * I1 u) := iI1.const_mul (2 * Kp)
          have i1 : Integrable (fun u => Kp * I0 u + 2 * Kp * I1 u) := i2.add i3
          rw [integral_add i1 iI2, integral_add i2 i3, integral_const_mul, integral_const_mul]
          rfl
  have hT2 : ‖z‖ ^ 2 * ‖paperFT t0 z‖ ≤
      Kp * expTail h (1 / 2) X + 2 * Kp * expTail k₁ (1 / 2) X + expTail k₂ (1 / 2) X := by
    rw [hsq]; exact (norm_paperFT_le_halfWeight s2 hz).trans hint2
  have hT0 : ‖paperFT t0 z‖ ≤ expTail h (1 / 2) X := norm_paperFT_tailK_le hh b hz
  have hre : |z.re| ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm z) 2
  have hsq2 : (1 + |z.re|) ^ 2 ≤ 2 * (1 + ‖z‖ ^ 2) := by nlinarith [sq_nonneg (1 - |z.re|)]
  have hn := norm_nonneg (paperFT t0 z)
  have hk0 : 0 ≤ Kp * expTail h (1 / 2) X := mul_nonneg hKp0 (expTail_nonneg _ _ _)
  calc (1 + |z.re|) ^ 2 * ‖paperFT t0 z‖ ≤ 2 * (1 + ‖z‖ ^ 2) * ‖paperFT t0 z‖ :=
        mul_le_mul_of_nonneg_right hsq2 hn
    _ = 2 * ‖paperFT t0 z‖ + 2 * (‖z‖ ^ 2 * ‖paperFT t0 z‖) := by ring
    _ ≤ 2 * expTail h (1 / 2) X + 2 * (Kp * expTail h (1 / 2) X +
          2 * Kp * expTail k₁ (1 / 2) X + expTail k₂ (1 / 2) X) := by linarith
    _ = 2 * ((1 + Kp) * expTail h (1 / 2) X + 2 * Kp * expTail k₁ (1 / 2) X +
          expTail k₂ (1 / 2) X) := by ring


/-! ## The Weil sum when every other zero sees a decaying transform -/

/-- **Finitely many nodes against decaying transforms.** If a `C²` test of compact support has
`(1 + |t_ρ|)² |f̂(γ_ρ)| ≤ B` and `(1 + |t_ρ|)² |f̂(conj γ_ρ)| ≤ B` at every zero outside a finite
set `F`, then `Re W(f,f) ≤ Σ_{ρ ∈ F} Re(summand) + (5/4) S_Z B²`. -/
theorem re_W_le_nodes_add_decay {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (F : Finset zetaZeroConfig.carrier) {B : ℝ} (hB : 0 ≤ B)
    (hoff : ∀ ρ : zetaZeroConfig.carrier, ρ ∉ F →
      (1 + |(ρ : ℂ).im|) ^ 2 * ‖paperFT f (gammaOf (ρ : ℂ))‖ ≤ B ∧
      (1 + |(ρ : ℂ).im|) ^ 2 * ‖paperFT f ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖ ≤ B) :
    (zetaZeroConfig.W f f).re ≤
      ∑ ρ ∈ F, (zetaZeroConfig.Wsummand f f ρ).re + (5 / 4) * zeroSumZ * B ^ 2 := by
  classical
  set ws : zetaZeroConfig.carrier → ℂ := fun ρ => zetaZeroConfig.Wsummand f f ρ with hws
  have hsumws : Summable ws := zeta_Wsummand_summable hf hf hfc hfc
  have hsum := summable_zeroSumZ
  set T : Set zetaZeroConfig.carrier := ((↑F : Set zetaZeroConfig.carrier)ᶜ) with hT
  have hsplit : ∑ ρ ∈ F, ws ρ + ∑' x : T, ws x = ∑' ρ, ws ρ :=
    hsumws.sum_add_tsum_compl (s := F)
  have hW : zetaZeroConfig.W f f = ∑ ρ ∈ F, ws ρ + ∑' x : T, ws x := by
    unfold ZeroConfig.W; rw [hsplit]
  have hb : ∀ x : T, ‖ws x‖ ≤ (5 / 4) * B ^ 2 *
      ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
        (1 + Complex.normSq (gammaOf (x : zetaZeroConfig.carrier)))) := by
    intro x
    have hx : (x : zetaZeroConfig.carrier) ∉ F := x.2
    obtain ⟨h1, h2⟩ := hoff _ hx
    set t := |((x : zetaZeroConfig.carrier) : ℂ).im|
    have hp : 1 ≤ (1 + t) ^ 2 := by have := abs_nonneg ((x : zetaZeroConfig.carrier) : ℂ).im; nlinarith
    have hp0 : 0 < (1 + t) ^ 2 := by linarith
    have hq := one_div_one_add_abs_im_sq_le (zetaZeroConfig.strip _ (x : zetaZeroConfig.carrier).2)
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult (x : zetaZeroConfig.carrier) := Nat.cast_nonneg _
    have hn : ‖ws x‖ = (zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) *
        ‖paperFT f (gammaOf (x : zetaZeroConfig.carrier))‖ *
        ‖paperFT f ((starRingEnd ℂ) (gammaOf (x : zetaZeroConfig.carrier)))‖ := by
      simp only [hws, ZeroConfig.Wsummand]
      rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
    rw [hn]
    obtain ⟨u₁, hu₁⟩ : ∃ v, v = ‖paperFT f (gammaOf (x : zetaZeroConfig.carrier))‖ := ⟨_, rfl⟩
    obtain ⟨u₂, hu₂⟩ : ∃ v,
        v = ‖paperFT f ((starRingEnd ℂ) (gammaOf (x : zetaZeroConfig.carrier)))‖ := ⟨_, rfl⟩
    rw [← hu₁] at h1 ⊢; rw [← hu₂] at h2 ⊢
    have hu₁0 : 0 ≤ u₁ := by rw [hu₁]; exact norm_nonneg _
    have hu₂0 : 0 ≤ u₂ := by rw [hu₂]; exact norm_nonneg _
    obtain ⟨q, hqd⟩ : ∃ v, v = 1 / (1 + Complex.normSq (gammaOf (x : zetaZeroConfig.carrier))) :=
      ⟨_, rfl⟩
    rw [← hqd] at hq
    have e : (zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
        (1 + Complex.normSq (gammaOf (x : zetaZeroConfig.carrier))) =
        (zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) * q := by rw [hqd]; ring
    rw [e]
    -- `u₁ u₂ (1+t)⁴ ≤ B²` and `1/(1+t)⁴ ≤ 1/(1+t)² ≤ (5/4) q`
    have hprod : u₁ * u₂ * ((1 + t) ^ 2 * (1 + t) ^ 2) ≤ B ^ 2 := by
      have := mul_le_mul h1 h2 (by positivity) hB
      nlinarith
    have hinv : 1 / ((1 + t) ^ 2 * (1 + t) ^ 2) ≤ (5 / 4) * q := by
      have h4 : 1 / ((1 + t) ^ 2 * (1 + t) ^ 2) ≤ 1 / (1 + t) ^ 2 := by
        apply one_div_le_one_div_of_le hp0; nlinarith
      exact h4.trans (by simpa [div_eq_mul_inv] using hq)
    have huu : u₁ * u₂ ≤ B ^ 2 * (1 / ((1 + t) ^ 2 * (1 + t) ^ 2)) := by
      rw [mul_one_div, le_div_iff₀ (by positivity)]; exact hprod
    have hB2 : 0 ≤ B ^ 2 := sq_nonneg _
    calc (zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) * u₁ * u₂
        = (zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) * (u₁ * u₂) := by ring
      _ ≤ (zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) *
            (B ^ 2 * ((5 / 4) * q)) :=
          mul_le_mul_of_nonneg_left (huu.trans (mul_le_mul_of_nonneg_left hinv hB2)) hm
      _ = (5 / 4) * B ^ 2 * ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) * q) := by
          ring
  have hsT : Summable (fun x : T => (5 / 4) * B ^ 2 *
      ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
        (1 + Complex.normSq (gammaOf (x : zetaZeroConfig.carrier))))) :=
    (hsum.subtype T).mul_left _
  have hwsT : Summable (fun x : T => ‖ws x‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hsT
  have hrest : (∑' x : T, ws x).re ≤ (5 / 4) * zeroSumZ * B ^ 2 := by
    calc (∑' x : T, ws x).re ≤ ‖∑' x : T, ws x‖ := Complex.re_le_norm _
      _ ≤ ∑' x : T, ‖ws x‖ := norm_tsum_le_tsum_norm hwsT
      _ ≤ ∑' x : T, (5 / 4) * B ^ 2 *
            ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
              (1 + Complex.normSq (gammaOf (x : zetaZeroConfig.carrier)))) :=
          Summable.tsum_le_tsum hb hwsT hsT
      _ = (5 / 4) * B ^ 2 * ∑' x : T,
            ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
              (1 + Complex.normSq (gammaOf (x : zetaZeroConfig.carrier)))) := tsum_mul_left
      _ ≤ (5 / 4) * B ^ 2 * zeroSumZ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Summable.tsum_subtype_le (fun ρ : zetaZeroConfig.carrier =>
            (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) T
            (fun _ => div_nonneg (Nat.cast_nonneg _)
              (add_pos_of_pos_of_nonneg one_pos (Complex.normSq_nonneg _)).le) hsum
      _ = (5 / 4) * zeroSumZ * B ^ 2 := by ring
  rw [hW, Complex.add_re, Complex.re_sum]
  linarith

/-- **A tilted node pair.** If `X conj X' = -1`, `|X| = |X'| = 1`, `|e| = |e'| = A`, the main term
has real part `≤ -(2/3)A²`, and the defects `Y, Y'` are at most `η ≤ A/8`, then
`Re((eX - Y) conj(e'X' - Y')) ≤ -(3/8) A²`. -/
theorem re_tilted_node_pair_le {e e' X X' Y Y' : ℂ} {A η : ℝ} (hX : ‖X‖ = 1) (hX' : ‖X'‖ = 1)
    (he : ‖e‖ = A) (he' : ‖e'‖ = A)
    (hmain : (e * (starRingEnd ℂ) e' * (X * (starRingEnd ℂ) X')).re ≤ -(2 / 3) * A ^ 2)
    (hY : ‖Y‖ ≤ η) (hY' : ‖Y'‖ ≤ η) (hη : 0 ≤ η) (hηA : η ≤ A / 8) :
    ((e * X - Y) * (starRingEnd ℂ) (e' * X' - Y')).re ≤ -(3 / 8) * A ^ 2 := by
  have hA : 0 ≤ A := by rw [← he]; exact norm_nonneg _
  have hexp : (e * X - Y) * (starRingEnd ℂ) (e' * X' - Y') =
      e * (starRingEnd ℂ) e' * (X * (starRingEnd ℂ) X') - e * X * (starRingEnd ℂ) Y' -
        Y * (starRingEnd ℂ) (e' * X') + Y * (starRingEnd ℂ) Y' := by
    rw [map_sub, map_mul]; ring
  rw [hexp]
  simp only [Complex.add_re, Complex.sub_re]
  have t1 : -(e * X * (starRingEnd ℂ) Y').re ≤ A * η := by
    have := Complex.abs_re_le_norm (e * X * (starRingEnd ℂ) Y')
    rw [norm_mul, norm_mul, RCLike.norm_conj, he, hX, mul_one] at this
    have := mul_le_mul_of_nonneg_left hY' hA
    linarith [neg_abs_le (e * X * (starRingEnd ℂ) Y').re]
  have t2 : -(Y * (starRingEnd ℂ) (e' * X')).re ≤ η * A := by
    have := Complex.abs_re_le_norm (Y * (starRingEnd ℂ) (e' * X'))
    rw [norm_mul, RCLike.norm_conj, norm_mul, he', hX', mul_one] at this
    have := mul_le_mul_of_nonneg_right hY hA
    linarith [neg_abs_le (Y * (starRingEnd ℂ) (e' * X')).re]
  have t3 : (Y * (starRingEnd ℂ) Y').re ≤ η * η := by
    have := Complex.re_le_norm (Y * (starRingEnd ℂ) Y')
    rw [norm_mul, RCLike.norm_conj] at this
    have := mul_le_mul hY hY' (norm_nonneg _) hη
    linarith
  have h1 : A * η ≤ A * (A / 8) := mul_le_mul_of_nonneg_left hηA hA
  have h2 : η * η ≤ (A / 8) * (A / 8) := mul_le_mul hηA hηA hη (by positivity)
  nlinarith

/-- The main term of a tilted node pair: `Re(-e^{2γθ}) ≤ -(2/3) e^{2θ Re γ}` for `|Im γ| ≤ ½`,
`0 ≤ θ < π/4`. -/
theorem re_neg_cexp_two_mul_le {γ : ℂ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2)
    (hγ : |γ.im| ≤ 1 / 2) :
    (-(cexp (γ * θ) * cexp (γ * θ))).re ≤ -(2 / 3) * Real.exp (θ * γ.re) ^ 2 := by
  have e : cexp (γ * θ) * cexp (γ * θ) =
      cexp (((2 * θ * γ.re : ℝ) : ℂ) + ((2 * θ * γ.im : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hre : ((((2 * θ * γ.re : ℝ) : ℂ) + ((2 * θ * γ.im : ℝ) : ℂ) * I)).re = 2 * θ * γ.re := by
    simp
  have him : ((((2 * θ * γ.re : ℝ) : ℂ) + ((2 * θ * γ.im : ℝ) : ℂ) * I)).im = 2 * θ * γ.im := by
    simp
  rw [e, Complex.neg_re, Complex.exp_re, hre, him]
  have hx : |2 * θ * γ.im| ≤ π / 4 := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * θ)]
    have : 2 * θ * |γ.im| ≤ (π / 2) * (1 / 2) :=
      mul_le_mul hθ.le hγ (abs_nonneg _) (by linarith [Real.pi_pos])
    linarith
  have hc : 2 / 3 ≤ Real.cos (2 * θ * γ.im) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := 2 * θ * γ.im)
    have hsq : (2 * θ * γ.im) ^ 2 ≤ (π / 4) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    have hpi : π / 4 < 4 / 5 := by linarith [Real.pi_lt_d2]
    have : (π / 4) ^ 2 ≤ (4 / 5) ^ 2 := pow_le_pow_left₀ (by positivity) hpi.le 2
    nlinarith
  have hsq : Real.exp (θ * γ.re) ^ 2 = Real.exp (2 * θ * γ.re) := by
    rw [sq, ← Real.exp_add]; ring_nf
  rw [hsq]
  have hp := Real.exp_pos (2 * θ * γ.re)
  nlinarith [mul_le_mul_of_nonneg_left hc hp.le]

/-! ## The tilted kernel over the cluster -/

namespace ClusterSetup

variable (C : ClusterSetup)

/-- The tilted kernel divided by the node divisor. -/
def Kθ (θ : ℝ) : ℝ → ℂ := multiResolvent C.L (tiltedPhi θ)

theorem dense_divisorEval_ne_zero : Dense {z : ℂ | divisorEval C.L z ≠ 0} := by
  have hsub : {z : ℂ | divisorEval C.L z = 0} ⊆ {z : ℂ | z ∈ C.L.map Prod.fst} := by
    intro z hz
    by_contra hc
    have hz' : divisorEval C.L z = 0 := hz
    exact divisorEval_ne_zero (fun p hp e => hc (by
      show z ∈ C.L.map Prod.fst
      rw [e]; exact List.mem_map.mpr ⟨p, hp, rfl⟩)) hz'
  have hfin : {z : ℂ | z ∈ C.L.map Prod.fst}.Finite := (C.L.map Prod.fst).finite_toSet
  have hc := (hfin.subset hsub).countable.dense_compl ℂ
  have e : {z : ℂ | divisorEval C.L z = 0}ᶜ = {z : ℂ | divisorEval C.L z ≠ 0} := by
    ext z; simp
  rwa [e] at hc

/-- **The tilted divided kernel.** `K_θ` decays super-exponentially and `K̂_θ = e^{zθ} K̂`. -/
theorem Kθ_spec {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) :
    SuperExpDecay (C.Kθ θ) ∧ ∀ z, paperFT (C.Kθ θ) z = cexp (z * θ) * paperFT C.K z := by
  obtain ⟨h1, h2, -, -⟩ := multiResolvent_spec C.L (superExpDecay_tiltedPhi hθ0 hθ)
    (divisorData_nodeList_tilted hθ0 hθ C.t₀ C.X C.y₀)
  obtain ⟨hK, hprod, -⟩ := C.K_spec
  refine ⟨h1, fun z => ?_⟩
  have hcont1 : Continuous (paperFT (C.Kθ θ)) := h1.continuous_paperFT
  have hcont2 : Continuous (fun z : ℂ => cexp (z * θ) * paperFT C.K z) :=
    (by fun_prop : Continuous fun z : ℂ => cexp (z * θ)).mul hK.continuous_paperFT
  have heq : EqOn (paperFT (C.Kθ θ)) (fun z : ℂ => cexp (z * θ) * paperFT C.K z)
      {z : ℂ | divisorEval C.L z ≠ 0} := by
    intro w hw
    have e1 := h2 w
    have e2 := hprod w
    rw [paperFT_tiltedPhi_eq hθ0 hθ] at e1
    apply mul_left_cancel₀ (show divisorEval C.L w ≠ 0 from hw)
    change divisorEval C.L w * paperFT (multiResolvent C.L (tiltedPhi θ)) w = _
    rw [e1, ← e2]; ring
  exact congrFun (Continuous.ext_on C.dense_divisorEval_ne_zero hcont1 hcont2 heq) z

/-- **Calculus of the tilted divided kernel, with tails.** With `Γ = t₀ + 2` and
`T(c, X) = 2^N ∫_{|u| ≥ X} ‖Φ_θ‖ e^{(c + 3N/2)|u|}`, the kernel `K_θ` and its first two derivatives
decay super-exponentially with tails at most `T`, `(1+Γ)T`, `(1+Γ)²T`. -/
theorem Kθ_calculus {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ : XiDivisorSupport}
    (hρ : ρ ∈ C.nodes) :
    ∃ k₁ k₂ : ℝ → ℂ, (∀ x, HasDerivAt (C.Kθ θ) (k₁ x) x) ∧ (∀ x, HasDerivAt k₁ (k₂ x) x) ∧
      SuperExpDecay k₁ ∧ SuperExpDecay k₂ ∧
      (∀ c X : ℝ, 0 ≤ c → expTail (C.Kθ θ) c X ≤
        2 ^ windowCount C.t₀ * expTail (tiltedPhi θ) (c + 3 / 2 * windowCount C.t₀) X) ∧
      (∀ c X : ℝ, 0 ≤ c → expTail k₁ c X ≤ (1 + (C.t₀ + 2)) *
        (2 ^ windowCount C.t₀ * expTail (tiltedPhi θ) (c + 3 / 2 * windowCount C.t₀) X)) ∧
      (∀ c X : ℝ, 0 ≤ c → expTail k₂ c X ≤ (1 + (C.t₀ + 2)) ^ 2 *
        (2 ^ windowCount C.t₀ * expTail (tiltedPhi θ) (c + 3 / 2 * windowCount C.t₀) X)) := by
  have hg := superExpDecay_tiltedPhi hθ0 hθ
  have hD := divisorData_nodeList_tilted hθ0 hθ C.t₀ C.X C.y₀
  have hpos : ∀ p ∈ C.L, 1 ≤ p.2 := by
    intro p hp
    obtain ⟨ν, -, rfl⟩ := mem_nodeList.mp hp
    exact one_le_divMult ν
  obtain ⟨a, b, g₂, ⟨pa, hpa, rfl⟩, ⟨pb, hpb, rfl⟩, hg₂, hgp, heq, htail₂, htailp⟩ :=
    multiResolvent_two_step hg hD hpos (C.two_le_orderSum hρ)
  have hnorm : ∀ p ∈ C.L, ‖p.1‖ ≤ C.t₀ + 2 := by
    intro p hp
    obtain ⟨ν, hν, rfl⟩ := mem_nodeList.mp hp
    exact C.norm_node_le hν
  have ha := hnorm pa hpa
  have hb := hnorm pb hpb
  have hΓ : 0 ≤ C.t₀ + 2 := (norm_nonneg _).trans ha
  have hK : SuperExpDecay (C.Kθ θ) := (multiResolvent_spec C.L hg hD).1
  have hKt : ∀ c X : ℝ, 0 ≤ c → expTail (C.Kθ θ) c X ≤
      2 ^ orderSum C.L * expTail (tiltedPhi θ) (c + 3 / 2 * orderSum C.L) X :=
    fun c X hc => multiResolvent_tail C.L hg hD c X hc
  set T : ℝ → ℝ → ℝ := fun c X =>
    2 ^ windowCount C.t₀ * expTail (tiltedPhi θ) (c + 3 / 2 * windowCount C.t₀) X with hT
  have hup : ∀ c X : ℝ, 2 ^ orderSum C.L * expTail (tiltedPhi θ) (c + 3 / 2 * orderSum C.L) X ≤
      T c X := fun c X => pow_mul_expTail_le hg C.orderSum_le c X
  set gp := resolventDiv pb.1 g₂ with hgpdef
  set h := resolventDiv pa.1 gp with hhdef
  have hKh : C.Kθ θ = h := heq
  have hh : SuperExpDecay h := by rw [← hKh]; exact hK
  set k₁ : ℝ → ℂ := fun x => -I * pa.1 * h x - I * gp x with hk₁
  set p₁ : ℝ → ℂ := fun x => -I * pb.1 * gp x - I * g₂ x with hp₁
  set k₂ : ℝ → ℂ := fun x => -I * pa.1 * k₁ x - I * p₁ x with hk₂
  have hdk : ∀ x, HasDerivAt h (k₁ x) x := fun x => hasDerivAt_resolventDiv hgp pa.1 x
  have hdp : ∀ x, HasDerivAt gp (p₁ x) x := fun x => hasDerivAt_resolventDiv hg₂ pb.1 x
  have hdk₁ : ∀ x, HasDerivAt k₁ (k₂ x) x := by
    intro x
    exact ((hdk x).const_mul (-I * pa.1)).sub ((hdp x).const_mul I) |>.congr_deriv (by
      simp only [hk₂]; try ring)
  have sk₁ : SuperExpDecay k₁ := by
    have := (hh.const_mul (-I * pa.1)).add (hgp.const_mul (-I))
    convert this using 1; funext x; simp only [hk₁, Pi.add_apply]; ring
  have sp₁ : SuperExpDecay p₁ := by
    have := (hgp.const_mul (-I * pb.1)).add (hg₂.const_mul (-I))
    convert this using 1; funext x; simp only [hp₁, Pi.add_apply]; ring
  have sk₂ : SuperExpDecay k₂ := by
    have := (sk₁.const_mul (-I * pa.1)).add (sp₁.const_mul (-I))
    convert this using 1; funext x; simp only [hk₂, Pi.add_apply]; ring
  have nI : ‖-I‖ = 1 := by simp
  have na : ‖-I * pa.1‖ ≤ C.t₀ + 2 := by rw [norm_mul, nI, one_mul]; exact ha
  have nb : ‖-I * pb.1‖ ≤ C.t₀ + 2 := by rw [norm_mul, nI, one_mul]; exact hb
  have tK : ∀ c X, 0 ≤ c → expTail h c X ≤ T c X := fun c X hc => by
    rw [← hKh]; exact (hKt c X hc).trans (hup c X)
  have tgp : ∀ c X, 0 ≤ c → expTail gp c X ≤ T c X := fun c X hc => (htailp c X hc).trans (hup c X)
  have tg₂ : ∀ c X, 0 ≤ c → expTail g₂ c X ≤ T c X := fun c X hc => (htail₂ c X hc).trans (hup c X)
  have hT0 : ∀ c X, 0 ≤ T c X := fun c X => by
    simp only [hT]; exact mul_nonneg (by positivity) (expTail_nonneg _ _ _)
  have t₁ : ∀ c X, 0 ≤ c → expTail k₁ c X ≤ (1 + (C.t₀ + 2)) * T c X := by
    intro c X hc
    have e : k₁ = fun u => (-I * pa.1) * h u + (-I) * gp u := by
      funext u; simp only [hk₁]; ring
    rw [e]
    refine (expTail_add_le (hh.const_mul _) (hgp.const_mul _) c X).trans ?_
    rw [expTail_const_mul, expTail_const_mul, nI, one_mul]
    have h1 := mul_le_mul na (tK c X hc) (expTail_nonneg _ _ _) hΓ
    have h2 := tgp c X hc
    nlinarith
  have tp₁ : ∀ c X, 0 ≤ c → expTail p₁ c X ≤ (1 + (C.t₀ + 2)) * T c X := by
    intro c X hc
    have e : p₁ = fun u => (-I * pb.1) * gp u + (-I) * g₂ u := by
      funext u; simp only [hp₁]; ring
    rw [e]
    refine (expTail_add_le (hgp.const_mul _) (hg₂.const_mul _) c X).trans ?_
    rw [expTail_const_mul, expTail_const_mul, nI, one_mul]
    have h1 := mul_le_mul nb (tgp c X hc) (expTail_nonneg _ _ _) hΓ
    have h2 := tg₂ c X hc
    nlinarith
  have t₂ : ∀ c X, 0 ≤ c → expTail k₂ c X ≤ (1 + (C.t₀ + 2)) ^ 2 * T c X := by
    intro c X hc
    have e : k₂ = fun u => (-I * pa.1) * k₁ u + (-I) * p₁ u := by
      funext u; simp only [hk₂]; ring
    rw [e]
    refine (expTail_add_le (sk₁.const_mul _) (sp₁.const_mul _) c X).trans ?_
    rw [expTail_const_mul, expTail_const_mul, nI, one_mul]
    have h1 := mul_le_mul na (t₁ c X hc) (expTail_nonneg _ _ _) hΓ
    have h2 := tp₁ c X hc
    have h3 := hT0 c X
    nlinarith
  refine ⟨k₁, k₂, fun x => by rw [hKh]; exact hdk x, hdk₁, sk₁, sk₂, fun c X hc => ?_, t₁, t₂⟩
  rw [hKh]; exact tK c X hc


theorem superExpDecay_integrable {g : ℝ → ℂ} (hg : SuperExpDecay g) : Integrable g := by
  have h := hg.integrable_mul_cexp 0
  simpa using h

/-- The tilted cluster test at level `a`: `N_Q P_s (χ_{a-1/4} K_θ)` with the untilted
interpolant `Q`. -/
def testθ (θ a : ℝ) : ℝ → ℂ := clusterTest C.Q C.κ (heightPolarShift C.t₀) (a - 1 / 4) (C.Kθ θ)

/-- The decay constant of the discarded tail of `K_θ`:
`2((1 + Kp) + 2Kp(1+Γ) + (1+Γ)²) · 2^N ∫_{|u| ≥ a - 3/8} ‖Φ_θ‖ e^{(1/2 + 3N/2)|u|}`. -/
def tailDecay (θ a Kp : ℝ) : ℝ :=
  2 * ((1 + Kp) + 2 * Kp * (1 + (C.t₀ + 2)) + (1 + (C.t₀ + 2)) ^ 2) *
    (2 ^ windowCount C.t₀ *
      expTail (tiltedPhi θ) (1 / 2 + 3 / 2 * windowCount C.t₀) (a - 1 / 4 - shw))

theorem testθ_properties {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : XiDivisorSupport}
    (hρ₀ : ρ₀ ∈ C.nodes) (a : ℝ) {Kp : ℝ} (hKp2 : 2 ≤ Kp)
    (hKp : ∀ b x : ℝ, |plateau₁ b shw x| ≤ Kp ∧ |plateau₂ b shw x| ≤ Kp) :
    ContDiff ℝ 2 (C.testθ θ a) ∧ HasCompactSupport (C.testθ θ a) ∧
      tsupport (C.testθ θ a) ⊆ Icc (-a) a ∧ paperFT (C.testθ θ a) (I / 2) = 0 ∧
      paperFT (C.testθ θ a) (-(I / 2)) = 0 := by
  obtain ⟨hK, -⟩ := C.Kθ_spec hθ0 hθ
  obtain ⟨k₁, k₂, hd1, hd2, sk₁, sk₂, -, -, -⟩ := C.Kθ_calculus hθ0 hθ hρ₀
  have hΓ : 0 ≤ C.t₀ + 2 := by linarith [C.ht₀]
  have n0 : 0 ≤ ∫ x, ‖C.Kθ θ x‖ := integral_nonneg fun _ => norm_nonneg _
  have n1 : 0 ≤ ∫ x, ‖k₁ x‖ := integral_nonneg fun _ => norm_nonneg _
  have n2 : 0 ≤ ∫ x, ‖k₂ x‖ := integral_nonneg fun _ => norm_nonneg _
  obtain ⟨B, hB⟩ : ∃ x, x = (∫ x, ‖C.Kθ θ x‖) + (∫ x, ‖k₁ x‖) + ∫ x, ‖k₂ x‖ := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; linarith
  have g1 : 1 ≤ 1 + (C.t₀ + 2) := by linarith
  have g2 : 1 ≤ (1 + (C.t₀ + 2)) ^ 2 := by nlinarith
  have nh : ∫ x, ‖C.Kθ θ x‖ ≤ B := by rw [hB]; linarith
  have nk₁ : ∫ x, ‖k₁ x‖ ≤ (1 + (C.t₀ + 2)) * B := by
    have : ∫ x, ‖k₁ x‖ ≤ B := by rw [hB]; linarith
    nlinarith
  have nk₂ : ∫ x, ‖k₂ x‖ ≤ (1 + (C.t₀ + 2)) ^ 2 * B := by
    have : ∫ x, ‖k₂ x‖ ≤ B := by rw [hB]; linarith
    nlinarith
  obtain ⟨hC2, -⟩ := clusterTest_calculus hK hd1 hd2 sk₁.1 sk₂.1 (superExpDecay_integrable sk₁)
    (superExpDecay_integrable sk₂) hΓ nh nk₁ nk₂ C.Q C.κ (heightPolarShift C.t₀) (a - 1 / 4)
    hKp2 hKp
  have hsp0 : 0 ≤ heightPolarShift C.t₀ := by linarith [(heightPolarShift_mem C.ht₀).1]
  have hts : tsupport (C.testθ θ a) ⊆ Icc (-a) a :=
    tsupport_clusterTest C.κ_pos.le hsp0 (C.test_supp_bound a)
  refine ⟨hC2, IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hts, hts, ?_, ?_⟩
  · unfold testθ; rw [paperFT_clusterTest hK, polarSymbol_half_I]; ring
  · unfold testθ; rw [paperFT_clusterTest hK, polarSymbol_neg_half_I]; ring

/-- The tilted test at a node: `e^{γθ}·(±i)` up to the truncation tail. -/
theorem testθ_at_node {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) (a : ℝ) {ν : XiDivisorSupport}
    (hν : ν ∈ C.nodes) :
    ∃ Y : ℂ, paperFT (C.testθ θ a) (gammaOf (ν : ℂ)) = cexp (gammaOf (ν : ℂ) * θ) * sgn ν - Y ∧
      ‖Y‖ ≤ 6 * coeffMass C.Q * expTail (C.Kθ θ) (1 / 2) (a - 1 / 4 - shw) := by
  obtain ⟨hKθ, hKθK⟩ := C.Kθ_spec hθ0 hθ
  obtain ⟨-, -, hnode⟩ := C.K_spec
  have hγim : |(gammaOf (ν : ℂ)).im| ≤ 1 / 2 := (abs_gammaOf_divisorSupport_im_lt ν).le
  have hP : 1 ≤ ‖C.Pp (gammaOf (ν : ℂ))‖ := by
    apply one_le_norm_polarSymbol C.ht₀
    have := (C.node_coords hν).1
    linarith [C.hX2]
  have hP0 : C.Pp (gammaOf (ν : ℂ)) ≠ 0 := fun h => by rw [h, norm_zero] at hP; linarith
  have hK0 := hnode ν hν
  have hQ : C.Q.eval (Complex.exp (I * gammaOf (ν : ℂ) * C.κ)) = C.r ν := C.Q_eval_node hν
  have hPs : polarSymbol (heightPolarShift C.t₀) (gammaOf (ν : ℂ)) = C.Pp (gammaOf (ν : ℂ)) := rfl
  refine ⟨C.r ν * C.Pp (gammaOf (ν : ℂ)) * paperFT (tailK (a - 1 / 4) (C.Kθ θ)) (gammaOf (ν : ℂ)),
    ?_, ?_⟩
  · unfold testθ
    rw [paperFT_clusterTest hKθ, hQ, hPs, hKθK]
    have e : C.r ν * C.Pp (gammaOf (ν : ℂ)) * paperFT C.K (gammaOf (ν : ℂ)) = sgn ν := by
      unfold r sgn
      field_simp
    calc C.r ν * C.Pp (gammaOf (ν : ℂ)) * (cexp (gammaOf (ν : ℂ) * θ) *
          paperFT C.K (gammaOf (ν : ℂ)) - paperFT (tailK (a - 1 / 4) (C.Kθ θ)) (gammaOf (ν : ℂ)))
        = cexp (gammaOf (ν : ℂ) * θ) * (C.r ν * C.Pp (gammaOf (ν : ℂ)) *
            paperFT C.K (gammaOf (ν : ℂ))) - C.r ν * C.Pp (gammaOf (ν : ℂ)) *
            paperFT (tailK (a - 1 / 4) (C.Kθ θ)) (gammaOf (ν : ℂ)) := by ring
      _ = _ := by rw [e]
  · have h1 : ‖C.r ν‖ ≤ 2 * coeffMass C.Q := by rw [← hQ]; exact C.norm_Q_strip_le hγim
    have h2 := C.norm_Pp_le hγim
    have h3 := norm_paperFT_tailK_le hKθ (a - 1 / 4) hγim
    rw [norm_mul, norm_mul]
    have hc := coeffMass_nonneg C.Q
    calc ‖C.r ν‖ * ‖C.Pp (gammaOf (ν : ℂ))‖ *
          ‖paperFT (tailK (a - 1 / 4) (C.Kθ θ)) (gammaOf (ν : ℂ))‖
        ≤ (2 * coeffMass C.Q) * 3 * expTail (C.Kθ θ) (1 / 2) (a - 1 / 4 - shw) := by gcongr
      _ = 6 * coeffMass C.Q * expTail (C.Kθ θ) (1 / 2) (a - 1 / 4 - shw) := by ring

/-- The tilted test at a zero of `K̂`: `(1 + |Re z|)² |f̂(z)| ≤ 6 Σ|c_k| · tailDecay`. -/
theorem testθ_off {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : XiDivisorSupport}
    (hρ₀ : ρ₀ ∈ C.nodes) (a : ℝ) {Kp : ℝ} (hKp2 : 2 ≤ Kp)
    (hKp : ∀ b x : ℝ, |plateau₁ b shw x| ≤ Kp ∧ |plateau₂ b shw x| ≤ Kp) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) (hK0 : paperFT C.K z = 0) :
    (1 + |z.re|) ^ 2 * ‖paperFT (C.testθ θ a) z‖ ≤ 6 * coeffMass C.Q * C.tailDecay θ a Kp := by
  obtain ⟨hKθ, hKθK⟩ := C.Kθ_spec hθ0 hθ
  obtain ⟨k₁, k₂, hd1, hd2, sk₁, sk₂, t0, t1, t2⟩ := C.Kθ_calculus hθ0 hθ hρ₀
  have hdec := norm_paperFT_tailK_decay hKθ sk₁ sk₂ hd1 hd2 (by linarith) hKp (a - 1 / 4) hz
  have hval : paperFT (C.testθ θ a) z = -(C.Q.eval (Complex.exp (I * z * C.κ)) * C.Pp z *
      paperFT (tailK (a - 1 / 4) (C.Kθ θ)) z) := by
    unfold testθ
    rw [paperFT_clusterTest hKθ, hKθK, hK0, mul_zero, zero_sub]
    have : polarSymbol (heightPolarShift C.t₀) z = C.Pp z := rfl
    rw [this]; ring
  rw [hval, norm_neg, norm_mul, norm_mul]
  have h1 := C.norm_Q_strip_le hz
  have h2 := C.norm_Pp_le hz
  have hc := coeffMass_nonneg C.Q
  set τ := 2 ^ windowCount C.t₀ *
    expTail (tiltedPhi θ) (1 / 2 + 3 / 2 * windowCount C.t₀) (a - 1 / 4 - shw) with hτ
  have hΓ : 0 ≤ C.t₀ + 2 := by linarith [C.ht₀]
  have e0 := t0 (1 / 2) (a - 1 / 4 - shw) (by norm_num)
  have e1 := t1 (1 / 2) (a - 1 / 4 - shw) (by norm_num)
  have e2 := t2 (1 / 2) (a - 1 / 4 - shw) (by norm_num)
  have hKp0 : 0 ≤ Kp := by linarith
  have hdec' : (1 + |z.re|) ^ 2 * ‖paperFT (tailK (a - 1 / 4) (C.Kθ θ)) z‖ ≤ C.tailDecay θ a Kp := by
    refine hdec.trans ?_
    unfold tailDecay
    rw [← hτ]
    have a0 := mul_le_mul_of_nonneg_left e0 (by linarith : (0 : ℝ) ≤ 1 + Kp)
    have a1 := mul_le_mul_of_nonneg_left e1 (by linarith : (0 : ℝ) ≤ 2 * Kp)
    nlinarith
  have hT0 : 0 ≤ (1 + |z.re|) ^ 2 * ‖paperFT (tailK (a - 1 / 4) (C.Kθ θ)) z‖ := by positivity
  calc (1 + |z.re|) ^ 2 * (‖C.Q.eval (Complex.exp (I * z * C.κ))‖ * ‖C.Pp z‖ *
        ‖paperFT (tailK (a - 1 / 4) (C.Kθ θ)) z‖)
      = ‖C.Q.eval (Complex.exp (I * z * C.κ))‖ * ‖C.Pp z‖ *
          ((1 + |z.re|) ^ 2 * ‖paperFT (tailK (a - 1 / 4) (C.Kθ θ)) z‖) := by ring
    _ ≤ (2 * coeffMass C.Q) * 3 * C.tailDecay θ a Kp := by gcongr
    _ = 6 * coeffMass C.Q * C.tailDecay θ a Kp := by ring


theorem tailDecay_nonneg (θ a : ℝ) {Kp : ℝ} (hKp : 0 ≤ Kp) : 0 ≤ C.tailDecay θ a Kp := by
  unfold tailDecay
  have hΓ : 0 ≤ C.t₀ + 2 := by linarith [C.ht₀]
  have := expTail_nonneg (tiltedPhi θ) (1 / 2 + 3 / 2 * windowCount C.t₀) (a - 1 / 4 - shw)
  positivity

/-- **The tilted cluster inequality.** If the level-`a` Hodge index holds, then
`e^{θ(t₀ - 3/4)} ≤ (6 + 2 S_Z) · 6 Σ|c_k| · tailDecay(θ, a)`. The node block of the tilted test is
`≤ -(3/8) e^{2θ(t₀-3/4)}`, and every other zero sees two decaying tail factors. -/
theorem tilted_cluster_inequality {ρ₀ : XiDivisorSupport} (hρ₀ : ρ₀ ∈ C.nodes) {θ a : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) (hH : HodgeIndexAtLevel zetaZeroConfig a) {Kp : ℝ}
    (hKp2 : 2 ≤ Kp) (hKp : ∀ b x : ℝ, |plateau₁ b shw x| ≤ Kp ∧ |plateau₂ b shw x| ≤ Kp) :
    Real.exp (θ * (C.t₀ - 3 / 4)) ≤
      (6 + 2 * zeroSumZ) * (6 * coeffMass C.Q * C.tailDecay θ a Kp) := by
  classical
  obtain ⟨hC2, hcomp, hts, hp1, hp2⟩ := C.testθ_properties hθ0 hθ hρ₀ a hKp2 hKp
  have hW0 := hH (C.testθ θ a) hC2 hts hp1 hp2
  obtain ⟨-, hprod, -⟩ := C.K_spec
  have hKp0 : 0 ≤ Kp := by linarith
  set F : Finset zetaZeroConfig.carrier := C.nodes.image toCarrier with hF
  obtain ⟨Bd, hBd⟩ : ∃ x, x = 6 * coeffMass C.Q * C.tailDecay θ a Kp := ⟨_, rfl⟩
  have hcM := coeffMass_nonneg C.Q
  have hBd0 : 0 ≤ Bd := by rw [hBd]; exact mul_nonneg (by positivity) (C.tailDecay_nonneg θ a hKp0)
  have hS := zeroSumZ_nonneg
  -- `K̂` vanishes at every zero that is not a node
  have hKz : ∀ ρ : zetaZeroConfig.carrier, ρ ∉ F → paperFT C.K (gammaOf (ρ : ℂ)) = 0 := by
    intro ρ hρ
    have hdiv : divisorEval C.L (gammaOf (ρ : ℂ)) ≠ 0 := by
      refine C.divisorEval_ne_zero_of_not_node fun ν hν e => hρ ?_
      rw [hF, Finset.mem_image]
      exact ⟨ν, hν, Subtype.ext (gammaOf_injective e).symm⟩
    have h := hprod (gammaOf (ρ : ℂ))
    rw [riemannXiHat_gammaOf_eq_zero ρ.2] at h
    exact (mul_eq_zero.mp h).resolve_left hdiv
  have hstrip : ∀ ρ : zetaZeroConfig.carrier, |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := by
    intro ρ
    have h : IsNontrivialZero (ρ : ℂ) := ρ.2
    exact (WeilEF.abs_gammaOf_im_lt ⟨h.2.1, h.2.2⟩).le
  have hoff : ∀ ρ : zetaZeroConfig.carrier, ρ ∉ F →
      (1 + |(ρ : ℂ).im|) ^ 2 * ‖paperFT (C.testθ θ a) (gammaOf (ρ : ℂ))‖ ≤ Bd ∧
      (1 + |(ρ : ℂ).im|) ^ 2 *
        ‖paperFT (C.testθ θ a) ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖ ≤ Bd := by
    intro ρ hρ
    constructor
    · have h := C.testθ_off hθ0 hθ hρ₀ a hKp2 hKp (hstrip ρ) (hKz ρ hρ)
      rwa [WeilEF.gammaOf_re, ← hBd] at h
    · set ρr : zetaZeroConfig.carrier :=
        ⟨Zeta23.reflect (ρ : ℂ), zetaZeroConfig.reflect_mem (ρ : ℂ) ρ.2⟩ with hρr
      have hρrF : ρr ∉ F := by
        intro hmem
        rw [hF, Finset.mem_image] at hmem
        obtain ⟨ν, hν, hνe⟩ := hmem
        apply hρ
        rw [hF, Finset.mem_image]
        refine ⟨reflectSupport ν, C.reflect_mem_nodes hν, Subtype.ext ?_⟩
        have h1 : (ν : ℂ) = Zeta23.reflect (ρ : ℂ) := congrArg Subtype.val hνe
        change ((reflectSupport ν : XiDivisorSupport) : ℂ) = (ρ : ℂ)
        rw [reflectSupport_coe, h1, reflect_reflect]
      have hconj : (starRingEnd ℂ) (gammaOf (ρ : ℂ)) = gammaOf (ρr : ℂ) := by
        rw [hρr]; exact (gammaOf_reflect' _).symm
      have h := C.testθ_off hθ0 hθ hρ₀ a hKp2 hKp (hstrip ρr) (hKz ρr hρrF)
      rw [WeilEF.gammaOf_re, ← hBd] at h
      have him : (ρr : ℂ).im = (ρ : ℂ).im := by rw [hρr]; simp [Zeta23.reflect]
      rw [hconj, ← him]; exact h
  have hsplit := re_W_le_nodes_add_decay hC2 hcomp F hBd0 hoff
  have hsumF : ∑ ρ ∈ F, (zetaZeroConfig.Wsummand (C.testθ θ a) (C.testθ θ a) ρ).re =
      ∑ ν ∈ C.nodes, (zetaZeroConfig.Wsummand (C.testθ θ a) (C.testθ θ a) (toCarrier ν)).re :=
    Finset.sum_image fun x _ y _ h => toCarrier_injective h
  rw [hsumF] at hsplit
  obtain ⟨A, hA⟩ : ∃ x, x = Real.exp (θ * (C.t₀ - 3 / 4)) := ⟨_, rfl⟩
  rw [← hA]
  have hA0 : 0 < A := by rw [hA]; exact Real.exp_pos _
  obtain ⟨η, hη⟩ : ∃ x, x = 6 * coeffMass C.Q * expTail (C.Kθ θ) (1 / 2) (a - 1 / 4 - shw) :=
    ⟨_, rfl⟩
  have hη0 : 0 ≤ η := by rw [hη]; exact mul_nonneg (by positivity) (expTail_nonneg _ _ _)
  have hηB : η ≤ Bd / 2 := by
    obtain ⟨k₁, k₂, -, -, -, -, t0, -, -⟩ := C.Kθ_calculus hθ0 hθ hρ₀
    have e0 := t0 (1 / 2) (a - 1 / 4 - shw) (by norm_num)
    set τ := 2 ^ windowCount C.t₀ *
      expTail (tiltedPhi θ) (1 / 2 + 3 / 2 * windowCount C.t₀) (a - 1 / 4 - shw) with hτ
    have hτ0 : 0 ≤ τ := by rw [hτ]; exact mul_nonneg (by positivity) (expTail_nonneg _ _ _)
    have hΓ : 0 ≤ C.t₀ + 2 := by linarith [C.ht₀]
    have hdec : 2 * τ ≤ C.tailDecay θ a Kp := by
      unfold tailDecay
      rw [← hτ]
      have : 1 ≤ (1 + Kp) + 2 * Kp * (1 + (C.t₀ + 2)) + (1 + (C.t₀ + 2)) ^ 2 := by
        have : 0 ≤ 2 * Kp * (1 + (C.t₀ + 2)) := by positivity
        have : 0 ≤ (1 + (C.t₀ + 2)) ^ 2 := sq_nonneg _
        linarith
      nlinarith
    rw [hη, hBd]
    have := mul_le_mul_of_nonneg_left e0 (by positivity : (0 : ℝ) ≤ 6 * coeffMass C.Q)
    nlinarith
  have hfinal : A ≤ (6 + 2 * zeroSumZ) * Bd := by
    by_cases hηA : η ≤ A / 8
    · -- the node block
      have hpair : ∀ ν ∈ C.nodes,
          (zetaZeroConfig.Wsummand (C.testθ θ a) (C.testθ θ a) (toCarrier ν)).re ≤
            (zetaZeroConfig.mult (toCarrier ν) : ℝ) * (-(3 / 8) * A ^ 2) := by
        intro ν hν
        obtain ⟨Y, hY, hYn⟩ := C.testθ_at_node hθ0 hθ a hν
        obtain ⟨Y', hY', hY'n⟩ := C.testθ_at_node hθ0 hθ a (C.reflect_mem_nodes hν)
        rw [← hη] at hYn hY'n
        set γ := gammaOf (ν : ℂ) with hγ
        set γ' := gammaOf (reflectSupport ν : ℂ) with hγ'
        have hγγ' : γ' = (starRingEnd ℂ) γ := by rw [hγ', hγ]; exact gammaOf_reflectSupport ν
        have hconj : (starRingEnd ℂ) (gammaOf ((toCarrier ν : zetaZeroConfig.carrier) : ℂ)) = γ' := by
          rw [hγγ']; rfl
        have hγc : gammaOf ((toCarrier ν : zetaZeroConfig.carrier) : ℂ) = γ := rfl
        unfold ZeroConfig.Wsummand
        rw [hconj, hγc, hY, hY']
        set Aν := Real.exp (γ.re * θ) with hAν
        have hre' : γ'.re = γ.re := by rw [hγγ', Complex.conj_re]
        have he : ‖cexp (γ * θ)‖ = Aν := by
          rw [Complex.norm_exp, hAν]; congr 1; simp
        have he' : ‖cexp (γ' * θ)‖ = Aν := by
          rw [Complex.norm_exp, hAν, ← hre']; congr 1; simp
        have hmain : (cexp (γ * θ) * (starRingEnd ℂ) (cexp (γ' * θ)) *
            (sgn ν * (starRingEnd ℂ) (sgn (reflectSupport ν)))).re ≤ -(2 / 3) * Aν ^ 2 := by
          rw [C.sgn_mul_conj_sgn_reflect hν]
          have hc : (starRingEnd ℂ) (cexp (γ' * θ)) = cexp (γ * θ) := by
            rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, hγγ', Complex.conj_conj]
          rw [hc]
          have h := re_neg_cexp_two_mul_le hθ0 hθ (γ := γ) (abs_gammaOf_divisorSupport_im_lt ν).le
          have e : cexp (γ * θ) * cexp (γ * θ) * -1 = -(cexp (γ * θ) * cexp (γ * θ)) := by ring
          rw [e]
          have hAν' : Real.exp (θ * γ.re) = Aν := by rw [hAν, mul_comm]
          rw [hAν'] at h
          exact h
        have hAle : A ≤ Aν := by
          rw [hA, hAν]
          apply Real.exp_le_exp.mpr
          have hc := (C.node_coords hν).1
          have hγre : γ.re = (ν : ℂ).im := WeilEF.gammaOf_re _
          have hX := C.hX2
          have h1 : C.t₀ - 3 / 4 ≤ γ.re := by
            rw [hγre]; have := abs_lt.mp (lt_of_lt_of_le hc hX)
            linarith [this.1]
          nlinarith
        have hηAν : η ≤ Aν / 8 := hηA.trans (by linarith)
        have hpairle := re_tilted_node_pair_le (norm_sgn ν) (norm_sgn (reflectSupport ν)) he he'
          hmain hYn hY'n hη0 hηAν
        have e : (zetaZeroConfig.mult (toCarrier ν) : ℂ) * (cexp (γ * θ) * sgn ν - Y) *
            (starRingEnd ℂ) (cexp (γ' * θ) * sgn (reflectSupport ν) - Y') =
            ((zetaZeroConfig.mult (toCarrier ν) : ℝ) : ℂ) * ((cexp (γ * θ) * sgn ν - Y) *
              (starRingEnd ℂ) (cexp (γ' * θ) * sgn (reflectSupport ν) - Y')) := by
          push_cast; ring
        rw [e, Complex.re_ofReal_mul]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        refine hpairle.trans ?_
        have : A ^ 2 ≤ Aν ^ 2 := pow_le_pow_left₀ hA0.le hAle 2
        linarith
      have hblock : ∑ ν ∈ C.nodes,
          (zetaZeroConfig.Wsummand (C.testθ θ a) (C.testθ θ a) (toCarrier ν)).re ≤
            -(3 / 8) * A ^ 2 := by
        rw [← Finset.add_sum_erase _ _ hρ₀]
        have h1 := hpair ρ₀ hρ₀
        have hm : (1 : ℝ) ≤ zetaZeroConfig.mult (toCarrier ρ₀) := by
          exact_mod_cast zetaZeroConfig.one_le_mult _ (toCarrier ρ₀).2
        have hA2 : 0 ≤ A ^ 2 := sq_nonneg _
        have h2 : ∑ ν ∈ C.nodes.erase ρ₀,
            (zetaZeroConfig.Wsummand (C.testθ θ a) (C.testθ θ a) (toCarrier ν)).re ≤ 0 := by
          refine Finset.sum_nonpos fun ν hν => (hpair ν (Finset.mem_of_mem_erase hν)).trans ?_
          exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by nlinarith)
        nlinarith
      have hsq : A ^ 2 ≤ ((6 + 2 * zeroSumZ) * Bd) ^ 2 := by
        have h1 : (3 / 8) * A ^ 2 ≤ (5 / 4) * zeroSumZ * Bd ^ 2 := by linarith
        have h2 : (5 / 4) * zeroSumZ * Bd ^ 2 ≤ (3 / 8) * ((6 + 2 * zeroSumZ) * Bd) ^ 2 := by
          have hB2 : 0 ≤ Bd ^ 2 := sq_nonneg _
          have : (5 / 4) * zeroSumZ ≤ (3 / 8) * (6 + 2 * zeroSumZ) ^ 2 := by nlinarith
          calc (5 / 4) * zeroSumZ * Bd ^ 2 ≤ (3 / 8) * (6 + 2 * zeroSumZ) ^ 2 * Bd ^ 2 :=
                mul_le_mul_of_nonneg_right this hB2
            _ = (3 / 8) * ((6 + 2 * zeroSumZ) * Bd) ^ 2 := by ring
        nlinarith
      exact (pow_le_pow_iff_left₀ hA0.le (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
    · push Not at hηA
      nlinarith
  rw [hBd] at hfinal
  exact hfinal

end ClusterSetup


/-! ## The Landau-sharp cluster exclusion -/

local notation "Mt" => tiltedPhiTailConst

/-- **Tilted cluster exclusion, product form.** There is an absolute constant `K₀` such that, for
every tilt `0 ≤ θ < π/4`, if the level-`a` Hodge index holds (`a ≥ 1`), then every nontrivial zero
`ρ₀ = β₀ + it₀` with `β₀ > ½`, `t₀ ≥ 101` and `6 + 3N/2 ≤ 2π cos(2θ) e^{2X}` (`X = a - 3/8`,
`N` the window count) satisfies

`e^{θ(t₀ - 3/4)} ≤ K₀ 2^N (N+1) M (t₀+3)² e^{(6 + 3N/2) X} e^{-π cos(2θ) e^{2X}}`,

with `M = interpBound(t₀, β₀ - ½, N)`, of size `e^{π t₀/4 + O(N(log N + log 1/δ₀) + log t₀)}`.

The test is the cluster test of `HodgeClusterNyquistExclusion` built on the tilted kernel
`Φ(u + iθ)`, whose transform `e^{zθ} Ξ(z)` cancels the decay `e^{-πt/4}` of `Ξ` down to
`e^{-(π/4 - θ)t}`. Every zero outside the cluster sees two decaying truncation tails, so the
positive remainder is quadratic in the tail. -/
theorem hodgeIndex_excludes_tilted_cluster :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ {θ a : ℝ}, 0 ≤ θ → 2 * θ < π / 2 → 1 ≤ a →
      HodgeIndexAtLevel zetaZeroConfig a →
      ∀ {ρ₀ : ℂ}, ρ₀ ∈ zetaZeroConfig.carrier → 1 / 2 < ρ₀.re → 101 ≤ ρ₀.im →
        6 + 3 / 2 * (windowCount ρ₀.im : ℝ) ≤
          2 * π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8)) →
        Real.exp (θ * (ρ₀.im - 3 / 4)) ≤ K₀ * 2 ^ windowCount ρ₀.im *
          ((windowCount ρ₀.im + 1) *
            ClusterSetup.interpBound ρ₀.im (ρ₀.re - 1 / 2) (windowCount ρ₀.im)) *
          (ρ₀.im + 3) ^ 2 * Real.exp ((6 + 3 / 2 * windowCount ρ₀.im) * (a - 3 / 8)) *
          Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8)))) := by
  obtain ⟨Kp, hKp2, hKp⟩ := OffLinePairData.exists_plateau_constant
  have hS := zeroSumZ_nonneg
  have hM := tiltedPhiTailConst_nonneg
  refine ⟨96 * (6 + 2 * zeroSumZ) * Kp * (Mt + 1), by positivity, ?_⟩
  intro θ a hθ0 hθ ha hH ρ₀ hρ₀ hβ ht hlam
  obtain ⟨C, hCt, hCδ, ν₀, hν₀, -⟩ := exists_clusterSetup_node hρ₀ hβ ht
  have hraw := C.tilted_cluster_inequality hν₀ hθ0 hθ hH hKp2 hKp
  have hne : C.nodes.Nonempty := ⟨ν₀, hν₀⟩
  set W := windowCount C.t₀ with hWdef
  have hWt : windowCount C.t₀ = windowCount ρ₀.im := by rw [hCt]
  rw [← hWt, ← hCt, ← hCδ]
  -- the pieces
  obtain ⟨Mi, hMidef⟩ : ∃ x, x = ClusterSetup.interpBound C.t₀ C.δ₀ W := ⟨_, rfl⟩
  have hMi1 : 1 ≤ Mi := by rw [hMidef]; exact C.one_le_interpBound
  have hcM : coeffMass C.Q ≤ (W + 1) * Mi := by
    rw [hMidef]
    exact (C.coeffMass_le hne).trans (mul_le_mul_of_nonneg_left C.Mq_le_interpBound (by positivity))
  have hcM0 := coeffMass_nonneg C.Q
  have hsh : a - 1 / 4 - OffLinePairData.sh = a - 3 / 8 := by unfold OffLinePairData.sh; ring
  obtain ⟨τ, hτdef⟩ : ∃ x, x = expTail (tiltedPhi θ) (1 / 2 + 3 / 2 * W) (a - 3 / 8) := ⟨_, rfl⟩
  have hτ : τ ≤ 2 * Mt * Real.exp ((6 + 3 / 2 * W) * (a - 3 / 8)) *
      Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8)))) := by
    rw [hτdef]
    have h := expTail_tiltedPhi_le (c := 1 / 2 + 3 / 2 * W) (X := a - 3 / 8) hθ0 hθ
      (by positivity) (by rw [hWdef, hWt]; linarith)
    have e : (1 / 2 + 3 / 2 * (W : ℝ) + 11 / 2) = 6 + 3 / 2 * W := by ring
    rwa [e] at h
  have hτ0 : 0 ≤ τ := by rw [hτdef]; exact expTail_nonneg _ _ _
  have hdecay : C.tailDecay θ a Kp ≤ 8 * Kp * (C.t₀ + 3) ^ 2 * (2 ^ W * τ) := by
    unfold ClusterSetup.tailDecay
    rw [hsh, ← hτdef]
    have hs1 : (1 : ℝ) ≤ C.t₀ + 3 := by linarith [C.ht₀]
    have hs : 1 + (C.t₀ + 2) = C.t₀ + 3 := by ring
    rw [hs]
    have hin : (1 + Kp) + 2 * Kp * (C.t₀ + 3) + (C.t₀ + 3) ^ 2 ≤ 4 * Kp * (C.t₀ + 3) ^ 2 := by
      have hs2 : 2 ≤ (C.t₀ + 3) ^ 2 := by nlinarith
      have h1 : 1 + Kp ≤ Kp * (C.t₀ + 3) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hs2 (by linarith : (0 : ℝ) ≤ Kp)]
      have h2 : 2 * Kp * (C.t₀ + 3) ≤ 2 * Kp * (C.t₀ + 3) ^ 2 := by nlinarith
      have h3 : (C.t₀ + 3) ^ 2 ≤ Kp * (C.t₀ + 3) ^ 2 := by nlinarith
      linarith
    have hpw : (0 : ℝ) ≤ 2 ^ W * τ := by positivity
    nlinarith
  -- combine
  obtain ⟨E, hEdef⟩ : ∃ x, x = Real.exp ((6 + 3 / 2 * W) * (a - 3 / 8)) *
      Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8)))) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hτE : τ ≤ 2 * Mt * E := by rw [hEdef]; linarith [hτ]
  obtain ⟨T, hTdef⟩ : ∃ x, x = (C.t₀ + 3) ^ 2 := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hTdef]; positivity
  rw [← hTdef] at hdecay
  have hKp0 : 0 ≤ Kp := by linarith
  have hpw0 : (0 : ℝ) ≤ 2 ^ W := by positivity
  have step1 : C.tailDecay θ a Kp ≤ 8 * Kp * T * (2 ^ W * (2 * Mt * E)) :=
    hdecay.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hτE hpw0) (by positivity))
  have step2 : 6 * coeffMass C.Q * C.tailDecay θ a Kp ≤
      6 * ((W + 1) * Mi) * (8 * Kp * T * (2 ^ W * (2 * Mt * E))) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hcM (by norm_num)) step1
      (C.tailDecay_nonneg θ a hKp0) (by positivity)
  have step3 := hraw.trans (mul_le_mul_of_nonneg_left step2 (by positivity))
  have hMt : Mt ≤ Mt + 1 := by linarith
  calc Real.exp (θ * (C.t₀ - 3 / 4))
      ≤ (6 + 2 * zeroSumZ) * (6 * ((W + 1) * Mi) * (8 * Kp * T * (2 ^ W * (2 * Mt * E)))) :=
        step3
    _ ≤ (6 + 2 * zeroSumZ) * (6 * ((W + 1) * Mi) * (8 * Kp * T * (2 ^ W * (2 * (Mt + 1) * E)))) := by
        gcongr
    _ = 96 * (6 + 2 * zeroSumZ) * Kp * (Mt + 1) * 2 ^ W * ((W + 1) * Mi) * T * E := by ring
    _ = _ := by rw [hMidef, hTdef, hEdef]; ring

/-- **The Landau-sharp Nyquist horizon for clusters, logarithmic form.** Under the level-`a` Hodge
index (`a ≥ 1`), for every tilt `0 ≤ θ < π/4`, every nontrivial zero `ρ₀ = β₀ + it₀` with
`β₀ > ½`, `t₀ ≥ 101` and `6 + 3N/2 ≤ 2π cos(2θ) e^{2X}` (`X = a - 3/8`) satisfies

`π cos(2θ) e^{2X} ≤ (π/4 - θ) t₀ + π/4 + 3θ/4 + log(K₀ 2^N (N+1)) + L_N + 2 log(t₀+3) + (6 + 3N/2) X`,

where `L_N = log 32 + N log 3 + N log(32(N+1)) + 2N log(16e/δ₀) + 2 + N log 5 + 3C log t₀
- log δ₀`. With `θ = π/4 - ε`, `cos 2θ = sin 2ε`: no zero with `β₀ > ½` exists below
`t₀ = (π sin(2ε)/ε) e^{2X} - O(log t₀ (log log t₀ + log 1/δ₀) + N X)/ε`. The constant
`π sin(2ε)/ε` increases to `2π` as `ε → 0`, the Landau density at which the zero ordinates reach
the Nyquist rate of the level-`a` tests; at `θ = 0` it is `4`. -/
theorem hodgeIndex_tilted_cluster_horizon :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ {θ a : ℝ}, 0 ≤ θ → 2 * θ < π / 2 → 1 ≤ a →
      HodgeIndexAtLevel zetaZeroConfig a →
      ∀ {ρ₀ : ℂ}, ρ₀ ∈ zetaZeroConfig.carrier → 1 / 2 < ρ₀.re → 101 ≤ ρ₀.im →
        6 + 3 / 2 * (windowCount ρ₀.im : ℝ) ≤
          2 * π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8)) →
        π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8)) ≤
          (π / 4 - θ) * ρ₀.im + (π / 4 + 3 / 4 * θ) +
          Real.log (K₀ * 2 ^ windowCount ρ₀.im * (windowCount ρ₀.im + 1)) +
          (Real.log 32 + windowCount ρ₀.im * Real.log 3 +
            windowCount ρ₀.im * Real.log (32 * (windowCount ρ₀.im + 1 : ℝ)) +
            2 * windowCount ρ₀.im * Real.log (16 * Real.exp 1 / (ρ₀.re - 1 / 2)) +
            (2 + windowCount ρ₀.im * Real.log 5 + 3 * (windowLogConst * Real.log ρ₀.im)) -
            Real.log (ρ₀.re - 1 / 2)) +
          2 * Real.log (ρ₀.im + 3) + (6 + 3 / 2 * windowCount ρ₀.im) * (a - 3 / 8) := by
  obtain ⟨K₀, hK₀, h⟩ := hodgeIndex_excludes_tilted_cluster
  refine ⟨K₀, hK₀, fun {θ a} hθ0 hθ ha hH {ρ₀} hρ₀ hβ ht hlam => ?_⟩
  have hmain := h hθ0 hθ ha hH hρ₀ hβ ht hlam
  set W := windowCount ρ₀.im
  set δ₀ := ρ₀.re - 1 / 2
  have hδ : 0 < δ₀ := by simp only [δ₀]; linarith
  obtain ⟨Mi, hMidef⟩ : ∃ x, x = ClusterSetup.interpBound ρ₀.im δ₀ W := ⟨_, rfl⟩
  have hMi : 0 < Mi := by
    rw [hMidef]; unfold ClusterSetup.interpBound; have := Real.exp_pos 1; positivity
  rw [← hMidef] at hmain
  obtain ⟨Pc, hPc⟩ : ∃ x, x = K₀ * 2 ^ W * (W + 1 : ℝ) := ⟨_, rfl⟩
  have hPc0 : 0 < Pc := by rw [hPc]; positivity
  have ht3 : (0 : ℝ) < ρ₀.im + 3 := by linarith
  have hmain' : Real.exp (θ * (ρ₀.im - 3 / 4)) ≤ Pc * Mi * (ρ₀.im + 3) ^ 2 *
      Real.exp ((6 + 3 / 2 * W) * (a - 3 / 8) -
        π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8))) := by
    have e : Real.exp ((6 + 3 / 2 * W) * (a - 3 / 8) -
        π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8))) =
        Real.exp ((6 + 3 / 2 * W) * (a - 3 / 8)) *
          Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8)))) := by
      rw [← Real.exp_add]; ring_nf
    rw [hPc, e]
    calc Real.exp (θ * (ρ₀.im - 3 / 4)) ≤ _ := hmain
      _ = _ := by ring
  have hpos : 0 < Pc * Mi * (ρ₀.im + 3) ^ 2 *
      Real.exp ((6 + 3 / 2 * W) * (a - 3 / 8) -
        π * Real.cos (2 * θ) * Real.exp (2 * (a - 3 / 8))) := by positivity
  have hlog := Real.log_le_log (Real.exp_pos _) hmain'
  rw [Real.log_exp, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp,
    Real.log_mul (by positivity) (by positivity), Real.log_mul hPc0.ne' hMi.ne',
    Real.log_pow] at hlog
  have hLMi := log_interpBound ρ₀.im δ₀ hδ W
  rw [← hMidef] at hLMi
  rw [← hPc]
  push_cast at hlog
  nlinarith [hLMi]

end

end RHTower
