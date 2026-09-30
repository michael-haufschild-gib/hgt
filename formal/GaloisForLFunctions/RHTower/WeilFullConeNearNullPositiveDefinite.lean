import GaloisForLFunctions.RHTower.WeilFullConeMinorantRigidity
import GaloisForLFunctions.HTGeometry.PrimeDirichletPositiveDefinite

/-!
# The Riemann-kernel potential of a Weil-positive deviation is negative definite

Let `lam` be full-cone Weil-positive, `a(n) = (lam(n) − Λ(n))/√n` for `n ≥ 2`, and `K` the
autocorrelation of Riemann's kernel `Φ`. The potential

`ψ(y) = Σ_n a(n) (K(y + log n) + K(y − log n))`

satisfies `Σ_{i,j} c_i c_j ψ(x_j − x_i) ≤ 0` for all real `c_i`, `x_i`
(`sum_mul_deviationPotential_nonpos`). Hence `−ψ` is a continuous positive-definite function
(`positiveDefiniteOnReal_neg_deviationPotential`).

**The test.** `f_L = Σ_j c_j Φχ_L(· − x_j)` is a combination of translated truncated Riemann
kernels.
- Its transform is `(Σ_j c_j e^{izx_j}) (Φχ_L)^(z)`, so its zero side is at most
  `(Σ_j |c_j| e^{|x_j|/2})²` times the near-radical energy of `Φχ_L`, which tends to `0`.
- Its autocorrelation is `Σ_{i,j} c_i c_j K_L(y + x_j − x_i)`.

Weil positivity bounds the pairing of `a` with this autocorrelation by the zero side.

**The limit.** `K_L ≤ K ≤ C e^{−2|y|}` and `K_L → K` pointwise. Weil positivity gives
`|a(n)| ≤ 2 log n + C₀`, so dominated convergence passes the pairing to `ψ`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower.WeilExcess

noncomputable section

/-! ## The normalized deviation and its potential -/

/-- The normalized deviation `(lam(n) − Λ(n))/√n` on `n ≥ 2`. -/
def weilDeviation (lam : ℕ → ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n then (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n else 0

/-- The Riemann-kernel potential `ψ(y) = Σ_n a(n)(K(y + log n) + K(y − log n))`. -/
def deviationPotential (lam : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑' n : ℕ, weilDeviation lam n *
    (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n))

/-- The truncated potential, with `K_L` in place of `K`. -/
def truncatedDeviationPotential (lam : ℕ → ℝ) (L y : ℝ) : ℝ :=
  ∑' n : ℕ, weilDeviation lam n *
    (truncatedRiemannAutocorr L (y + Real.log n) + truncatedRiemannAutocorr L (y - Real.log n))

/-- Weil positivity bounds the normalized deviation logarithmically. -/
theorem exists_abs_weilDeviation_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |weilDeviation lam n| ≤ 2 * Real.log n + C := by
  obtain ⟨C₀, hC₀⟩ := abs_le_of_weilPositive (weilPositive_of_weilPositiveFull hW)
  refine ⟨|C₀|, abs_nonneg _, fun n => ?_⟩
  unfold weilDeviation
  split_ifs with hn
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have hs1 : 1 ≤ Real.sqrt n := by
      rw [Real.one_le_sqrt]; exact_mod_cast (show 1 ≤ n by omega)
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hΛ0 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log n :=
      ArithmeticFunction.vonMangoldt_le_log
    have hl := hC₀ n hn
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    have h1 : |lam n - ArithmeticFunction.vonMangoldt n| ≤ |lam n| + Real.log n := by
      calc |lam n - ArithmeticFunction.vonMangoldt n|
          ≤ |lam n| + |(ArithmeticFunction.vonMangoldt n : ℝ)| := abs_sub _ _
        _ ≤ |lam n| + Real.log n := by rw [abs_of_nonneg hΛ0]; linarith
    have h2 : Real.log n ≤ Real.log n * Real.sqrt n := le_mul_of_one_le_right hlog hs1
    have h3 : C₀ * Real.sqrt n ≤ |C₀| * Real.sqrt n :=
      mul_le_mul_of_nonneg_right (le_abs_self C₀) hs.le
    nlinarith
  · rw [abs_zero]; positivity

/-! ## Decay and convergence of the kernel -/

/-- Exponential decay of the autocorrelation of Riemann's kernel. -/
theorem exists_riemannAutocorr_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, riemannAutocorr y ≤ C * Real.exp (-(2 * |y|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_exp (B := 4) (by norm_num)
  have hΦ : ∀ x, riemannKernelReal x ≤ C * Real.exp (-(4 * |x|)) := by
    intro x
    have h := hC x
    rwa [riemannPhiKernel_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (riemannKernelReal_pos x)] at h
  refine ⟨C ^ 2 * ∫ t : ℝ, Real.exp (-|t|),
    mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => (Real.exp_pos _).le), fun y => ?_⟩
  unfold riemannAutocorr
  have hmaj : Integrable fun t : ℝ => C ^ 2 * Real.exp (-(2 * |y|)) * Real.exp (-|t|) :=
    integrable_exp_neg_abs.const_mul _
  calc (∫ t, riemannKernelReal t * riemannKernelReal (t - y))
      ≤ ∫ t : ℝ, C ^ 2 * Real.exp (-(2 * |y|)) * Real.exp (-|t|) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun t => mul_nonneg
          (riemannKernelReal_pos t).le (riemannKernelReal_pos _).le) hmaj
          (Eventually.of_forall fun t => ?_)
        have h1 := hΦ t
        have h2 := hΦ (t - y)
        have hexp : Real.exp (-(4 * |t|)) * Real.exp (-(4 * |t - y|)) ≤
            Real.exp (-(2 * |y|)) * Real.exp (-|t|) := by
          rw [← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hy : |y| ≤ |t| + |t - y| := by
            rw [abs_le]
            constructor <;>
              linarith [le_abs_self t, neg_abs_le t, le_abs_self (t - y), neg_abs_le (t - y)]
          linarith [abs_nonneg t, abs_nonneg (t - y)]
        calc riemannKernelReal t * riemannKernelReal (t - y)
            ≤ (C * Real.exp (-(4 * |t|))) * (C * Real.exp (-(4 * |t - y|))) :=
              mul_le_mul h1 h2 (riemannKernelReal_pos _).le (by positivity)
          _ = C ^ 2 * (Real.exp (-(4 * |t|)) * Real.exp (-(4 * |t - y|))) := by ring
          _ ≤ C ^ 2 * (Real.exp (-(2 * |y|)) * Real.exp (-|t|)) :=
              mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
          _ = _ := by ring
    _ = C ^ 2 * (∫ t : ℝ, Real.exp (-|t|)) * Real.exp (-(2 * |y|)) := by
        rw [integral_const_mul]; ring

theorem riemannAutocorr_nonneg (y : ℝ) : 0 ≤ riemannAutocorr y :=
  integral_nonneg fun t => mul_nonneg (riemannKernelReal_pos t).le (riemannKernelReal_pos _).le

theorem riemannAutocorr_neg (y : ℝ) : riemannAutocorr (-y) = riemannAutocorr y := by
  unfold riemannAutocorr
  rw [← integral_sub_right_eq_self (fun t => riemannKernelReal t * riemannKernelReal (t - -y)) y]
  congr 1; funext t
  rw [show t - y - -y = t by ring, mul_comm]

/-- The truncated autocorrelation converges to the full one. -/
theorem tendsto_truncatedRiemannAutocorr (y : ℝ) :
    Tendsto (fun L => truncatedRiemannAutocorr L y) atTop (𝓝 (riemannAutocorr y)) := by
  unfold truncatedRiemannAutocorr riemannAutocorr
  refine tendsto_integral_filter_of_dominated_convergence
    (fun t => riemannKernelReal t * riemannKernelReal (t - y)) ?_ ?_
    (integrable_riemannKernelReal_mul y) ?_
  · exact Eventually.of_forall fun L =>
      ((continuous_truncatedRiemannKernelReal L).mul
        ((continuous_truncatedRiemannKernelReal L).comp
          (continuous_id.sub continuous_const))).aestronglyMeasurable
  · refine Eventually.of_forall fun L => Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (truncatedRiemannKernelReal_nonneg L t)
      (truncatedRiemannKernelReal_nonneg L _))]
    exact mul_le_mul (truncatedRiemannKernelReal_le L t) (truncatedRiemannKernelReal_le L _)
      (truncatedRiemannKernelReal_nonneg L _) (riemannKernelReal_pos t).le
  · refine Eventually.of_forall fun t => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (|t| + |t - y| + 1)] with L hL
    have h1 : |t| ≤ L - 1 := by linarith [abs_nonneg (t - y)]
    have h2 : |t - y| ≤ L - 1 := by linarith [abs_nonneg t]
    simp only [truncatedRiemannKernelReal, bulkCutoff_eq_one h1, bulkCutoff_eq_one h2, mul_one]

/-- A summable majorant for the terms of the potential, uniform on `|y| ≤ R`. -/
theorem summable_log_add_mul_inv_sq {C : ℝ} (hC : 0 ≤ C) :
    Summable fun n : ℕ => (2 * Real.log n + C) * ((n : ℝ) ^ 2)⁻¹ := by
  have hs : Summable fun n : ℕ => (4 + C) * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · have := Real.log_natCast_nonneg n
    positivity
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
      Real.log_le_rpow_div hn0.le (by norm_num)
    have hsq : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
    have e1 : (n : ℝ) ^ (2 : ℕ) = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_add hn0, ← Real.rpow_natCast]; norm_num
    have hp : (0 : ℝ) < (n : ℝ) ^ (3 / 2 : ℝ) := by positivity
    have hq : (0 : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := by positivity
    rw [e1, mul_inv, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hp.le)
    rw [← div_eq_mul_inv, div_le_iff₀ hq]
    nlinarith

theorem potential_term_le {K : ℝ → ℝ} {C₁ : ℝ} (hK0 : ∀ y, 0 ≤ K y)
    (hK : ∀ y, K y ≤ C₁ * Real.exp (-(2 * |y|))) {C : ℝ} {a : ℕ → ℝ}
    (ha : ∀ n, |a n| ≤ 2 * Real.log n + C) (hC : 0 ≤ C) {R y : ℝ} (hy : |y| ≤ R) (n : ℕ)
    (hn : 1 ≤ n) :
    |a n * (K (y + Real.log n) + K (y - Real.log n))| ≤
      (2 * C₁ * Real.exp (2 * R)) * ((2 * Real.log n + C) * ((n : ℝ) ^ 2)⁻¹) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hexp : ∀ z, |z| ≤ R → ∀ s : ℝ, s = 1 ∨ s = -1 →
      K (z + s * Real.log n) ≤ C₁ * Real.exp (2 * R) * ((n : ℝ) ^ 2)⁻¹ := by
    intro z hz s hs
    refine (hK _).trans ?_
    have hC₁ : 0 ≤ C₁ := by
      have := (hK0 0).trans (hK 0); simp at this; exact this
    have hlogn : Real.exp (-(2 * Real.log n)) = ((n : ℝ) ^ 2)⁻¹ := by
      rw [show -(2 * Real.log n) = -(Real.log ((n : ℝ) ^ 2)) by rw [Real.log_pow]; push_cast; ring,
        Real.exp_neg, Real.exp_log (by positivity)]
    have habs : 2 * Real.log n - 2 * R ≤ 2 * |z + s * Real.log n| := by
      rcases hs with rfl | rfl
      · have := abs_sub_abs_le_abs_add (Real.log n) z
        rw [abs_of_nonneg hlog] at this
        have : Real.log n - |z| ≤ |z + 1 * Real.log n| := by
          rw [one_mul, add_comm]; linarith [abs_sub_abs_le_abs_sub (Real.log n) (-z), abs_neg z,
            show Real.log n - -z = Real.log n + z by ring]
        linarith
      · have := abs_sub_abs_le_abs_sub (Real.log n) z
        rw [abs_of_nonneg hlog] at this
        have e : |z + -1 * Real.log n| = |Real.log n - z| := by
          rw [show z + -1 * Real.log n = -(Real.log n - z) by ring, abs_neg]
        rw [e]; linarith
    calc C₁ * Real.exp (-(2 * |z + s * Real.log n|))
        ≤ C₁ * Real.exp (2 * R - 2 * Real.log n) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC₁
      _ = C₁ * Real.exp (2 * R) * ((n : ℝ) ^ 2)⁻¹ := by
          rw [sub_eq_add_neg, Real.exp_add, hlogn]; ring
  have e1 := hexp y hy 1 (Or.inl rfl)
  have e2 := hexp y hy (-1) (Or.inr rfl)
  rw [one_mul] at e1
  rw [show y + -1 * Real.log n = y - Real.log n by ring] at e2
  have hk0 : 0 ≤ K (y + Real.log n) + K (y - Real.log n) := add_nonneg (hK0 _) (hK0 _)
  rw [abs_mul, abs_of_nonneg hk0]
  have ha' := ha n
  have hb : 0 ≤ 2 * Real.log n + C := by linarith
  calc |a n| * (K (y + Real.log n) + K (y - Real.log n))
      ≤ (2 * Real.log n + C) * (2 * (C₁ * Real.exp (2 * R) * ((n : ℝ) ^ 2)⁻¹)) :=
        mul_le_mul ha' (by linarith) hk0 hb
    _ = _ := by ring

theorem weilDeviation_zero (lam : ℕ → ℝ) : weilDeviation lam 0 = 0 := by
  simp [weilDeviation]

/-- A summable majorant for the potential terms, uniform on `|y| ≤ R`, for any kernel dominated
by `C₁ e^{−2|y|}`. -/
theorem norm_potential_term_le {K : ℝ → ℝ} {C₁ : ℝ} (hK0 : ∀ y, 0 ≤ K y)
    (hK : ∀ y, K y ≤ C₁ * Real.exp (-(2 * |y|))) {C : ℝ} {a : ℕ → ℝ}
    (ha : ∀ n, |a n| ≤ 2 * Real.log n + C) (ha0 : a 0 = 0) (hC : 0 ≤ C) {R y : ℝ}
    (hy : |y| ≤ R) (n : ℕ) :
    ‖a n * (K (y + Real.log n) + K (y - Real.log n))‖ ≤
      (2 * C₁ * Real.exp (2 * R)) * ((2 * Real.log n + C) * ((n : ℝ) ^ 2)⁻¹) := by
  rw [Real.norm_eq_abs]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ha0]
  exact potential_term_le hK0 hK ha hC hy n hn

theorem summable_potential_term {K : ℝ → ℝ} {C₁ : ℝ} (hK0 : ∀ y, 0 ≤ K y)
    (hK : ∀ y, K y ≤ C₁ * Real.exp (-(2 * |y|))) {C : ℝ} {a : ℕ → ℝ}
    (ha : ∀ n, |a n| ≤ 2 * Real.log n + C) (ha0 : a 0 = 0) (hC : 0 ≤ C) (y : ℝ) :
    Summable fun n : ℕ => a n * (K (y + Real.log n) + K (y - Real.log n)) :=
  Summable.of_norm_bounded ((summable_log_add_mul_inv_sq hC).mul_left _)
    (norm_potential_term_le hK0 hK ha ha0 hC (le_refl |y|))

theorem continuous_riemannAutocorr : Continuous riemannAutocorr := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_exp (B := 1) zero_le_one
  have hΦ : ∀ x, riemannKernelReal x ≤ C * Real.exp (-|x|) := by
    intro x
    have h := hC x
    rw [riemannPhiKernel_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (riemannKernelReal_pos x), one_mul] at h
    exact h
  unfold riemannAutocorr
  refine continuous_of_dominated (bound := fun t => C ^ 2 * Real.exp (-|t|))
    (fun y => ((continuous_riemannKernelReal.mul (continuous_riemannKernelReal.comp
      (continuous_id.sub continuous_const))).aestronglyMeasurable))
    (fun y => Eventually.of_forall fun t => ?_) (integrable_exp_neg_abs.const_mul _)
    (Eventually.of_forall fun t => continuous_const.mul
      (continuous_riemannKernelReal.comp (continuous_const.sub continuous_id)))
  have h1 := hΦ t
  have h2 := hΦ (t - y)
  have p1 := riemannKernelReal_pos t
  have p2 := riemannKernelReal_pos (t - y)
  have he : Real.exp (-|t - y|) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg (t - y)])
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos p1 p2)]
  calc riemannKernelReal t * riemannKernelReal (t - y)
      ≤ (C * Real.exp (-|t|)) * (C * Real.exp (-|t - y|)) := mul_le_mul h1 h2 p2.le (by positivity)
    _ ≤ (C * Real.exp (-|t|)) * (C * 1) := by gcongr
    _ = C ^ 2 * Real.exp (-|t|) := by ring

theorem summable_deviationPotential_term {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) :
    Summable fun n : ℕ => weilDeviation lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_weilDeviation_le hW
  obtain ⟨C₁, -, hC₁⟩ := exists_riemannAutocorr_le
  exact summable_potential_term riemannAutocorr_nonneg hC₁ hC (weilDeviation_zero lam) hC0 y

theorem continuous_deviationPotential {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Continuous (deviationPotential lam) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_weilDeviation_le hW
  obtain ⟨C₁, -, hC₁⟩ := exists_riemannAutocorr_le
  rw [continuous_iff_continuousAt]
  intro y₀
  have hon : ContinuousOn (deviationPotential lam) (Metric.ball y₀ 1) := by
    refine continuousOn_tsum (fun n => ?_)
      ((summable_log_add_mul_inv_sq hC0).mul_left (2 * C₁ * Real.exp (2 * (|y₀| + 1))))
      (fun n y hy => norm_potential_term_le riemannAutocorr_nonneg hC₁ hC
        (weilDeviation_zero lam) hC0 ?_ n)
    · exact (continuous_const.mul ((continuous_riemannAutocorr.comp
        (continuous_id.add continuous_const)).add
        (continuous_riemannAutocorr.comp (continuous_id.sub continuous_const)))).continuousOn
    · rw [Metric.mem_ball, Real.dist_eq] at hy
      have := abs_sub_abs_le_abs_sub y y₀
      linarith
  exact hon.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))

theorem deviationPotential_neg (lam : ℕ → ℝ) (y : ℝ) :
    deviationPotential lam (-y) = deviationPotential lam y := by
  unfold deviationPotential
  refine tsum_congr fun n => ?_
  rw [show -y + Real.log n = -(y - Real.log n) by ring,
    show -y - Real.log n = -(y + Real.log n) by ring, riemannAutocorr_neg, riemannAutocorr_neg,
    add_comm (riemannAutocorr (y - Real.log n))]

/-- The truncated potential converges to the full potential. -/
theorem tendsto_truncatedDeviationPotential {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) :
    Tendsto (fun L => truncatedDeviationPotential lam L y) atTop
      (𝓝 (deviationPotential lam y)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_weilDeviation_le hW
  obtain ⟨C₁, -, hC₁⟩ := exists_riemannAutocorr_le
  have hK : ∀ L z, truncatedRiemannAutocorr L z ≤ C₁ * Real.exp (-(2 * |z|)) :=
    fun L z => (truncatedRiemannAutocorr_le_riemannAutocorr L z).trans (hC₁ z)
  refine tendsto_tsum_of_dominated_convergence
    ((summable_log_add_mul_inv_sq hC0).mul_left (2 * C₁ * Real.exp (2 * |y|))) (fun n => ?_)
    (Eventually.of_forall fun L n => norm_potential_term_le (truncatedRiemannAutocorr_nonneg L)
      (hK L) hC (weilDeviation_zero lam) hC0 le_rfl n)
  exact ((tendsto_truncatedRiemannAutocorr _).add (tendsto_truncatedRiemannAutocorr _)).const_mul _

/-! ## Translated combs of truncated kernels -/

/-- The real profile `Σ_j c_j Φχ_L(u − x_j)`. -/
def shiftCombReal {ι : Type*} (s : Finset ι) (c x : ι → ℝ) (L u : ℝ) : ℝ :=
  ∑ j ∈ s, c j * truncatedRiemannKernelReal L (u - x j)

/-- The complex test `Σ_j c_j Φχ_L(· − x_j)`. -/
def shiftComb {ι : Type*} (s : Finset ι) (c x : ι → ℝ) (L : ℝ) (u : ℝ) : ℂ :=
  (shiftCombReal s c x L u : ℂ)

variable {ι : Type*} (s : Finset ι) (c x : ι → ℝ) (L : ℝ)

theorem shiftComb_eq_sum :
    shiftComb s c x L = fun u => ∑ j ∈ s, (c j : ℂ) * truncatedRiemannKernel L (u - x j) := by
  funext u
  simp only [shiftComb, shiftCombReal, truncatedRiemannKernel_eq]
  push_cast; rfl

theorem contDiff_shiftComb : ContDiff ℝ 2 (shiftComb s c x L) := by
  rw [shiftComb_eq_sum]
  have h := contDiff_nearRadicalTest L (fun _ : Fin 1 => (1 : ℂ))
  exact ContDiff.sum fun j _ => contDiff_const.mul (h.comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_shiftComb : HasCompactSupport (shiftComb s c x L) := by
  set M : ℝ := ∑ j ∈ s, |x j| with hM
  refine HasCompactSupport.intro (isCompact_Icc (a := -(|L| + M)) (b := |L| + M)) fun u hu => ?_
  have hu' : |L| + M < |u| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hu
    rcases hu with hu | hu
    · linarith [neg_abs_le u]
    · linarith [le_abs_self u]
  simp only [shiftComb, shiftCombReal, Complex.ofReal_eq_zero]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hxj : |x j| ≤ M := Finset.single_le_sum (f := fun j => |x j|)
    (fun j _ => abs_nonneg (x j)) hj
  have : L ≤ |u - x j| := by
    have := abs_sub_abs_le_abs_sub u (x j)
    linarith [le_abs_self L]
  rw [truncatedRiemannKernelReal_eq_zero_of_le this, mul_zero]

/-- The transform of the translated comb. -/
theorem paperFT_shiftComb (z : ℂ) :
    paperFT (shiftComb s c x L) z =
      (∑ j ∈ s, (c j : ℂ) * Complex.exp (I * z * x j)) *
        paperFT (truncatedRiemannKernel L) z := by
  have hint : ∀ j ∈ s, Integrable fun u : ℝ =>
      (c j : ℂ) * truncatedRiemannKernel L (u - x j) * Complex.exp (I * z * u) :=
    fun j _ => by
      simpa [mul_assoc] using (integrable_translate_mul_cexp L (x j) z).const_mul (c j : ℂ)
  rw [shiftComb_eq_sum]
  unfold paperFT
  have hsplit : (fun u : ℝ => (∑ j ∈ s, (c j : ℂ) * truncatedRiemannKernel L (u - x j)) *
      Complex.exp (I * z * u)) = fun u : ℝ => ∑ j ∈ s,
        (c j : ℂ) * truncatedRiemannKernel L (u - x j) * Complex.exp (I * z * u) := by
    funext u; rw [Finset.sum_mul]
  rw [hsplit, integral_finsetSum _ hint, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e := paperFT_comp_sub (truncatedRiemannKernel L) (x j) z
  unfold paperFT at e
  rw [show (fun u : ℝ => (c j : ℂ) * truncatedRiemannKernel L (u - x j) * Complex.exp (I * z * u))
      = fun u : ℝ => (c j : ℂ) * (truncatedRiemannKernel L (u - x j) * Complex.exp (I * z * u))
      from funext fun u => by ring, integral_const_mul, e]
  ring

theorem norm_shiftMultiplier_le {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖∑ j ∈ s, (c j : ℂ) * Complex.exp (I * z * x j)‖ ≤ ∑ j ∈ s, |c j| * Real.exp (|x j| / 2) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
  have hre : (I * z * ((x j : ℝ) : ℂ)).re = -(z.im * x j) := by simp [Complex.mul_re]
  rw [hre]
  have h1 : |z.im * x j| ≤ |x j| / 2 := by
    rw [abs_mul]; nlinarith [abs_nonneg (x j), abs_nonneg z.im]
  linarith [neg_abs_le (z.im * x j)]

/-- The zero side of the translated comb. -/
theorem norm_W_shiftComb_le {Λ : ℝ} (hΛ : ∀ y : ℝ, |deriv Real.smoothTransition y| ≤ Λ) :
    ‖zetaZeroConfig.W (shiftComb s c x L) (shiftComb s c x L)‖ ≤
      (∑ j ∈ s, |c j| * Real.exp (|x j| / 2)) ^ 2 *
        ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) := by
  set B := ∑ j ∈ s, |c j| * Real.exp (|x j| / 2) with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => by positivity
  have hE0 := truncatedRiemannTailEnergy_nonneg L
  have h := norm_W_le_of_zero_bound (f := shiftComb s c x L)
    (E := B * truncatedRiemannTailEnergy L) (by positivity) (fun ρ => ?_)
  · calc _ ≤ (5 / 4) * zetaInvSqSum * (B * truncatedRiemannTailEnergy L) ^ 2 := h
      _ = _ := by ring
  have hmem := ρ.2
  have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
    have h : IsNontrivialZero (ρ : ℂ) := hmem
    exact ⟨h.2.1, h.2.2⟩
  have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
  have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
    rw [Complex.conj_im, abs_neg]; exact hIm
  obtain ⟨hv1, hv2⟩ := truncatedRiemannKernel_zero_bound L hΛ ρ
  constructor
  · rw [paperFT_shiftComb, norm_mul]
    have hm := norm_shiftMultiplier_le s c x hIm
    calc (1 + |(ρ : ℂ).im|) * (‖∑ j ∈ s, (c j : ℂ) * Complex.exp (I * gammaOf ρ * x j)‖ *
          ‖paperFT (truncatedRiemannKernel L) (gammaOf ρ)‖)
        = ‖∑ j ∈ s, (c j : ℂ) * Complex.exp (I * gammaOf ρ * x j)‖ *
          ((1 + |(ρ : ℂ).im|) * ‖paperFT (truncatedRiemannKernel L) (gammaOf ρ)‖) := by ring
      _ ≤ B * truncatedRiemannTailEnergy L := mul_le_mul hm hv1 (by positivity) hB0
  · rw [paperFT_shiftComb, norm_mul]
    have hm := norm_shiftMultiplier_le s c x hIm'
    calc (1 + |(ρ : ℂ).im|) *
          (‖∑ j ∈ s, (c j : ℂ) * Complex.exp (I * (starRingEnd ℂ) (gammaOf ρ) * x j)‖ *
          ‖paperFT (truncatedRiemannKernel L) ((starRingEnd ℂ) (gammaOf ρ))‖)
        = ‖∑ j ∈ s, (c j : ℂ) * Complex.exp (I * (starRingEnd ℂ) (gammaOf ρ) * x j)‖ *
          ((1 + |(ρ : ℂ).im|) *
            ‖paperFT (truncatedRiemannKernel L) ((starRingEnd ℂ) (gammaOf ρ))‖) := by ring
      _ ≤ B * truncatedRiemannTailEnergy L := mul_le_mul hm hv2 (by positivity) hB0

/-- The autocorrelation of the translated comb. -/
theorem weilTest_shiftComb (y : ℝ) :
    EF.weilTest (shiftComb s c x L) (shiftComb s c x L) y =
      ((∑ i ∈ s, ∑ j ∈ s, c i * c j * truncatedRiemannAutocorr L (y + x j - x i) : ℝ) : ℂ) := by
  have e := weilTest_ofReal_eq (shiftCombReal s c x L) y
  rw [show (fun u => (shiftCombReal s c x L u : ℂ)) = shiftComb s c x L from rfl] at e
  rw [e]
  congr 1
  have h := integral_translateComb_autocorr s c x (continuous_truncatedRiemannKernelReal L)
    (hasCompactSupport_truncatedRiemannKernelReal L) y
  unfold shiftCombReal
  exact h

/-! ## The negative-definite inequality -/

/-- At a fixed truncation, Weil positivity bounds the quadratic form of the truncated potential
by the zero side of the translated comb. -/
theorem sum_mul_truncatedDeviationPotential_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∑ i ∈ s, ∑ j ∈ s, c i * c j * truncatedDeviationPotential lam L (x j - x i) ≤
      ‖zetaZeroConfig.W (shiftComb s c x L) (shiftComb s c x L)‖ := by
  set f := shiftComb s c x L with hf
  have hfd := contDiff_shiftComb s c x L
  have hfc := hasCompactSupport_shiftComb s c x L
  set k := EF.weilTest f f with hk
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  set kr : ℝ → ℝ := fun y => ∑ i ∈ s, ∑ j ∈ s,
    c i * c j * truncatedRiemannAutocorr L (y + x j - x i) with hkr
  have hkeq : ∀ y, k y = ((kr y : ℝ) : ℂ) := fun y => weilTest_shiftComb s c x L y
  have hpos := hW f hfd hfc
  rw [weilFullFunctional_eq_sub lam hkc, ← weilFullFunctional_vonMangoldt,
    ← zeta_W_eq_weilFullFunctional hfd hfc] at hpos
  set a := weilDeviation lam with ha
  have hsum := summable_primeAtoms a hkc
  change 0 ≤ (zetaZeroConfig.W f f -
    ∑' n : ℕ, ((a n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))).re at hpos
  rw [Complex.sub_re, Complex.re_tsum hsum] at hpos
  have hre : ∀ n : ℕ, (((a n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))).re =
      a n * (kr (Real.log n) + kr (-Real.log n)) := by
    intro n
    rw [hkeq, hkeq, ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [tsum_congr hre] at hpos
  have hle : ∑' n : ℕ, a n * (kr (Real.log n) + kr (-Real.log n)) ≤
      ‖zetaZeroConfig.W f f‖ := by
    have := Complex.re_le_norm (zetaZeroConfig.W f f); linarith
  refine le_trans (le_of_eq ?_) hle
  obtain ⟨C, hC0, hC⟩ := exists_abs_weilDeviation_le hW
  obtain ⟨C₁, -, hC₁⟩ := exists_truncatedRiemannAutocorr_le
  have hsm : ∀ d : ℝ, Summable fun n : ℕ => a n *
      (truncatedRiemannAutocorr L (d + Real.log n) + truncatedRiemannAutocorr L (d - Real.log n)) :=
    fun d => summable_potential_term (truncatedRiemannAutocorr_nonneg L) (hC₁ L) hC
      (weilDeviation_zero lam) hC0 d
  have hterm : ∀ n : ℕ, a n * (kr (Real.log n) + kr (-Real.log n)) =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * (a n * (truncatedRiemannAutocorr L ((x j - x i) + Real.log n)
        + truncatedRiemannAutocorr L ((x j - x i) - Real.log n))) := by
    intro n
    simp only [hkr, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show Real.log n + x j - x i = (x j - x i) + Real.log n by ring,
      show -Real.log n + x j - x i = (x j - x i) - Real.log n by ring]
    ring
  rw [tsum_congr hterm, Summable.tsum_finsetSum fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Summable.tsum_finsetSum fun j _ => ((hsm _).mul_left _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tsum_mul_left]
    rfl
  · exact summable_sum fun j _ => (hsm _).mul_left _

/-- **The potential is negative definite.** For a full-cone Weil-positive `lam`, all real
coefficients `c` and all shifts `x`, `Σ_{i,j} c_i c_j ψ(x_j − x_i) ≤ 0`. -/
theorem sum_mul_deviationPotential_nonpos {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∑ i ∈ s, ∑ j ∈ s, c i * c j * deviationPotential lam (x j - x i) ≤ 0 := by
  obtain ⟨Λ', -, hΛ'⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  set B := ∑ j ∈ s, |c j| * Real.exp (|x j| / 2) with hB
  have hlim : Tendsto (fun L => ∑ i ∈ s, ∑ j ∈ s,
      c i * c j * truncatedDeviationPotential lam L (x j - x i)) atTop
      (𝓝 (∑ i ∈ s, ∑ j ∈ s, c i * c j * deviationPotential lam (x j - x i))) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      (tendsto_truncatedDeviationPotential hW _).const_mul _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨L₀, hL₀⟩ := exists_nearRadicalEnergy_le (ε := ε / (B ^ 2 + 1)) (by positivity)
  have hev : ∀ᶠ L in atTop, ∑ i ∈ s, ∑ j ∈ s,
      c i * c j * truncatedDeviationPotential lam L (x j - x i) ≤ ε := by
    filter_upwards [eventually_ge_atTop L₀] with L hL
    have hB2 : 0 ≤ B ^ 2 := sq_nonneg _
    calc _ ≤ ‖zetaZeroConfig.W (shiftComb s c x L) (shiftComb s c x L)‖ :=
          sum_mul_truncatedDeviationPotential_le s c x L hW
      _ ≤ B ^ 2 * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) :=
          norm_W_shiftComb_le s c x L hΛ'
      _ ≤ B ^ 2 * (ε / (B ^ 2 + 1)) := mul_le_mul_of_nonneg_left (hL₀ L hL) hB2
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have := le_of_tendsto hlim hev
  linarith

/-- **`−ψ` is a positive-definite function.** -/
theorem positiveDefiniteOnReal_neg_deviationPotential {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal
      (fun y => ((-deviationPotential lam y : ℝ) : ℂ)) := by
  intro N t v
  set φ : Fin N → Fin N → ℝ := fun i j => -deviationPotential lam (t j - t i) with hφ
  have hsym : ∀ i j, φ i j = φ j i := fun i j => by
    simp only [hφ]; rw [← deviationPotential_neg, neg_sub]
  set u : Fin N → ℝ := fun i => (v i).re
  set w : Fin N → ℝ := fun i => (v i).im
  refine ⟨∑ i, ∑ j, (u i * u j + w i * w j) * φ i j, ?_, ?_⟩
  · have h1 := sum_mul_deviationPotential_nonpos Finset.univ u t hW
    have h2 := sum_mul_deviationPotential_nonpos Finset.univ w t hW
    have e : ∑ i, ∑ j, (u i * u j + w i * w j) * φ i j =
        -(∑ i, ∑ j, u i * u j * deviationPotential lam (t j - t i)) -
          ∑ i, ∑ j, w i * w j * deviationPotential lam (t j - t i) := by
      simp only [hφ, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e]; linarith
  · have hanti : ∑ i, ∑ j, (u i * w j - w i * u j) * φ i j = 0 := by
      have hsw : ∑ i, ∑ j, w i * u j * φ i j = ∑ i, ∑ j, u i * w j * φ i j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hsym]; ring
      simp only [sub_mul, Finset.sum_sub_distrib, hsw, sub_self]
    apply Complex.ext
    · simp only [Complex.re_sum, Complex.ofReal_re]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, hφ, u, w]
      ring
    · simp only [Complex.im_sum, Complex.ofReal_im]
      rw [← hanti]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [Complex.mul_im, Complex.mul_re, Complex.star_def, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, hφ, u, w]
      ring

end

end RHTower.WeilExcess
