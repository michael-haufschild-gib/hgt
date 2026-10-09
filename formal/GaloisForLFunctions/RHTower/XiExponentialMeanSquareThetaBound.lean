import GaloisForLFunctions.RHTower.RiemannKernelStripLPMaximality
import GaloisForLFunctions.RHTower.XiSecondOrderLaguerrePolyaPreimage

/-!
# The exponentially weighted mean square of `Ξ` from the theta boundary

For `X ≥ 2`,

  `∫_X^{2X} e^{πy/2} |Ξ(y)|² dy ≤ C X^{9/2} log X`   (`exists_integral_exp_mul_norm_sq_XiC_le`).

Proof.  Put `δ = 1/X`, `c = π/4 − δ/2`, `κ = cos 2c = sin δ ≍ 1/X`.  On `[X, 2X]`,
`e^{πy/2} ≤ e² e^{2cy}`, and Plancherel for the strip-shifted kernel gives
`∫ e^{2cy}|Ξ(y)|² dy = 2π ∫ |Φ(u + ic)|² du`.  On the line `Im u = c` Riemann's kernel is a
combination of the theta moments `S₄, S₂` at `τ = x(u) + i y(u)`, `y(u) = e^{2u}κ`.  Unit windows
in `u` with `y(u) ≤ 1` carry mass `≲ κ^{−9/2}` each (`integral_norm_sq_kernelC_line_le`), and there
are `≲ log(1/κ)` of them; windows with `y(u) ≥ 1` carry mass `≲ κ^{−9/2} e^{−2y(u)}`, because the
Parseval masses `Σ n^{2k} e^{−2πn²y}` decay like `e^{−πy}` (`thetaMomentMass_le_exp`).  Hence
`∫|Φ(u + ic)|² du ≲ κ^{−9/2} log(1/κ) ≍ X^{9/2} log X`.

The logarithm is the number of unit windows between the natural boundary and height one; no
approximate functional equation is used.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open GaloisForLFunctions.HTGeometry Zeta23

noncomputable section

namespace RHTower.KernelStrip


/-- For `y ≥ 1` the Parseval mass decays like `e^{−πy}`. -/
theorem thetaMomentMass_le_exp {k : ℕ} (hk : 1 ≤ k) {y : ℝ} (hy : 1 ≤ y) :
    thetaMomentMass k y ≤ Real.exp (-(π * y)) * thetaMomentMass k (1 / 2) := by
  unfold thetaMomentMass
  rw [← tsum_mul_left]
  have hs : ∀ z : ℝ, 0 < z → Summable fun n : ℕ => (n : ℝ) ^ (2 * k) * Real.exp (-2 * π * n ^ 2 * z) :=
    fun z hz => (summable_pow_mul_exp_neg_sq (2 * k) (by positivity : 0 < 2 * z)).congr
      fun n => by ring_nf
  refine Summable.tsum_le_tsum (fun n => ?_) (hs y (by linarith)) ((hs _ (by norm_num)).mul_left _)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Nat.cast_zero, zero_pow (by omega : 2 * k ≠ 0), zero_mul, zero_mul, mul_zero]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have hexp : Real.exp (-2 * π * n ^ 2 * y) ≤ Real.exp (-(π * y)) * Real.exp (-2 * π * n ^ 2 * (1 / 2)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
      have hpi := Real.pi_pos
      have a1 := mul_nonneg (mul_nonneg hpi.le (by linarith : (0 : ℝ) ≤ y))
        (by linarith : (0 : ℝ) ≤ (n : ℝ) ^ 2 - 1)
      have a2 := mul_nonneg (mul_nonneg hpi.le (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2))
        (by linarith : (0 : ℝ) ≤ y - 1)
      nlinarith
    calc (n : ℝ) ^ (2 * k) * Real.exp (-2 * π * n ^ 2 * y)
        ≤ (n : ℝ) ^ (2 * k) * (Real.exp (-(π * y)) * Real.exp (-2 * π * n ^ 2 * (1 / 2))) := by gcongr
      _ = Real.exp (-(π * y)) * ((n : ℝ) ^ (2 * k) * Real.exp (-2 * π * n ^ 2 * (1 / 2))) := by ring

/-- **Window bound in mass form.** `∫_U^{U+1}|S_k|² ≤ 12(Σ_k(y₀) + 121π²y₀²Σ_{k+2}(y₀))`,
`y₀ = y(U)`. -/
theorem integral_norm_sq_thetaMoment_line_le_mass (k : ℕ) {c : ℝ}
    (hs : 1 / 2 ≤ Real.sin (2 * c)) (hcos : 0 < Real.cos (2 * c)) {U : ℝ} (hU : 0 ≤ U) :
    ∫ u in U..U + 1, ‖thetaMoment k (lineIm c u) (lineRe c u)‖ ^ 2 ≤
      12 * (thetaMomentMass k (lineIm c U) +
        121 * π ^ 2 * lineIm c U ^ 2 * thetaMomentMass (k + 2) (lineIm c U)) := by
  have hs0 : 0 < Real.sin (2 * c) := by linarith
  set s := Real.sin (2 * c) with hs_def
  set κ := Real.cos (2 * c) with hκ_def
  set t := κ / s with ht_def
  have ht : 0 < t := div_pos hcos hs0
  set Y := Real.exp (2 * U) with hY_def
  have hY1 : 1 ≤ Y := Real.one_le_exp (by linarith)
  have hx₁ : lineRe c U = -(Y * s) := rfl
  have hx₂ : lineRe c (U + 1) = -(Real.exp 2 * Y * s) := by
    rw [lineRe, show 2 * (U + 1) = 2 * U + 2 by ring, Real.exp_add]; ring
  have hx₁neg : lineRe c U < 0 := lineRe_neg hs0 U
  have hx₂₁ : lineRe c (U + 1) ≤ lineRe c U := lineRe_antitone hs0 (by linarith)
  have hy₀' : lineIm c U = t * -lineRe c U := lineIm_eq hs0 U
  have hy₀pos : 0 < lineIm c U := mul_pos (Real.exp_pos _) hcos
  set y₀ := lineIm c U with hy₀_def
  set x₁ := lineRe c U with hx₁_def
  set x₂ := lineRe c (U + 1) with hx₂_def
  set g : ℝ → ℝ := fun x => ‖thetaMoment k (t * -x) x‖ ^ 2 with hg_def
  have hrw : ∀ u, ‖thetaMoment k (lineIm c u) (lineRe c u)‖ ^ 2 = g (lineRe c u) := by
    intro u; simp only [hg_def]; rw [lineIm_eq hs0 u]
  simp_rw [hrw]
  have hgc : ContinuousOn g (Set.Icc x₂ x₁) := by
    have h := continuousOn_thetaMoment_comp k hy₀pos (s := Set.Icc x₂ x₁)
      (g := fun x => t * -x) (by fun_prop) (fun x hx => by rw [hy₀']; nlinarith [hx.2])
    exact (continuous_norm.comp_continuousOn h).pow 2
  rw [integral_comp_lineRe hs0 (by linarith) hgc]
  have hstep : ∫ x in x₂..x₁, g x / (-2 * x) ≤ (∫ x in x₂..x₁, g x) / (-2 * x₁) := by
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_mono_on hx₂₁ ?_ ?_ fun x hx => ?_
    · refine (hgc.div (continuousOn_const.mul continuousOn_id) fun x hx => ?_).intervalIntegrable_of_Icc
        hx₂₁
      exact mul_ne_zero (by norm_num) (by linarith [hx.2] : x < 0).ne
    · exact (hgc.div continuousOn_const fun _ _ => by nlinarith).intervalIntegrable_of_Icc hx₂₁
    · have hgx : 0 ≤ g x := by positivity
      have h1 : 0 < -2 * x₁ := by linarith
      have h2 : -2 * x₁ ≤ -2 * x := by linarith [hx.2]
      exact div_le_div_of_nonneg_left hgx h1 h2
  have hray := integral_norm_sq_thetaMoment_ray_le k ht hx₂₁ hx₁neg
  rw [← hy₀'] at hray
  set K : ℕ := ⌈(x₁ - x₂) / 2⌉₊ with hK_def
  set δ : ℝ := t * (x₁ - x₂ + 2) with hδ_def
  have hK : (K : ℝ) ≤ (x₁ - x₂) / 2 + 1 :=
    (Nat.ceil_lt_add_one (by linarith)).le
  have he := exp_two_le
  have hYs : 1 / 2 ≤ Y * s := by nlinarith
  have hy₀eq : y₀ = t * (Y * s) := by rw [hy₀', hx₁]; ring
  have hδy : δ ≤ 11 * y₀ := by
    rw [hδ_def, hy₀eq, hx₁, hx₂]
    have : -(Y * s) - -(Real.exp 2 * Y * s) + 2 ≤ 11 * (Y * s) := by nlinarith
    nlinarith
  have hδ0 : 0 ≤ δ := by rw [hδ_def, hx₁, hx₂]; have := Real.exp_pos 2; nlinarith
  have hKx : (K : ℝ) / (-2 * x₁) ≤ 3 := by
    rw [div_le_iff₀ (by linarith), hx₁]
    have : (x₁ - x₂) / 2 + 1 ≤ 3 * (-2 * -(Y * s)) := by rw [hx₁, hx₂]; nlinarith
    linarith
  have hδsq : δ ^ 2 ≤ 121 * y₀ ^ 2 :=
    calc δ ^ 2 ≤ (11 * y₀) ^ 2 := pow_le_pow_left₀ hδ0 hδy 2
      _ = 121 * y₀ ^ 2 := by ring
  have hB0 := thetaMomentMass_nonneg k y₀
  have hB2 := thetaMomentMass_nonneg (k + 2) y₀
  have hx1pos : 0 < -2 * x₁ := by linarith
  calc ∫ x in x₂..x₁, g x / (-2 * x)
      ≤ (∫ x in x₂..x₁, g x) / (-2 * x₁) := hstep
    _ ≤ ((K : ℝ) * (4 * thetaMomentMass k y₀ + 4 * δ ^ 2 * π ^ 2 *
          thetaMomentMass (k + 2) y₀)) / (-2 * x₁) := by
        gcongr
    _ = (K : ℝ) / (-2 * x₁) * (4 * thetaMomentMass k y₀ + 4 * δ ^ 2 * π ^ 2 *
          thetaMomentMass (k + 2) y₀) := by ring
    _ ≤ 3 * (4 * thetaMomentMass k y₀ + 4 * (121 * y₀ ^ 2) * π ^ 2 *
          thetaMomentMass (k + 2) y₀) := by
        refine mul_le_mul hKx ?_ (by positivity) (by norm_num)
        gcongr
    _ = 12 * (thetaMomentMass k y₀ + 121 * π ^ 2 * y₀ ^ 2 * thetaMomentMass (k + 2) y₀) := by
        ring


/-- `y⁷e^{−πy} ≤ 5040 e^{−2y}` for `y ≥ 0`. -/
theorem pow_seven_mul_exp_le {y : ℝ} (hy : 0 ≤ y) :
    y ^ 7 * Real.exp (-(π * y)) ≤ 5040 * Real.exp (-(2 * y)) := by
  have h1 := Real.pow_div_factorial_le_exp y hy 7
  have hfac : ((Nat.factorial 7 : ℕ) : ℝ) = 5040 := by norm_num [Nat.factorial]
  rw [hfac, div_le_iff₀ (by norm_num)] at h1
  have h2 : Real.exp y * Real.exp (-(π * y)) ≤ Real.exp (-(2 * y)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    have := Real.pi_gt_three; nlinarith
  have h3 : y ^ 7 * Real.exp (-(π * y)) ≤ (Real.exp y * 5040) * Real.exp (-(π * y)) :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  nlinarith [Real.exp_pos (-(π * y))]

/-- The theta Parseval masses at height `1/2`. -/
def thetaHalfMassConst : ℝ :=
  Real.exp 9 * (384 * π ^ 4 * (thetaMomentMass 4 (1 / 2) + 121 * π ^ 2 * thetaMomentMass 6 (1 / 2)) +
    864 * π ^ 2 * (thetaMomentMass 2 (1 / 2) + 121 * π ^ 2 * thetaMomentMass 4 (1 / 2)))

theorem thetaHalfMassConst_nonneg : 0 ≤ thetaHalfMassConst := by
  unfold thetaHalfMassConst
  have := thetaMomentMass_nonneg 4 (1 / 2); have := thetaMomentMass_nonneg 6 (1 / 2)
  have := thetaMomentMass_nonneg 2 (1 / 2)
  positivity

/-- **Far windows decay.** If `y(U) = e^{2U}cos 2c ≥ 1`, then
`∫_U^{U+1}|Φ(u+ic)|² ≤ 10080·D·κ^{-4}κ^{-1/2}e^{−2y(U)}`. -/
theorem integral_norm_sq_kernelC_line_le_far {c : ℝ} (hc0 : 0 ≤ c) (hc : c < π / 4)
    (hs : 1 / 2 ≤ Real.sin (2 * c)) {U : ℝ} (hU : 0 ≤ U) (hy : 1 ≤ lineIm c U) :
    ∫ u in U..U + 1, ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 ≤
      10080 * thetaHalfMassConst * ((Real.cos (2 * c))⁻¹ ^ 4 * (1 / Real.sqrt (Real.cos (2 * c)))) *
        Real.exp (-(2 * lineIm c U)) := by
  have hκ : 0 < Real.cos (2 * c) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  set κ := Real.cos (2 * c) with hκ_def
  set y₀ := lineIm c U with hy₀_def
  have hy0 : y₀ = Real.exp (2 * U) * κ := rfl
  have hUU : U ≤ U + 1 := by linarith
  have h4c := continuousOn_thetaMoment_line 4 hκ U (U + 1)
  have h2c := continuousOn_thetaMoment_line 2 hκ U (U + 1)
  have hI4 : IntervalIntegrable (fun u => ‖thetaMoment 4 (lineIm c u) (lineRe c u)‖ ^ 2)
      volume U (U + 1) := ((continuous_norm.comp_continuousOn h4c).pow 2).intervalIntegrable_of_Icc hUU
  have hI2 : IntervalIntegrable (fun u => ‖thetaMoment 2 (lineIm c u) (lineRe c u)‖ ^ 2)
      volume U (U + 1) := ((continuous_norm.comp_continuousOn h2c).pow 2).intervalIntegrable_of_Icc hUU
  have hstep : ∫ u in U..U + 1, ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 ≤
      ∫ u in U..U + 1, (32 * π ^ 4 * Real.exp (9 * (U + 1)) *
          ‖thetaMoment 4 (lineIm c u) (lineRe c u)‖ ^ 2 +
        72 * π ^ 2 * Real.exp (5 * (U + 1)) * ‖thetaMoment 2 (lineIm c u) (lineRe c u)‖ ^ 2) := by
    refine intervalIntegral.integral_mono_on hUU
      (((continuous_kernelC_line hc0 hc).norm.pow 2).intervalIntegrable _ _)
      ((hI4.const_mul _).add (hI2.const_mul _)) fun u hu => ?_
    refine (norm_sq_kernelC_line_le hκ u).trans ?_
    have e9 : Real.exp (9 * u) ≤ Real.exp (9 * (U + 1)) := Real.exp_le_exp.mpr (by linarith [hu.2])
    have e5 : Real.exp (5 * u) ≤ Real.exp (5 * (U + 1)) := Real.exp_le_exp.mpr (by linarith [hu.2])
    gcongr
  rw [intervalIntegral.integral_add (hI4.const_mul _) (hI2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hstep
  have hW4 := integral_norm_sq_thetaMoment_line_le_mass 4 hs hκ hU
  have hW2 := integral_norm_sq_thetaMoment_line_le_mass 2 hs hκ hU
  rw [← hy₀_def] at hW4 hW2
  have hB4 := thetaMomentMass_le_exp (k := 4) (by norm_num) hy
  have hB6 := thetaMomentMass_le_exp (k := 4 + 2) (by norm_num) hy
  have hB2 := thetaMomentMass_le_exp (k := 2) (by norm_num) hy
  have hB4' := thetaMomentMass_le_exp (k := 2 + 2) (by norm_num) hy
  set E := Real.exp (-(π * y₀)) with hE_def
  have hE0 : 0 < E := Real.exp_pos _
  set b4 := thetaMomentMass 4 (1 / 2)
  set b6 := thetaMomentMass 6 (1 / 2)
  set b2 := thetaMomentMass 2 (1 / 2)
  have hb4 : 0 ≤ b4 := thetaMomentMass_nonneg _ _
  have hb6 : 0 ≤ b6 := thetaMomentMass_nonneg _ _
  have hb2 : 0 ≤ b2 := thetaMomentMass_nonneg _ _
  have hy1sq : 1 ≤ y₀ ^ 2 := by nlinarith
  -- windows of `S₄` and `S₂`
  have hW4' : ∫ u in U..U + 1, ‖thetaMoment 4 (lineIm c u) (lineRe c u)‖ ^ 2 ≤
      12 * (b4 + 121 * π ^ 2 * b6) * (y₀ ^ 2 * E) := by
    refine hW4.trans ?_
    have : thetaMomentMass 4 y₀ + 121 * π ^ 2 * y₀ ^ 2 * thetaMomentMass (4 + 2) y₀ ≤
        E * b4 + 121 * π ^ 2 * y₀ ^ 2 * (E * b6) := by gcongr
    nlinarith [mul_le_mul_of_nonneg_left hy1sq (by positivity : (0 : ℝ) ≤ E * b4)]
  have hW2' : ∫ u in U..U + 1, ‖thetaMoment 2 (lineIm c u) (lineRe c u)‖ ^ 2 ≤
      12 * (b2 + 121 * π ^ 2 * b4) * (y₀ ^ 2 * E) := by
    refine hW2.trans ?_
    have : thetaMomentMass 2 y₀ + 121 * π ^ 2 * y₀ ^ 2 * thetaMomentMass (2 + 2) y₀ ≤
        E * b2 + 121 * π ^ 2 * y₀ ^ 2 * (E * b4) := by gcongr
    nlinarith [mul_le_mul_of_nonneg_left hy1sq (by positivity : (0 : ℝ) ≤ E * b2)]
  -- `e^{9U} = (y₀/κ)^{9/2}` bounded by `y₀⁵ κ^{-4}κ^{-1/2}`
  have hY : Real.exp (2 * U) = y₀ * κ⁻¹ := by rw [hy0]; field_simp
  have hsq : Real.exp U = Real.sqrt y₀ * Real.sqrt κ⁻¹ := by
    rw [← Real.sqrt_mul (by linarith), ← hY, show 2 * U = U + U by ring, Real.exp_add,
      Real.sqrt_mul_self (Real.exp_pos _).le]
  have hsy : Real.sqrt y₀ ≤ y₀ := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hκinv : Real.sqrt κ⁻¹ = 1 / Real.sqrt κ := by rw [Real.sqrt_inv, one_div]
  have h9 : Real.exp (9 * U) ≤ y₀ ^ 5 * (κ⁻¹ ^ 4 * (1 / Real.sqrt κ)) := by
    have : Real.exp (9 * U) = Real.exp (2 * U) ^ 4 * Real.exp U := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    rw [this, hY, hsq, hκinv]
    have hκs : 0 ≤ 1 / Real.sqrt κ := by positivity
    calc (y₀ * κ⁻¹) ^ 4 * (Real.sqrt y₀ * (1 / Real.sqrt κ))
        = y₀ ^ 4 * Real.sqrt y₀ * (κ⁻¹ ^ 4 * (1 / Real.sqrt κ)) := by ring
      _ ≤ y₀ ^ 4 * y₀ * (κ⁻¹ ^ 4 * (1 / Real.sqrt κ)) := by gcongr
      _ = y₀ ^ 5 * (κ⁻¹ ^ 4 * (1 / Real.sqrt κ)) := by ring
  have h5 : Real.exp (5 * U) ≤ Real.exp (9 * U) := Real.exp_le_exp.mpr (by linarith)
  set Q := κ⁻¹ ^ 4 * (1 / Real.sqrt κ) with hQ_def
  have hQ : 0 ≤ Q := by positivity
  have hp7 := pow_seven_mul_exp_le (y := y₀) (by linarith)
  have hy7 : y₀ ^ 5 * (y₀ ^ 2 * E) = y₀ ^ 7 * E := by ring
  -- assemble
  calc ∫ u in U..U + 1, ‖kernelC ((u : ℂ) + c * I)‖ ^ 2
      ≤ 32 * π ^ 4 * Real.exp (9 * (U + 1)) *
          (∫ u in U..U + 1, ‖thetaMoment 4 (lineIm c u) (lineRe c u)‖ ^ 2) +
        72 * π ^ 2 * Real.exp (5 * (U + 1)) *
          (∫ u in U..U + 1, ‖thetaMoment 2 (lineIm c u) (lineRe c u)‖ ^ 2) := hstep
    _ ≤ 32 * π ^ 4 * Real.exp (9 * (U + 1)) * (12 * (b4 + 121 * π ^ 2 * b6) * (y₀ ^ 2 * E)) +
        72 * π ^ 2 * Real.exp (5 * (U + 1)) * (12 * (b2 + 121 * π ^ 2 * b4) * (y₀ ^ 2 * E)) := by
        gcongr
    _ ≤ thetaHalfMassConst * (Q * (y₀ ^ 7 * E)) := by
        have e9 : Real.exp (9 * (U + 1)) = Real.exp 9 * Real.exp (9 * U) := by
          rw [← Real.exp_add]; ring_nf
        have e5 : Real.exp (5 * (U + 1)) ≤ Real.exp 9 * Real.exp (9 * U) := by
          rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
        have hP : 0 ≤ y₀ ^ 2 * E := by positivity
        have hA4 : 0 ≤ 12 * (b4 + 121 * π ^ 2 * b6) * (y₀ ^ 2 * E) := by positivity
        have hA2 : 0 ≤ 12 * (b2 + 121 * π ^ 2 * b4) * (y₀ ^ 2 * E) := by positivity
        have k9 : Real.exp 9 * Real.exp (9 * U) ≤ Real.exp 9 * (y₀ ^ 5 * Q) := by gcongr
        calc 32 * π ^ 4 * Real.exp (9 * (U + 1)) * (12 * (b4 + 121 * π ^ 2 * b6) * (y₀ ^ 2 * E)) +
              72 * π ^ 2 * Real.exp (5 * (U + 1)) * (12 * (b2 + 121 * π ^ 2 * b4) * (y₀ ^ 2 * E))
            ≤ 32 * π ^ 4 * (Real.exp 9 * (y₀ ^ 5 * Q)) * (12 * (b4 + 121 * π ^ 2 * b6) * (y₀ ^ 2 * E)) +
              72 * π ^ 2 * (Real.exp 9 * (y₀ ^ 5 * Q)) * (12 * (b2 + 121 * π ^ 2 * b4) * (y₀ ^ 2 * E)) := by
              rw [e9]
              gcongr
              all_goals first | exact k9 | exact e5.trans k9
          _ = thetaHalfMassConst * (Q * (y₀ ^ 7 * E)) := by
              unfold thetaHalfMassConst; ring
    _ ≤ thetaHalfMassConst * (Q * (5040 * Real.exp (-(2 * y₀)))) := by
        have := thetaHalfMassConst_nonneg
        gcongr
    _ = 10080 * thetaHalfMassConst * Q * Real.exp (-(2 * y₀)) / 2 := by ring
    _ ≤ 10080 * thetaHalfMassConst * Q * Real.exp (-(2 * y₀)) := by
        have := thetaHalfMassConst_nonneg
        have : 0 ≤ 10080 * thetaHalfMassConst * Q * Real.exp (-(2 * y₀)) := by positivity
        linarith


theorem kernelWindowConst_nonneg : 0 ≤ kernelWindowConst := by
  unfold kernelWindowConst
  have := thetaWindowConst_nonneg 4; have := thetaWindowConst_nonneg 2
  positivity

/-- **Truncated line mass.**  `∫_0^N |Φ(u + ic)|² ≤ A κ^{−9/2}(log(1/κ)/2 + 3)`. -/
theorem integral_norm_sq_kernelC_line_zero_le {c : ℝ} (hc0 : 0 ≤ c) (hc : c < π / 4)
    (hs : 1 / 2 ≤ Real.sin (2 * c)) (N : ℕ) :
    ∫ u in (0 : ℝ)..N, ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 ≤
      (kernelWindowConst + 10080 * thetaHalfMassConst) *
        ((Real.cos (2 * c))⁻¹ ^ 4 * (1 / Real.sqrt (Real.cos (2 * c)))) *
        (Real.log (Real.cos (2 * c))⁻¹ / 2 + 3) := by
  have hκ : 0 < Real.cos (2 * c) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hκ1 : Real.cos (2 * c) ≤ 1 := Real.cos_le_one _
  set κ := Real.cos (2 * c) with hκ_def
  set Q := κ⁻¹ ^ 4 * (1 / Real.sqrt κ) with hQ_def
  have hQ : 0 ≤ Q := by positivity
  set K := kernelWindowConst with hK_def
  have hK : 0 ≤ K := kernelWindowConst_nonneg
  set D := 10080 * thetaHalfMassConst with hD_def
  have hD : 0 ≤ D := by have := thetaHalfMassConst_nonneg; positivity
  have hlog : 0 ≤ Real.log κ⁻¹ := Real.log_nonneg (one_le_inv_iff₀.mpr ⟨hκ, hκ1⟩)
  set U₀ : ℕ := ⌈Real.log κ⁻¹ / 2⌉₊ with hU₀_def
  have hU₀ : (U₀ : ℝ) ≤ Real.log κ⁻¹ / 2 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hU₀' : 1 ≤ Real.exp (2 * U₀) * κ := by
    have h1 : Real.log κ⁻¹ ≤ 2 * U₀ := by
      have := Nat.le_ceil (Real.log κ⁻¹ / 2); linarith
    have h2 : κ⁻¹ ≤ Real.exp (2 * U₀) := by
      rw [← Real.exp_log (inv_pos.mpr hκ)]; exact Real.exp_le_exp.mpr h1
    calc (1 : ℝ) = κ⁻¹ * κ := (inv_mul_cancel₀ hκ.ne').symm
      _ ≤ Real.exp (2 * U₀) * κ := by gcongr
  set φ : ℕ → ℝ := fun U => if U < U₀ then 1 else (1 / 2) ^ (U - U₀) with hφ_def
  have hφ0 : ∀ U, 0 ≤ φ U := fun U => by simp only [hφ_def]; split_ifs <;> positivity
  have hφ1 : ∀ U, φ U ≤ 1 := fun U => by
    simp only [hφ_def]; split_ifs
    · exact le_rfl
    · exact pow_le_one₀ (by norm_num) (by norm_num)
  have he1 : Real.exp (-1) ≤ 1 / 2 := by
    have := Real.add_one_le_exp 1
    rw [Real.exp_neg, one_div]; exact inv_anti₀ (by norm_num) (by linarith)
  have hwin : ∀ U : ℕ, ∫ u in (U : ℝ)..U + 1, ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 ≤
      (K + D) * Q * φ U := by
    intro U
    by_cases hU : U < U₀
    · simp only [hφ_def, if_pos hU, mul_one]
      calc ∫ u in (U : ℝ)..U + 1, ‖kernelC ((u : ℂ) + c * I)‖ ^ 2
          ≤ K * κ⁻¹ ^ 4 * (1 / Real.sqrt κ) :=
            integral_norm_sq_kernelC_line_le hc0 hc hs (Nat.cast_nonneg U)
        _ = K * Q := by rw [hQ_def]; ring
        _ ≤ (K + D) * Q := by gcongr; linarith
    · simp only [hφ_def, if_neg hU]
      push Not at hU
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hU
      rw [Nat.add_sub_cancel_left]
      have hyeq : lineIm c ((U₀ + j : ℕ) : ℝ) = Real.exp (2 * j) * (Real.exp (2 * U₀) * κ) := by
        rw [lineIm, ← hκ_def, ← mul_assoc, ← Real.exp_add]; congr 2; push_cast; ring
      have hej : 1 + 2 * (j : ℝ) ≤ Real.exp (2 * j) := by
        have := Real.add_one_le_exp (2 * (j : ℝ)); linarith
      have hy : 1 + 2 * (j : ℝ) ≤ lineIm c ((U₀ + j : ℕ) : ℝ) := by
        rw [hyeq]
        calc 1 + 2 * (j : ℝ) ≤ Real.exp (2 * j) := hej
          _ = Real.exp (2 * j) * 1 := (mul_one _).symm
          _ ≤ Real.exp (2 * j) * (Real.exp (2 * U₀) * κ) := by gcongr
      have hy1 : 1 ≤ lineIm c ((U₀ + j : ℕ) : ℝ) := by
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith
      have hfar := integral_norm_sq_kernelC_line_le_far hc0 hc hs (Nat.cast_nonneg _) hy1
      have hexp : Real.exp (-(2 * lineIm c ((U₀ + j : ℕ) : ℝ))) ≤ (1 / 2) ^ j := by
        calc Real.exp (-(2 * lineIm c ((U₀ + j : ℕ) : ℝ)))
            ≤ Real.exp (j * (-1)) := Real.exp_le_exp.mpr (by
              have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
              linarith)
          _ = Real.exp (-1) ^ j := Real.exp_nat_mul _ _
          _ ≤ (1 / 2) ^ j := pow_le_pow_left₀ (Real.exp_pos _).le he1 j
      calc ∫ u in ((U₀ + j : ℕ) : ℝ)..((U₀ + j : ℕ) : ℝ) + 1, ‖kernelC ((u : ℂ) + c * I)‖ ^ 2
          ≤ D * Q * Real.exp (-(2 * lineIm c ((U₀ + j : ℕ) : ℝ))) := by
            rw [hD_def, hQ_def]; exact hfar
        _ ≤ D * Q * (1 / 2) ^ j := by gcongr
        _ ≤ (K + D) * Q * (1 / 2) ^ j := by gcongr; linarith
  have hII : ∀ U : ℕ, IntervalIntegrable (fun u : ℝ => ‖kernelC ((u : ℂ) + c * I)‖ ^ 2) volume
      (U : ℝ) ((U + 1 : ℕ) : ℝ) := fun U =>
    ((continuous_kernelC_line hc0 hc).norm.pow 2).intervalIntegrable _ _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ)) (n := N) (fun k _ => hII k)
  simp only [Nat.cast_zero] at hsum
  rw [← hsum]
  have hsumφ : ∑ U ∈ Finset.range N, φ U ≤ U₀ + 2 := by
    calc ∑ U ∈ Finset.range N, φ U ≤ ∑ U ∈ Finset.range (U₀ + N), φ U :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_add_left N U₀))
            (fun U _ _ => hφ0 U)
      _ = ∑ U ∈ Finset.range U₀, φ U + ∑ j ∈ Finset.range N, φ (U₀ + j) :=
          Finset.sum_range_add _ _ _
      _ ≤ ∑ U ∈ Finset.range U₀, (1 : ℝ) + ∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j := by
          gcongr with U _ j _
          · exact hφ1 U
          · simp only [hφ_def, if_neg (by omega : ¬ U₀ + j < U₀), Nat.add_sub_cancel_left,
              le_refl]
      _ ≤ U₀ + 2 := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          linarith [sum_geometric_two_le N]
  calc ∑ k ∈ Finset.range N, ∫ u in (k : ℝ)..((k + 1 : ℕ) : ℝ), ‖kernelC ((u : ℂ) + c * I)‖ ^ 2
      ≤ ∑ k ∈ Finset.range N, (K + D) * Q * φ k := by
        refine Finset.sum_le_sum fun k _ => ?_
        have := hwin k
        rw [Nat.cast_add, Nat.cast_one]; exact this
    _ = (K + D) * Q * ∑ k ∈ Finset.range N, φ k := by rw [Finset.mul_sum]
    _ ≤ (K + D) * Q * (Real.log κ⁻¹ / 2 + 3) := by
        have hKD : 0 ≤ (K + D) * Q := by positivity
        exact mul_le_mul_of_nonneg_left (by linarith) hKD

/-- **Whole-line mass.**  `∫_ℝ |Φ(u + ic)|² ≤ 2A κ^{−9/2}(log(1/κ)/2 + 3)`. -/
theorem integral_norm_sq_kernelC_line_whole_le {c : ℝ} (hc0 : 0 ≤ c) (hc : c < π / 4)
    (hs : 1 / 2 ≤ Real.sin (2 * c)) :
    ∫ u : ℝ, ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 ≤
      2 * ((kernelWindowConst + 10080 * thetaHalfMassConst) *
        ((Real.cos (2 * c))⁻¹ ^ 4 * (1 / Real.sqrt (Real.cos (2 * c)))) *
        (Real.log (Real.cos (2 * c))⁻¹ / 2 + 3)) := by
  set f : ℝ → ℝ := fun u => ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 with hf_def
  obtain ⟨-, h2, -, -⟩ := shiftedProfile_integrability (m := fun _ => 1) (M := 1) hc0 hc
    (fun _ _ _ => differentiableAt_const _) (fun _ _ _ => by simp)
  have hfi : Integrable f := by
    have := h2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp [hf_def, shiftedProfile]
  have hlim := MeasureTheory.intervalIntegral_tendsto_integral hfi
    (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    (tendsto_natCast_atTop_atTop (R := ℝ))
  refine le_of_tendsto' hlim fun N => ?_
  simp only [Function.comp_apply]
  have hcont : Continuous f := (continuous_kernelC_line hc0 hc).norm.pow 2
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)]
  have hneg : ∫ u in -(N : ℝ)..0, f u = ∫ u in (0 : ℝ)..N, f u := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := (N : ℝ)) f
    rw [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hf_def]
    rw [norm_kernelC_neg_line hc0 hc u]
  rw [hneg]
  have := integral_norm_sq_kernelC_line_zero_le hc0 hc hs N
  linarith

theorem kernelPsi_one_eq_XiC (x : ℝ) : kernelPsi (fun _ => 1) x = XiC x := by
  rw [← Littlewood.paperFT_riemannPhiKernel_eq_XiC]
  unfold kernelPsi paperFT
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [mul_one]

/-- `κ^{−9/2}(log(1/κ)/2 + 3) ≤ 6(π/2)^{9/2} X^{9/2} log X` when `κ ≥ 2/(πX)`. -/
theorem kappa_power_log_le {κ X : ℝ} (hX : 2 ≤ X) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hκX : 2 / (π * X) ≤ κ) :
    κ⁻¹ ^ 4 * (1 / Real.sqrt κ) * (Real.log κ⁻¹ / 2 + 3) ≤
      (π / 2) ^ 4 * Real.sqrt (π / 2) * 6 * (X ^ (9 / 2 : ℝ) * Real.log X) := by
  have hX0 : 0 < X := by linarith
  have hπ := Real.pi_pos
  have hinv : κ⁻¹ ≤ π / 2 * X := by
    have := inv_anti₀ (by positivity) hκX
    rw [inv_div] at this; linarith [show π * X / 2 = π / 2 * X by ring]
  have h4 : κ⁻¹ ^ 4 ≤ (π / 2) ^ 4 * X ^ 4 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hinv 4
  have hsq : 1 / Real.sqrt κ ≤ Real.sqrt (π / 2) * Real.sqrt X := by
    rw [one_div, ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hinv
  have hlog1 : Real.log κ⁻¹ ≤ Real.log X + 1 := by
    have h1 : Real.log κ⁻¹ ≤ Real.log (π / 2 * X) :=
      Real.log_le_log (by positivity) hinv
    rw [Real.log_mul (by positivity) hX0.ne'] at h1
    have h2 : Real.log (π / 2) ≤ π / 2 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : π / 2 - 1 ≤ 1 := by linarith [Real.pi_lt_four]
    linarith
  have hlog0 : 0 ≤ Real.log κ⁻¹ := Real.log_nonneg (one_le_inv_iff₀.mpr ⟨hκ, hκ1⟩)
  have hlogX : 0.6931471803 < Real.log X := by
    have := Real.log_le_log (by norm_num) hX
    linarith [Real.log_two_gt_d9]
  have hL : Real.log κ⁻¹ / 2 + 3 ≤ 6 * Real.log X := by linarith
  have hrp : X ^ (9 / 2 : ℝ) = X ^ 4 * Real.sqrt X := by
    rw [show (9 / 2 : ℝ) = (4 : ℕ) + 1 / 2 by norm_num, Real.rpow_add hX0, Real.rpow_natCast,
      Real.sqrt_eq_rpow]
  rw [hrp]
  calc κ⁻¹ ^ 4 * (1 / Real.sqrt κ) * (Real.log κ⁻¹ / 2 + 3)
      ≤ ((π / 2) ^ 4 * X ^ 4) * (Real.sqrt (π / 2) * Real.sqrt X) * (6 * Real.log X) := by
        gcongr
    _ = (π / 2) ^ 4 * Real.sqrt (π / 2) * 6 * (X ^ 4 * Real.sqrt X * Real.log X) := by ring

/-- **The exponentially weighted mean square of `Ξ`.**
`∫_X^{2X} e^{πy/2}|Ξ(y)|² dy ≤ C X^{9/2} log X` for `X ≥ 2`. -/
theorem exists_integral_exp_mul_norm_sq_XiC_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 2 ≤ X →
      ∫ y in X..2 * X, Real.exp (π / 2 * y) * ‖XiC (y : ℂ)‖ ^ 2 ≤
        C * X ^ (9 / 2 : ℝ) * Real.log X := by
  set A := kernelWindowConst + 10080 * thetaHalfMassConst with hA_def
  have hA : 0 ≤ A := by
    have := kernelWindowConst_nonneg; have := thetaHalfMassConst_nonneg; positivity
  refine ⟨Real.exp 2 * (2 * π) * (2 * A) * ((π / 2) ^ 4 * Real.sqrt (π / 2) * 6),
    by positivity, fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hπ3 := Real.pi_gt_three
  obtain ⟨δ, hδ_def⟩ : ∃ δ : ℝ, δ = 1 / X := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ_def]; positivity
  have hδ : δ ≤ 1 / 2 := by
    rw [hδ_def, div_le_div_iff₀ hX0 (by norm_num)]; linarith
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = π / 4 - δ / 2 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc_def]; linarith
  have hc : c < π / 4 := by rw [hc_def]; linarith
  have h2c : 2 * c = π / 2 - δ := by rw [hc_def]; ring
  have hκ : Real.cos (2 * c) = Real.sin δ := by rw [h2c, Real.cos_pi_div_two_sub]
  have hs : 1 / 2 ≤ Real.sin (2 * c) := by
    rw [h2c, Real.sin_pi_div_two_sub]
    have := Real.one_sub_sq_div_two_le_cos (x := δ)
    nlinarith
  have hκlow : 2 / π * δ ≤ Real.sin δ := Real.mul_le_sin hδ0.le (by linarith)
  have hκX : 2 / (π * X) ≤ Real.cos (2 * c) := by
    rw [hκ]; refine le_trans (le_of_eq ?_) hκlow; rw [hδ_def]; field_simp
  have hκpos : 0 < Real.cos (2 * c) := lt_of_lt_of_le (by positivity) hκX
  have hW := integral_norm_sq_kernelC_line_whole_le hc0 hc hs
  have hAlg := kappa_power_log_le hX hκpos (Real.cos_le_one _) hκX
  -- Plancherel with `m ≡ 1`
  have hm : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c → DifferentiableAt ℂ (fun _ : ℂ => (1 : ℂ)) z :=
    fun _ _ _ => differentiableAt_const _
  have hmb : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c → ‖(fun _ : ℂ => (1 : ℂ)) z‖ ≤ 1 :=
    fun _ _ _ => by simp
  have hP := integral_norm_sq_exp_mul_kernelPsi hc0 hc hm hmb
  obtain ⟨g1, g2, -, -⟩ := shiftedProfile_integrability hc0 hc hm hmb
  set g : ℝ → ℝ := fun x => ‖(Real.exp (c * x) : ℂ) * kernelPsi (fun _ => 1) x‖ ^ 2 with hg_def
  have hgi : Integrable g := by
    refine (integrable_norm_sq_paperFT g1 g2).congr (Eventually.of_forall fun x => ?_)
    simp only [hg_def]
    rw [← exp_mul_kernelPsi_eq hc0 hc hm hmb x]
  have hg0 : ∀ x, 0 ≤ g x := fun x => by positivity
  have hshift : ∫ u : ℝ, ‖shiftedProfile (fun _ => 1) c u‖ ^ 2 =
      ∫ u : ℝ, ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp [shiftedProfile]
  rw [hshift] at hP
  -- pointwise comparison on `[X, 2X]`
  have hpt : ∀ y ∈ Ioc X (2 * X), Real.exp (π / 2 * y) * ‖XiC (y : ℂ)‖ ^ 2 ≤
      Real.exp 2 * g y := by
    intro y hy
    simp only [hg_def]
    rw [kernelPsi_one_eq_XiC, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]
    gcongr
    have : δ * y ≤ 2 := by
      rw [hδ_def, one_div, inv_mul_le_iff₀ hX0]; linarith [hy.2]
    have e : π / 2 * y = ((2 : ℕ) : ℝ) * (c * y) + δ * y := by rw [hc_def]; push_cast; ring
    linarith
  rw [intervalIntegral.integral_of_le (by linarith)]
  calc ∫ y in Ioc X (2 * X), Real.exp (π / 2 * y) * ‖XiC (y : ℂ)‖ ^ 2
      ≤ ∫ y in Ioc X (2 * X), Real.exp 2 * g y := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity)
          (hgi.const_mul _).integrableOn ?_
        exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hpt)
    _ ≤ ∫ y, Real.exp 2 * g y :=
        setIntegral_le_integral (hgi.const_mul _)
          (Eventually.of_forall fun y => mul_nonneg (Real.exp_pos _).le (hg0 y))
    _ = Real.exp 2 * (2 * π * ∫ u : ℝ, ‖kernelC ((u : ℂ) + c * I)‖ ^ 2) := by
        rw [integral_const_mul, ← hP]
    _ ≤ Real.exp 2 * (2 * π * (2 * (A * ((Real.cos (2 * c))⁻¹ ^ 4 *
          (1 / Real.sqrt (Real.cos (2 * c)))) * (Real.log (Real.cos (2 * c))⁻¹ / 2 + 3)))) := by
        gcongr
    _ = Real.exp 2 * (2 * π) * (2 * A) * ((Real.cos (2 * c))⁻¹ ^ 4 *
          (1 / Real.sqrt (Real.cos (2 * c))) * (Real.log (Real.cos (2 * c))⁻¹ / 2 + 3)) := by ring
    _ ≤ Real.exp 2 * (2 * π) * (2 * A) * ((π / 2) ^ 4 * Real.sqrt (π / 2) * 6 *
          (X ^ (9 / 2 : ℝ) * Real.log X)) := by gcongr
    _ = _ := by ring

end RHTower.KernelStrip
