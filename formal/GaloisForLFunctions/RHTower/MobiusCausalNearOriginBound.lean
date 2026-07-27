import GaloisForLFunctions.RHTower.MobiusCausalPoleUnit
import GaloisForLFunctions.HTGeometry.ComplexBallMeanValue

/-!
# The near-origin bound for the parameter derivative

Close to the origin the parameter derivative of the coupled causal multiplier is bounded
**uniformly in the parameter**: the two `1/z` contributions of `(5)` and `(6)` cancel, and what is
left is a difference quotient of the entire pole unit `Z(s) = (s-1)ζ(s)` and of the quotient

```text
q̇_ω(z) = N(ω,z)/D(ω,z),   N = 2aZ - u(Z + 2aZ′),   D = (aZ)²,
a = 1+ω+z,  u = 2ω+z,  Z = Z(1+2ω+z).
```

Both `N` and `D` are entire in `z`, so the mean-value bound on a fixed ball around `1`, where `Z`
stays away from `0`, gives a bound independent of `ω`.
-/

open Metric

namespace RHTower

noncomputable section

/-! ### Derivatives of the entire pole unit -/

theorem differentiable_deriv_zetaPoleUnit : Differentiable ℂ (deriv zetaPoleUnit) := by
  have h : AnalyticOnNhd ℂ zetaPoleUnit Set.univ :=
    differentiable_zetaPoleUnit.differentiableOn.analyticOnNhd isOpen_univ
  exact fun z => (h.deriv z (Set.mem_univ z)).differentiableAt

theorem differentiable_deriv2_zetaPoleUnit : Differentiable ℂ (deriv (deriv zetaPoleUnit)) := by
  have h : AnalyticOnNhd ℂ (deriv zetaPoleUnit) Set.univ :=
    differentiable_deriv_zetaPoleUnit.differentiableOn.analyticOnNhd isOpen_univ
  exact fun z => (h.deriv z (Set.mem_univ z)).differentiableAt

/-- A radius around `1` on which the pole unit stays away from `0`, together with a common bound
for it and its first two derivatives. -/
theorem exists_poleUnit_ball_bounds :
    ∃ ρ Cb : ℝ, 0 < ρ ∧ ρ ≤ 1 / 8 ∧ 1 ≤ Cb ∧
      ∀ s ∈ closedBall (1 : ℂ) ρ,
        1 / 2 ≤ ‖zetaPoleUnit s‖ ∧ ‖zetaPoleUnit s‖ ≤ Cb ∧
          ‖deriv zetaPoleUnit s‖ ≤ Cb ∧ ‖deriv (deriv zetaPoleUnit) s‖ ≤ Cb := by
  have hcont : ContinuousAt zetaPoleUnit 1 := (differentiable_zetaPoleUnit 1).continuousAt
  have hev : ∀ᶠ s in nhds (1 : ℂ), dist (zetaPoleUnit s) (zetaPoleUnit 1) < 1 / 2 :=
    hcont (Metric.ball_mem_nhds _ (by norm_num))
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.1 hev
  have hρpos : 0 < min (ε / 2) (1 / 8 : ℝ) := lt_min (by linarith) (by norm_num)
  have hlow : ∀ s ∈ closedBall (1 : ℂ) (min (ε / 2) (1 / 8 : ℝ)), 1 / 2 ≤ ‖zetaPoleUnit s‖ := by
    intro s hs
    have hds : dist s 1 ≤ min (ε / 2) (1 / 8 : ℝ) := hs
    have hlt : dist s 1 < ε := by
      have h1 : min (ε / 2) (1 / 8 : ℝ) ≤ ε / 2 := min_le_left _ _
      linarith
    have h := hε hlt
    rw [zetaPoleUnit_one, dist_eq_norm] at h
    have h3 : ‖(1 : ℂ)‖ - ‖zetaPoleUnit s‖ ≤ ‖(1 : ℂ) - zetaPoleUnit s‖ :=
      norm_sub_norm_le _ _
    rw [norm_sub_rev] at h3
    rw [norm_one] at h3
    linarith
  have hcomp := isCompact_closedBall (1 : ℂ) (min (ε / 2) (1 / 8 : ℝ))
  obtain ⟨C1, hC1⟩ :=
    hcomp.exists_bound_of_continuousOn differentiable_zetaPoleUnit.continuous.continuousOn
  obtain ⟨C2, hC2⟩ :=
    hcomp.exists_bound_of_continuousOn differentiable_deriv_zetaPoleUnit.continuous.continuousOn
  obtain ⟨C3, hC3⟩ :=
    hcomp.exists_bound_of_continuousOn differentiable_deriv2_zetaPoleUnit.continuous.continuousOn
  refine ⟨min (ε / 2) (1 / 8 : ℝ), max 1 (max C1 (max C2 C3)), hρpos, min_le_right _ _,
    le_max_left _ _, fun s hs => ⟨hlow s hs, ?_, ?_, ?_⟩⟩
  · exact le_trans (hC1 s hs) (le_max_of_le_right (le_max_left _ _))
  · exact le_trans (hC2 s hs) (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · exact le_trans (hC3 s hs) (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))

/-! ### The entire numerator and denominator of `q̇` -/

/-- The numerator of the parameter derivative of the shifted pole-unit quotient. -/
def poleQNum (ω : ℝ) (z : ℂ) : ℂ :=
  2 * ((1 + (ω : ℂ) + z) * zetaPoleUnit (1 + 2 * (ω : ℂ) + z)) -
    (2 * (ω : ℂ) + z) * (zetaPoleUnit (1 + 2 * (ω : ℂ) + z) +
      (1 + (ω : ℂ) + z) * (2 * deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + z)))

/-- The denominator of the parameter derivative of the shifted pole-unit quotient. -/
def poleQDen (ω : ℝ) (z : ℂ) : ℂ :=
  ((1 + (ω : ℂ) + z) * zetaPoleUnit (1 + 2 * (ω : ℂ) + z)) ^ 2

theorem mobiusCausalQDeriv_eq_div (ω : ℝ) (z : ℂ) :
    mobiusCausalQDeriv ω z = poleQNum ω z / poleQDen ω z := rfl

/-- The `z`-derivative of the numerator. -/
def poleQNumDeriv (ω : ℝ) (z : ℂ) : ℂ :=
  zetaPoleUnit (1 + 2 * (ω : ℂ) + z) -
    (2 * (ω : ℂ) + z) * (3 * deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + z) +
      2 * (1 + (ω : ℂ) + z) * deriv (deriv zetaPoleUnit) (1 + 2 * (ω : ℂ) + z))

/-- The `z`-derivative of the denominator. -/
def poleQDenDeriv (ω : ℝ) (z : ℂ) : ℂ :=
  2 * ((1 + (ω : ℂ) + z) * zetaPoleUnit (1 + 2 * (ω : ℂ) + z)) *
    (zetaPoleUnit (1 + 2 * (ω : ℂ) + z) +
      (1 + (ω : ℂ) + z) * deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + z))

theorem hasDerivAt_shift (c : ℂ) (z : ℂ) : HasDerivAt (fun w : ℂ => c + w) 1 z := by
  simpa using (hasDerivAt_id z).const_add c

theorem hasDerivAt_zetaPoleUnit_comp (ω : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => zetaPoleUnit (1 + 2 * (ω : ℂ) + w))
      (deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + z)) z := by
  have h := ((differentiable_zetaPoleUnit (1 + 2 * (ω : ℂ) + z)).hasDerivAt).comp z
    (hasDerivAt_shift (1 + 2 * (ω : ℂ)) z)
  simpa [Function.comp] using h

theorem hasDerivAt_deriv_zetaPoleUnit_comp (ω : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + w))
      (deriv (deriv zetaPoleUnit) (1 + 2 * (ω : ℂ) + z)) z := by
  have h := ((differentiable_deriv_zetaPoleUnit (1 + 2 * (ω : ℂ) + z)).hasDerivAt).comp z
    (hasDerivAt_shift (1 + 2 * (ω : ℂ)) z)
  simpa [Function.comp] using h

theorem hasDerivAt_poleQNum (ω : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => poleQNum ω w) (poleQNumDeriv ω z) z := by
  have hZ := hasDerivAt_zetaPoleUnit_comp ω z
  have hZ' := hasDerivAt_deriv_zetaPoleUnit_comp ω z
  have ha : HasDerivAt (fun w : ℂ => 1 + (ω : ℂ) + w) 1 z := hasDerivAt_shift (1 + (ω : ℂ)) z
  have hu : HasDerivAt (fun w : ℂ => 2 * (ω : ℂ) + w) 1 z := hasDerivAt_shift (2 * (ω : ℂ)) z
  have h := ((ha.mul hZ).const_mul (2 : ℂ)).sub
    (hu.mul (hZ.add (ha.mul (hZ'.const_mul (2 : ℂ)))))
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.add_apply]
  rw [poleQNumDeriv]
  ring

theorem hasDerivAt_poleQDen (ω : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => poleQDen ω w) (poleQDenDeriv ω z) z := by
  have hZ := hasDerivAt_zetaPoleUnit_comp ω z
  have ha : HasDerivAt (fun w : ℂ => 1 + (ω : ℂ) + w) 1 z := hasDerivAt_shift (1 + (ω : ℂ)) z
  have h := (ha.mul hZ).pow 2
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [poleQDenDeriv]
  ring

theorem hasDerivAt_zetaPoleUnit_one_add (z : ℂ) :
    HasDerivAt (fun w : ℂ => zetaPoleUnit (1 + w)) (deriv zetaPoleUnit (1 + z)) z := by
  have h := ((differentiable_zetaPoleUnit (1 + z)).hasDerivAt).comp z (hasDerivAt_shift 1 z)
  simpa [Function.comp] using h

/-! ### The uniform bound -/

/-- **Uniform near-origin bound.**  There are a radius `δ`, a parameter cutoff `ω₀` and a constant
`C` such that the parameter derivative of the coupled causal multiplier is bounded by `C` for every
parameter `0 < ω ≤ ω₀` and every point `0 < ‖z‖ ≤ δ` of the closed right half plane. -/
theorem exists_near_origin_bound :
    ∃ δ ω₀ C : ℝ, 0 < δ ∧ 0 < ω₀ ∧ 0 ≤ C ∧
      ∀ ω : ℝ, 0 < ω → ω ≤ ω₀ → ∀ z : ℂ, 0 ≤ z.re → z ≠ 0 → ‖z‖ ≤ δ →
        ‖mobiusCausalMultiplierDeriv ω z‖ ≤ C := by
  obtain ⟨ρ, Cb, hρpos, hρ8, hCb1, hbd⟩ := exists_poleUnit_ball_bounds
  have hCb0 : (0 : ℝ) < Cb := by linarith
  refine ⟨ρ / 4, ρ / 8, Cb * (2 * (40 * Cb ^ 2) * (40 * Cb ^ 2) / (1 / 16 : ℝ) ^ 2) +
    Cb * ((40 * Cb ^ 2) / (1 / 16 : ℝ)), by linarith, by linarith, by positivity, ?_⟩
  intro ω hω hωle z hzre hz0 hzδ
  -- abbreviations
  set B : ℝ := 40 * Cb ^ 2 with hBdef
  have hB0 : (0 : ℝ) ≤ B := by positivity
  -- membership facts, valid for every point of the small ball
  have hmemZ : ∀ w : ℂ, ‖w‖ ≤ ρ / 4 → (1 : ℂ) + 2 * (ω : ℂ) + w ∈ closedBall (1 : ℂ) ρ := by
    intro w hw
    have h1 : dist ((1 : ℂ) + 2 * (ω : ℂ) + w) 1 = ‖2 * (ω : ℂ) + w‖ := by
      rw [dist_eq_norm]
      ring_nf
    rw [Metric.mem_closedBall, h1]
    have h2 : ‖2 * (ω : ℂ) + w‖ ≤ 2 * ω + ‖w‖ := by
      refine le_trans (norm_add_le _ _) ?_
      have : ‖2 * ((ω : ℝ) : ℂ)‖ = 2 * ω := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hω]
        norm_num
      rw [this]
    linarith
  have hmem1 : ∀ w : ℂ, ‖w‖ ≤ ρ / 4 → (1 : ℂ) + w ∈ closedBall (1 : ℂ) ρ := by
    intro w hw
    have h1 : dist ((1 : ℂ) + w) 1 = ‖w‖ := by
      rw [dist_eq_norm]
      ring_nf
    rw [Metric.mem_closedBall, h1]
    linarith
  -- the linear factor
  have halb : ∀ w : ℂ, ‖w‖ ≤ ρ / 4 → (1 : ℝ) / 2 ≤ ‖1 + (ω : ℂ) + w‖ := by
    intro w hw
    have hre : ((1 : ℂ) + (ω : ℂ) + w).re = 1 + ω + w.re := by
      simp [Complex.add_re]
    have hwre : |w.re| ≤ ‖w‖ := by
      have := Complex.abs_re_le_norm w
      exact this
    have h1 : ((1 : ℂ) + (ω : ℂ) + w).re ≤ ‖1 + (ω : ℂ) + w‖ := Complex.re_le_norm _
    have h2 : -w.re ≤ ‖w‖ := by
      have := abs_le.1 hwre
      linarith [this.1]
    rw [hre] at h1
    have : ‖w‖ ≤ ρ / 4 := hw
    have hρ32 : ρ / 4 ≤ 1 / 32 := by linarith
    linarith
  have haub : ∀ w : ℂ, ‖w‖ ≤ ρ / 4 → ‖1 + (ω : ℂ) + w‖ ≤ 2 := by
    intro w hw
    have h1 : ‖1 + (ω : ℂ) + w‖ ≤ ‖(1 : ℂ) + (ω : ℂ)‖ + ‖w‖ := norm_add_le _ _
    have h2 : ‖(1 : ℂ) + (ω : ℂ)‖ ≤ 1 + ω := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hω]
    have : ω ≤ ρ / 8 := hωle
    linarith
  have huub : ∀ w : ℂ, ‖w‖ ≤ ρ / 4 → ‖2 * (ω : ℂ) + w‖ ≤ 1 / 2 := by
    intro w hw
    have h2 : ‖2 * (ω : ℂ) + w‖ ≤ 2 * ω + ‖w‖ := by
      refine le_trans (norm_add_le _ _) ?_
      have : ‖2 * ((ω : ℝ) : ℂ)‖ = 2 * ω := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hω]
        norm_num
      rw [this]
    have : ω ≤ ρ / 8 := hωle
    linarith
  -- bounds on the numerator, denominator and their derivatives
  have hnum : ∀ w : ℂ, ‖w‖ ≤ ρ / 4 → ‖poleQNum ω w‖ ≤ B := by
    intro w hw
    obtain ⟨-, hZ, hZ', -⟩ := hbd _ (hmemZ w hw)
    have hZ0 : (0 : ℝ) ≤ ‖zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖ := norm_nonneg _
    have ha := haub w hw
    have hu := huub w hw
    have ha0 : (0 : ℝ) ≤ ‖1 + (ω : ℂ) + w‖ := norm_nonneg _
    have hu0 : (0 : ℝ) ≤ ‖2 * (ω : ℂ) + w‖ := norm_nonneg _
    have e1 : ‖2 * ((1 + (ω : ℂ) + w) * zetaPoleUnit (1 + 2 * (ω : ℂ) + w))‖
        = 2 * (‖1 + (ω : ℂ) + w‖ * ‖zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖) := by
      rw [norm_mul, norm_mul]
      norm_num
    have e2 : ‖(2 * (ω : ℂ) + w) * (zetaPoleUnit (1 + 2 * (ω : ℂ) + w) +
        (1 + (ω : ℂ) + w) * (2 * deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + w)))‖
        ≤ ‖2 * (ω : ℂ) + w‖ * (‖zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖ +
          ‖1 + (ω : ℂ) + w‖ * (2 * ‖deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖)) := by
      rw [norm_mul]
      gcongr
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul]
      norm_num
    have e3 := norm_sub_le (2 * ((1 + (ω : ℂ) + w) * zetaPoleUnit (1 + 2 * (ω : ℂ) + w)))
      ((2 * (ω : ℂ) + w) * (zetaPoleUnit (1 + 2 * (ω : ℂ) + w) +
        (1 + (ω : ℂ) + w) * (2 * deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + w))))
    have hp1 : ‖1 + (ω : ℂ) + w‖ * ‖zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖ ≤ 2 * Cb :=
      mul_le_mul ha hZ hZ0 (by norm_num)
    have hp2 : ‖1 + (ω : ℂ) + w‖ * (2 * ‖deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖)
        ≤ 2 * (2 * Cb) := mul_le_mul ha (by linarith) (by positivity) (by norm_num)
    have hp3 : ‖2 * (ω : ℂ) + w‖ * (‖zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖ +
        ‖1 + (ω : ℂ) + w‖ * (2 * ‖deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖))
        ≤ (1 / 2) * (Cb + 2 * (2 * Cb)) :=
      mul_le_mul hu (by linarith) (by positivity) (by norm_num)
    have hfinal : (2 : ℝ) * (2 * Cb) + (1 / 2) * (Cb + 2 * (2 * Cb)) ≤ B := by
      rw [hBdef]
      nlinarith
    rw [poleQNum]
    linarith [e3, e1.le, e2, hp1, hp3]
  have hnumd : ∀ w : ℂ, ‖w‖ ≤ ρ / 4 → ‖poleQNumDeriv ω w‖ ≤ B := by
    intro w hw
    obtain ⟨-, hZ, hZ', hZ''⟩ := hbd _ (hmemZ w hw)
    have ha := haub w hw
    have hu := huub w hw
    have e2 : ‖(2 * (ω : ℂ) + w) * (3 * deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + w) +
        2 * (1 + (ω : ℂ) + w) * deriv (deriv zetaPoleUnit) (1 + 2 * (ω : ℂ) + w))‖
        ≤ ‖2 * (ω : ℂ) + w‖ * (3 * ‖deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖ +
          2 * ‖1 + (ω : ℂ) + w‖ * ‖deriv (deriv zetaPoleUnit) (1 + 2 * (ω : ℂ) + w)‖) := by
      rw [norm_mul]
      gcongr
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul, norm_mul]
      norm_num
    have e3 := norm_sub_le (zetaPoleUnit (1 + 2 * (ω : ℂ) + w))
      ((2 * (ω : ℂ) + w) * (3 * deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + w) +
        2 * (1 + (ω : ℂ) + w) * deriv (deriv zetaPoleUnit) (1 + 2 * (ω : ℂ) + w)))
    have hp2 : 2 * ‖1 + (ω : ℂ) + w‖ * ‖deriv (deriv zetaPoleUnit) (1 + 2 * (ω : ℂ) + w)‖
        ≤ 2 * 2 * Cb := by
      have h1 : (0 : ℝ) ≤ ‖deriv (deriv zetaPoleUnit) (1 + 2 * (ω : ℂ) + w)‖ := norm_nonneg _
      nlinarith [norm_nonneg (1 + (ω : ℂ) + w)]
    have hp3 : ‖2 * (ω : ℂ) + w‖ * (3 * ‖deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖ +
        2 * ‖1 + (ω : ℂ) + w‖ * ‖deriv (deriv zetaPoleUnit) (1 + 2 * (ω : ℂ) + w)‖)
        ≤ (1 / 2) * (3 * Cb + 2 * 2 * Cb) :=
      mul_le_mul hu (by linarith) (by positivity) (by norm_num)
    have hfinal : Cb + (1 / 2) * (3 * Cb + 2 * 2 * Cb) ≤ B := by
      rw [hBdef]
      nlinarith
    rw [poleQNumDeriv]
    linarith [e3, e2, hp3]
  have hden : ∀ w : ℂ, ‖w‖ ≤ ρ / 4 → ‖poleQDen ω w‖ ≤ B := by
    intro w hw
    obtain ⟨-, hZ, -, -⟩ := hbd _ (hmemZ w hw)
    have ha := haub w hw
    have e1 : ‖poleQDen ω w‖ = (‖1 + (ω : ℂ) + w‖ * ‖zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖) ^ 2 := by
      rw [poleQDen, norm_pow, norm_mul]
    have hp1 : ‖1 + (ω : ℂ) + w‖ * ‖zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖ ≤ 2 * Cb :=
      mul_le_mul ha hZ (norm_nonneg _) (by norm_num)
    have hp0 : (0 : ℝ) ≤ ‖1 + (ω : ℂ) + w‖ * ‖zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖ := by positivity
    rw [e1, hBdef]
    nlinarith
  have hdend : ∀ w : ℂ, ‖w‖ ≤ ρ / 4 → ‖poleQDenDeriv ω w‖ ≤ B := by
    intro w hw
    obtain ⟨-, hZ, hZ', -⟩ := hbd _ (hmemZ w hw)
    have ha := haub w hw
    have e1 : ‖poleQDenDeriv ω w‖
        = 2 * (‖1 + (ω : ℂ) + w‖ * ‖zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖) *
          ‖zetaPoleUnit (1 + 2 * (ω : ℂ) + w) +
            (1 + (ω : ℂ) + w) * deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖ := by
      rw [poleQDenDeriv, norm_mul, norm_mul, norm_mul]
      norm_num
    have e2 : ‖zetaPoleUnit (1 + 2 * (ω : ℂ) + w) +
        (1 + (ω : ℂ) + w) * deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖
        ≤ Cb + 2 * Cb := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul]
      have : ‖1 + (ω : ℂ) + w‖ * ‖deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖ ≤ 2 * Cb :=
        mul_le_mul ha hZ' (norm_nonneg _) (by norm_num)
      linarith
    have hp1 : ‖1 + (ω : ℂ) + w‖ * ‖zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖ ≤ 2 * Cb :=
      mul_le_mul ha hZ (norm_nonneg _) (by norm_num)
    have hp0 : (0 : ℝ) ≤ ‖1 + (ω : ℂ) + w‖ * ‖zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖ := by positivity
    have hq0 : (0 : ℝ) ≤ ‖zetaPoleUnit (1 + 2 * (ω : ℂ) + w) +
        (1 + (ω : ℂ) + w) * deriv zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖ := norm_nonneg _
    rw [e1, hBdef]
    nlinarith
  have hdenlb : ∀ w : ℂ, ‖w‖ ≤ ρ / 4 → (1 / 16 : ℝ) ≤ ‖poleQDen ω w‖ := by
    intro w hw
    obtain ⟨hZlb, -, -, -⟩ := hbd _ (hmemZ w hw)
    have ha := halb w hw
    have e1 : ‖poleQDen ω w‖ = (‖1 + (ω : ℂ) + w‖ * ‖zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖) ^ 2 := by
      rw [poleQDen, norm_pow, norm_mul]
    have h4 : (1 / 4 : ℝ) ≤ ‖1 + (ω : ℂ) + w‖ * ‖zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖ := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ‖1 + (ω : ℂ) + w‖ - 1 / 2)
        (by linarith : (0 : ℝ) ≤ ‖zetaPoleUnit (1 + 2 * (ω : ℂ) + w)‖ - 1 / 2)]
    rw [e1]
    nlinarith [h4]
  -- mean-value bounds
  have hzball : z ∈ closedBall (0 : ℂ) (ρ / 4) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hzδ
  have h0ball : (0 : ℂ) ∈ closedBall (0 : ℂ) (ρ / 4) := by
    rw [Metric.mem_closedBall, dist_self]
    linarith
  have hmvN : ‖poleQNum ω z - poleQNum ω 0‖ ≤ B * ‖z‖ := by
    have h := HTGeometry.norm_sub_le_of_hasDerivAt_ball (f := fun w : ℂ => poleQNum ω w)
      (f' := fun w : ℂ => poleQNumDeriv ω w) (c := (0 : ℂ)) (r := ρ / 4) (C := B)
      (fun w => hasDerivAt_poleQNum ω w)
      (fun w hw => hnumd w (by rwa [Metric.mem_closedBall, dist_zero_right] at hw))
      h0ball hzball
    simpa using h
  have hmvD : ‖poleQDen ω z - poleQDen ω 0‖ ≤ B * ‖z‖ := by
    have h := HTGeometry.norm_sub_le_of_hasDerivAt_ball (f := fun w : ℂ => poleQDen ω w)
      (f' := fun w : ℂ => poleQDenDeriv ω w) (c := (0 : ℂ)) (r := ρ / 4) (C := B)
      (fun w => hasDerivAt_poleQDen ω w)
      (fun w hw => hdend w (by rwa [Metric.mem_closedBall, dist_zero_right] at hw))
      h0ball hzball
    simpa using h
  have hmvZ : ‖zetaPoleUnit (1 + z) - 1‖ ≤ Cb * ‖z‖ := by
    have h := HTGeometry.norm_sub_le_of_hasDerivAt_ball (f := fun w : ℂ => zetaPoleUnit (1 + w))
      (f' := fun w : ℂ => deriv zetaPoleUnit (1 + w)) (c := (0 : ℂ)) (r := ρ / 4) (C := Cb)
      (fun w => hasDerivAt_zetaPoleUnit_one_add w)
      (fun w hw => (hbd _ (hmem1 w (by rwa [Metric.mem_closedBall, dist_zero_right] at hw))).2.2.1)
      h0ball hzball
    simpa [zetaPoleUnit_one] using h
  -- the quotient difference
  have hq : ‖mobiusCausalQDeriv ω z - mobiusCausalQDeriv ω 0‖ ≤ 2 * B * (B * ‖z‖) / (1 / 16 : ℝ) ^ 2 := by
    rw [mobiusCausalQDeriv_eq_div, mobiusCausalQDeriv_eq_div]
    refine HTGeometry.norm_div_sub_div_le (by norm_num)
      (hdenlb z hzδ) (hdenlb 0 (by simpa using le_of_lt (by linarith : (0:ℝ) < ρ / 4)))
      (hnum 0 (by simpa using le_of_lt (by linarith : (0:ℝ) < ρ / 4)))
      (hden 0 (by simpa using le_of_lt (by linarith : (0:ℝ) < ρ / 4)))
      hmvN hmvD (by positivity)
  have hq0 : ‖mobiusCausalQDeriv ω 0‖ ≤ B / (1 / 16 : ℝ) := by
    rw [mobiusCausalQDeriv_eq_div, norm_div]
    have h1 := hnum 0 (by simpa using le_of_lt (by linarith : (0:ℝ) < ρ / 4))
    have h2 := hdenlb 0 (by simpa using le_of_lt (by linarith : (0:ℝ) < ρ / 4))
    exact div_le_div₀ hB0 h1 (by norm_num) h2
  have hZub : ‖zetaPoleUnit (1 + z)‖ ≤ Cb := (hbd _ (hmem1 z hzδ)).2.1
  -- assemble
  have hsplit : mobiusCausalNumeratorDeriv ω z
      = zetaPoleUnit (1 + z) * (mobiusCausalQDeriv ω z - mobiusCausalQDeriv ω 0) +
        (zetaPoleUnit (1 + z) - 1) * mobiusCausalQDeriv ω 0 := by
    rw [mobiusCausalNumeratorDeriv]
    ring
  have hznorm : (0 : ℝ) < ‖z‖ := by
    rw [norm_pos_iff]
    exact hz0
  rw [mobiusCausalMultiplierDeriv_eq_numeratorDeriv_div hω hzre hz0, norm_div, hsplit]
  have hnorm : ‖zetaPoleUnit (1 + z) * (mobiusCausalQDeriv ω z - mobiusCausalQDeriv ω 0) +
      (zetaPoleUnit (1 + z) - 1) * mobiusCausalQDeriv ω 0‖
      ≤ (Cb * (2 * B * (B * ‖z‖) / (1 / 16 : ℝ) ^ 2) + Cb * ‖z‖ * (B / (1 / 16 : ℝ))) := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖zetaPoleUnit (1 + z)‖ * ‖mobiusCausalQDeriv ω z - mobiusCausalQDeriv ω 0‖
        ≤ Cb * (2 * B * (B * ‖z‖) / (1 / 16 : ℝ) ^ 2) :=
      mul_le_mul hZub hq (norm_nonneg _) (by positivity)
    have h2 : ‖zetaPoleUnit (1 + z) - 1‖ * ‖mobiusCausalQDeriv ω 0‖ ≤ Cb * ‖z‖ * (B / (1 / 16 : ℝ)) :=
      mul_le_mul hmvZ hq0 (norm_nonneg _) (by positivity)
    linarith
  rw [div_le_iff₀ hznorm]
  have hfin : (Cb * (2 * B * (B * ‖z‖) / (1 / 16 : ℝ) ^ 2) + Cb * ‖z‖ * (B / (1 / 16 : ℝ)))
      = (Cb * (2 * B * B / (1 / 16 : ℝ) ^ 2) + Cb * (B / (1 / 16 : ℝ))) * ‖z‖ := by
    ring
  rw [← hfin]
  exact hnorm

end

end RHTower
