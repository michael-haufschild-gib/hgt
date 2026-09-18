import GaloisForLFunctions.RHTower.XiWardCubicAdaptiveSecantHalfDensityQuantum

/-!
# Cubic Ward adaptive primitive-sector no-go

W-H207 rules out a uniform cubic-charge bound from one fixed primitive lower secant.  This
strengthens that no-go to every adaptive selection of a *single* literal primitive secant: both
its rate and aperture may vary with horizontal depth, but the rate remains at least `1 / 2`, as
every primitive Euler rate does, and the aperture stays nonnegative.

The obstruction is uniform.  On `0 ≤ a ≤ 1 / 4`, every such reflection defect has absolute value
at most `128 a`; its square therefore vanishes quadratically while the cubic Hellinger charge has
a fixed positive lower quantum.  Thus adapting a pole within the primitive Euler sector cannot
produce W-H208's inverse-square scale.  The surviving mechanism must create its sub-Euler doubled
rate before divisor restriction (the completed bichamber current), or use genuinely collective
signed current data rather than one primitive secant.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- Uniform primitive-sector estimate: a lower Cauchy secant with rate at least `1 / 2` has at
most linear reflection defect near the critical line, regardless of its nonnegative aperture. -/
theorem xiWardCubicPrimitiveLowerSecantReflectionDefect_abs_le_linear_of_eulerRate
    {lambda c a : ℝ} (hlambda : 1 / 2 ≤ lambda) (hc : 0 ≤ c)
    (ha : 0 ≤ a) (haq : a ≤ 1 / 4) :
    |xiWardCubicPrimitiveLowerSecantReflectionDefect lambda c a| ≤ 128 * a := by
  have hlambda0 : 0 ≤ lambda := by linarith
  have hlc0 : 0 ≤ lambda + c := by linarith
  have hla : lambda / 2 ≤ lambda - a := by linarith
  have hlca : (lambda + c) / 2 ≤ lambda + c - a := by linarith
  have hla0 : 0 ≤ lambda - a := le_trans (by positivity) hla
  have hlca0 : 0 ≤ lambda + c - a := le_trans (by positivity) hlca
  have hlpa : lambda ≤ lambda + a := by linarith
  have hlcpa : lambda + c ≤ lambda + c + a := by linarith
  have hden12 : (lambda / 2) * ((lambda + c) / 2) ≤
      (lambda - a) * (lambda + c - a) := by
    exact mul_le_mul hla hlca (by positivity) hla0
  have hden34 : lambda * (lambda + c) ≤
      (lambda + a) * (lambda + c + a) := by
    exact mul_le_mul hlpa hlcpa hlc0 (by positivity)
  have hden : lambda ^ 2 * (lambda + c) ^ 2 / 4 ≤
      (lambda - a) * (lambda + c - a) * (lambda + a) * (lambda + c + a) := by
    calc
      lambda ^ 2 * (lambda + c) ^ 2 / 4 =
          ((lambda / 2) * ((lambda + c) / 2)) * (lambda * (lambda + c)) := by ring
      _ ≤ ((lambda - a) * (lambda + c - a)) *
          ((lambda + a) * (lambda + c + a)) :=
        mul_le_mul hden12 hden34 (by positivity) (by positivity)
      _ = _ := by ring
  have hsum : lambda + (lambda + c) ≤ 16 * lambda ^ 2 * (lambda + c) ^ 2 := by
    have hx : 0 ≤ 2 * lambda - 1 := by linarith
    have hy : 0 ≤ 2 * (lambda + c) - 1 := by linarith
    have hxy : 0 ≤ (2 * lambda - 1) * (2 * (lambda + c) - 1) :=
      mul_nonneg hx hy
    nlinarith [sq_nonneg (4 * lambda * (lambda + c) - 1)]
  have hden' : (2 * lambda + c) / 64 ≤
      (lambda - a) * (lambda + c - a) * (lambda + a) * (lambda + c + a) := by
    have hrewrite : 2 * lambda + c = lambda + (lambda + c) := by ring
    rw [hrewrite]
    nlinarith
  have hdenpos : 0 <
      (lambda - a) * (lambda + c - a) * (lambda + a) * (lambda + c + a) := by
    have hlpos : 0 < lambda := by linarith
    have hlcpos : 0 < lambda + c := by linarith
    have hlaPos : 0 < lambda - a := lt_of_lt_of_le (half_pos hlpos) hla
    have hlcaPos : 0 < lambda + c - a := lt_of_lt_of_le (half_pos hlcpos) hlca
    have hlpaPos : 0 < lambda + a := by linarith
    have hlcpaPos : 0 < lambda + c + a := by linarith
    exact mul_pos (mul_pos (mul_pos hlaPos hlcaPos) hlpaPos) hlcpaPos
  have hnum : 0 ≤ 2 * a * (2 * lambda + c) := by positivity
  rw [xiWardCubicPrimitiveLowerSecantReflectionDefect]
  have hrewrite : -2 * a * (2 * lambda + c) = -(2 * a * (2 * lambda + c)) := by ring
  rw [hrewrite, neg_div, abs_neg, abs_div, abs_of_nonneg hnum, abs_of_pos hdenpos]
  rw [div_le_iff₀ hdenpos]
  nlinarith

/-- No uniform cubic-Hellinger domination is available from any depth-adaptive selection of one
literal primitive lower secant.  The rate and aperture can both depend arbitrarily on depth; only
the source-native constraints `rate ≥ 1 / 2` and `aperture ≥ 0` are imposed. -/
theorem not_exists_uniform_cubicHellinger_domination_by_adaptivePrimitiveLowerSecantDefect
    (rate aperture : ℝ → ℝ)
    (hrate : ∀ a, 1 / 2 ≤ rate a)
    (haperture : ∀ a, 0 ≤ aperture a) :
    ¬ ∃ C : ℝ, ∀ a : ℝ, 0 < a → a < 1 / 4 →
      cubicLogMomentHellingerHorizontalKernel a a ≤
        C * xiWardCubicPrimitiveLowerSecantReflectionDefect
          (rate a) (aperture a) a ^ 2 := by
  rintro ⟨C, hC⟩
  by_cases hCnonpos : C ≤ 0
  · let a : ℝ := 1 / 8
    have ha : 0 < a := by norm_num [a]
    have haquarter : a < 1 / 4 := by norm_num [a]
    have hquant : 0 < cubicLogMomentHellingerHorizontalKernel a a := by
      have hhalf : a ≤ 1 / 2 := by linarith
      have hlow := cubicLogMomentHellingerHorizontalKernel_self_ge ha hhalf
      linarith
    have hright : C * xiWardCubicPrimitiveLowerSecantReflectionDefect
        (rate a) (aperture a) a ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hCnonpos (sq_nonneg _)
    exact (not_le_of_gt hquant) (le_trans (hC a ha haquarter) hright)
  · have hCpos : 0 < C := lt_of_not_ge hCnonpos
    let a : ℝ := 1 / (512 * (C + 1))
    have hCplus : 0 < C + 1 := by linarith
    have hden : 0 < 512 * (C + 1) := by positivity
    have ha : 0 < a := by
      exact div_pos (by norm_num) hden
    have haquarter : a < 1 / 4 := by
      change 1 / (512 * (C + 1)) < 1 / 4
      rw [div_lt_iff₀ hden]
      nlinarith
    have hCratio : C / (C + 1) ^ 2 ≤ 1 := by
      rw [div_le_one (sq_pos_of_pos hCplus)]
      nlinarith [sq_nonneg C]
    have hmajor : C * (128 * a) ^ 2 ≤ 1 := by
      have heq : C * (128 * a) ^ 2 =
          (1 / 16 : ℝ) * (C / (C + 1) ^ 2) := by
        dsimp [a]
        field_simp [hCplus.ne']
        ring
      rw [heq]
      calc
        (1 / 16 : ℝ) * (C / (C + 1) ^ 2) ≤ (1 / 16 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hCratio (by norm_num)
        _ ≤ 1 := by norm_num
    have hdef := xiWardCubicPrimitiveLowerSecantReflectionDefect_abs_le_linear_of_eulerRate
      (hrate a) (haperture a) ha.le haquarter.le
    have hdefsq : xiWardCubicPrimitiveLowerSecantReflectionDefect
        (rate a) (aperture a) a ^ 2 ≤ (128 * a) ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hdef
    have hsource : C * xiWardCubicPrimitiveLowerSecantReflectionDefect
        (rate a) (aperture a) a ^ 2 ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left hdefsq hCpos.le) hmajor
    have hhalf : a ≤ 1 / 2 := by linarith
    have hquant := cubicLogMomentHellingerHorizontalKernel_self_ge ha hhalf
    have htarget := hC a ha haquarter
    nlinarith

end

end RHTower
