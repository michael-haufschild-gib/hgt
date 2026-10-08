import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticNotchSourceBound

/-!
# Harmonic smallness excludes a positive notch-ramp floor

The refined moment lower bound and the exact shifted-pole upper bound
meet at one good scale. No uniform square-root mass decay is assumed.
-/

noncomputable section
open Finset GaloisForLFunctions.HTGeometry

namespace RHTower.WeilSingularArithmetic
open WeilAbscissa ZetaNotch

/-- The abstract ramp receiver needs only harmonic smallness and its actual
pairing summability inputs. -/
theorem nonpos_of_rampPartial_ge_harmonic {q : ℝ → ℝ} {Q : ℂ → ℂ}
    (hQd : Differentiable ℂ Q) {CQ : ℝ} (hQb1 : ∀ z : ℂ, |z.im| ≤ 1 → ‖Q z‖ ≤ CQ)
    (hQq : ∀ t : ℝ, Q t = q t) (hq0 : ∀ t, 0 ≤ q t) (hqc : Continuous q)
    (hqb : ∀ t, |q t| ≤ CQ) {W : ℕ → ℝ} {eP K₀ Dr : ℝ}
    (heP : 0 < eP) (hK₀ : 1 ≤ K₀) (hDr : 0 ≤ Dr)
    (hmoment : ∀ {v : ℕ → ℝ}, v 0 = 0 → ∀ N : ℕ, ∀ u : ℝ, 16 ≤ u →
      eP * u * rampSum (fun n => v n * W n) N K₀ notchProfileMass notchProfileLogMass u -
        Dr * refErrSum v (range (N + 1)) (2 * K₀ ^ 3) 7 u ≤
          ∑ n ∈ range (N + 1), v n * (ZetaNotch.weightedMoment u q (Real.log n)).re)
    {v : ℕ → ℝ} (hv0 : v 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hs34 : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-(3 / 4 : ℝ)))
    (hs1 : Summable fun n : ℕ => |v n| * (n : ℝ)⁻¹)
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ))
    (hharm : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ range (N + 1), |sqrtScaled v n| / n) ≤ B + η * Real.log N)
    {Y B : ℝ} {T : ℕ} (hT : 1 ≤ T)
    (hB : ∀ k, -B ≤ rampPartial (fun n => v n * W n) k)
    (hfloor : ∀ k, T ≤ k → Y ≤ rampPartial (fun n => v n * W n) k) : Y ≤ 0 := by
  by_contra hY
  push Not at hY
  let a (n : ℕ) := v n * W n
  have ha0 : a 0 = 0 := by simp [a, hv0]
  have hβ : 0 < notchProfileMass := lt_of_lt_of_le zero_lt_one one_le_notchProfileMass
  obtain ⟨CG, hCG⟩ := exists_rampSum_ge a ha0 (β₁ := notchProfileLogMass) hY.le
    hβ.le notchProfile_log_two_add_nonneg hK₀ hT hB hfloor
  let k := eP * notchProfileMass * Y
  let C₀ := eP * max CG 0
  have hk : 0 < k := by dsimp [k]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hc : 0 < 2 * K₀ ^ 3 := by positivity
  have hE (N : ℕ) (hNT : T ≤ N) (u : ℝ) (hu : 16 ≤ u) :
      u * (k * Real.log u - C₀) - Dr * refErrSum v (range (N + 1)) (2 * K₀ ^ 3) 7 u ≤
        ∑ n ∈ range (N + 1), v n * (ZetaNotch.weightedMoment u q (Real.log n)).re := by
    have hm := hmoment hv0 N u hu
    have hr := hCG N hNT u (by linarith)
    have hhead : notchProfileMass * Y * Real.log u - max CG 0 ≤
        rampSum a N K₀ notchProfileMass notchProfileLogMass u := by
      have := le_max_left CG 0
      linarith
    have hmul := mul_le_mul_of_nonneg_left hhead (show 0 ≤ eP * u by positivity)
    dsimp [k, C₀, a] at *
    nlinarith only [hm, hmul]
  obtain ⟨K, hK, hscale⟩ := exists_pairing_notchMassBudget_bound hQd hQb1 hQq hq0 hqc hqb
    hv0 hA ha hs34 hs1 hPD hk hC₀ hDr hc hE
  have hκ : 0 < 2 * Real.exp (-1) * k := by positivity
  obtain ⟨L, hL, hlt⟩ := exists_notchMassBudget_lt_log_floor (sqrtScaled v) hharm
    (mul_pos (by norm_num : (0 : ℝ) < 2) hc) hκ hK (C₀ * gaussHalf) (32 + T)
  exact (not_lt_of_ge (hscale L ((le_max_right _ _).trans hL))) hlt

end RHTower.WeilSingularArithmetic
