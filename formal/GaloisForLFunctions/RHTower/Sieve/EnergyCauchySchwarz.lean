import GaloisForLFunctions.RHTower.Sieve.SecondReciprocalEnergy

/-!
# Cauchy–Schwarz between the two reciprocal energies

The two energies of a factored Dirichlet polynomial carry exactly reciprocal powers of the shell
parameter, so their geometric mean is free of it.  The inequality itself is the discriminant of the
nonnegative quadratic `λ ↦ ∫ (f − λg)²`, which needs no completeness and no `L²` structure.
-/

namespace RHTower.Sieve

open MeasureTheory

noncomputable section

/-- **Cauchy–Schwarz for an interval integral.**  The discriminant of `λ ↦ ∫ (f − λg)²`. -/
theorem integral_mul_sq_le {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    (∫ t in a..b, f t * g t) ^ 2
      ≤ (∫ t in a..b, f t ^ 2) * (∫ t in a..b, g t ^ 2) := by
  set A : ℝ := ∫ t in a..b, f t ^ 2 with hA
  set Bv : ℝ := ∫ t in a..b, f t * g t with hB
  set C : ℝ := ∫ t in a..b, g t ^ 2 with hC
  have hAnn : 0 ≤ A := by
    rw [hA]
    exact intervalIntegral.integral_nonneg hab fun t _ => by positivity
  have hCnn : 0 ≤ C := by
    rw [hC]
    exact intervalIntegral.integral_nonneg hab fun t _ => by positivity
  have hquad : ∀ lam : ℝ, 0 ≤ A - 2 * lam * Bv + lam ^ 2 * C := by
    intro lam
    have hnn : (0 : ℝ) ≤ ∫ t in a..b, (f t - lam * g t) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun t _ => by positivity
    have hexp : (∫ t in a..b, (f t - lam * g t) ^ 2)
        = A - 2 * lam * Bv + lam ^ 2 * C := by
      have hpt : ∀ t : ℝ, (f t - lam * g t) ^ 2
          = f t ^ 2 - 2 * lam * (f t * g t) + lam ^ 2 * (g t ^ 2) := by
        intro t; ring
      rw [funext hpt]
      have hI1 : IntervalIntegrable (fun t : ℝ => f t ^ 2) volume a b :=
        (hf.pow 2).intervalIntegrable _ _
      have hI2 : IntervalIntegrable (fun t : ℝ => 2 * lam * (f t * g t)) volume a b :=
        (continuous_const.mul (hf.mul hg)).intervalIntegrable _ _
      have hI3 : IntervalIntegrable (fun t : ℝ => lam ^ 2 * g t ^ 2) volume a b :=
        (continuous_const.mul (hg.pow 2)).intervalIntegrable _ _
      rw [intervalIntegral.integral_add (hI1.sub hI2) hI3,
        intervalIntegral.integral_sub hI1 hI2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [hexp] at hnn
    exact hnn
  rcases eq_or_lt_of_le hCnn with hC0 | hCpos
  · have hlin : ∀ lam : ℝ, 0 ≤ A - 2 * lam * Bv := by
      intro lam
      have h := hquad lam
      rw [← hC0] at h
      linarith
    have hBv0 : Bv = 0 := by
      by_contra hne
      have h := hlin ((A + 1) / (2 * Bv))
      have hid : 2 * ((A + 1) / (2 * Bv)) * Bv = A + 1 := by field_simp
      rw [hid] at h
      linarith
    rw [hBv0, ← hC0]
    norm_num
  · have h := hquad (Bv / C)
    have hid : A - 2 * (Bv / C) * Bv + (Bv / C) ^ 2 * C = A - Bv ^ 2 / C := by
      field_simp
      ring
    rw [hid] at h
    have hstep : Bv ^ 2 / C ≤ A := by linarith
    rw [div_le_iff₀ hCpos] at hstep
    linarith

/-- **Equation (F3): the Cauchy–Schwarz step between the two energies.** -/
theorem energy_cauchy_schwarz_le {T : ℝ} (hT : 0 ≤ T) {A B F : ℝ → ℝ}
    (hA : Continuous A) (hB : Continuous B) (hF : Continuous F) (hFnn : ∀ t, 0 ≤ F t)
    {I1 I2 : ℝ}
    (h1 : (∫ t in (-T)..T, A t ^ 2) ≤ I1)
    (h2 : (∫ t in (-T)..T, B t ^ 2 * F t / (1 + t ^ 2)) ≤ I2) :
    (∫ t in (-T)..T, A t * (B t * Real.sqrt (F t) / Real.sqrt (1 + t ^ 2)))
      ≤ Real.sqrt (I1 * I2) := by
  have hle : (-T : ℝ) ≤ T := by linarith
  set g : ℝ → ℝ := fun t => B t * Real.sqrt (F t) / Real.sqrt (1 + t ^ 2) with hg
  have hgc : Continuous g := by
    refine (hB.mul (Real.continuous_sqrt.comp hF)).div
      (Real.continuous_sqrt.comp (by continuity)) fun t => ?_
    have h1t : (0 : ℝ) < 1 + t ^ 2 := by positivity
    exact (Real.sqrt_pos.2 h1t).ne'
  have hgsq : ∀ t : ℝ, g t ^ 2 = B t ^ 2 * F t / (1 + t ^ 2) := by
    intro t
    have h1t : (0 : ℝ) < 1 + t ^ 2 := by positivity
    rw [hg, div_pow, mul_pow, Real.sq_sqrt (hFnn t), Real.sq_sqrt h1t.le]
  have hcs := integral_mul_sq_le hle hA hgc
  rw [funext hgsq] at hcs
  have hAnn : (0 : ℝ) ≤ ∫ t in (-T)..T, A t ^ 2 :=
    intervalIntegral.integral_nonneg hle fun t _ => by positivity
  have hgnn : (0 : ℝ) ≤ ∫ t in (-T)..T, B t ^ 2 * F t / (1 + t ^ 2) := by
    refine intervalIntegral.integral_nonneg hle fun t _ => ?_
    have h1t : (0 : ℝ) < 1 + t ^ 2 := by positivity
    have := hFnn t
    positivity
  have hprod : (∫ t in (-T)..T, A t ^ 2) * (∫ t in (-T)..T, B t ^ 2 * F t / (1 + t ^ 2))
      ≤ I1 * I2 := by
    refine mul_le_mul h1 h2 hgnn (le_trans hAnn h1)
  have hsq : (∫ t in (-T)..T, A t * g t) ^ 2 ≤ I1 * I2 := le_trans hcs hprod
  have habs : |∫ t in (-T)..T, A t * g t| ≤ Real.sqrt (I1 * I2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  exact le_trans (le_abs_self _) habs

/-- The two energies carry reciprocal powers of the shell parameter, so their geometric mean is
free of it. -/
theorem sqrt_reciprocal_energies {C₁ C₂ L u : ℝ} (hu : 0 < u) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hL : 0 ≤ L) :
    Real.sqrt ((C₁ / u) * (C₂ * L ^ 2 * u)) = Real.sqrt (C₁ * C₂) * L := by
  have hid : (C₁ / u) * (C₂ * L ^ 2 * u) = (C₁ * C₂) * L ^ 2 := by
    field_simp
  rw [hid, Real.sqrt_mul (by positivity), Real.sqrt_sq hL]

end

end RHTower.Sieve
