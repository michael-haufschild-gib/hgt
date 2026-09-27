import GaloisForLFunctions.RHTower.XiGaussianSpectralGapCancellation
import GaloisForLFunctions.RHTower.PolynomialGaussianCompletedPrimeGammaWedge
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The fixed critical-node floor does not dominate the current global budget

For the constant polynomial alone, the gap envelope eventually exceeds every
fixed floor with rate greater than 32. This separates two proved estimates; it
does not assert a negative actual Hankel form or an obstruction to a sharper
signed phase estimate.
-/

open scoped Real SchwartzMap
open Filter MeasureTheory GaloisForLFunctions
noncomputable section

namespace RHTower

/-- Fixed positive Gaussian mass left after the constant polynomial's heat Jacobian cancels. -/
def xiGaussianConstantNormMass : ℝ :=
  ‖(polyGaussSchwartz (evenSquarePolynomial (1 : Polynomial ℝ))).toLp 2
    (volume : Measure ℝ)‖ ^ 2

theorem xiGaussianConstantNormMass_eq_scaled_mass (t : {t : ℝ // 0 < t}) :
    xiGaussianConstantNormMass =
      (xiGaussianHeatScale t : ℝ) * routeUPolynomialGaussianMass 1 t := by
  simpa only [xiGaussianUnscalePolynomial, Polynomial.one_comp, xiGaussianConstantNormMass]
    using xiGaussianUnscalePolynomial_norm_sq 1 t

theorem xiGaussianConstantNormMass_pos : 0 < xiGaussianConstantNormMass := by
  rw [xiGaussianConstantNormMass_eq_scaled_mass ⟨1, one_pos⟩]
  exact mul_pos (xiGaussianHeatScale ⟨1, one_pos⟩).property
    (routeUPolynomialGaussianMass_pos ⟨1, one_ne_zero⟩ ⟨1, one_pos⟩)

/-- Even in the constant direction, the current envelope has a slower-decaying lower bound
than the critical-node floor. This is a bound on the envelope, not on actual phase debt. -/
theorem xiGaussianGapBudget_constant_mass_ge (d : ℕ) (t : {t : ℝ // 0 < t}) :
    (8 * (198 / 3175 : ℝ) * xiGaussianConstantNormMass / (t : ℝ)) *
      Real.exp (-(125 * (t : ℝ) / 16)) ≤
        xiGaussianGapCancellationBudget d t *
          routeUPolynomialGaussianMass 1 (xiGaussianHalfHeat t) := by
  let C : ℝ := 1 + 2 * Real.sqrt (4 * π * ((d : ℝ) + 3))
  let S : ℝ := 4 * (d : ℝ) + 9 + 3 / 4 * Real.sqrt ((t : ℝ) * ((d : ℝ) + 2))
  have hC : 1 ≤ C :=
    le_add_of_nonneg_right (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  have hS : 1 ≤ S := by
    dsimp only [S]
    have h := Real.sqrt_nonneg ((t : ℝ) * ((d : ℝ) + 2))
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith only [h, hd]
  have hS2 : 1 ≤ S ^ 2 := by nlinarith only [hS, sq_nonneg (S - 1)]
  have he : Real.exp (-(125 * (t : ℝ) / 16)) ≤
      Real.exp (-(125 * (t : ℝ) / 16) + Real.sqrt ((t : ℝ) * ((d : ℝ) + 2))) :=
    Real.exp_le_exp.mpr (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hp : Real.exp (-(125 * (t : ℝ) / 16)) ≤ C *
      Real.exp (-(125 * (t : ℝ) / 16) + Real.sqrt ((t : ℝ) * ((d : ℝ) + 2))) * S ^ 2 := by
    simpa only [one_mul, mul_one] using
      mul_le_mul (mul_le_mul hC he (Real.exp_pos _).le (by linarith only [hC]))
        hS2 zero_le_one (mul_nonneg (zero_le_one.trans hC) (Real.exp_pos _).le)
  have hm := xiGaussianConstantNormMass_eq_scaled_mass (xiGaussianHalfHeat t)
  have hb := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (8 / (t : ℝ)) * (198 / 3175 : ℝ) * xiGaussianConstantNormMass by
      exact mul_nonneg (mul_nonneg (div_nonneg (by positivity) t.property.le)
        (by positivity)) xiGaussianConstantNormMass_pos.le)
  rw [xiGaussianGapCancellationBudget_eq]
  calc
    _ = ((8 / (t : ℝ)) * (198 / 3175 : ℝ) * xiGaussianConstantNormMass) *
        Real.exp (-(125 * (t : ℝ) / 16)) := by ring
    _ ≤ _ := hb
    _ = _ := by rw [hm]; dsimp only [C, S]; ring

/-- At arbitrarily large positive times, the existing full budget exceeds twice any fixed
critical-node floor. Thus these two bounds alone cannot certify all-time positivity. -/
theorem exists_xiGaussianGapBudget_exceeds_critical_floor
    (c : {c : ℝ // 0 < c}) (L : {L : ℝ // 32 < L}) (d : ℕ) (T : ℝ) :
    ∃ t : {t : ℝ // 0 < t}, T < (t : ℝ) ∧
      2 * (c : ℝ) * Real.exp (-((L : ℝ) * (t : ℝ))) <
        xiGaussianGapCancellationBudget d t *
          routeUPolynomialGaussianMass 1 (xiGaussianHalfHeat t) := by
  let k : ℝ := 8 * (198 / 3175 : ℝ) * xiGaussianConstantNormMass
  have hk : 0 < k := mul_pos (by positivity) xiGaussianConstantNormMass_pos
  have hrate : 0 < (L : ℝ) - 125 / 16 := by linarith only [L.property]
  have hlim : Tendsto (fun x : ℝ => x * Real.exp (-((L : ℝ) - 125 / 16) * x))
      atTop (nhds 0) := by
    simpa only [Real.rpow_one] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 ((L : ℝ) - 125 / 16) hrate
  have hev := hlim.eventually
    (gt_mem_nhds (div_pos hk (mul_pos (by positivity : (0 : ℝ) < 2) c.property)))
  obtain ⟨x, hx, hx0, hxT⟩ :=
    (hev.and ((eventually_gt_atTop (0 : ℝ)).and (eventually_gt_atTop T))).exists
  let t : {t : ℝ // 0 < t} := ⟨x, hx0⟩
  refine ⟨t, hxT, ?_⟩
  have hsmall : 2 * (c : ℝ) * (x * Real.exp (-((L : ℝ) - 125 / 16) * x)) < k := by
    have h := (lt_div_iff₀ (mul_pos (by positivity : (0 : ℝ) < 2) c.property)).mp hx
    nlinarith only [h]
  have he : Real.exp (-((L : ℝ) - 125 / 16) * x) * Real.exp (-(125 * x / 16)) =
      Real.exp (-((L : ℝ) * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hbound : 2 * (c : ℝ) * Real.exp (-((L : ℝ) * x)) <
      (k / x) * Real.exp (-(125 * x / 16)) := by
    calc
      _ = (2 * (c : ℝ) * (x * Real.exp (-((L : ℝ) - 125 / 16) * x))) *
          (Real.exp (-(125 * x / 16)) / x) := by
        rw [← he]
        field_simp
      _ < k * (Real.exp (-(125 * x / 16)) / x) :=
        mul_lt_mul_of_pos_right hsmall (div_pos (Real.exp_pos _) hx0)
      _ = _ := by ring
  exact hbound.trans_le (xiGaussianGapBudget_constant_mass_ge d t)

end RHTower
