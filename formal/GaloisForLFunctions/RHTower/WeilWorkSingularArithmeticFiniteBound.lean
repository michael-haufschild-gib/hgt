import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticFiniteGaussian
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticFiniteShift
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticFiniteEnergy

/-!
# A length-uniform arithmetic quadratic bound from full positivity

The final constant depends only on the actual source. Coefficient energy,
polynomial length, and Gaussian width remain explicit.
-/

open Complex MeasureTheory

noncomputable section

namespace RHTower.WeilSingularArithmetic

open GaussZeroSum

/-- Full positivity bounds the complete finite arithmetic quadratic uniformly in its length. -/
theorem exists_re_sourceFiniteGaussianSum_energy_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (N : ℕ) (c : ℕ → ℝ) (T : ℝ), 1 ≤ T →
      (sourceFiniteGaussianSum lam N c T).re ≤
        D * sourceFiniteEnergy N c * ((N : ℝ) + 1) ^ (9 / 8 : ℝ) * T ^ (5 / 6 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_source_finite_contour_sub_gaussian_le hW
  obtain ⟨K, hK0, hK⟩ := exists_sourceFiniteEnergy_budget_le
  let P : ℝ := Real.pi * ‖sourcePoleNumerator hW 1‖ * Real.exp (1 / 4)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  refine ⟨(P + C) * K / (4 * Real.pi), by positivity, fun N c T hT => ?_⟩
  let A : ℂ := ∫ t : ℝ, sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
    gaussWeight T ((3 / 2 : ℂ) + t * I) * sourceFiniteWeight N c ((3 / 2 : ℂ) + t * I)
  let e : ℂ := A - (4 * Real.pi : ℂ) * sourceFiniteGaussianSum lam N c T
  have hE : 0 ≤ sourceFiniteEnergy N c :=
    Finset.sum_nonneg fun m _ => by positivity
  have hTp : 1 ≤ T ^ (5 / 6 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hT (show (0 : ℝ) ≤ 5 / 6 by norm_num)
  have hb : A.re ≤ P * ‖sourceFiniteWeight N c 1‖ :=
    re_integral_sourceZetaPairing_finite_right_le hW N c hT
  have hbe : A.re ≤ P * K * sourceFiniteEnergy N c *
      ((N : ℝ) + 1) ^ (9 / 8 : ℝ) * T ^ (5 / 6 : ℝ) := by
    calc
      _ ≤ P * (K * sourceFiniteEnergy N c * ((N : ℝ) + 1) ^ (9 / 8 : ℝ)) :=
        hb.trans (mul_le_mul_of_nonneg_left (hK N c).2 hP)
      _ ≤ (P * (K * sourceFiniteEnergy N c * ((N : ℝ) + 1) ^ (9 / 8 : ℝ))) * T ^ (5 / 6 : ℝ) :=
        le_mul_of_one_le_right (by positivity) hTp
      _ = _ := by ring
  have he : -e.re ≤ C * T ^ (5 / 6 : ℝ) *
      (∑ m ∈ Finset.Icc 1 N, |c m| * (m : ℝ) ^ (-9 / 8 : ℝ)) *
      (∑ n ∈ Finset.Icc 1 N, |c n| * (n : ℝ) ^ (1 / 8 : ℝ)) :=
    (neg_le_abs e.re).trans ((Complex.abs_re_le_norm e).trans (hC N c T hT))
  have hee : -e.re ≤ C * K * sourceFiniteEnergy N c *
      ((N : ℝ) + 1) ^ (9 / 8 : ℝ) * T ^ (5 / 6 : ℝ) := by
    calc
      _ ≤ C * T ^ (5 / 6 : ℝ) *
          ((∑ m ∈ Finset.Icc 1 N, |c m| * (m : ℝ) ^ (-9 / 8 : ℝ)) *
           (∑ n ∈ Finset.Icc 1 N, |c n| * (n : ℝ) ^ (1 / 8 : ℝ))) := by simpa only [mul_assoc] using he
      _ ≤ C * T ^ (5 / 6 : ℝ) *
          (K * sourceFiniteEnergy N c * ((N : ℝ) + 1) ^ (9 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hK N c).1 (by positivity)
      _ = _ := by ring
  have hid : e.re = A.re - 4 * Real.pi * (sourceFiniteGaussianSum lam N c T).re := by
    simp only [e, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.re_ofNat,
      Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
      add_zero, sub_zero]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < 4 * Real.pi)).mpr
  calc
    _ = A.re + (-e.re) := by linarith only [hid]
    _ ≤ P * K * sourceFiniteEnergy N c * ((N : ℝ) + 1) ^ (9 / 8 : ℝ) * T ^ (5 / 6 : ℝ) +
        C * K * sourceFiniteEnergy N c * ((N : ℝ) + 1) ^ (9 / 8 : ℝ) * T ^ (5 / 6 : ℝ) :=
      add_le_add hbe hee
    _ = _ := by ring

/-- The same source constant controls moving lengths; the exponent is sublinear for `θ < 4/27`. -/
theorem exists_re_sourceFiniteGaussianSum_growing_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (θ : ℝ) (N : ℕ) (c : ℕ → ℝ) (T : ℝ), 1 ≤ T →
      (N : ℝ) + 1 ≤ T ^ θ →
      (sourceFiniteGaussianSum lam N c T).re ≤
        D * sourceFiniteEnergy N c * T ^ (5 / 6 + 9 * θ / 8 : ℝ) := by
  obtain ⟨D, hD0, hD⟩ := exists_re_sourceFiniteGaussianSum_energy_le hW
  refine ⟨D, hD0, fun θ N c T hT hN => ?_⟩
  have hT0 : 0 < T := by linarith
  have hE : 0 ≤ sourceFiniteEnergy N c := Finset.sum_nonneg fun m _ => by positivity
  calc
    _ ≤ D * sourceFiniteEnergy N c * ((N : ℝ) + 1) ^ (9 / 8 : ℝ) * T ^ (5 / 6 : ℝ) :=
      hD N c T hT
    _ ≤ D * sourceFiniteEnergy N c * (T ^ θ) ^ (9 / 8 : ℝ) * T ^ (5 / 6 : ℝ) := by
      gcongr
    _ = D * sourceFiniteEnergy N c * ((T ^ θ) ^ (9 / 8 : ℝ) * T ^ (5 / 6 : ℝ)) := by ring
    _ = _ := by
      rw [← Real.rpow_mul hT0.le, ← Real.rpow_add hT0]
      congr 1
      congr 1
      ring

end RHTower.WeilSingularArithmetic
