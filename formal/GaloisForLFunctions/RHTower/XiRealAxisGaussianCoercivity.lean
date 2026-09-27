import GaloisForLFunctions.RHTower.XiRealAxisGaussianSampling
import GaloisForLFunctions.RHTower.EvenGaussianHalfLineEnergy

/-!
# Uniform Gaussian energy floor on actual Xi ordinates

The lower zero-window density, Gaussian quadrature, and the low-height mass
bound give a relative floor with error proportional to scale times square root
of degree. After degree normalization one cutoff controls every even polynomial.
This is real-ordinate reference energy, before variable complex-shift transfer.
-/

open scoped Real SchwartzMap NNReal
open MeasureTheory Filter Topology
open GaloisForLFunctions
noncomputable section

namespace RHTower

/-- The actual real-ordinate reference has a coefficient-uniform relative lower bound. -/
theorem exists_xiRealAxisGaussian_relative_floor :
    ∃ h : ℝ, 0 < h ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (P : Polynomial ℝ) (r : {r : ℝ // 0 < r}),
        (1 / 2 - C * (r : ℝ) * Real.sqrt (((2 * P.natDegree : ℕ) : ℝ) + 1)) *
            ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
          ((r : ℝ) * h) * xiRealAxisSchwartzEnergy (polyGaussSchwartz (evenSquarePolynomial P)) r := by
  obtain ⟨a, ha, h, hh, hsample⟩ := exists_xiRealAxisGaussian_halfLine_sampling_bound
  refine ⟨h, hh, 9 * a + 2 * h * Real.sqrt (4 * Real.pi), by positivity, ?_⟩
  intro P r
  have hlow := evenPolynomialGaussian_tail_energy_lower P
    (⟨(r : ℝ) * a, (mul_pos r.property ha).le⟩ : ℝ≥0)
  have hupp := hsample (evenSquarePolynomial P) r
  rw [natDegree_evenSquarePolynomial,
    Real.sqrt_mul (by positivity : 0 ≤ 4 * Real.pi)] at hupp
  change (1 / 2 - 9 * ((r : ℝ) * a) * Real.sqrt (((2 * P.natDegree : ℕ) : ℝ) + 1)) *
      ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
    ∫ x : ℝ in Set.Ioi ((r : ℝ) * a), ‖polyGaussSchwartz (evenSquarePolynomial P) x‖ ^ 2 at hlow
  nlinarith only [hlow, hupp]

/-- A positive spatial scale normalized by the full even-polynomial degree. -/
def xiGaussianParabolicScale (P : Polynomial ℝ) (τ : ℝ) : {r : ℝ // 0 < r} :=
  ⟨Real.exp τ / Real.sqrt (((2 * P.natDegree : ℕ) : ℝ) + 1),
    div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr (by positivity))⟩

/-- One rescaled cutoff gives a quarter-energy floor for all coefficients and all degrees. -/
theorem exists_eventually_forall_xiRealAxisGaussian_parabolic_floor :
    ∃ h : ℝ, 0 < h ∧ ∀ᶠ τ : ℝ in atBot, ∀ P : Polynomial ℝ,
      (1 / 4 : ℝ) *
          ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
        ((xiGaussianParabolicScale P τ : ℝ) * h) *
          xiRealAxisSchwartzEnergy (polyGaussSchwartz (evenSquarePolynomial P))
            (xiGaussianParabolicScale P τ) := by
  obtain ⟨h, hh, C, hC, hfloor⟩ := exists_xiRealAxisGaussian_relative_floor
  refine ⟨h, hh, ?_⟩
  have he : ∀ᶠ τ : ℝ in atBot, Real.exp τ < 1 / (4 * C) :=
    Real.tendsto_exp_atBot.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / (4 * C)))
  filter_upwards [he] with τ hτ P
  have h := hfloor P (xiGaussianParabolicScale P τ)
  have hs : 0 < Real.sqrt (((2 * P.natDegree : ℕ) : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hscale : C * (xiGaussianParabolicScale P τ : ℝ) *
      Real.sqrt (((2 * P.natDegree : ℕ) : ℝ) + 1) = C * Real.exp τ := by
    change C * (Real.exp τ / Real.sqrt (((2 * P.natDegree : ℕ) : ℝ) + 1)) * _ = _
    rw [mul_assoc, div_mul_cancel₀ _ hs.ne']
  rw [hscale] at h
  have hc := mul_le_mul_of_nonneg_left hτ.le hC.le
  have hcancel : C * (1 / (4 * C)) = (1 / 4 : ℝ) := by field_simp
  rw [hcancel] at hc
  have hm := mul_le_mul_of_nonneg_right hc
    (sq_nonneg ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖)
  linarith only [h, hm]

end RHTower
