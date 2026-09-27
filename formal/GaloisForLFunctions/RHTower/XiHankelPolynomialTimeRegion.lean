import GaloisForLFunctions.RHTower.XiGaussianPolynomialTimeControl
import GaloisForLFunctions.RHTower.XiGaussianHankelSlopeControl

/-!
# A common polynomial time region for the full Xi Hankel family

One cutoff now controls all finite orders and all coefficient directions after
an explicit polynomial time normalization. Every cross term remains inside the
complete Gaussian polynomial norm and the literal actual Hankel form.
-/

open scoped Real SchwartzMap NNReal
open MeasureTheory Filter Topology GaloisForLFunctions
noncomputable section

namespace RHTower

/-- The normalized spatial scale gives an exact fifth-power heat-time relation. -/
theorem xiGaussianDegreeScale_heat_identity (d : ℕ) (τ : ℝ) :
    (2 * π * (xiGaussianDegreeScale d τ : ℝ) ^ 2) * ((d : ℝ) + 3) ^ 5 =
      2 * π * (Real.exp τ) ^ 2 := by
  have hw : gaussianDegreeWeight d ^ 2 = ((d : ℝ) + 3) ^ 5 := by
    rw [gaussianDegreeWeight, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  change (2 * π * (Real.exp τ / gaussianDegreeWeight d) ^ 2) * ((d : ℝ) + 3) ^ 5 = _
  rw [div_pow, ← hw]
  field_simp [(gaussianDegreeWeight_pos d).ne']

/-- One cutoff gives a full Gaussian-norm margin simultaneously for every Hankel order. -/
theorem exists_eventually_forall_xiHeatHankel_degreeScale_coercive :
    ∃ h : ℝ, 0 < h ∧ ∀ᶠ τ : ℝ in atBot, ∀ (N : ℕ) (a : ℕ → ℝ),
      (1 / 8 : ℝ) *
        ‖(polyGaussSchwartz (evenSquarePolynomial
          (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j))).toLp 2
            (volume : Measure ℝ)‖ ^ 2 ≤
      ((xiGaussianDegreeScale (2 * N) τ : ℝ) * h) *
        xiHeatHankelForm N (fun j => a j * (xiGaussianDegreeScale (2 * N) τ : ℝ) ^ (2 * j))
          (2 * π * (xiGaussianDegreeScale (2 * N) τ : ℝ) ^ 2) := by
  classical
  obtain ⟨h, hh, C, hC, hfloor⟩ := exists_xiGaussian_trace_slope_lower_bound
  refine ⟨h, hh, ?_⟩
  filter_upwards [eventually_forall_xiGaussianTraceLoss_degreeScale_lt
    (⟨C, hC.le⟩ : ℝ≥0) (⟨h, hh.le⟩ : ℝ≥0)] with τ hτ N a
  let P : Polynomial ℝ := ∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j
  let r := xiGaussianDegreeScale (2 * N) τ
  have hd : P.natDegree ≤ N := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact (Polynomial.natDegree_C_mul_X_pow_le (a j) j).trans (Finset.mem_range.mp hj).le
  have hmono := xiGaussianTraceLoss_mono (⟨C, hC.le⟩ : ℝ≥0) (⟨h, hh.le⟩ : ℝ≥0)
    (⟨(r : ℝ), r.property.le⟩ : ℝ≥0) (Nat.mul_le_mul_left 2 hd)
  have hsmall : xiGaussianTraceLoss C h (2 * P.natDegree) r < 1 / 8 :=
    hmono.trans_lt (hτ (2 * N))
  have hm := mul_le_mul_of_nonneg_right
    (show (1 / 8 : ℝ) ≤ 1 / 4 - xiGaussianTraceLoss C h (2 * P.natDegree) r by
      linarith only [hsmall])
    (sq_nonneg ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖)
  have hall := hm.trans (hfloor P r)
  dsimp only [P] at hall
  rw [xiGaussian_rangePolynomial_comp_scale,
    xiPolynomialGaussianHeatTraceReal_rangeSum
      (mul_pos (mul_pos (by positivity) Real.pi_pos) (pow_pos r.property 2))] at hall
  exact hall

/-- The literal full Hankel family obeys the common polynomial time region in every direction. -/
theorem exists_eventually_forall_xiHeatHankel_degreeScale_weighted_coercive :
    ∃ h : ℝ, 0 < h ∧ ∀ᶠ τ : ℝ in atBot, ∀ (N : ℕ) (a : ℕ → ℝ),
      (1 / 8 : ℝ) *
        ‖(polyGaussSchwartz (evenSquarePolynomial
          (∑ j ∈ Finset.range N,
            Polynomial.C (a j / (xiGaussianDegreeScale (2 * N) τ : ℝ) ^ (2 * j)) *
              Polynomial.X ^ j))).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
      ((xiGaussianDegreeScale (2 * N) τ : ℝ) * h) *
        xiHeatHankelForm N a (2 * π * (xiGaussianDegreeScale (2 * N) τ : ℝ) ^ 2) := by
  obtain ⟨h, hh, hall⟩ := exists_eventually_forall_xiHeatHankel_degreeScale_coercive
  refine ⟨h, hh, ?_⟩
  filter_upwards [hall] with τ hτ N a
  have hc (j : ℕ) : a j / (xiGaussianDegreeScale (2 * N) τ : ℝ) ^ (2 * j) *
      (xiGaussianDegreeScale (2 * N) τ : ℝ) ^ (2 * j) = a j :=
    div_mul_cancel₀ _ (pow_ne_zero _ (xiGaussianDegreeScale (2 * N) τ).property.ne')
  simpa only [hc] using hτ N
    (fun j => a j / (xiGaussianDegreeScale (2 * N) τ : ℝ) ^ (2 * j))

end RHTower
