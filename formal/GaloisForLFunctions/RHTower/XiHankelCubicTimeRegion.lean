import GaloisForLFunctions.RHTower.XiGaussianCubicTimeControl
import GaloisForLFunctions.RHTower.XiGaussianHankelSlopeControl
import GaloisForLFunctions.RHTower.XiHeatThirdChannelDecomposition

/-!
# A common cubic time region for the full Xi Hankel family

One cutoff now controls all finite orders and all coefficient directions after
an explicit polynomial time normalization. Every cross term remains inside the
complete Gaussian polynomial norm and the literal actual Hankel form.
-/

open scoped Real SchwartzMap NNReal
open MeasureTheory Filter Topology GaloisForLFunctions
noncomputable section

namespace RHTower

/-- The normalized spatial scale gives an exact cubic heat-time relation. -/
theorem xiGaussianCubicScale_heat_identity (d : ℕ) (τ : ℝ) :
    (2 * π * (xiGaussianCubicScale d τ : ℝ) ^ 2) * ((d : ℝ) + 3) ^ 3 =
      2 * π * (Real.exp τ) ^ 2 := by
  have hv : 0 < Real.sqrt ((d : ℝ) + 3) := Real.sqrt_pos.mpr (by positivity)
  have hD : 0 < (d : ℝ) + 3 := by positivity
  have hv2 := Real.sq_sqrt hD.le
  change (2 * π * (Real.exp τ / (((d : ℝ) + 3) * Real.sqrt ((d : ℝ) + 3))) ^ 2) *
    ((d : ℝ) + 3) ^ 3 = _
  field_simp
  nlinarith only [hv2]

/-- One cutoff gives a full Gaussian-norm margin simultaneously for every Hankel order. -/
theorem exists_eventually_forall_xiHeatHankel_cubicScale_coercive :
    ∃ h : ℝ, 0 < h ∧ ∀ᶠ τ : ℝ in atBot, ∀ (N : ℕ) (a : ℕ → ℝ),
      (1 / 8 : ℝ) *
        ‖(polyGaussSchwartz (evenSquarePolynomial
          (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j))).toLp 2
            (volume : Measure ℝ)‖ ^ 2 ≤
      ((xiGaussianCubicScale (2 * N) τ : ℝ) * h) *
        xiHeatHankelForm N (fun j => a j * (xiGaussianCubicScale (2 * N) τ : ℝ) ^ (2 * j))
          (2 * π * (xiGaussianCubicScale (2 * N) τ : ℝ) ^ 2) := by
  classical
  obtain ⟨h, hh, C, hC, hfloor⟩ := exists_xiGaussian_trace_threeHalves_lower_bound
  refine ⟨h, hh, ?_⟩
  filter_upwards [eventually_forall_xiGaussianThreeHalvesTraceLoss_cubicScale_lt
    (⟨C, hC.le⟩ : ℝ≥0) (⟨h, hh.le⟩ : ℝ≥0)] with τ hτ N a
  let P : Polynomial ℝ := ∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j
  let r := xiGaussianCubicScale (2 * N) τ
  let L := xiGaussianCubicInterpolationScale (2 * N) τ
  have hd : P.natDegree ≤ N := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact (Polynomial.natDegree_C_mul_X_pow_le (a j) j).trans (Finset.mem_range.mp hj).le
  have hmono := xiGaussianThreeHalvesTraceLoss_mono (⟨C, hC.le⟩ : ℝ≥0) (⟨h, hh.le⟩ : ℝ≥0)
    (⟨(r : ℝ), r.property.le⟩ : ℝ≥0)
    (⟨(L : ℝ), L.property.le⟩ : ℝ≥0) (Nat.mul_le_mul_left 2 hd)
  have hsmall : xiGaussianThreeHalvesTraceLoss C h (2 * P.natDegree) r L < 1 / 8 :=
    hmono.trans_lt (hτ (2 * N))
  have hm := mul_le_mul_of_nonneg_right
    (show (1 / 8 : ℝ) ≤ 1 / 4 - xiGaussianThreeHalvesTraceLoss C h (2 * P.natDegree) r L by
      linarith only [hsmall])
    (sq_nonneg ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖)
  have hall := hm.trans (hfloor P r L)
  dsimp only [P] at hall
  rw [xiGaussian_rangePolynomial_comp_scale,
    xiPolynomialGaussianHeatTraceReal_rangeSum
      (mul_pos (mul_pos (by positivity) Real.pi_pos) (pow_pos r.property 2))] at hall
  exact hall

/-- The literal full Hankel family obeys the common cubic time region in every direction. -/
theorem exists_eventually_forall_xiHeatHankel_cubicScale_weighted_coercive :
    ∃ h : ℝ, 0 < h ∧ ∀ᶠ τ : ℝ in atBot, ∀ (N : ℕ) (a : ℕ → ℝ),
      (1 / 8 : ℝ) *
        ‖(polyGaussSchwartz (evenSquarePolynomial
          (∑ j ∈ Finset.range N,
            Polynomial.C (a j / (xiGaussianCubicScale (2 * N) τ : ℝ) ^ (2 * j)) *
              Polynomial.X ^ j))).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
      ((xiGaussianCubicScale (2 * N) τ : ℝ) * h) *
        xiHeatHankelForm N a (2 * π * (xiGaussianCubicScale (2 * N) τ : ℝ) ^ 2) := by
  obtain ⟨h, hh, hall⟩ := exists_eventually_forall_xiHeatHankel_cubicScale_coercive
  refine ⟨h, hh, ?_⟩
  filter_upwards [hall] with τ hτ N a
  have hc (j : ℕ) : a j / (xiGaussianCubicScale (2 * N) τ : ℝ) ^ (2 * j) *
      (xiGaussianCubicScale (2 * N) τ : ℝ) ^ (2 * j) = a j :=
    div_mul_cancel₀ _ (pow_ne_zero _ (xiGaussianCubicScale (2 * N) τ).property.ne')
  simpa only [hc] using hτ N
    (fun j => a j / (xiGaussianCubicScale (2 * N) τ : ℝ) ^ (2 * j))

/-- The complete actual 3×3 form inherits the cubic region with every cross term intact. -/
theorem exists_eventually_forall_xiHeatThird_cubicScale_coercive :
    ∃ h : ℝ, 0 < h ∧ ∀ᶠ τ : ℝ in atBot, ∀ a b c : ℝ,
      (1 / 8 : ℝ) *
        ‖(polyGaussSchwartz (evenSquarePolynomial
          (xiHeatThirdPolynomial a (b / (xiGaussianCubicScale 6 τ : ℝ) ^ 2)
            (c / (xiGaussianCubicScale 6 τ : ℝ) ^ 4)))).toLp 2
              (volume : Measure ℝ)‖ ^ 2 ≤
      ((xiGaussianCubicScale 6 τ : ℝ) * h) *
        xiHeatThirdQuadratic a b c (2 * π * (xiGaussianCubicScale 6 τ : ℝ) ^ 2) := by
  obtain ⟨h, hh, hall⟩ := exists_eventually_forall_xiHeatHankel_cubicScale_weighted_coercive
  refine ⟨h, hh, ?_⟩
  filter_upwards [hall] with τ hτ a b c
  have hs := hτ 3 (fun n => if n = 0 then a else if n = 1 then b else c)
  rw [← xiHeatThirdQuadratic_eq_hankel] at hs
  simpa [Finset.sum_range_succ, xiHeatThirdPolynomial] using hs

end RHTower
