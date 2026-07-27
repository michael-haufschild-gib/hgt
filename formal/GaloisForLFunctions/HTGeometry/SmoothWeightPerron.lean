import GaloisForLFunctions.HTGeometry.SmoothWeightInversion
import Mathlib.Analysis.PSeries

/-!
# The smoothed Perron formula

For unit-bounded coefficients and `σ > 1`,

`2π ∑ₙ aₙ w(n) = ∫ (∑ₙ aₙ n^{-(σ+iy)}) W(σ+iy) dy`.

Both sides converge absolutely: the Dirichlet series because `σ > 1`, the vertical integral because
`W` decays quadratically.  The proof inserts the Mellin inversion formula for `w(n)` into each term
and interchanges the sum with the integral, the interchange being justified by
`∑ₙ ∫ ‖aₙ n^{-(σ+iy)} W(σ+iy)‖ dy ≤ (∑ₙ n^{-σ}) ∫ ‖W(σ+iy)‖ dy < ∞`.
-/

open MeasureTheory Complex Set Filter

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- The modulus of `n^{-(σ+iy)}` is `n^{-σ}`, independently of `y`. -/
theorem norm_natCast_cpow_neg_line {n : ℕ} (hn : 0 < n) (σ y : ℝ) :
    ‖(n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * I))‖ = (n : ℝ) ^ (-σ) := by
  rw [Complex.norm_natCast_cpow_of_pos hn]
  congr 1
  simp

/-- Each term of the Perron integrand is integrable along the line. -/
theorem integrable_perron_term (ha : ∀ n, ‖a n‖ ≤ 1) (ha0 : a 0 = 0) {N H : ℝ} (hN : 0 < N)
    (hH : 0 < H) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    Integrable (fun y : ℝ => a n * ((n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * I)) *
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ha0]
  obtain ⟨C, hC, hbd⟩ := exists_bound_mellin_smoothWeight_line hN hH hσ
  have hcont : Continuous (fun y : ℝ => a n * ((n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * I)) *
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I))) := by
    refine continuous_const.mul (Continuous.mul ?_ (continuous_mellin_smoothWeight_line hH hσ))
    exact Continuous.const_cpow (by fun_prop) (Or.inl (Nat.cast_ne_zero.mpr hn.ne'))
  have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul ((n : ℝ) ^ (-σ) * C))
    hcont.aestronglyMeasurable ?_
  filter_upwards with y
  rw [norm_mul, norm_mul, norm_natCast_cpow_neg_line hn]
  calc ‖a n‖ * ((n : ℝ) ^ (-σ) *
        ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I)‖)
      ≤ 1 * ((n : ℝ) ^ (-σ) * (C * (1 + y ^ 2)⁻¹)) := by
        refine mul_le_mul (ha n) (mul_le_mul_of_nonneg_left (hbd y) hnn) ?_ zero_le_one
        positivity
    _ = (n : ℝ) ^ (-σ) * C * (1 + y ^ 2)⁻¹ := by ring

/-- Each term integrates to `2π` times the corresponding term of the smoothed sum: this is Mellin
inversion for the cutoff, evaluated at `x = n`. -/
theorem integral_perron_term {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {σ : ℝ} (hσ : 0 < σ) {n : ℕ}
    (hn : 0 < n) :
    (∫ y : ℝ, a n * ((n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * I)) *
        mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I)))
      = a n * ((2 * Real.pi : ℝ) • ((smoothWeight N H (n : ℝ) : ℝ) : ℂ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hinv := mellinInv_mellin_smoothWeight hN hH hσ (x := (n : ℝ)) hn0
  rw [mellinInv] at hinv
  have hcast : ∀ y : ℝ, (((n : ℝ) : ℂ)) ^ (-((σ : ℂ) + (y : ℝ) * I))
      = (n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * I)) := by
    intro y
    norm_cast
  have hJ : (∫ y : ℝ, (n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * I)) *
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I))
      = (2 * Real.pi : ℝ) • ((smoothWeight N H (n : ℝ) : ℝ) : ℂ) := by
    rw [← hinv, smul_smul]
    have hpi : (2 * Real.pi : ℝ) * (1 / (2 * Real.pi)) = 1 := by
      field_simp
    rw [hpi, one_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul, hcast y]
  rw [integral_const_mul, hJ]

/-- **The smoothed Perron formula.**  For unit-bounded coefficients and `σ > 1`, the smoothed sum
equals `1/2π` times the vertical integral of the Dirichlet series against the Mellin transform of
the cutoff. -/
theorem tsum_mul_smoothWeight_eq_integral (ha : ∀ n, ‖a n‖ ≤ 1) (ha0 : a 0 = 0) {N H : ℝ}
    (hN : 0 < N) (hH : 0 < H) {σ : ℝ} (hσ : 1 < σ) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ, a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      = ∫ y : ℝ, (∑' n : ℕ, a n * (n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * I))) *
          mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I) := by
  classical
  have hσ0 : (0 : ℝ) < σ := by linarith
  set W : ℝ → ℂ := fun y =>
    mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I) with hWdef
  set F : ℕ → ℝ → ℂ := fun n y => a n * ((n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * I)) * W y) with hF
  have hWint : Integrable W := verticalIntegrable_mellin_smoothWeight hN hH hσ0
  have hint : ∀ n, Integrable (F n) := fun n => integrable_perron_term ha ha0 hN hH hσ0 n
  -- the sum of the `L¹` norms converges
  set V : ℝ := ∫ y : ℝ, ‖W y‖ with hV
  have hV0 : 0 ≤ V := integral_nonneg fun y => norm_nonneg _
  have hrpow : Summable fun n : ℕ => (n : ℝ) ^ (-σ) := by
    refine (Real.summable_nat_rpow_inv.mpr hσ).congr fun n => ?_
    rw [← Real.rpow_neg (Nat.cast_nonneg n)]
  have hnormle : ∀ n : ℕ, (∫ y : ℝ, ‖F n y‖) ≤ (n : ℝ) ^ (-σ) * V := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF, ha0, Real.zero_rpow (by linarith : -σ ≠ 0)]
    have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have heq : ∀ y : ℝ, ‖F n y‖ = ‖a n‖ * (n : ℝ) ^ (-σ) * ‖W y‖ := by
      intro y
      rw [hF]
      simp only
      rw [norm_mul, norm_mul, norm_natCast_cpow_neg_line hn]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall heq),
      integral_const_mul]
    have := hWint.norm
    calc ‖a n‖ * (n : ℝ) ^ (-σ) * V ≤ 1 * (n : ℝ) ^ (-σ) * V := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (ha n) hnn) hV0
      _ = (n : ℝ) ^ (-σ) * V := by ring
  have hsum : Summable fun n : ℕ => ∫ y : ℝ, ‖F n y‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _) hnormle ?_
    exact hrpow.mul_right V
  have hHS := hasSum_integral_of_summable_integral_norm hint hsum
  -- identify the integral of the sum
  have hpoint : ∀ y : ℝ, (∑' n : ℕ, F n y)
      = (∑' n : ℕ, a n * (n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * I))) * W y := by
    intro y
    rw [← tsum_mul_right]
    refine tsum_congr fun n => ?_
    rw [hF]
    ring
  -- identify each term's integral
  have hterm : ∀ n : ℕ, (∫ y : ℝ, F n y)
      = (2 * Real.pi : ℝ) • (a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF, ha0]
    rw [hF]
    simp only
    rw [integral_perron_term hN hH hσ0 hn]
    exact mul_smul_comm _ _ _
  -- the smoothed sum is a finite sum, hence summable
  have hfin : Summable fun n : ℕ => a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ) := by
    refine summable_of_ne_finset_zero (s := Finset.range (⌈N + H⌉₊ + 1)) fun n hn => ?_
    rw [Finset.mem_range] at hn
    have hge : N + H ≤ (n : ℝ) := by
      have h1 : (N + H : ℝ) ≤ (⌈N + H⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈N + H⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.le_of_not_lt hn
      push_cast at h2
      linarith
    rw [smoothWeight_eq_zero hH hge]
    simp
  have hHS2 : HasSum (fun n : ℕ => (2 * Real.pi : ℝ) •
      (a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ)))
      ((2 * Real.pi : ℝ) • ∑' n : ℕ, a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ)) :=
    hfin.hasSum.const_smul _
  have hHS3 : HasSum (fun n : ℕ => ∫ y : ℝ, F n y)
      ((2 * Real.pi : ℝ) • ∑' n : ℕ, a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ)) := by
    have hfun : (fun n : ℕ => ∫ y : ℝ, F n y)
        = fun n : ℕ => (2 * Real.pi : ℝ) • (a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ)) :=
      funext hterm
    rw [hfun]
    exact hHS2
  rw [hHS3.unique hHS]
  exact integral_congr_ae (Filter.Eventually.of_forall hpoint)

end GaloisForLFunctions.HTGeometry
