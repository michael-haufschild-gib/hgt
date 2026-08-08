import GaloisForLFunctions.RHTower.Sieve.GeneralAffineMeanSquare
import GaloisForLFunctions.RHTower.Sieve.GhsStepFour
import GaloisForLFunctions.RHTower.Sieve.MoebiusSmoothCancellation
import GaloisForLFunctions.RHTower.Sieve.PerronNearDiagonal
import GaloisForLFunctions.RHTower.Sieve.GhsPerronSum
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# The first moment from the affine mean square

Cauchy–Schwarz against the constant `1` converts the affine mean square into a first-moment bound:

`∫_{|y| ≤ T} ‖L(a,σ+iy)‖ dy ≤ √(2T·(Q_1 + Q_0·T))`,

with `Q_1 = 5πe∑_n n‖a_n n^{-σ}‖²` the `n`-weighted mass and `Q_0 = (5π/2)∑_n ‖a_n n^{-σ}‖²` the plain
mass.  For coefficients bounded by `1` supported below `N` and `σ = 1 + 1/log N` the two masses are
`Q_1 ≍ log N` and `Q_0 ≍ 1`, so the bound is `≍ √(T(T + log N))`, against a trivial bound `≍ T log N`:
the saving is a whole square root of the mass, and it needs no distance, no sieve level and no
exceptional frequency.

Compared with the window route, which balances the damped size against the width of the exceptional
window and reaches `(T log N)^{4/5}`, the square root of the mean square is the stronger estimate for
the first moment.  The window law remains the only one of the two that locates the exceptional
frequency; the mean square is blind to it.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **The first moment of a finitely supported Dirichlet series.**  Cauchy–Schwarz against `1` on the
range, then the affine mean square. -/
theorem integral_Icc_norm_LSeries_le_sqrt_general_affine {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (σ : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ y in Set.Icc (-T) T, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖)
      ≤ Real.sqrt (2 * T
          * (generalMeanSquareConst a s σ + generalMeanSquareRate a s σ * T)) := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set g : ℝ → ℝ := fun y => ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ with hg
  have hcont : Continuous g := (continuous_LSeries_line_of_support hs0 hsupp σ).norm
  have hμuniv : (volume.restrict (Set.Icc (-T) T)) Set.univ = ENNReal.ofReal (2 * T) := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    congr 1
    ring
  have hfinite : IsFiniteMeasure (volume.restrict (Set.Icc (-T) T)) := by
    refine ⟨?_⟩
    rw [hμuniv]
    exact ENNReal.ofReal_lt_top
  have hg2 : Integrable (fun y => g y ^ 2) (volume.restrict (Set.Icc (-T) T)) :=
    (hcont.pow 2).integrableOn_Icc
  have hone : Integrable (fun _ : ℝ => (1 : ℝ) ^ 2) (volume.restrict (Set.Icc (-T) T)) := by
    simp only [one_pow]
    exact integrable_const 1
  have hCS := GaloisForLFunctions.HTGeometry.sq_integral_mul_le
    (μ := volume.restrict (Set.Icc (-T) T)) (f := fun _ : ℝ => (1 : ℝ)) (g := g)
    aestronglyMeasurable_const hcont.aestronglyMeasurable hone hg2
  simp only [one_mul, one_pow] at hCS
  have hmass : (∫ _y : ℝ, (1 : ℝ) ∂(volume.restrict (Set.Icc (-T) T))) = 2 * T := by
    rw [integral_const, measureReal_def, hμuniv, ENNReal.toReal_ofReal (by linarith), smul_eq_mul,
      mul_one]
  rw [hmass] at hCS
  have hms := integral_Icc_normSq_LSeries_le_general_affine hs0 hsupp σ hT
  have hmsg : (∫ y in Set.Icc (-T) T, g y ^ 2)
      ≤ generalMeanSquareConst a s σ + generalMeanSquareRate a s σ * T := hms
  have hint0 : (0 : ℝ) ≤ ∫ y in Set.Icc (-T) T, g y :=
    setIntegral_nonneg measurableSet_Icc fun y _ => norm_nonneg _
  have hbound : (∫ y in Set.Icc (-T) T, g y) ^ 2
      ≤ 2 * T * (generalMeanSquareConst a s σ + generalMeanSquareRate a s σ * T) := by
    refine le_trans hCS ?_
    exact mul_le_mul_of_nonneg_left hmsg (by linarith)
  have hnn : (0 : ℝ)
      ≤ 2 * T * (generalMeanSquareConst a s σ + generalMeanSquareRate a s σ * T) :=
    le_trans (sq_nonneg _) hbound
  exact (Real.le_sqrt hint0 hnn).mpr hbound

/-- The summand mass of a bounded sequence truncated at `N` is at most `1/n²`. -/
theorem norm_truncSeq_mul_rpow_sq_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) {σ : ℝ}
    (hσ : 1 ≤ σ) {n : ℕ} (hn : 1 ≤ n) :
    ‖truncSeq f N n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 ≤ 1 / (n : ℝ) ^ 2 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hrpow : (n : ℝ) ^ (-σ) ≤ 1 / (n : ℝ) := by
    have hstep : (n : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
    have hval : (n : ℝ) ^ (-1 : ℝ) = 1 / (n : ℝ) := by
      rw [Real.rpow_neg hn0.le, Real.rpow_one, one_div]
    rwa [hval] at hstep
  have hrpow0 : (0 : ℝ) < (n : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hn0 _
  have hnorm : ‖truncSeq f N n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ≤ 1 / (n : ℝ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpow0]
    calc ‖truncSeq f N n‖ * (n : ℝ) ^ (-σ) ≤ 1 * (n : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right (norm_truncSeq_le hf N n) hrpow0.le
      _ = (n : ℝ) ^ (-σ) := one_mul _
      _ ≤ 1 / (n : ℝ) := hrpow
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc ‖truncSeq f N n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 ≤ (1 / (n : ℝ)) ^ 2 := hsq
    _ = 1 / (n : ℝ) ^ 2 := by rw [div_pow, one_pow]

/-- **The plain mass of a bounded truncated sequence.** -/
theorem generalMeanSquareRate_truncSeq_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) {σ : ℝ}
    (hσ : 1 ≤ σ) :
    generalMeanSquareRate (truncSeq f N) (Finset.Icc 1 N) σ ≤ 5 * Real.pi := by
  have hpos : ∀ n ∈ Finset.Icc 1 N, 0 < n := fun n hn => (Finset.mem_Icc.1 hn).1
  have hstep : ∑ n ∈ Finset.Icc 1 N, ‖truncSeq f N n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ) ^ 2 :=
    Finset.sum_le_sum fun n hn => norm_truncSeq_mul_rpow_sq_le hf N hσ (Finset.mem_Icc.1 hn).1
  have htwo := sum_inv_sq_le_two_of_pos hpos
  rw [generalMeanSquareRate]
  have hπ : (0 : ℝ) ≤ 5 * Real.pi / 2 := by positivity
  have hfin : ∑ n ∈ Finset.Icc 1 N, ‖truncSeq f N n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 ≤ 2 :=
    le_trans hstep htwo
  calc (5 * Real.pi / 2) * ∑ n ∈ Finset.Icc 1 N,
        ‖truncSeq f N n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
      ≤ (5 * Real.pi / 2) * 2 := mul_le_mul_of_nonneg_left hfin hπ
    _ = 5 * Real.pi := by ring

/-- **The `n`-weighted mass of a bounded truncated sequence.**  One logarithm. -/
theorem generalMeanSquareConst_truncSeq_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) {σ : ℝ}
    (hσ : 1 ≤ σ) :
    generalMeanSquareConst (truncSeq f N) (Finset.Icc 1 N) σ
      ≤ 5 * Real.pi * Real.exp 1 * (1 + Real.log N) := by
  have hstep : ∑ n ∈ Finset.Icc 1 N,
        (n : ℝ) * ‖truncSeq f N n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ) := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hb := norm_truncSeq_mul_rpow_sq_le hf N hσ hn1
    calc (n : ℝ) * ‖truncSeq f N n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
        ≤ (n : ℝ) * (1 / (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hb (by linarith)
      _ = 1 / (n : ℝ) := by
          field_simp
  have hlog : ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ) ≤ 1 + Real.log N :=
    sum_inv_comp_le_one_add_log (φ := id) (fun _ _ _ _ h => h) (fun a ha => ha)
  rw [generalMeanSquareConst]
  have hc : (0 : ℝ) ≤ 5 * Real.pi * Real.exp 1 := by positivity
  exact mul_le_mul_of_nonneg_left (le_trans hstep hlog) hc

/-- **The first moment of a bounded truncated Dirichlet series.**  Explicit and unconditional: no
distance, no sieve level, no exceptional frequency. -/
theorem integral_Icc_norm_LSeries_truncSeq_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) {σ : ℝ}
    (hσ : 1 ≤ σ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ y in Set.Icc (-T) T, ‖LSeries (truncSeq f N) ((σ : ℂ) + (y : ℝ) * I)‖)
      ≤ Real.sqrt (2 * T
          * (5 * Real.pi * Real.exp 1 * (1 + Real.log N) + 5 * Real.pi * T)) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 N := by simp
  have hsupp : ∀ n : ℕ, truncSeq f N n ≠ 0 → n ∈ Finset.Icc 1 N := fun _ h => truncSeq_support h
  have hmain := integral_Icc_norm_LSeries_le_sqrt_general_affine hs0 hsupp σ hT
  refine le_trans hmain (Real.sqrt_le_sqrt ?_)
  have hC := generalMeanSquareConst_truncSeq_le hf N hσ
  have hR := generalMeanSquareRate_truncSeq_le hf N hσ
  have hRT : generalMeanSquareRate (truncSeq f N) (Finset.Icc 1 N) σ * T ≤ 5 * Real.pi * T :=
    mul_le_mul_of_nonneg_right hR hT0.le
  have h2T : (0 : ℝ) ≤ 2 * T := by linarith
  exact mul_le_mul_of_nonneg_left (by linarith) h2T

end RHTower.Sieve
end
