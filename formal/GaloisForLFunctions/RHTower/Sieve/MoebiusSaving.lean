import GaloisForLFunctions.RHTower.Sieve.MoebiusContourBound

/-!
# The saving made explicit

The left-edge term of the contour bound is `(N+H)^{c(K)}` with `c(K) = 1 - c₀/(16 log⁹K)`.  Written
as a saving,

    (N+H)^{c(K)} = (N+H) · exp( -c₀·log(N+H) / (16 log⁹K) ),

so the term is the trivial size `N+H` multiplied by a genuine decay whenever `log(N+H)/log⁹K` tends
to infinity.  That is the whole mechanism of the argument, and putting the bound in this form is
what turns the choice of `K` into an elementary optimisation.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

/-- The left-edge power, written as the trivial size times an explicit saving. -/
theorem rpow_leftAbscissa {K : ℕ} {x : ℝ} (hx : 0 < x) :
    x ^ leftAbscissa K
      = x * Real.exp (-(zeroFreeConst / (16 * (Real.log K) ^ 9)) * Real.log x) := by
  rw [leftAbscissa, Real.rpow_def_of_pos hx,
    show Real.log x * (1 - zeroFreeConst / (16 * (Real.log K) ^ 9))
      = Real.log x + (-(zeroFreeConst / (16 * (Real.log K) ^ 9)) * Real.log x) by ring,
    Real.exp_add, Real.exp_log hx]

/-- **The contour bound with the saving exposed.**  The left-edge term is the trivial size `N+H`
times `exp(-c₀ log(N+H)/(16 log⁹K))`. -/
theorem exists_norm_tsum_moebius_smoothWeight_le_saving {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    (j : ℕ) :
    ∃ (C M₀ : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ M₀ ∧ ∀ K : ℕ, K₀ ≤ K →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          (ArithmeticFunction.moebius n : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * (invZetaRightBound K * C) / truncHeight K
            + invZetaEdgeBound K * C / (truncHeight K) ^ (j + 1)
                * (rightAbscissa K - leftAbscissa K)
            + invZetaEdgeBound K * C / (truncHeight K) ^ (j + 1)
                * (rightAbscissa K - leftAbscissa K)
            + max M₀ (invZetaEdgeBound K)
                * (4 * ((N + H) * Real.exp (-(zeroFreeConst / (16 * (Real.log K) ^ 9))
                      * Real.log (N + H))) + 2 * C) := by
  obtain ⟨C, M₀, K₁, hC, hM₀, hmain⟩ :=
    exists_norm_tsum_moebius_smoothWeight_le_concrete hN hH j
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.1 (hlog.eventually_ge_atTop 3)
  refine ⟨C, M₀, max K₁ K₂, hC, hM₀, fun K hKle => ?_⟩
  have hbase := hmain K (le_trans (le_max_left _ _) hKle)
  have hlogK : (3 : ℝ) ≤ Real.log K := hK₂ K (le_trans (le_max_right _ _) hKle)
  have hNH : (0 : ℝ) < N + H := by linarith
  have hA0 := zeroFreeConst_pos
  have hA1 := zeroFreeConst_le_one
  have hL0 : (0 : ℝ) < Real.log K := by linarith
  have hL9 : (27 : ℝ) ≤ (Real.log K) ^ 9 := by
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
      _ ≤ (Real.log K) ^ 3 := by gcongr
      _ ≤ (Real.log K) ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h16small : zeroFreeConst / (16 * (Real.log K) ^ 9) ≤ 1 / 54 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hL9, hA1, hA0]
  have hcge : (1 : ℝ) / 2 ≤ leftAbscissa K := by rw [leftAbscissa]; linarith
  have hcpos : (0 : ℝ) < leftAbscissa K := by linarith
  set X : ℝ := (N + H) * Real.exp (-(zeroFreeConst / (16 * (Real.log K) ^ 9))
    * Real.log (N + H)) with hXdef
  have hX0 : (0 : ℝ) ≤ X := by rw [hXdef]; positivity
  have hstep : 2 * ((N + H) ^ leftAbscissa K / leftAbscissa K) ≤ 4 * X := by
    rw [rpow_leftAbscissa hNH, ← hXdef]
    have hdiv : X / leftAbscissa K ≤ X * 2 := by
      rw [div_le_iff₀ hcpos]
      nlinarith [hX0, hcge]
    linarith
  have hlast : max M₀ (invZetaEdgeBound K)
      * (2 * ((N + H) ^ leftAbscissa K / leftAbscissa K) + 2 * C)
      ≤ max M₀ (invZetaEdgeBound K) * (4 * X + 2 * C) :=
    mul_le_mul_of_nonneg_left (by linarith) (le_trans hM₀ (le_max_left _ _))
  rw [hXdef] at hlast
  linarith

end RHTower.Sieve
