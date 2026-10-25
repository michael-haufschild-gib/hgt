import GaloisForLFunctions.BezoutValuationIncidence.TheHalfDampingVaughanGramLimitsFormARankThreeRay
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
At the cutoff-product horizon, logarithmic Möbius cancellation removes the
endpoint harmonic mass uniformly over factorizations. When both cutoffs grow,
the centered Gram therefore tends to its actual finite rank-two limit.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

private def halfLogHarmonicWeight (N : ℕ) : ℝ :=
  deningerHarmonicPartial N ^ 2 * (1 + Real.log (N : ℝ))

private theorem halfLogHarmonicWeight_nonneg (N : ℕ) : 0 ≤ halfLogHarmonicWeight N := by
  have hlog : 0 ≤ Real.log (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [Nat.cast_zero, Real.log_zero, le_refl]
    · exact Real.log_nonneg (by exact_mod_cast hN)
  exact mul_nonneg (sq_nonneg _) (by linarith only [hlog])

private theorem tendsto_halfLogHarmonicWeight :
    Tendsto halfLogHarmonicWeight atTop (𝓝 0) := by
  have h0 : Tendsto deningerHarmonicPartial atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul] using Sieve.tendsto_log_pow_mul_deningerHarmonicPartial_zero 0
  have h1 : Tendsto (fun N : ℕ => Real.log (N : ℝ) * deningerHarmonicPartial N) atTop (𝓝 0) := by
    simpa only [pow_one] using Sieve.tendsto_log_pow_mul_deningerHarmonicPartial_zero 1
  have h := (h0.mul h0).add (h1.mul h0)
  simp only [zero_mul, zero_add] at h
  convert h using 1
  funext N
  dsimp only [halfLogHarmonicWeight]
  ring

private theorem exists_halfLogHarmonicWeight_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N, |halfLogHarmonicWeight N| ≤ B := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp tendsto_halfLogHarmonicWeight 1 zero_lt_one
  let B : ℝ := 1 + ∑ n ∈ range N, |halfLogHarmonicWeight n|
  have hB1 : 1 ≤ B := le_add_of_nonneg_right (sum_nonneg fun _ _ => abs_nonneg _)
  refine ⟨B, zero_le_one.trans hB1, fun n => ?_⟩
  by_cases hn : n < N
  · have h : |halfLogHarmonicWeight n| ≤ ∑ m ∈ range N, |halfLogHarmonicWeight m| :=
      single_le_sum (fun _ _ => abs_nonneg _) (mem_range.mpr hn)
    exact h.trans (le_add_of_nonneg_left zero_le_one)
  · have h := hN n (not_lt.mp hn)
    exact (by simpa only [Real.dist_eq, sub_zero] using h : |halfLogHarmonicWeight n| < 1).le.trans hB1

/-- Positive cutoff factors separate the logarithmic cost of the product horizon. -/
theorem sum_Icc_reciprocal_succ_product_le {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) :
    (∑ n ∈ Icc 1 (U * V), 1 / ((n : ℝ) + 1)) ≤
      (1 + Real.log (U : ℝ)) * (1 + Real.log (V : ℝ)) := by
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hV0 : (0 : ℝ) < V := by exact_mod_cast hV
  have hlogU : 0 ≤ Real.log (U : ℝ) := Real.log_nonneg (by exact_mod_cast hU)
  have hlogV : 0 ≤ Real.log (V : ℝ) := Real.log_nonneg (by exact_mod_cast hV)
  calc
    _ ≤ ∑ n ∈ Icc 1 (U * V), 1 / (n : ℝ) := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      exact one_div_le_one_div_of_le hn0 (by linarith)
    _ ≤ 1 + Real.log ((U * V : ℕ) : ℝ) := Sieve.sum_Icc_one_div_le_one_add_log _
    _ = 1 + Real.log (U : ℝ) + Real.log (V : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul hU0.ne' hV0.ne']
      ring
    _ ≤ _ := by nlinarith only [mul_nonneg hlogU hlogV]

private theorem halfHarmonicMass_product_le (U V : ℕ) :
    pmPronicVaughanHalfHarmonicMass U V (U * V) ≤
      subHalfZetaCoeff (1 / 2) ^ 2 * halfLogHarmonicWeight U * halfLogHarmonicWeight V := by
  rcases Nat.eq_zero_or_pos (U * V) with hz | hUV
  · simp only [pmPronicVaughanHalfHarmonicMass, hz, Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1),
      sum_empty, mul_zero]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (halfLogHarmonicWeight_nonneg U))
      (halfLogHarmonicWeight_nonneg V)
  · have hU : 1 ≤ U := Nat.pos_of_mul_pos_right hUV
    have hV : 1 ≤ V := Nat.pos_of_mul_pos_left hUV
    calc
      _ ≤ (subHalfZetaCoeff (1 / 2) * deningerHarmonicPartial U * deningerHarmonicPartial V) ^ 2 *
          ((1 + Real.log (U : ℝ)) * (1 + Real.log (V : ℝ))) :=
        mul_le_mul_of_nonneg_left (sum_Icc_reciprocal_succ_product_le hU hV) (sq_nonneg _)
      _ = _ := by dsimp only [halfLogHarmonicWeight]; ring

/-- Endpoint harmonic mass vanishes along every divergent cutoff product, uniformly in its factorization. -/
theorem tendsto_pmPronicVaughanHalfHarmonicMass_product
    (U V : ℕ → ℕ) (hUV : Tendsto (fun t => U t * V t) atTop atTop) :
    Tendsto (fun t => pmPronicVaughanHalfHarmonicMass (U t) (V t) (U t * V t))
      atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := exists_halfLogHarmonicWeight_bound
  have h := (tendsto_mul_of_product_indices_atTop hB hbound
    tendsto_halfLogHarmonicWeight U V hUV).const_mul (subHalfZetaCoeff (1 / 2) ^ 2)
  simp only [mul_zero] at h
  apply squeeze_zero' (Eventually.of_forall fun t => pmPronicVaughanHalfHarmonicMass_nonneg _ _ _)
    (Eventually.of_forall fun t => ?_) h
  simpa only [mul_assoc] using halfHarmonicMass_product_le (U t) (V t)

/-- One finite bound controls the endpoint harmonic mass at every product horizon. -/
theorem exists_uniform_pmPronicVaughanHalfHarmonicMass_product_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ U V : ℕ, pmPronicVaughanHalfHarmonicMass U V (U * V) ≤ K := by
  obtain ⟨B, hB, hbound⟩ := exists_halfLogHarmonicWeight_bound
  refine ⟨subHalfZetaCoeff (1 / 2) ^ 2 * B ^ 2, by positivity, fun U V => ?_⟩
  have hg (N : ℕ) : halfLogHarmonicWeight N ≤ B := (le_abs_self _).trans (hbound N)
  calc
    _ ≤ subHalfZetaCoeff (1 / 2) ^ 2 * halfLogHarmonicWeight U * halfLogHarmonicWeight V :=
      halfHarmonicMass_product_le U V
    _ ≤ _ := by
      rw [mul_assoc, pow_two B]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (hg U) (hg V) (halfLogHarmonicWeight_nonneg V) hB) (sq_nonneg _)

/-- Every centered endpoint Gram entry is uniformly bounded at all product horizons. -/
theorem exists_uniform_pmPronicVaughanCentredGram_half_product_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ U V : ℕ, ∀ i j : Fin 5,
      |pmPronicVaughanCentredGram (1 / 2) U V (U * V) i j| ≤ B := by
  obtain ⟨K, hK, hmass⟩ := exists_uniform_pmPronicVaughanHalfHarmonicMass_product_bound
  obtain ⟨C, hC, herror⟩ := exists_uniform_pmPronicVaughanCentredGram_half_harmonic_error_bound
  refine ⟨C + K, add_nonneg hC hK, fun U V i j => ?_⟩
  let m := pmPronicVaughanHalfHarmonicMass U V (U * V) *
    pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j
  have hs (k : Fin 5) : |pmPronicVaughanSmoothSigns k| ≤ 1 := by
    fin_cases k <;> norm_num [pmPronicVaughanSmoothSigns]
  have hm : |m| ≤ K := by
    dsimp only [m]
    rw [abs_mul, abs_mul, abs_of_nonneg (pmPronicVaughanHalfHarmonicMass_nonneg _ _ _)]
    calc
      _ ≤ pmPronicVaughanHalfHarmonicMass U V (U * V) :=
        (mul_le_of_le_one_right
          (mul_nonneg (pmPronicVaughanHalfHarmonicMass_nonneg _ _ _) (abs_nonneg _)) (hs j)).trans
          (mul_le_of_le_one_right (pmPronicVaughanHalfHarmonicMass_nonneg _ _ _) (hs i))
      _ ≤ K := hmass U V
  have he : |pmPronicVaughanCentredGram (1 / 2) U V (U * V) i j - m| ≤ C := by
    convert herror U V (U * V) i j using 1
    congr 1
    dsimp only [m, pmPronicVaughanHalfHarmonicMass]
    ring
  calc
    _ = |(pmPronicVaughanCentredGram (1 / 2) U V (U * V) i j - m) + m| := by rw [sub_add_cancel]
    _ ≤ |pmPronicVaughanCentredGram (1 / 2) U V (U * V) i j - m| + |m| := abs_add_le _ _
    _ ≤ C + K := add_le_add he hm

/-- The complete centered endpoint trace has one finite bound over every cutoff pair. -/
theorem exists_uniform_pmPronicVaughanCentredGram_half_product_trace_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ U V : ℕ,
      (∑ i : Fin 5, pmPronicVaughanCentredGram (1 / 2) U V (U * V) i i) ≤ B := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_pmPronicVaughanCentredGram_half_product_bound
  refine ⟨5 * C, by positivity, fun U V => ?_⟩
  calc
    _ ≤ ∑ _i : Fin 5, C := sum_le_sum fun i _ => (le_abs_self _).trans (hbound U V i i)
    _ = _ := by simp

/-- When both cutoffs diverge, their product-horizon endpoint Gram converges to the nonzero rank-two limit. -/
theorem tendsto_pmPronicVaughanCentredGram_half_product
    {U V : ℕ → ℕ} (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop) (i j : Fin 5) :
    Tendsto (fun t => pmPronicVaughanCentredGram (1 / 2) (U t) (V t) (U t * V t) i j)
      atTop (𝓝 (pmPronicVaughanHalfLimitGram i j)) := by
  have hUV : Tendsto (fun t => U t * V t) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [hU.eventually_ge_atTop N, hV.eventually_ge_atTop 1] with t hUt hVt
    simpa only [mul_one] using Nat.mul_le_mul hUt hVt
  simpa only [pmPronicVaughanHalfLimitRay_zero] using
    tendsto_pmPronicVaughanCentredGram_half_of_harmonic_mass hUV hU hV
      (tendsto_pmPronicVaughanHalfHarmonicMass_product U V hUV) i j

#print axioms sum_Icc_reciprocal_succ_product_le
#print axioms tendsto_pmPronicVaughanHalfHarmonicMass_product
#print axioms exists_uniform_pmPronicVaughanHalfHarmonicMass_product_bound
#print axioms exists_uniform_pmPronicVaughanCentredGram_half_product_bound
#print axioms exists_uniform_pmPronicVaughanCentredGram_half_product_trace_bound
#print axioms tendsto_pmPronicVaughanCentredGram_half_product
end GaloisForLFunctions.BezoutValuationIncidence
