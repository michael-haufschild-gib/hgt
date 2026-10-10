import GaloisForLFunctions.RHTower.WeilLogShiftSingletonGramCost
import GaloisForLFunctions.RHTower.WeilLogShiftGramAmplitudeCost
import GaloisForLFunctions.RHTower.WeilLogShiftSuperpolynomialGramCost

/-! A prescribed coordinate has an exact unit response at quadratic cost when
the other coefficients are unrestricted. -/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable section
namespace RHTower

theorem finiteWeilGramTailCost_scaleTest (B : ℝ) (t : NNReal) (w : FiniteWeilGramTest) :
    finiteWeilGramTailCost B (finiteWeilGramScale t w) =
      (t : ℝ) * finiteWeilGramTailCost B w := by
  rcases w with ⟨N, x, u, a⟩
  dsimp only [finiteWeilGramScale, finiteWeilGramTailCost]
  simp only [NNReal.coe_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The cost constant is uniform over every support and every chosen coordinate. -/
theorem exists_finiteWeilGram_quadratic_unit_response :
    ∃ A : ℝ, 0 < A ∧ ∀ (s : Finset ℕ) (i : s), ∃ w : FiniteWeilGramTest,
      finiteWeilGramCoefficientVector s w i = 1 ∧
        finiteWeilGramTailCost 1 w ≤ A * (((i : ℕ) + 2 : ℕ) : ℝ) ^ 2 := by
  obtain ⟨B, C, hB, hC, _, hcert⟩ := exists_singletonWeil_quadratic_cost_certificate
  have hscaleB (w : FiniteWeilGramTest) :
      finiteWeilGramTailCost B w = B * finiteWeilGramTailCost 1 w := by
    simpa only [mul_one] using finiteWeilGramTailCost_scale B 1 w
  refine ⟨C / B, div_pos hC hB, ?_⟩
  intro s i
  let k : ℕ := i
  let j : ({k} : Finset ℕ) := ⟨k, Finset.mem_singleton_self k⟩
  let p : ({k} : Finset ℕ) → ℝ := Pi.single j 1
  have hpnorm : ‖p‖ = 1 := by simp only [p, Pi.norm_single, norm_one]
  have hpne : -p ≠ 0 := by
    intro he
    have h := congrArg norm he
    simp only [norm_neg, hpnorm, norm_zero] at h
    norm_num at h
  obtain ⟨tests, _, htests, htotal⟩ := hcert k
  obtain ⟨w, hwmem, hresponse⟩ := htests (-p) hpne
  rw [map_neg, norm_neg, hpnorm] at hresponse
  change -finiteWeilGramCoefficientVector {k} w j < -1 at hresponse
  have hcoord : finiteWeilGramCoefficientVector s w i =
      finiteWeilGramCoefficientVector {k} w j := by
    rcases w with ⟨N, x, u, a⟩
    rw [finiteWeilGramCoefficientVector_apply, finiteWeilGramCoefficientVector_apply]
  rw [← hcoord] at hresponse
  have hv : 1 < finiteWeilGramCoefficientVector s w i := by linarith only [hresponse]
  have hvpos : 0 < finiteWeilGramCoefficientVector s w i := by linarith only [hv]
  have hwcost : finiteWeilGramTailCost B w ≤ C * ((k + 2 : ℕ) : ℝ) ^ 2 := by
    apply (Finset.single_le_sum (fun z (_ : z ∈ tests) => ?_) hwmem).trans htotal
    rw [hscaleB]
    exact mul_nonneg hB.le (finiteWeilGramTailCost_one_nonneg z)
  rw [hscaleB] at hwcost
  have hunit : finiteWeilGramTailCost 1 w ≤ (C / B) * ((k + 2 : ℕ) : ℝ) ^ 2 := by
    have hd : finiteWeilGramTailCost 1 w ≤ (C * ((k + 2 : ℕ) : ℝ) ^ 2) / B :=
      (le_div_iff₀ hB).mpr (by nlinarith only [hwcost])
    convert hd using 1
    ring
  let t : NNReal := NNReal.mk (finiteWeilGramCoefficientVector s w i)⁻¹ (inv_pos.mpr hvpos).le
  refine ⟨finiteWeilGramScale t w, ?_, ?_⟩
  · rw [finiteWeilGramCoefficientVector_scale]
    change (finiteWeilGramCoefficientVector s w i)⁻¹ * finiteWeilGramCoefficientVector s w i = 1
    exact inv_mul_cancel₀ hvpos.ne'
  · rw [finiteWeilGramTailCost_scaleTest]
    change (finiteWeilGramCoefficientVector s w i)⁻¹ * finiteWeilGramTailCost 1 w ≤ _
    calc
      _ ≤ 1 * finiteWeilGramTailCost 1 w := mul_le_mul_of_nonneg_right
        ((inv_le_one₀ hvpos).mpr hv.le) (finiteWeilGramTailCost_one_nonneg w)
      _ ≤ (C / B) * ((k + 2 : ℕ) : ℝ) ^ 2 := by simpa only [one_mul] using hunit

end RHTower
