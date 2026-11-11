import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheCoupledEulerCorrectionPreservesThePolynomialLimit
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheCorrectionCoefficientJetsHaveASummableMajorant
import GaloisForLFunctions.MultiscaleMollifiedZetaField.ThePrincipalRowDerivativesShiftTheProfiles

/-!
# Differentiating corrected rows

A directional derivative either differentiates the correction coefficient,
inserts one harmonic logarithm, or multiplies one profile by `1−x`.
Every term with a positive-order correction jet vanishes in the coupled
limit, by the common pair majorant and the uniform principal-row bound.
-/

open Filter Set Topology
open RHTower.Sieve

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- Corrected harmonic row with specified logarithmic weight and correction-jet order. -/
def correctedProfileJetSum (P Q : ℝ → ℝ) (N : ℕ) (c v : ℝ) (k j : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
    realNormalizedCorrectionCoeffJet N a b j c * shiftedProfileHarmonicRow P Q N a b c v k

/-- Zero correction-jet order gives the coupled corrected profile sum. -/
theorem correctedProfileJetSum_zero_coupled (P Q : ℝ → ℝ) (N : ℕ) (v : ℝ) (k : ℕ) :
    correctedProfileJetSum P Q N (-2 * v) v k 0 = correctedCoupledProfileSum P Q N v k := by
  simp only [correctedProfileJetSum, correctedCoupledProfileSum, realNormalizedCorrectionCoeffJet_zero]

/-- The four derivative terms remain in the same corrected-row family. -/
theorem hasDerivAt_correctedProfileJetSum_direction
    (P Q : ℝ → ℝ) (N k j : ℕ) (c v κ ν z : ℝ) :
    HasDerivAt (fun y => correctedProfileJetSum P Q N (c + κ * y) (v + ν * y) k j)
      (κ * correctedProfileJetSum P Q N (c + κ * z) (v + ν * z) k (j + 1) +
        κ * correctedProfileJetSum P Q N (c + κ * z) (v + ν * z) (k + 1) j +
        ν * correctedProfileJetSum (logComplementProfile P) Q N (c + κ * z) (v + ν * z) k j +
        ν * correctedProfileJetSum P (logComplementProfile Q) N (c + κ * z) (v + ν * z) k j) z := by
  have hterm (a b : ℕ) : HasDerivAt (fun y : ℝ =>
      realNormalizedCorrectionCoeffJet N a b j (c + κ * y) *
        shiftedProfileHarmonicRow P Q N a b (c + κ * y) (v + ν * y) k)
      (κ * (realNormalizedCorrectionCoeffJet N a b (j + 1) (c + κ * z) *
        shiftedProfileHarmonicRow P Q N a b (c + κ * z) (v + ν * z) k) +
      κ * (realNormalizedCorrectionCoeffJet N a b j (c + κ * z) *
        shiftedProfileHarmonicRow P Q N a b (c + κ * z) (v + ν * z) (k + 1)) +
      ν * (realNormalizedCorrectionCoeffJet N a b j (c + κ * z) *
        shiftedProfileHarmonicRow (logComplementProfile P) Q N a b (c + κ * z) (v + ν * z) k) +
      ν * (realNormalizedCorrectionCoeffJet N a b j (c + κ * z) *
        shiftedProfileHarmonicRow P (logComplementProfile Q) N a b (c + κ * z) (v + ν * z) k)) z := by
    have hc : HasDerivAt (fun y : ℝ => realNormalizedCorrectionCoeffJet N a b j (c + κ * y))
        (realNormalizedCorrectionCoeffJet N a b (j + 1) (c + κ * z) * κ) z := by
      simpa only [id_eq, mul_one, Function.comp_def] using
        (hasDerivAt_realNormalizedCorrectionCoeffJet N a b j (c + κ * z)).comp z
          (((hasDerivAt_id z).const_mul κ).const_add c)
    apply (hc.mul (hasDerivAt_shiftedProfileHarmonicRow_direction P Q N a b k c v κ ν z)).congr_deriv
    ring
  have hh := HasDerivAt.fun_sum (u := Finset.Icc 1 N) (fun a _ =>
    HasDerivAt.fun_sum (u := Finset.Icc 1 N) (fun b _ => hterm a b))
  apply hh.congr_deriv
  simp only [correctedProfileJetSum, Finset.sum_add_distrib, ← Finset.mul_sum]

private def correctionJetRowPair (P Q : ℝ → ℝ) (N : ℕ) (v : ℝ) (k j : ℕ) (x : ℕ × ℕ) : ℝ :=
  if x.1 ∈ Finset.Icc 1 N ∧ x.2 ∈ Finset.Icc 1 N then
    realNormalizedCorrectionCoeffJet N x.1 x.2 j (-2 * v) *
      shiftedProfileHarmonicRow P Q N x.1 x.2 (-2 * v) v k else 0

private theorem tsum_correctionJetRowPair (P Q : ℝ → ℝ) (N : ℕ) (v : ℝ) (k j : ℕ) :
    (∑' x : ℕ × ℕ, correctionJetRowPair P Q N v k j x) = correctedProfileJetSum P Q N (-2 * v) v k j := by
  classical
  rw [tsum_eq_sum (s := (Finset.Icc 1 N).product (Finset.Icc 1 N))]
  · rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    simp only [correctionJetRowPair, if_pos ⟨ha, hb⟩, correctedProfileJetSum]
  · intro x hx
    exact if_neg (by simpa only [Finset.mem_product] using hx)

/-- Every positive correction-jet term vanishes after summing all retained polynomial rows. -/
theorem tendsto_correctedProfileJetSum_succ_coupled (P Q : ℝ[X])
    (hP0 : P.eval 0 = 0) (hQ0 : Q.eval 0 = 0)
    {v : ℕ → ℝ} {v₀ : ℝ} (hv : Tendsto v atTop (𝓝 v₀)) (k j : ℕ) :
    Tendsto (fun N : ℕ => correctedProfileJetSum P.eval Q.eval N (-2 * v N) (v N) k (j + 1))
      atTop (𝓝 0) := by
  obtain ⟨B, hB, hrows⟩ := exists_eventually_coupledPolynomialRow_bound P Q hP0 hQ0 hv
  let V : ℝ := |v₀| + 1
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hcentres : ∀ᶠ N : ℕ in atTop, |-2 * v N| ≤ 2 * V := by
    have hh := hv.eventually (Metric.ball_mem_nhds v₀ zero_lt_one)
    filter_upwards [hh] with N hN
    rw [Real.dist_eq] at hN
    have hnv : |v N| ≤ V := by
      have he : v N = (v N - v₀) + v₀ := by ring
      calc
        _ = |(v N - v₀) + v₀| := by rw [he]
        _ ≤ |v N - v₀| + |v₀| := abs_add_le _ _
        _ ≤ V := by dsimp only [V]; linarith only [hN]
    rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
    exact mul_le_mul_of_nonneg_left hnv (by norm_num)
  let K : ℝ := ((j + 1).factorial : ℝ) * Real.exp (4 * (2 * V + 1)) * B
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hs : Summable (fun x : ℕ × ℕ => K * absoluteSelbergCorrectionCoeff x.1 x.2) :=
    summable_absoluteSelbergCorrectionCoeff.mul_left K
  have hpoint (x : ℕ × ℕ) :
      Tendsto (fun N : ℕ => correctionJetRowPair P.eval Q.eval N (v N) k (j + 1) x) atTop (𝓝 0) := by
    have hc := tendsto_realNormalizedCorrectionCoeffJet_succ hcentres x.1 x.2 j
    have hh : Tendsto (fun N : ℕ => B * |realNormalizedCorrectionCoeffJet N x.1 x.2 (j + 1) (-2 * v N)|)
        atTop (𝓝 0) := by simpa only [abs_zero, mul_zero] using hc.abs.const_mul B
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [hrows, hh.eventually_lt_const hε] with N hrow hsmall
    rw [Real.dist_eq, sub_zero]
    refine lt_of_le_of_lt ?_ hsmall
    by_cases hx : x.1 ∈ Finset.Icc 1 N ∧ x.2 ∈ Finset.Icc 1 N
    · have hx1 := Finset.mem_Icc.mp hx.1
      have hx2 := Finset.mem_Icc.mp hx.2
      rw [correctionJetRowPair, if_pos hx, abs_mul]
      have hb := mul_le_mul_of_nonneg_left (hrow _ _ k hx1.1 hx2.1 hx1.2 hx2.2)
        (abs_nonneg (realNormalizedCorrectionCoeffJet N x.1 x.2 (j + 1) (-2 * v N)))
      simpa only [mul_comm] using hb
    · rw [correctionJetRowPair, if_neg hx, abs_zero]
      exact mul_nonneg hB (abs_nonneg _)
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ x : ℕ × ℕ,
      ‖correctionJetRowPair P.eval Q.eval N (v N) k (j + 1) x‖ ≤
        K * absoluteSelbergCorrectionCoeff x.1 x.2 := by
    filter_upwards [eventually_ge_atTop 2, hrows, hcentres] with N hN hrow hcentre
    intro x
    by_cases hx : x.1 ∈ Finset.Icc 1 N ∧ x.2 ∈ Finset.Icc 1 N
    · have hx1 := Finset.mem_Icc.mp hx.1
      have hx2 := Finset.mem_Icc.mp hx.2
      have hc := abs_realNormalizedCorrectionCoeffJet_le (by omega : 1 < N) (-2 * v N) (j + 1) hx1.2 hx2.2
      have hc' : |realNormalizedCorrectionCoeffJet N x.1 x.2 (j + 1) (-2 * v N)| ≤
          ((j + 1).factorial : ℝ) * Real.exp (4 * (2 * V + 1)) * absoluteSelbergCorrectionCoeff x.1 x.2 := by
        refine hc.trans (mul_le_mul_of_nonneg_right ?_ (absoluteSelbergCorrectionCoeff_nonneg _ _))
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Real.exp_le_exp.mpr
        linarith only [hcentre]
      rw [correctionJetRowPair, if_pos hx, Real.norm_eq_abs, abs_mul]
      have hh := mul_le_mul hc' (hrow _ _ k hx1.1 hx2.1 hx1.2 hx2.2) (abs_nonneg _) (by positivity)
      exact hh.trans_eq (by dsimp only [K]; ring)
    · rw [correctionJetRowPair, if_neg hx, norm_zero]
      exact mul_nonneg hK (absoluteSelbergCorrectionCoeff_nonneg _ _)
  have hh := tendsto_tsum_of_dominated_convergence hs hpoint hbound
  simpa only [tsum_correctionJetRowPair, tsum_zero] using hh

end GaloisForLFunctions.MultiscaleMollifiedZetaField
