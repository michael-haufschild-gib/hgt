import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfSourceMass
import GaloisForLFunctions.HTGeometry.BoundedCoefficientLaplaceMellin

/-!
# A positive reserve in the actual signed heat source

At `s = 2/3`, the complete square-supported correction has absolute tail mass below one.
An absolutely convergent multiplicative-fiber rearrangement therefore places the signed heat
sum within that fraction of the positive zeta-half heat mass. The latter diverges by its prime
coefficients, so the signed source's real part tends to positive infinity as heat time tends to zero.

No time-mesh condition, Tauberian asymptotic, or zero-location hypothesis is used. This result
concerns the literal heat source; a normalized root-approximation claim must also audit its factors.
-/

open ArithmeticFunction Complex Filter Topology Set
open scoped BigOperators ComplexOrder
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- Positive heat mass of the actual zeta-half coefficients at the test point. -/
def zetaHalfTwoThirdsHeatMass (t : ℝ) : ℝ :=
  ∑' n, ‖LSeries.term zetaBinomialHalf (2 / 3 : ℂ) n‖ * Real.exp (-(n : ℝ) * t)

private theorem norm_zetaHalf_twoThirds_term_le_one (n : ℕ) :
    ‖LSeries.term zetaBinomialHalf (2 / 3 : ℂ) n‖ ≤ 1 := by
  have h := LSeries.norm_term_le_of_re_le_re zetaBinomialHalf
    (s := 0) (s' := 2 / 3) (by norm_num) n
  refine h.trans ?_
  rw [LSeries.norm_term_eq]
  split
  · exact zero_le_one
  · simpa using norm_zetaBinomialHalf_le_one n

private theorem summable_zetaHalf_twoThirds_heat {t : ℝ} (ht : 0 < t) :
    Summable (fun n => ‖LSeries.term zetaBinomialHalf (2 / 3 : ℂ) n‖ *
      Real.exp (-(n : ℝ) * t)) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => ?_) (summable_exp_neg_nat_mul ht)
  simpa only [one_mul, neg_mul] using
    mul_le_mul_of_nonneg_right (norm_zetaHalf_twoThirds_term_le_one n)
      (Real.exp_pos (-(n : ℝ) * t)).le

/-- Complete signed-source comparison, with the entire correction tail retained. -/
theorem squarefreeHalf_heat_twoThirds_source_mass_bound {t : ℝ} (ht : 0 < t) :
    ‖coeffLaplaceProfile (LSeries.term squarefreeConvolutionHalf (2 / 3 : ℂ)) t -
      (zetaHalfTwoThirdsHeatMass t : ℂ)‖ ≤
      (∑' n : ℕ, if n = 1 then 0 else
        ‖LSeries.term squareDilatedMoebiusBinomialHalf (2 / 3 : ℂ) n‖) *
          zetaHalfTwoThirdsHeatMass t := by
  let q := LSeries.term squareDilatedMoebiusBinomialHalf (2 / 3 : ℂ)
  let b := LSeries.term zetaBinomialHalf (2 / 3 : ℂ)
  let y : ℕ → ℝ := fun n => ‖b n‖ * Real.exp (-(n : ℝ) * t)
  let G : ℕ × ℕ → ℂ := fun p =>
    q p.1 * b p.2 * Complex.exp (-(((p.1 * p.2 : ℕ) : ℝ) * t))
  have hq : Summable q :=
    LSeriesSummable_squareDilatedMoebiusBinomialHalf (by norm_num)
  have hy : Summable y := summable_zetaHalf_twoThirds_heat ht
  have hy0 : ∀ n, 0 ≤ y n := fun n => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hmaj := hq.norm.mul_of_nonneg hy (fun n => norm_nonneg _) hy0
  have hbound (p : ℕ × ℕ) : ‖G p‖ ≤ ‖q p.1‖ * y p.2 := by
    by_cases hi : p.1 = 0
    · simp [G, q, hi]
    have hi1 : (1 : ℝ) ≤ p.1 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
    have hj0 : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg p.2
    have hexp : Real.exp (-(((p.1 * p.2 : ℕ) : ℝ) * t)) ≤
        Real.exp (-(p.2 : ℝ) * t) := by
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hi1 hj0]
    dsimp [G, y]
    rw [norm_mul, norm_mul, Complex.norm_exp]
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    simpa using hexp
  have hG : Summable G := Summable.of_norm_bounded hmaj hbound
  have hsource : coeffLaplaceProfile
      (LSeries.term squarefreeConvolutionHalf (2 / 3 : ℂ)) t = ∑' p, G p := by
    rw [← (hG.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)).tsum_eq]
    unfold coeffLaplaceProfile
    apply tsum_congr
    intro n
    rw [squarefreeConvolutionHalf_eq_zetaBinomialHalf_mul_squareCorrection,
      show zetaBinomialHalf * squareDilatedMoebiusBinomialHalf =
        squareDilatedMoebiusBinomialHalf * zetaBinomialHalf from mul_comm _ _,
      ← ArithmeticFunction.coe_mul, LSeries.term_convolution']
    rw [← tsum_mul_right]
    apply tsum_congr
    intro p
    have hp : p.val.1 * p.val.2 = n := p.property
    dsimp [G, q, b]
    rw [hp]
    push_cast
    ring
  have hrow (i : ℕ) : ‖∑' j, G (i, j)‖ ≤ ‖q i‖ * zetaHalfTwoThirdsHeatMass t := by
    refine (norm_tsum_le_tsum_norm (hG.prod_factor i).norm).trans ?_
    have h := ((hG.prod_factor i).norm).tsum_le_tsum (fun j => hbound (i,j))
      (hy.mul_left ‖q i‖)
    simpa only [tsum_mul_left, zetaHalfTwoThirdsHeatMass, y, b] using h
  have hb (n : ℕ) : b n = (‖b n‖ : ℂ) := by
    apply Complex.eq_coe_norm_of_nonneg
    dsimp [b]
    rw [show (2 / 3 : ℂ) = ((2 / 3 : ℝ) : ℂ) by push_cast; rfl]
    exact LSeries.term_nonneg (zetaBinomialHalf_apply_nonneg_complex n) (2 / 3 : ℝ)
  have hone : (∑' j, G (1,j)) = (zetaHalfTwoThirdsHeatMass t : ℂ) := by
    unfold zetaHalfTwoThirdsHeatMass
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    dsimp [G, q]
    rw [LSeries.term_of_ne_zero one_ne_zero, Nat.cast_one, Complex.one_cpow,
      div_one, squareDilatedMoebiusBinomialHalf_apply_one, one_mul, one_mul,
      hb n]
    push_cast
    congr 2
    ring
  have htail : Summable (fun i => if i = 1 then (0 : ℂ) else ∑' j, G (i,j)) := by
    apply Summable.of_norm_bounded hG.prod.norm
    intro i
    split_ifs <;> simp
  have hmTail : Summable (fun i => if i = 1 then 0 else ‖q i‖) := by
    apply Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hq.norm
    · split_ifs <;> positivity
    · split_ifs <;> simp
  have hsplit := hG.prod.tsum_eq_add_tsum_ite 1
  rw [hone] at hsplit
  rw [hsource, hG.tsum_prod, hsplit, add_sub_cancel_left]
  refine (norm_tsum_le_tsum_norm htail.norm).trans ?_
  have hpoint (i : ℕ) : ‖if i = 1 then (0 : ℂ) else ∑' j, G (i,j)‖ ≤
      (if i = 1 then 0 else ‖q i‖) * zetaHalfTwoThirdsHeatMass t := by
    split_ifs with hi
    · simp
    · exact hrow i
  have h := htail.norm.tsum_le_tsum hpoint (hmTail.mul_right _)
  simpa only [tsum_mul_right] using h

/-- Exact positive fraction that the correction tail cannot cancel. -/
def squarefreeHalfHeatReserve : ℝ := 1 -
  ∑' n : ℕ, if n = 1 then 0 else
    ‖LSeries.term squareDilatedMoebiusBinomialHalf (2 / 3 : ℂ) n‖

theorem squarefreeHalfHeatReserve_pos : 0 < squarefreeHalfHeatReserve :=
  sub_pos.mpr squareCorrection_two_thirds_tail_mass_lt_one

theorem squarefreeHalfHeatReserve_mul_mass_le_re {t : ℝ} (ht : 0 < t) :
    squarefreeHalfHeatReserve * zetaHalfTwoThirdsHeatMass t ≤
      (coeffLaplaceProfile (LSeries.term squarefreeConvolutionHalf (2 / 3 : ℂ)) t).re := by
  have h := squarefreeHalf_heat_twoThirds_source_mass_bound ht
  have hre := (abs_le.mp (Complex.abs_re_le_norm
    (coeffLaplaceProfile (LSeries.term squarefreeConvolutionHalf (2 / 3 : ℂ)) t -
      (zetaHalfTwoThirdsHeatMass t : ℂ)))).1
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  unfold squarefreeHalfHeatReserve
  nlinarith

theorem not_summable_zetaHalf_twoThirds_weights :
    ¬ Summable (fun n => ‖LSeries.term zetaBinomialHalf (2 / 3 : ℂ) n‖) := by
  intro hs
  have hprime : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-2 / 3 : ℝ)) := by
    have h := (hs.subtype Nat.Prime).mul_left (2 : ℝ)
    apply h.congr
    intro p
    have hp : zetaBinomialHalf (p : ℕ) = (1 / 2 : ℂ) := by
      have hp := zetaBinomialHalf_apply_prime_pow_eq_centralBinom (k := 1) p.property
      norm_num [Nat.centralBinom, Nat.choose] at hp
      exact hp
    change 2 * ‖LSeries.term zetaBinomialHalf (2 / 3 : ℂ) (p : ℕ)‖ =
      (p : ℝ) ^ (-2 / 3 : ℝ)
    rw [LSeries.norm_term_eq, if_neg p.property.ne_zero, hp]
    rw [show (2 / 3 : ℂ).re = (2 / 3 : ℝ) by norm_num]
    simp only [neg_div, Real.rpow_neg (show 0 ≤ (p : ℝ) by positivity)]
    norm_num [div_eq_mul_inv, mul_assoc]
    ring
  have h := Nat.Primes.summable_rpow.mp hprime
  norm_num at h

theorem tendsto_zetaHalfTwoThirdsHeatMass_atTop :
    Tendsto zetaHalfTwoThirdsHeatMass (𝓝[>] 0) atTop := by
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => norm_nonneg (LSeries.term zetaBinomialHalf (2 / 3 : ℂ) n))).mp
      not_summable_zetaHalf_twoThirds_weights
  apply tendsto_atTop.2
  intro M
  obtain ⟨N, hN⟩ := (hdiv.eventually (eventually_gt_atTop M)).exists
  have hc : ContinuousAt (fun t : ℝ => ∑ n ∈ Finset.range N,
      ‖LSeries.term zetaBinomialHalf (2 / 3 : ℂ) n‖ * Real.exp (-(n : ℝ) * t)) 0 := by
    fun_prop
  have hlim : Tendsto (fun t : ℝ => ∑ n ∈ Finset.range N,
      ‖LSeries.term zetaBinomialHalf (2 / 3 : ℂ) n‖ * Real.exp (-(n : ℝ) * t))
      (𝓝[>] 0) (𝓝 (∑ n ∈ Finset.range N,
        ‖LSeries.term zetaBinomialHalf (2 / 3 : ℂ) n‖)) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [hlim.eventually (Ioi_mem_nhds hN), self_mem_nhdsWithin] with t hMt ht
  exact hMt.le.trans ((summable_zetaHalf_twoThirds_heat ht).sum_le_tsum _
    (fun _ _ => by positivity))

/-- The actual signed source diverges along every approach through positive heat times. -/
theorem tendsto_re_squarefreeHalf_twoThirds_heat_atTop :
    Tendsto (fun t =>
      (coeffLaplaceProfile (LSeries.term squarefreeConvolutionHalf (2 / 3 : ℂ)) t).re)
      (𝓝[>] 0) atTop := by
  have h := Filter.Tendsto.const_mul_atTop' squarefreeHalfHeatReserve_pos
    tendsto_zetaHalfTwoThirdsHeatMass_atTop
  apply tendsto_atTop_mono' (𝓝[>] (0 : ℝ)) ?_ h
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact squarefreeHalfHeatReserve_mul_mass_le_re ht

end RHTower

