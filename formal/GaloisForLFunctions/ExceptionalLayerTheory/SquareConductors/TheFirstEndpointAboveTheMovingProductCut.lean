import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheEndpointAtQuotientZero
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheQuotientCellsOfTheCappedSpline

/-!
# Ordinary-prime endpoints above a moving product cut

Keep the original upper horizon in both quotient sums. Their difference
recovers the complete prime contact once the product cut is below the
first spline knot. In particular every fixed subquadratic power cut
eventually gives precisely the same prime coefficient.
-/

noncomputable section
open Finset ArithmeticFunction Filter
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- First-cell difference with the far horizon clipped in both readings. -/
def clippedFirstEndpoint (n q : ℕ) : ℝ :=
  let D := lastProductHorizon n q
  let r (k : ℕ) := (sampledSpline n k-sampledSpline n (k+1))*centeredPrimeWeight 1 (k/q)
  (∑ k ∈ Ico q D, r k) - ∑ k ∈ range D, r k

/-- All products above two reach the first positive quotient cell before
their far cutoff, even when a later cell is clipped. -/
theorem clippedFirstEndpoint_eq {n q : ℕ} (hq : 2 < q) (hL : q ≤ splineHorizon n) :
    clippedFirstEndpoint n q = sampledSpline n q := by
  let t := (q+1)/2
  have ht : 2 ≤ t := by dsimp only [t]; omega
  have he : q ≤ unitProductHorizonEnd q := calc
    q ≤ 2*t := by dsimp only [t]; omega
    _ ≤ t*t := Nat.mul_le_mul_right t ht
    _ = _ := (sq t).symm
  have hqL := hL.trans (Nat.le_succ _)
  have hD : q ≤ lastProductHorizon n q := le_min hqL he
  let r (k : ℕ) := (sampledSpline n k-sampledSpline n (k+1))*centeredPrimeWeight 1 (k/q)
  have h := first_quotient_endpoint (n := n) hqL
  rw [sum_Ico_eq_sub _ hqL] at h
  change (∑ k ∈ range (splineHorizon n+1), r k) - (∑ k ∈ range q, r k) =
    (∑ k ∈ range (splineHorizon n+1), r k) + sampledSpline n q at h
  change (∑ k ∈ Ico q (lastProductHorizon n q), r k) -
    (∑ k ∈ range (lastProductHorizon n q), r k) = sampledSpline n q
  rw [sum_Ico_eq_sub r hD]
  linarith only [h]

/-- Returned ordinary-prime mass on the very products above the sharp cut. -/
def retainedPrimeEndpoint (U n : ℕ) : ℝ :=
  ∑ q ∈ (ordinaryPrimeLags (splineHorizon n)).filter (U < ·),
    vonMangoldt q * clippedFirstEndpoint n q

theorem retainedPrimeEndpoint_eq {n U : ℕ} (hn : 0 < n) (hU : 2 ≤ U)
    (hfirst : (U:ℝ) < Real.exp (-8)*(n:ℝ)^2) :
    retainedPrimeEndpoint U n = dyadicPrimeContact n := by
  let S := ordinaryPrimeLags (splineHorizon n)
  have he : retainedPrimeEndpoint U n =
      ∑ q ∈ S.filter (U < ·), vonMangoldt q * sampledSpline n q := by
    exact sum_congr rfl fun q hq => by
      obtain ⟨hS,hqU⟩ := mem_filter.mp hq
      rw [clippedFirstEndpoint_eq (hU.trans_lt hqU) (mem_Icc.mp (mem_filter.mp hS).1).2]
  rw [he, show (∑ q ∈ S.filter (U < ·), vonMangoldt q * sampledSpline n q) =
      ∑ q ∈ S, vonMangoldt q * sampledSpline n q by
    apply sum_subset (filter_subset _ _)
    intro q hq hnot
    have hle : q ≤ U := le_of_not_gt fun h => hnot (mem_filter.mpr ⟨hq,h⟩)
    rw [sampledSpline_eq_zero_before hn ((Nat.cast_le.mpr hle).trans_lt hfirst),mul_zero]]
  unfold dyadicPrimeContact
  exact sum_congr rfl fun q hq => by
    rw [sampledSpline_prime_contact hn (mem_filter.mp hq).2.pos,mul_comm]

/-- A fixed subquadratic product cutoff changes only finitely many of the
ordinary-prime endpoint coefficients. -/
theorem eventually_retainedPrimeEndpoint {α : ℝ} (hα : 0 < α) (h₂ : α < 2) :
    ∀ᶠ n : ℕ in atTop, retainedPrimeEndpoint ⌊(n:ℝ)^α⌋₊ n = dyadicPrimeContact n := by
  have ha := (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
  have hg := (tendsto_rpow_atTop (sub_pos.mpr h₂)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1:ℕ),ha.eventually_ge_atTop 2,
    hg.eventually_gt_atTop (Real.exp 8)] with n hn hl hu
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  apply retainedPrimeEndpoint_eq hn (Nat.le_floor (by exact_mod_cast hl))
  refine (Nat.floor_le (Real.rpow_nonneg hn'.le _)).trans_lt ?_
  change Real.exp 8 < (n:ℝ)^(2-α) at hu
  have hmul := mul_lt_mul_of_pos_left hu (Real.rpow_pos_of_pos hn' α)
  rw [←Real.rpow_add hn',show α+(2-α)=2 by ring,Real.rpow_two] at hmul
  rw [Real.exp_neg,inv_mul_eq_div,lt_div_iff₀ (Real.exp_pos 8)]
  exact hmul

/-- Beyond the quadratic exponent the whole finite product horizon is
eventually below the cut, so the retained endpoint is identically zero. -/
theorem eventually_retainedPrimeEndpoint_zero_of_two_lt {α : ℝ} (hα : 2 < α) :
    ∀ᶠ n : ℕ in atTop, retainedPrimeEndpoint ⌊(n:ℝ)^α⌋₊ n = 0 := by
  obtain ⟨A,_,hwin⟩ := successorSquare_window_bound
  have hg := (tendsto_rpow_atTop (sub_pos.mpr hα)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1:ℕ),hg.eventually_ge_atTop (A^2)] with n hn hgap
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hL : splineHorizon n ≤ ⌊(n:ℝ)^α⌋₊ := by
    apply Nat.le_floor
    calc (splineHorizon n:ℝ) ≤ (A*n)^2 := hwin hn
         _ ≤ (n:ℝ)^(α-2)*(n:ℝ)^2 := by rw [mul_pow]; exact mul_le_mul_of_nonneg_right hgap (sq_nonneg _)
         _ = _ := by rw [←Real.rpow_two,←Real.rpow_add hn',sub_add_cancel]
  unfold retainedPrimeEndpoint
  apply sum_eq_zero
  intro q hq
  obtain ⟨hp,hU⟩ := mem_filter.mp hq
  have hqL := (mem_Icc.mp (mem_filter.mp hp).1).2
  exact ((hqL.trans hL).not_gt hU).elim

/-- Every sufficiently late terminal fragment at the seventeen-ninths cut
contains the entire ordinary-prime endpoint, with no accumulated error. -/
theorem seventeenNinths_retainedPrimeEndpoint_fragments :
    ∃ n₀ : ℕ, ∀ L M : ℕ, n₀ ≤ L →
      (∑ n ∈ Ioc L M, (n:ℝ)^2 * retainedPrimeEndpoint ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n) =
      ∑ n ∈ Ioc L M, (n:ℝ)^2 * dyadicPrimeContact n := by
  obtain ⟨n₀,h⟩ := eventually_atTop.mp (eventually_retainedPrimeEndpoint
    (by norm_num : (0:ℝ)<17/9) (by norm_num : (17/9:ℝ)<2))
  exact ⟨n₀,fun L M hL => sum_congr rfl fun n hn =>
    congrArg (fun x : ℝ => (n:ℝ)^2*x) (h n (hL.trans (mem_Ioc.mp hn).1.le))⟩

/-- Restoring the finitely many initial endpoint samples has a fixed total
cost, uniform in both ends of the conductor interval. -/
theorem retainedPrimeEndpoint_initial_cost {α : ℝ} (hα : 0 < α) (h₂ : α < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L M : ℕ,
      |∑ n ∈ Ioc L M, (n:ℝ)^2 *
        (retainedPrimeEndpoint ⌊(n:ℝ)^α⌋₊ n - firstQuotientPrimeEndpoint n)| ≤ C := by
  obtain ⟨b,hb⟩ := eventually_atTop.mp (eventually_retainedPrimeEndpoint hα h₂)
  let f (n : ℕ) := (n:ℝ)^2*(retainedPrimeEndpoint ⌊(n:ℝ)^α⌋₊ n-firstQuotientPrimeEndpoint n)
  refine ⟨∑ n ∈ range b, |f n|,sum_nonneg (fun _ _ => abs_nonneg _),fun L M => ?_⟩
  change |∑ n ∈ Ioc L M, f n| ≤ _
  have he : (∑ n ∈ (Ioc L M).filter (· < b), f n) = ∑ n ∈ Ioc L M, f n := by
    apply sum_subset (filter_subset _ _)
    intro n hn hnot
    have hnb : b ≤ n := le_of_not_gt fun h => hnot (mem_filter.mpr ⟨hn,h⟩)
    have hn0 := (Nat.zero_le L).trans_lt (mem_Ioc.mp hn).1
    simp only [f,hb n hnb,firstQuotientPrimeEndpoint_eq hn0,sub_self,mul_zero]
  rw [←he]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum_of_subset_of_nonneg
    (fun n hn => mem_range.mpr (mem_filter.mp hn).2) (fun _ _ _ => abs_nonneg _))

/-- The literal endpoint with both moving cuts accounts for the rational
conductor price on every terminal fragment, up to a cubic error. -/
theorem retainedPrimeEndpoint_fragment_prices {α : ℝ} (hα : 0 < α) (h₂ : α < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L M : ℕ,
      |Real.log ((∏ n ∈ Ioc L M, ordinaryPrimeGenerator (n • successorSquareTriple n) : ℚ):ℝ) -
        ∑ n ∈ Ioc L M, (n:ℝ)^2 * retainedPrimeEndpoint ⌊(n:ℝ)^α⌋₊ n| ≤ C*(M:ℝ)^3 := by
  obtain ⟨A,hA,ha⟩ := firstQuotientPrimeEndpoint_partial_prefix
  obtain ⟨B,hB,hb⟩ := retainedPrimeEndpoint_initial_cost hα h₂
  refine ⟨A+B,add_nonneg hA hB,fun L M => ?_⟩
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  let X := Real.log ((∏ n ∈ Ioc L M, ordinaryPrimeGenerator (n • successorSquareTriple n):ℚ):ℝ)
  let F (n : ℕ) := (n:ℝ)^2 * firstQuotientPrimeEndpoint n
  let G (n : ℕ) := (n:ℝ)^2 * retainedPrimeEndpoint ⌊(n:ℝ)^α⌋₊ n
  have h := hb L M
  simp only [mul_sub,sum_sub_distrib] at h
  change |(∑ n ∈ Ioc L M, G n) - ∑ n ∈ Ioc L M, F n| ≤ B at h
  have hp : |X - ∑ n ∈ Ioc L M, F n| ≤ A*(M:ℝ)^3 := ha L M
  have hB' := le_mul_of_one_le_right hB (one_le_pow₀ (by exact_mod_cast hM : 1 ≤ (M:ℝ)) : 1 ≤ (M:ℝ)^3)
  change |X-∑ n ∈ Ioc L M, G n| ≤ _
  rw [show X-(∑ n ∈ Ioc L M, G n) = (X-∑ n ∈ Ioc L M, F n) -
    ((∑ n ∈ Ioc L M, G n)-∑ n ∈ Ioc L M, F n) by ring,add_mul]
  exact (abs_sub _ _).trans (add_le_add hp (h.trans hB'))

#print axioms retainedPrimeEndpoint_eq
#print axioms eventually_retainedPrimeEndpoint_zero_of_two_lt
#print axioms seventeenNinths_retainedPrimeEndpoint_fragments
#print axioms retainedPrimeEndpoint_fragment_prices
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
