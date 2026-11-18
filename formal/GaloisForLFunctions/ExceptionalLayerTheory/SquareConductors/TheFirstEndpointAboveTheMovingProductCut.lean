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
  unfold clippedFirstEndpoint
  rw [sum_Ico_eq_sub _ hD]
  change ((∑ k ∈ range (lastProductHorizon n q), r k) - (∑ k ∈ range q, r k)) -
    (∑ k ∈ range (lastProductHorizon n q), r k) = sampledSpline n q
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

#print axioms retainedPrimeEndpoint_eq
#print axioms seventeenNinths_retainedPrimeEndpoint_fragments
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
