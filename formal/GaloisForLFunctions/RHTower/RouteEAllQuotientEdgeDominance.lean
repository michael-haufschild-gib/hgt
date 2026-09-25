import GaloisForLFunctions.RHTower.RouteEQuotientParentDominance
import GaloisForLFunctions.RHTower.RouteEUpperBoundaryEdgePair

/-!
# Nonpositive physical parity-paired Route E quotient section

The cross-quotient parent dominance theorem applies to the literal two-edge
Gamma--Hankel covariance at exponent one. For each odd squarefree cofactor,
all coprime quotient pairs `q≥3` inside a physical cutoff have nonpositive
aggregate; summing cofactors preserves this upper sign. Edge indexing is
injective/disjoint by `RouteEUpperBoundaryEdgePair`, and this module records
cutoff support without requiring an absent fourth rectangle corner.
This is not a bound for all off-diagonal entries or the moving `r>1` receiver.
-/

open Finset ArithmeticFunction
open scoped BigOperators

namespace RHTower

noncomputable section

def routeEAllQuotientPairedEdgeSection (N : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Odd d ∧ Squarefree d),
    ∑ q ∈ (Finset.Icc 3 (N / d)).filter (fun q => d.Coprime q),
      routeEUpperBoundaryEdgePair q d

theorem routeE_allQuotient_edgeRay_le_zero
    {d Q : ℕ} (hd : 1 ≤ d) (hodd : Odd d) (hsf : Squarefree d) :
    (∑ q ∈ (Finset.Icc 3 Q).filter (fun q => d.Coprime q),
      routeEUpperBoundaryEdgePair q d) ≤ 0 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hsum := signedQuotientWeight_le_zero d Q
  have heq :
      (∑ q ∈ (Finset.Icc 3 Q).filter (fun q => d.Coprime q),
        routeEUpperBoundaryEdgePair q d) =
        (2 / (d : ℝ)) *
          (∑ q ∈ (Finset.Icc 3 Q).filter (fun q => d.Coprime q),
            (moebius q : ℝ) * quotientEdgeWeight q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hcop : d.Coprime q := (Finset.mem_filter.mp hq).2
    rw [routeEUpperBoundaryEdgePair_eq hd hodd hsf hcop]
    unfold mobiusRealCoefficient quotientEdgeWeight
    have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
    have hq2 : (0 : ℝ) < (q : ℝ) + 2 := by positivity
    field_simp
  rw [heq]
  exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg (by norm_num) hdpos.le) hsum

theorem routeEAllQuotientPairedEdgeSection_le_zero (N : ℕ) :
    routeEAllQuotientPairedEdgeSection N ≤ 0 := by
  unfold routeEAllQuotientPairedEdgeSection
  apply Finset.sum_nonpos
  intro d hd
  obtain ⟨hdi, hodd, hsf⟩ := Finset.mem_filter.mp hd
  exact routeE_allQuotient_edgeRay_le_zero (Finset.mem_Icc.mp hdi).1 hodd hsf

theorem routeE_allQuotient_edge_physical
    {N d q : ℕ} (hd : 1 ≤ d) (hq : q ∈ Finset.Icc 3 (N / d)) :
    1 ≤ d ∧ d < 2 * d ∧ 2 * d < q * d ∧ q * d ≤ N := by
  have hq3 : 3 ≤ q := (Finset.mem_Icc.mp hq).1
  have hqhi : q ≤ N / d := (Finset.mem_Icc.mp hq).2
  have hcut : q * d ≤ N := by
    have := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hqhi
    simpa [Nat.mul_comm] using this
  refine ⟨hd, by omega, ?_, hcut⟩
  nlinarith

end
end RHTower
