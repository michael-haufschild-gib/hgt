import GaloisForLFunctions.RHTower.RouteEQuotientPowerTransport
import GaloisForLFunctions.RHTower.RouteEUpperBoundaryEdgePair

/-!
# Physical parity-paired Route E section at every receiver exponent

The normalized two-entry pair below is exactly the part of the finite
Gamma--Hankel off-diagonal covariance with endpoints `(d, q*d)` and
`(2*d, q*d)`.  Multiplying its complete finite section by `Gamma r` restores
the literal covariance normalization.  For every real `r ≥ 1`, each full
coprime quotient ray and hence the whole selected physical section is
nonpositive.  Both entries are inside the cutoff for `q ≥ 3`; their index
disjointness is proved in `RouteEUpperBoundaryEdgePair`.

No claim is made for the complementary noninteger primitive-ratio pairs.
-/

open Finset ArithmeticFunction
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Normalized literal two-entry Gamma--Hankel pair at real exponent `r`. -/
def routeEPowerEdgePair (r : ℝ) (q d : ℕ) : ℝ :=
  2 * mobiusRealCoefficient d * mobiusRealCoefficient (q * d) /
      (((d + q * d : ℕ) : ℝ) ^ r) +
    2 * mobiusRealCoefficient (2 * d) * mobiusRealCoefficient (q * d) /
      (((2 * d + q * d : ℕ) : ℝ) ^ r)

theorem routeEPowerEdgePair_one (q d : ℕ) :
    routeEPowerEdgePair 1 q d = routeEUpperBoundaryEdgePair q d := by
  simp [routeEPowerEdgePair, routeEUpperBoundaryEdgePair]

/-- The signed quotient weight is the exact literal paired matrix entry. -/
theorem routeEPowerEdgePair_eq {r : ℝ} {q d : ℕ}
    (hd : 1 ≤ d) (hodd : Odd d) (hsf : Squarefree d)
    (hcop : d.Coprime q) :
    routeEPowerEdgePair r q d =
      (2 / ((d : ℝ) ^ r)) * mobiusRealCoefficient q * quotientPowerEdgeWeight r q := by
  let md : ℝ := mobiusRealCoefficient d
  let mq : ℝ := mobiusRealCoefficient q
  have hmd : md ^ 2 = 1 := by
    dsimp [md]
    have hne : moebius d ≠ 0 := moebius_ne_zero_iff_squarefree.mpr hsf
    rcases moebius_ne_zero_iff_eq_or.mp hne with hm | hm <;>
      simp [mobiusRealCoefficient, hm]
  have hμqd : mobiusRealCoefficient (q * d) = mq * md := by
    dsimp [mq, md, mobiusRealCoefficient]
    rw [Sieve.moebius_mul_of_coprime hcop.symm]
    push_cast
    ring
  have hμ2d : mobiusRealCoefficient (2 * d) = -md := by
    have hm2 : moebius 2 = -1 := by
      simpa using ArithmeticFunction.moebius_apply_prime Nat.prime_two
    dsimp [md, mobiusRealCoefficient]
    rw [Sieve.moebius_mul_of_coprime hodd.coprime_two_left]
    rw [hm2]
    norm_num
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hq2 : (0 : ℝ) < (q : ℝ) + 2 := by positivity
  have hden1 : (((d + q * d : ℕ) : ℝ)) = (d : ℝ) * ((q : ℝ) + 1) := by
    push_cast; ring
  have hden2 : (((2 * d + q * d : ℕ) : ℝ)) = (d : ℝ) * ((q : ℝ) + 2) := by
    push_cast; ring
  have hqpow1 : (1 / ((q : ℝ) + 1)) ^ r = 1 / (((q : ℝ) + 1) ^ r) := by
    rw [Real.div_rpow (by norm_num) hq1.le r]
    simp
  have hqpow2 : (1 / ((q : ℝ) + 2)) ^ r = 1 / (((q : ℝ) + 2) ^ r) := by
    rw [Real.div_rpow (by norm_num) hq2.le r]
    simp
  unfold routeEPowerEdgePair
  rw [hμqd, hμ2d, hden1, hden2,
    Real.mul_rpow hdpos.le hq1.le, Real.mul_rpow hdpos.le hq2.le]
  rw [show quotientPowerEdgeWeight r q =
      1 / (((q : ℝ) + 1) ^ r) - 1 / (((q : ℝ) + 2) ^ r) by
        unfold quotientPowerEdgeWeight
        rw [hqpow1, hqpow2]]
  change 2 * md * (mq * md) /
      ((d : ℝ) ^ r * ((q : ℝ) + 1) ^ r) +
    2 * -md * (mq * md) /
      ((d : ℝ) ^ r * ((q : ℝ) + 2) ^ r) =
    (2 / ((d : ℝ) ^ r)) * mq *
      (1 / (((q : ℝ) + 1) ^ r) - 1 / (((q : ℝ) + 2) ^ r))
  calc
    _ = md ^ 2 * ((2 / ((d : ℝ) ^ r)) * mq *
        (1 / (((q : ℝ) + 1) ^ r) - 1 / (((q : ℝ) + 2) ^ r))) := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
    _ = _ := by rw [hmd]; ring

/-- Every complete quotient ray of literal paired entries has upper sign. -/
theorem routeE_power_edgeRay_le_zero {r : ℝ} (hr : 1 ≤ r)
    {d Q : ℕ} (hd : 1 ≤ d) (hodd : Odd d) (hsf : Squarefree d) :
    (∑ q ∈ (Finset.Icc 3 Q).filter (fun q => d.Coprime q),
      routeEPowerEdgePair r q d) ≤ 0 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hcoef : 0 ≤ 2 / ((d : ℝ) ^ r) :=
    div_nonneg (by norm_num) (Real.rpow_pos_of_pos hdpos r).le
  have hsign := signedQuotientPowerWeight_le_zero hr d Q
  have heq :
      (∑ q ∈ (Finset.Icc 3 Q).filter (fun q => d.Coprime q),
        routeEPowerEdgePair r q d) =
      (2 / ((d : ℝ) ^ r)) *
        (∑ q ∈ (Finset.Icc 3 Q).filter (fun q => d.Coprime q),
          (moebius q : ℝ) * quotientPowerEdgeWeight r q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hcop : d.Coprime q := (Finset.mem_filter.mp hq).2
    rw [routeEPowerEdgePair_eq hd hodd hsf hcop]
    unfold mobiusRealCoefficient
    ring
  rw [heq]
  exact mul_nonpos_of_nonneg_of_nonpos hcoef hsign

/-- The selected source-faithful section, including the actual Gamma factor. -/
def routeEAllQuotientPowerPairedEdgeSection (N : ℕ) (r : ℝ) : ℝ :=
  Real.Gamma r *
    ∑ d ∈ (Finset.Icc 1 N).filter (fun d => Odd d ∧ Squarefree d),
      ∑ q ∈ (Finset.Icc 3 (N / d)).filter (fun q => d.Coprime q),
        routeEPowerEdgePair r q d

/-- Entire selected physical matrix section is nonpositive at every `r ≥ 1`. -/
theorem routeEAllQuotientPowerPairedEdgeSection_le_zero
    (N : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    routeEAllQuotientPowerPairedEdgeSection N r ≤ 0 := by
  have hGamma : 0 ≤ Real.Gamma r :=
    (Real.Gamma_pos_of_pos (by linarith : 0 < r)).le
  have hinner :
      (∑ d ∈ (Finset.Icc 1 N).filter (fun d => Odd d ∧ Squarefree d),
        ∑ q ∈ (Finset.Icc 3 (N / d)).filter (fun q => d.Coprime q),
          routeEPowerEdgePair r q d) ≤ 0 := by
    apply Finset.sum_nonpos
    intro d hd
    obtain ⟨hdi, hodd, hsf⟩ := Finset.mem_filter.mp hd
    exact routeE_power_edgeRay_le_zero hr (Finset.mem_Icc.mp hdi).1 hodd hsf
  unfold routeEAllQuotientPowerPairedEdgeSection
  exact mul_nonpos_of_nonneg_of_nonpos hGamma hinner

end
end RHTower
