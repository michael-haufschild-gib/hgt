import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Ranks.Observable
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Ranks.Ordered

/-! # Exact signed thermometry from two unlabeled outgoing ranks -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks

open _root_.HTGeometry
open scoped ComplexConjugate

theorem boson_odds_eq (S : Finset Nat.Primes) (m : ℕ) (s : ℂ) :
    measuredOdds S (fun _ => m) m s =
      logOdds (finiteGibbsStateWeight (2*s.re-1) (read primeEnergy : Boson S m → ℝ)) := by
  rw [measuredOdds_eq]
  simp_rw [energy_eq_read]

/-- At every complex parameter, subtracting the reflected log odds cancels the unsigned
part and leaves signed damping times the difference of the two adjacent edge gaps. -/
theorem signed_rank_contrast (S : Finset Nat.Primes) (h : 3 ≤ S.card) (n : ℕ) (s : ℂ) :
    measuredOdds S (fun _ => n+1) (n+1) s - measuredOdds S (fun _ => n+1) (n+1) (1-conj s) =
      (2*s.re-1)*edgeDifference S h := by
  let l := bottom S h
  let q := nextLow S h
  let r := nextHigh S h
  let u := topMode S h
  have low := firstTwo_boson n primeEnergy l q (low_lt S h) (above_nextLow S h)
  have high := firstTwo_boson n (fun i : S => -primeEnergy i) u r (neg_lt_neg (high_lt S h))
    (fun i hu hr => neg_lt_neg (below_nextHigh S h i hu hr))
  rw [read_neg_fun] at high
  have upper : read primeEnergy (pure (n+1) u)-read primeEnergy (firstExcitation n u r) =
      primeEnergy u-primeEnergy r := by linarith only [first_gap n u r primeEnergy]
  rw [boson_odds_eq,boson_odds_eq,
    show 2*(1-conj s).re-1 = -(2*s.re-1) by rw [Complex.sub_re,Complex.one_re,Complex.conj_re]; ring,
    odds_contrast low high, first_gap, upper]
  rfl

theorem recover_damping (S : Finset Nat.Primes) (h : 3 ≤ S.card) (n : ℕ) (s : ℂ) :
    (measuredOdds S (fun _ => n+1) (n+1) s - measuredOdds S (fun _ => n+1) (n+1) (1-conj s)) /
      edgeDifference S h = 2*s.re-1 := by
  rw [signed_rank_contrast S h, mul_div_cancel_right₀ _ (edgeDifference_ne S h)]

/-- Equality of the two rank readings decides isometry on the entire infinite gas. -/
theorem ranked_match_iff_isometry (S : Finset Nat.Primes) (h : 3 ≤ S.card) (n : ℕ) (s : ℂ) :
    measuredOdds S (fun _ => n+1) (n+1) s = measuredOdds S (fun _ => n+1) (n+1) (1-conj s) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  rw [split_isometric_iff, ← sub_eq_zero, signed_rank_contrast S h, mul_eq_zero,
    or_iff_left (edgeDifference_ne S h)]
  constructor <;> intro hx <;> linarith only [hx]

#print axioms signed_rank_contrast
#print axioms recover_damping
#print axioms ranked_match_iff_isometry

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks
