import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodPrimeCubeLeeYangCone
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberRadialEdge

/-!
# Prime-cube theta radial moment law

At a prime cube, the reflected divisor packet has exactly four logarithmic radii: the two outer
points at `±3 log(p)/2` and the two inner points at `±log(p)/2`.  Combining this arithmetic
classification with the product-fiber radial-edge coefficient theorem gives every even packet
moment, and hence every surviving cosine-edge coefficient, in closed form.
-/

open Complex Real Finset Polynomial

namespace RHTower

noncomputable section

/-- **Prime-cube radial moment law.**  Every even reflected-divisor moment at `p³` is the sum of
two outer and two inner radial powers. -/
theorem thetaProductFiberEvenMoment_primeCube
    {p : ℕ} (hp : p.Prime) (r : ℕ) :
    thetaProductFiberEvenMoment (p ^ 3) r =
      2 * (3 * Real.log p / 2) ^ (2 * r) +
        2 * (Real.log p / 2) ^ (2 * r) := by
  rw [thetaProductFiberEvenMoment, thetaPositiveFactorPairs_prime_cube hp]
  obtain ⟨hpp, hp2p3⟩ := prime_lt_sq_and_sq_lt_cube hp
  have hp3one : 1 < p ^ 3 := hp.one_lt.trans (hpp.trans hp2p3)
  have hpOne : 1 ≤ p := hp.one_lt.le
  have hp2One : 1 ≤ p ^ 2 := hpOne.trans (hpp.le)
  have hp3One : 1 ≤ p ^ 3 := hp3one.le
  have hleft : (0, p ^ 3 - 1) ∉
      ({(p - 1, p ^ 2 - 1), (p ^ 2 - 1, p - 1), (p ^ 3 - 1, 0)} :
        Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]
    omega
  have hinnerLeft : (p - 1, p ^ 2 - 1) ∉
      ({(p ^ 2 - 1, p - 1), (p ^ 3 - 1, 0)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro heq
      have hfst : p - 1 = p ^ 2 - 1 := congrArg Prod.fst heq
      have hpEq : p = p ^ 2 := by
        calc
          p = (p - 1) + 1 := (Nat.sub_add_cancel hpOne).symm
          _ = (p ^ 2 - 1) + 1 := by rw [hfst]
          _ = p ^ 2 := Nat.sub_add_cancel hp2One
      exact (ne_of_lt hpp) hpEq
    · intro heq
      have hfst : p - 1 = p ^ 3 - 1 := congrArg Prod.fst heq
      have hpEq : p = p ^ 3 := by
        calc
          p = (p - 1) + 1 := (Nat.sub_add_cancel hpOne).symm
          _ = (p ^ 3 - 1) + 1 := by rw [hfst]
          _ = p ^ 3 := Nat.sub_add_cancel hp3One
      exact (ne_of_lt (hpp.trans hp2p3)) hpEq
  have hinnerRight : (p ^ 2 - 1, p - 1) ∉
      ({(p ^ 3 - 1, 0)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_singleton]
    intro heq
    have hfst : p ^ 2 - 1 = p ^ 3 - 1 := congrArg Prod.fst heq
    have hpEq : p ^ 2 = p ^ 3 := by
      calc
        p ^ 2 = (p ^ 2 - 1) + 1 := (Nat.sub_add_cancel hp2One).symm
        _ = (p ^ 3 - 1) + 1 := by rw [hfst]
        _ = p ^ 3 := Nat.sub_add_cancel hp3One
    exact (ne_of_lt hp2p3) hpEq
  rw [Finset.sum_insert hleft, Finset.sum_insert hinnerLeft,
    Finset.sum_insert hinnerRight, Finset.sum_singleton]
  rw [thetaFactorPairLogDisplacement_primeCube_left hp,
    thetaFactorPairLogDisplacement_primeCube_innerLeft hp,
    thetaFactorPairLogDisplacement_primeCube_innerRight hp,
    thetaFactorPairLogDisplacement_primeCube_right hp]
  have heven : Even (2 * r) := even_two_mul r
  have hnegOuter : -3 * Real.log p / 2 = -(3 * Real.log p / 2) := by ring
  have hnegInner : -Real.log p / 2 = -(Real.log p / 2) := by ring
  rw [hnegOuter, hnegInner]
  rw [heven.neg_pow, heven.neg_pow]
  ring

/-- Every surviving even coefficient of the prime-cube reflected cosine packet has an explicit
two-radius formula. -/
theorem coeff_sum_finiteCosinePolynomial_primeCube_two_mul
    {p : ℕ} (hp : p.Prime) (d l : ℕ) :
    (∑ q ∈ thetaPositiveFactorPairs (p ^ 3),
      finiteCosinePolynomial d (thetaFactorPairLogDisplacement q)).coeff (2 * l) =
      if l ≤ d then
        ((-1 : ℂ) ^ l *
          (2 * (3 * Real.log p / 2) ^ (2 * l) +
            2 * (Real.log p / 2) ^ (2 * l) : ℝ)) /
          (2 * l).factorial
      else 0 := by
  rw [coeff_sum_finiteCosinePolynomial_thetaFactorPairLogDisplacement_two_mul]
  by_cases hl : l ≤ d
  · simp only [if_pos hl, thetaProductFiberEvenMoment_primeCube hp l]
  · simp only [if_neg hl]

end

end RHTower
