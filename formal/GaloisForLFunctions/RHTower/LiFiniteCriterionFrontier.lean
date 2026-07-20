import GaloisForLFunctions.RHTower.SecularMoments

/-!
# Finite Li--Keiper / secular-moment frontier

Li's criterion uses the infinite zero sum
`lambda_n = sum_rho (1 - (1 - 1/rho)^n)`.  The existing `SecularMoments` module proves the
pointwise binomial identities.  This file performs the complete finite-spectrum passage: finite
Li coefficients and finite reciprocal moments determine one another by explicit integral
triangular transforms.

Everything here is unconditional and involves no numerical zero data.  The precise remaining Li
wall is analytic, not algebraic: construct the canonical multiplicity-sensitive infinite sums (or
the equivalent logarithmic derivatives of completed xi), justify the limiting transforms, and
establish the Bombieri--Lagarias positivity equivalence.  None of those infinite claims is
silently represented by the finite definitions below.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

variable {R I : Type*} [CommRing R]

/-- Li's `n`-th coefficient for a finite spectral packet in reciprocal coordinates. -/
def finiteLiCoefficient (s : Finset I) (x : I → R) (n : ℕ) : R :=
  ∑ q ∈ s, (1 - (1 - x q) ^ n)

/-- The `k`-th reciprocal power sum of a finite spectral packet. -/
def finiteSecularMoment (s : Finset I) (x : I → R) (k : ℕ) : R :=
  ∑ q ∈ s, (x q) ^ k

/-- Finite Li coefficients are the binomial transform of finite secular moments. -/
theorem finiteLiCoefficient_eq_secularMoments
    (s : Finset I) (x : I → R) (n : ℕ) :
    finiteLiCoefficient s x n =
      ∑ j ∈ Finset.range n,
        (n.choose (j + 1) : R) * (-1) ^ j * finiteSecularMoment s x (j + 1) := by
  classical
  simp only [finiteLiCoefficient, finiteSecularMoment,
    GaloisForLFunctions.li_secular_pointwise]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]

/-- Conversely, every positive-degree finite secular moment is the inverse binomial transform of
the finite Li coefficients. -/
theorem finiteSecularMoment_eq_liCoefficients
    (s : Finset I) (x : I → R) (k : ℕ) (hk : 0 < k) :
    finiteSecularMoment s x k =
      ∑ m ∈ Finset.range k,
        (-1) ^ m * (k.choose (m + 1) : R) * finiteLiCoefficient s x (m + 1) := by
  classical
  simp only [finiteLiCoefficient, finiteSecularMoment,
    GaloisForLFunctions.secular_li_pointwise_inv R _ k hk]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]

end

end RHTower
