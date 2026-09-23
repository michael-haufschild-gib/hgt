import GaloisForLFunctions.HTGeometry.FZZCigarHigherGenusTwistRedshift

/-!
# FZZ cigar torus replica neutrality

This file isolates a genus-one constraint specific to the fractional-winding
definition of stringy black-hole area.

Halder--Jafferis, *Stretched horizon, replica trick and off-shell winding
condensate, and all that* (arXiv:2402.00932, eqs. (3.29)--(3.33)), define the
area insertion by differentiating the two opposite fractional-winding fields
`W⁺_δ` and `W⁻_δ` at `δ = 0`.  They stress that the resulting operator is
non-local, has branch cuts with physical vertex operators, and that its torus
one-point function is an open problem.  Their sphere calculation avoids the
branch issue by differentiating the exponentiated condensate.

The relevant torus obstruction is exact.  Around a winding cycle the two
fields acquire reciprocal multipliers `exp(∓2πiδ)`.  Their tangents therefore
acquire opposite additive monodromies.  In a sector with `nPlus` positive and
`nMinus` negative screenings, the tangent defect is

`(nMinus - nPlus) * c * plus * minus`,

where physically `c = 2πi`.  Thus a nonzero sector is single-valued exactly
when its two screening counts agree.  In particular an isolated area tangent
is not a scalar torus observable, while the tangent of every neutral term in
the exponentiated condensate is single-valued.

This is the first source-faithful completion rule for the proposed torus area:
differentiate the full neutral FZZ screening sum, not a bare one-point field.
It does **not** evaluate that sum, prove positivity of its continuum
completion, or assert an RH consequence.
-/

namespace GaloisForLFunctions.HTGeometry.FZZCigar

section ReplicaNeutrality

variable {R : Type*} [CommRing R]

/-- Tangent of a product of the aggregate positive- and negative-winding
screening factors.  `plusTangent` and `minusTangent` already include the sums
over the differentiated insertion in their respective screening products. -/
def torusReplicaTangent
    (plus minus plusTangent minusTangent : R) : R :=
  plusTangent * minus + plus * minusTangent

/-- Exact additive monodromy of a fractional-winding replica tangent.

The aggregate positive tangent shifts by `-nPlus * c * plus`; the aggregate
negative tangent shifts by `+nMinus * c * minus`.  Their paired tangent retains
only the net winding-charge defect. -/
theorem torusReplicaTangent_monodromy_defect
    (nPlus nMinus : ℕ) (c plus minus plusTangent minusTangent : R) :
    torusReplicaTangent plus minus
          (plusTangent - (nPlus : R) * c * plus)
          (minusTangent + (nMinus : R) * c * minus)
        - torusReplicaTangent plus minus plusTangent minusTangent =
      ((nMinus : R) - (nPlus : R)) * c * (plus * minus) := by
  simp only [torusReplicaTangent]
  ring

/-- Every charge-neutral screening sector has a single-valued replica
tangent: opposite fractional-winding branch cocycles cancel exactly. -/
theorem balanced_torusReplicaTangent_monodromy_invariant
    (n : ℕ) (c plus minus plusTangent minusTangent : R) :
    torusReplicaTangent plus minus
          (plusTangent - (n : R) * c * plus)
          (minusTangent + (n : R) * c * minus) =
      torusReplicaTangent plus minus plusTangent minusTangent := by
  simp only [torusReplicaTangent]
  ring

/-- With nonzero monodromy and nonzero screening products, single-valuedness
is equivalent to equality of the two screening counts.  This is the sharp
torus neutrality law for the exponentiated replica condensate. -/
theorem torusReplicaTangent_monodromy_invariant_iff_neutral
    [IsDomain R] [CharZero R]
    (nPlus nMinus : ℕ) (c plus minus plusTangent minusTangent : R)
    (hc : c ≠ 0) (hplus : plus ≠ 0) (hminus : minus ≠ 0) :
    torusReplicaTangent plus minus
          (plusTangent - (nPlus : R) * c * plus)
          (minusTangent + (nMinus : R) * c * minus) =
        torusReplicaTangent plus minus plusTangent minusTangent ↔
      nPlus = nMinus := by
  constructor
  · intro h
    have hzero : ((nMinus : R) - (nPlus : R)) * c * (plus * minus) = 0 := by
      rw [← torusReplicaTangent_monodromy_defect]
      rw [h]
      simp
    have hcast : (nMinus : R) - (nPlus : R) = 0 := by
      rcases mul_eq_zero.mp hzero with hcoeffc | hpm
      · rcases mul_eq_zero.mp hcoeffc with hcoeff | hc0
        · exact hcoeff
        · exact (hc hc0).elim
      · exact ((mul_ne_zero hplus hminus) hpm).elim
    exact (by exact_mod_cast (sub_eq_zero.mp hcast).symm)
  · intro h
    subst nMinus
    exact balanced_torusReplicaTangent_monodromy_invariant
      nPlus c plus minus plusTangent minusTangent

/-- A single uncompensated positive-winding tangent cannot descend to the
torus when its monodromy and screening products are nonzero. -/
theorem unpaired_positive_torusReplicaTangent_not_invariant
    [IsDomain R] [CharZero R]
    (c plus minus plusTangent minusTangent : R)
    (hc : c ≠ 0) (hplus : plus ≠ 0) (hminus : minus ≠ 0) :
    torusReplicaTangent plus minus
          (plusTangent - (1 : R) * c * plus)
          (minusTangent + (0 : R) * c * minus) ≠
      torusReplicaTangent plus minus plusTangent minusTangent := by
  intro h
  have hcounts : (1 : ℕ) = 0 :=
    (torusReplicaTangent_monodromy_invariant_iff_neutral
      1 0 c plus minus plusTangent minusTangent hc hplus hminus).mp (by
        simpa using h)
  exact Nat.one_ne_zero hcounts

end ReplicaNeutrality

section ExponentiatedCondensate

/-- Coefficient of the charge-neutral depth-`n` term obtained by expanding
the two exponentials of the opposite FZZ winding condensates.  The two signs
square away, leaving `μ^(2n)/(n!)²`. -/
noncomputable def neutralScreeningCoefficient (μ : ℂ) (n : ℕ) : ℂ :=
  μ ^ (2 * n) / ((n.factorial : ℂ) ^ (2 : ℕ))

/-- A nonzero FZZ cosmological constant activates every neutral screening
depth in the exponentiated replica condensate.  Torus neutrality therefore
does not justify a finite-depth or bare-one-point truncation. -/
theorem neutralScreeningCoefficient_ne_zero
    {μ : ℂ} (hμ : μ ≠ 0) (n : ℕ) :
    neutralScreeningCoefficient μ n ≠ 0 := by
  apply div_ne_zero
  · exact pow_ne_zero _ hμ
  · exact pow_ne_zero _ (by exact_mod_cast n.factorial_ne_zero)

end ExponentiatedCondensate

end GaloisForLFunctions.HTGeometry.FZZCigar
