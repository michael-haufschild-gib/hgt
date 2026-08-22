import GaloisForLFunctions.HTGeometry.ProjectiveHorizonAllRankQSystem

/-!
# Schur coordinates of a family lying in a subring

The corpus carries `PolynomialCoefficientsIn` for an `IntermediateField`, which is what the
*algebraic* statements about the Schur coordinates need.  The *arithmetic* statements need the same
closure over a `Subring` — a valuation subring is not a field — so this module mirrors it.

```text
PolyCoeffsIn                        all coefficients lie in the subring
  .one .add .neg .sub .mul .pow .sum
finiteUnitPolynomial_polyCoeffsIn
truncatedReciprocalKernel_polyCoeffsIn
finiteReciprocalPositive_mem
finiteUnitSquarePositive_mem
finiteReciprocalSquarePositive_mem  ** the Schur coordinates of a family in a subring stay in it **
```

The point is that `truncatedReciprocalKernel N U = ∑_{j < N} (-(U-1))^j` involves **no division**, so
the reciprocal coordinates are integral polynomial expressions in the normalised jet and stay inside
any subring containing it.  Applied to the pullback of the upper Schur valuation ring along a sheet,
this is what puts every Schur coordinate of every sheet inside that valuation ring, once the scale
is known to be a unit there.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- A polynomial all of whose coefficients lie in a subring. -/
def PolyCoeffsIn {E : Type*} [CommRing E] (S : Subring E) (P : E[X]) : Prop :=
  ∀ k, P.coeff k ∈ S

namespace PolyCoeffsIn

variable {E : Type*} [CommRing E] {S : Subring E} {P Q : E[X]}

theorem one : PolyCoeffsIn S 1 := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

theorem add (hP : PolyCoeffsIn S P) (hQ : PolyCoeffsIn S Q) : PolyCoeffsIn S (P + Q) := by
  intro k
  rw [Polynomial.coeff_add]
  exact S.add_mem (hP k) (hQ k)

theorem neg (hP : PolyCoeffsIn S P) : PolyCoeffsIn S (-P) := by
  intro k
  rw [Polynomial.coeff_neg]
  exact S.neg_mem (hP k)

theorem sub (hP : PolyCoeffsIn S P) (hQ : PolyCoeffsIn S Q) : PolyCoeffsIn S (P - Q) := by
  intro k
  rw [Polynomial.coeff_sub]
  exact S.sub_mem (hP k) (hQ k)

theorem mul (hP : PolyCoeffsIn S P) (hQ : PolyCoeffsIn S Q) : PolyCoeffsIn S (P * Q) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact Subring.sum_mem _ fun x _ => S.mul_mem (hP x.1) (hQ x.2)

theorem pow (hP : PolyCoeffsIn S P) (r : ℕ) : PolyCoeffsIn S (P ^ r) := by
  induction r with
  | zero => simpa using (one : PolyCoeffsIn S 1)
  | succ r ihr => simpa [pow_succ] using ihr.mul hP

theorem sum {I : Type*} {s : Finset I} {P : I → E[X]}
    (hP : ∀ i ∈ s, PolyCoeffsIn S (P i)) : PolyCoeffsIn S (∑ i ∈ s, P i) := by
  intro k
  rw [Polynomial.finsetSum_coeff]
  exact Subring.sum_mem _ fun i hi => hP i hi k

end PolyCoeffsIn

variable {E : Type*} [Field E] {L : ℕ}

theorem finiteUnitPolynomial_polyCoeffsIn (S : Subring E) (u : Fin L → E)
    (hu : ∀ i, u i ∈ S) : PolyCoeffsIn S (finiteUnitPolynomial u) := by
  intro k
  rw [finiteUnitPolynomial, Polynomial.coeff_add, Polynomial.coeff_one]
  refine S.add_mem ?_ ?_
  · split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  · rw [Polynomial.finsetSum_coeff]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [Polynomial.coeff_monomial]
    split_ifs
    · exact hu i
    · exact S.zero_mem

theorem truncatedReciprocalKernel_polyCoeffsIn [CharZero E] (S : Subring E) (N : ℕ)
    {U : E[X]} (hU : PolyCoeffsIn S U) :
    PolyCoeffsIn S (truncatedReciprocalKernel N U) := by
  rw [truncatedReciprocalKernel]
  refine PolyCoeffsIn.sum fun j _ => ?_
  exact ((hU.sub PolyCoeffsIn.one).neg).pow j

theorem finiteReciprocalPositive_mem [CharZero E] (S : Subring E) (u : Fin L → E)
    (hu : ∀ i, u i ∈ S) (i : Fin L) : finiteReciprocalPositive u i ∈ S :=
  truncatedReciprocalKernel_polyCoeffsIn S (L + 1)
    (finiteUnitPolynomial_polyCoeffsIn S u hu) ((i : ℕ) + 1)

theorem finiteUnitSquarePositive_mem (S : Subring E) (z : Fin L → E)
    (hz : ∀ i, z i ∈ S) (i : Fin L) : finiteUnitSquarePositive z i ∈ S := by
  rw [finiteUnitSquarePositive]
  exact ((finiteUnitPolynomial_polyCoeffsIn S z hz).pow 2) ((i : ℕ) + 1)

/-- **The reciprocal-square coordinates of a family lying in a subring lie in that subring.** -/
theorem finiteReciprocalSquarePositive_mem [CharZero E] (S : Subring E) (u : Fin L → E)
    (hu : ∀ i, u i ∈ S) (i : Fin L) : finiteReciprocalSquarePositive u i ∈ S := by
  rw [finiteReciprocalSquarePositive]
  exact finiteUnitSquarePositive_mem S _ (finiteReciprocalPositive_mem S u hu) i

end GaloisForLFunctions.HTGeometry
