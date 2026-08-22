import GaloisForLFunctions.HTGeometry.ProjectiveHorizonAllRankQSystem

/-!
# The Schur coordinates over an arbitrary commutative ring

The corpus defines the Schur coordinate construction over a field, but **no step of it divides**:
the unit polynomial is `1 + ∑ u_i X^{i+1}`, the truncated reciprocal kernel is
`∑_{j<N} (−(U−1))^j`, and the square is a square.  So the whole construction lives over any
commutative ring, and it is natural in ring homomorphisms.

```text
ringUnitPolynomial, ringTruncatedReciprocalKernel
ringReciprocalPositive, ringUnitSquarePositive, ringReciprocalSquarePositive
ringUnitPolynomial_eq, ringTruncatedReciprocalKernel_eq, ringReciprocalSquarePositive_eq
    the ring versions are DEFINITIONALLY the corpus's field versions
ringUnitPolynomial_map, ringTruncatedReciprocalKernel_map
ringReciprocalPositive_map, ringUnitSquarePositive_map
ringReciprocalSquarePositive_map
    ** f (coordinate of u) = coordinate of (f ∘ u), for every ring hom f **
```

Naturality is what the collision argument needs, applied to the *residue map* of the upper Schur
valuation ring, which is a ring hom out of a ring that is not a field: two sheets whose fibre
coefficients have the same residues therefore have the same residues on every Schur coordinate, and
so cut out the same centre on the Schur coordinate ring.  Stating the construction only over a field
makes that step inexpressible.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] {L : ℕ}

/-- The unit polynomial of a finite family, over any commutative ring. -/
noncomputable def ringUnitPolynomial (u : Fin L → R) : R[X] :=
  1 + ∑ i : Fin L, Polynomial.monomial ((i : ℕ) + 1) (u i)

/-- The truncated reciprocal kernel, over any commutative ring. -/
noncomputable def ringTruncatedReciprocalKernel (N : ℕ) (U : R[X]) : R[X] :=
  ∑ j ∈ Finset.range N, (-(U - 1)) ^ j

/-- The positive reciprocal coordinates, over any commutative ring. -/
noncomputable def ringReciprocalPositive (u : Fin L → R) : Fin L → R :=
  fun i => (ringTruncatedReciprocalKernel (L + 1) (ringUnitPolynomial u)).coeff ((i : ℕ) + 1)

/-- The positive square coordinates, over any commutative ring. -/
noncomputable def ringUnitSquarePositive (z : Fin L → R) : Fin L → R :=
  fun i => ((ringUnitPolynomial z) ^ 2).coeff ((i : ℕ) + 1)

/-- The Schur reciprocal-square coordinates, over any commutative ring. -/
noncomputable def ringReciprocalSquarePositive (u : Fin L → R) : Fin L → R :=
  ringUnitSquarePositive (ringReciprocalPositive u)

theorem ringUnitPolynomial_eq {E : Type*} [Field E] (u : Fin L → E) :
    ringUnitPolynomial u = finiteUnitPolynomial u := rfl

theorem ringTruncatedReciprocalKernel_eq {E : Type*} [Field E] [CharZero E] (N : ℕ) (U : E[X]) :
    ringTruncatedReciprocalKernel N U = truncatedReciprocalKernel N U := rfl

theorem ringReciprocalSquarePositive_eq {E : Type*} [Field E] [CharZero E] (u : Fin L → E) :
    ringReciprocalSquarePositive u = finiteReciprocalSquarePositive u := rfl

/-! ## Naturality -/

theorem ringUnitPolynomial_map (f : R →+* S) (u : Fin L → R) :
    (ringUnitPolynomial u).map f = ringUnitPolynomial (fun j => f (u j)) := by
  rw [ringUnitPolynomial, ringUnitPolynomial, Polynomial.map_add, Polynomial.map_one,
    Polynomial.map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.map_monomial]

theorem ringTruncatedReciprocalKernel_map (f : R →+* S) (N : ℕ) (U : R[X]) :
    (ringTruncatedReciprocalKernel N U).map f
      = ringTruncatedReciprocalKernel N (U.map f) := by
  rw [ringTruncatedReciprocalKernel, ringTruncatedReciprocalKernel, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_sub, Polynomial.map_one]

theorem ringReciprocalPositive_map (f : R →+* S) (u : Fin L → R) (i : Fin L) :
    f (ringReciprocalPositive u i) = ringReciprocalPositive (fun j => f (u j)) i := by
  rw [ringReciprocalPositive, ringReciprocalPositive, ← Polynomial.coeff_map,
    ringTruncatedReciprocalKernel_map, ringUnitPolynomial_map]

theorem ringUnitSquarePositive_map (f : R →+* S) (z : Fin L → R) (i : Fin L) :
    f (ringUnitSquarePositive z i) = ringUnitSquarePositive (fun j => f (z j)) i := by
  rw [ringUnitSquarePositive, ringUnitSquarePositive, ← Polynomial.coeff_map,
    Polynomial.map_pow, ringUnitPolynomial_map]

/-- **The Schur reciprocal-square coordinates are natural in the ring.** -/
theorem ringReciprocalSquarePositive_map (f : R →+* S) (u : Fin L → R) (i : Fin L) :
    f (ringReciprocalSquarePositive u i)
      = ringReciprocalSquarePositive (fun j => f (u j)) i := by
  rw [ringReciprocalSquarePositive, ringReciprocalSquarePositive,
    ringUnitSquarePositive_map]
  congr 1
  funext j
  exact ringReciprocalPositive_map f u j

end GaloisForLFunctions.HTGeometry
