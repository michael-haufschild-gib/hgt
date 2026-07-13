# Prime--arch theta Hankel degree-two tail gate

- **ID:** `prime-arch-theta-hankel-degree-two-tail-gate`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** not new scientific knowledge
- **Lean file:** `formal/GaloisForLFunctions/RHTower/PrimeArchThetaHankelDegreeTail.lean`
- **Statement:** The two theta-cusp ratio inequalities plus prime--Gamma source-Hankel
  nonnegativity only for integer polynomials of degree at least two imply RH.

## Goal

Remove the already-controlled constant and linear faces from the countable prime--Gamma Hankel
criterion.  This separates the explicit low-degree theta problem from the genuinely cofinal
higher-degree source problem without changing either open mathematical input.

## The chain

Let

```text
ThetaCuspUpperAdjacentRatioSeparation
ThetaCuspRelaxedFourthMomentConcentration
```

be the two source-pure moment-ratio inequalities.  Their existing Lean gate proves nonnegativity
of `primeArchSourceTraceHankel` on every real polynomial `a + b X`.  Define the remaining tail by

```text
forall p : Polynomial Z,
  2 <= p.natDegree ->
  0 <= re (primeArchSourceTraceHankel (p mapped to R)).
```

Every integer polynomial either belongs to that tail or has degree at most one.  In the latter
case `eq_X_add_C_of_degree_le_one` writes it exactly as `a + b X`, so the theta ratio gate applies.
The complete countable source positivity criterion then gives RH.

Thus the formal chain is

```text
two theta-cusp ratio inequalities
  + degree-at-least-two integer source-Hankel tail
  -> complete integer-polynomial source-Hankel nonnegativity
  -> RH.
```

This theorem does not prove either ratio inequality or any member of the higher-degree tail.

## Scalar determinant-tail refinement

If at least one of the two ratio inequalities has strict margin, their exact weighted identity
makes the `2 x 2` prime--Gamma moment determinant strictly positive.  The empty determinant and
the `1 x 1` determinant are already unconditionally positive.  The leading-determinant RH
criterion therefore gives the sharper chain

```text
two theta-cusp ratio inequalities, with at least one strict
  + det(prime--Gamma moment matrix n) > 0 for every n >= 3
  -> all leading prime--Gamma moment determinants are positive
  -> RH.
```

This replaces the higher-degree polynomial cone by one scalar determinant at each size.  It does
not assert the strict ratio margin or the determinant tail.

## Principal declarations

- `PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative`
- `primeArchSourceTraceHankelIntNonnegative_of_ratioSplit_of_degreeTwoTail`
- `riemannHypothesis_of_thetaCuspRatioSplit_of_primeArchDegreeTwoTail`
- `det_primeArchSourceMomentHankelMatrix_two_pos_of_ratioSplit_of_one_strict`
- `PrimeArchSourceMomentHankelDeterminantTailFromThreePositive`
- `riemannHypothesis_of_strictThetaCuspRatioSplit_of_primeArchDeterminantTailFromThree`

## Gates

- [x] 0 -> 1  source-pure interfaces and exact degree split identified
- [x] 1 -> 2  complete paper proof
- [x] 2 -> 3  formalized in Lean with no new axioms
- [ ] 3 -> 4  publication-ready treatment not warranted for this interface theorem
