# Xi--Hedenmalm common Kummer-root collision

- **ID:** `xi-hedenmalm-common-kummer-root-collision`
- **Stage:** 3-formalized
- **Type:** TOP-DOWN RH CHAIN / HEDENMALM KUMMER CONSTRAINT
- **Scientific status:** `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean parents:** `XiHedenmalmDeBrangesSeam`, `KummerObstruction`, `RHLadderTheory`
- **Lean module:** `formal/GaloisForLFunctions/RHTower/XiHedenmalmKummerCollision.lean`

## Statement

Write

\[
E_\Xi(z)=\Xi(z)+i\Xi'(z).
\]

Let `d>1`.  If both `XiC` and `E_Xi` admit analytic `d`-th roots on the centered upper
half-plane, then RH holds.  At any upper-half-plane Xi zero of order `m`, the derivative term
dominates in `E_Xi`, so

\[
\operatorname{ord}(E_\Xi)=m-1.
\]

The two roots would therefore force `d | m` and `d | (m-1)`, hence `d | 1`, a contradiction.
Failure of RH supplies such an upper-half-plane Xi zero by functional-equation reflection of a
right-half zeta zero.

```text
common analytic d-th Kummer cover of XiC and E_Xi on Im z > 0, d > 1
  -> d divides ord(XiC) and ord(E_Xi)
  -> exact Hedenmalm order shift ord(E_Xi)=ord(XiC)-1
  -> no upper-half-plane XiC zero
  -> RH.
```

For `d=2`, the XiC root is supplied by `RHLadder 1` after functional-equation transport.  Hence

```text
RHLadder 1
  + analytic square root of E_Xi on Im z > 0
  -> RH.
```

## Attack and non-circularity

This is weaker than assuming that `E_Xi` is zero-free or Hermite--Biehler: the Kummer premise
allows arbitrary `E_Xi` zeros whose multiplicities are divisible by `d`.  It also does not ask for
the Hedenmalm Bezoutian sign.

Neither root premise alone is zero-freeness.  A `d`-th power may retain zeros.  Conversely, for
the elementary entire function `F(z)=1-exp(i z)`, one has `F+iF'=1`; thus the Hedenmalm combination
has a root of every degree while `F` still has zeros.  The obstruction is genuinely simultaneous.

The route dies if the `E_Xi` root is constructed only after deleting Xi zeros, if its branch is
selected from the Xi divisor, or if the claimed root is merely a pointwise choice without one
analytic branch on the complete upper half-plane.

## Open core

`[OPEN CORE]` Construct an analytic square root of the source-defined Hedenmalm function `E_Xi` on
the centered upper half-plane, allowing even-multiplicity zeros, and construct `RHLadder 1` from a
source constraint.  This is strictly below full Hermite--Biehler zero-freeness and does not require
positivity of the Hedenmalm Bezoutian.

## Gates

- [x] source-defined Hedenmalm function `E_Xi` exists in Lean
- [x] analytic roots force order divisibility
- [x] formalize the exact order drop in `E_Xi`
- [x] formalize the common-root RH collision
- [ ] construct the two source roots
- [ ] RH

## Formal verification

Lean proves `analyticOrderAt_xiHedenmalmDeBrangesE_eq_pred_of_XiC_zero`, the general common-degree
capstone `riemannHypothesis_of_xiHedenmalmCommonKummerRootUpperHalf`, and the square specialization
`riemannHypothesis_of_rhLadder_one_of_xiHedenmalmESquareRootUpperHalf`.  The named module build
passes in the repository toolchain.  These declarations use only `propext`, `Classical.choice`,
and `Quot.sound`.

## Next source move

The first source move is now the shorter ladder--simplicity collision: the existing Hedenmalm
value or density interface supplies `XiZerosSimple`, and `RHLadder 1 + XiZerosSimple` already
forces RH.  It does not require a square root of `E_Xi`.

`[CONJECTURE]` A source-selected analytic skew/Pfaffian family remains a secondary way to obtain a
global square root of `E_Xi`, but it passes the non-circularity gate only if its matrix or operator
entries are independently fixed by theta or prime--Gamma source data before reading `E_Xi` or its
divisor.  An existential finite skew factorization is exactly the square-root premise in disguise:
the determinant of `[[0,g],[-g,0]]` is `g^2`.  Therefore a free Pfaffian factorization is not an
advance on the Kummer hypothesis.
