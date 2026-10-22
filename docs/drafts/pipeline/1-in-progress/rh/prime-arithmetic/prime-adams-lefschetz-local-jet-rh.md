# Prime-Adams Lefschetz defect on the local Xi jet

- **ID:** `prime-adams-lefschetz-local-jet-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`, `[RH ROUTE]`, `[LARGE OUTLANDISH DETOUR]`
- **Lean source law:** `LocalDivisorJetAdamsDilation.lean`
- **Inputs:** `AdamsOperations.lean`, `PrimeWordSupportSelector.lean`

## Corrected claim

For the actual Euler/Adams operation, the order-`m` local jet

```text
A_m = C[X]/(X^m)
```

has diagonal action `X^j |-> n^j X^j`, not `X |-> X^n`.  Therefore

```text
Tr(Psi^n | A_m) - Tr(id | A_m)
  = sum_(0 <= j < m) (n^j - 1).                       (1)
```

For `n>=2`, every term is nonnegative and the `j=1` term is positive whenever `m>1`.  Thus `(1)`
vanishes exactly when `m=1`.  The previous formula `m-1` belonged to the false ramification action
and is retired.

It would suffice to construct a completed prime--Gamma complex whose local cohomology is `A_m`,
whose Adams action is the genuine dilation, and for which a source-derived comparison makes its
Lefschetz supertrace equal to that of the identity.  Equality plus positivity forces simplicity.

## Two-ended chain

```text
completed marked Euler--Gamma complex
  -> Adams action before scalar supertrace
       [OPEN CORE A: completed Adams complex]
  -> local cohomology A_m and action X^j |-> n^j X^j
       [OPEN CORE B: local comparison]
       [PROVED LEAN: actual prime derivative-jet coefficient law]
  -> source comparison Lef(Psi^n)=Lef(id)
       [OPEN CORE C: relative homotopy or trace identity]
  -> sum_(j<m)(n^j-1)=0
  -> m=1
  + independently source RHLadder 1
  -> RH.
```

Unlike the retired ramification route, the Adams operation is invertible for every `m`; the
Lefschetz defect uses its nontrivial weights, not failure of invertibility.

## Determinant companion

The same diagonal action has

```text
det(Psi^n | A_m) = n^(m(m-1)/2).
```

This is formalized by `adamsDilationDeterminant_eq`.  Raw determinant equality with the identity
would also force `m=1`.  However an FE-centered normalization makes the total determinant one for
all `m`, so a completed determinant-line argument must retain the uncentered relative anomaly.  A
bare normalized determinant trivialization cannot close the route.

## Source-provider attack

The naive homotopy `Psi^n ~ id` is not supplied by the Euler product: Adams sends the prime germ to
its `n`-th power and is not a symmetry of zeta.  A valid provider must therefore be relative.  The
remaining plausible forms are:

1. an Euler--Gamma product-formula comparison whose boundary term is exactly the uncentered trace
   defect and is independently zero;
2. a paired Adams/dual-Adams complex in which all boundary contributions cancel except the positive
   local excess `(1)`;
3. a source filtration spectral sequence whose total Adams trace is fixed while its local graded
   trace is the geometric sum.

Each proposal must prove the comparison on the same completed complex.  Appending a Gamma number to
cancel `(1)` is target-fed bookkeeping.

## Firewalls

1. A trace identity written after inserting Xi multiplicities is only consumer algebra.
2. Satake power sums do not automatically act on the divisor cohomology.
3. Scalar marked-prime support loses the connected local operation; retain the complex before
   scalarization.
4. FE centering can erase the determinant detector.
5. A signed uncontrolled boundary destroys positivity.
6. Global simplicity may not be assumed in the local comparison.

## Status

- `[PROVED NO-GO]` the old ramification trace `m-1` is not the Euler/Adams action;
- `[PROVED LEAN]` the source-correct action has dilation weights `n^j`;
- `[PROVED PAPER]` the corrected trace excess is nonnegative and vanishes exactly at `m=1`;
- `[PROVED LEAN]` the determinant is `n^(m(m-1)/2)`;
- `[OPEN CORE]` completed Adams action, local comparison, and source relative-trace equality;
- `[OPEN]` independent first ladder rung.
