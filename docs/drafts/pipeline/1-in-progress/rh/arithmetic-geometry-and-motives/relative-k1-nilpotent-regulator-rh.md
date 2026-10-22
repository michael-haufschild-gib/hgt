# Relative K1 nilpotent regulator to RH

- **ID:** `relative-k1-nilpotent-regulator-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`, `[RH ROUTE]`, `[LARGE OUTLANDISH DETOUR]`
- **Lean bridge:** `formal/GaloisForLFunctions/RHTower/LocalDivisorJetRelativeKOne.lean`
- **Inputs:** `FittingSeamBoundary.lean`, `PinnedAffinePrimeJetRigidity.lean`, completed determinant-line cards

## Local class

At a zero of multiplicity `m`, put

```text
A_m = C[X]/(X^m),       u_m = 1 + X.
```

Since `X` is nilpotent, `u_m` is a unit.  As `A_m` is commutative, this unit is the elementary
relative-`K1` class in the kernel of reduction `A_m^x -> C^x`.  Lean proves

```text
0 < m  ->  (u_m = 1 <-> m = 1).
```

Thus the relative infinitesimal unit is a multiplicity detector that does not require a metric,
zero separation, or an exterior census.

## Determinant-line no-go

Multiplication by `u_m` on the basis `1,X,...,X^(m-1)` is unipotent triangular.  Its regular
determinant equals one for every `m`.  Therefore every construction that passes immediately from
the local automorphism to its scalar determinant line kills the relative class.  A determinant
trivialization cannot imply simplicity; it has already forgotten the obstruction.

This is the positive residue of the no-go: retain the full relative unit, its logarithm

```text
log(1+X) = X - X^2/2 + ... + (-1)^m X^(m-1)/(m-1),
```

or a regulator injective on the nilpotent relative-`K1` group.  The finite logarithm identifies the
local relative group with the additive nilpotent ideal in characteristic zero and exposes all
`m-1` infinitesimal layers.  For the canonical class, this injectivity is already formalized:
`localDivisorJetLogUnit_eq_zero_iff` proves that its logarithmic regulator vanishes exactly at
`m=1`.

## Two-ended chain

```text
completed Euler--Gamma determinant/Koszul object before scalar determinant
  -> localize at the completed-SEM divisor algebra A_m
       [OPEN CORE A: source-to-local K1 comparison]
  -> canonical relative unit u_m=1+X
       [PROVED LEAN: unit and nontriviality]
  -> source logarithmic regulator Reg(u_m)
       [OPEN CORE B: regulator on the actual completed object]
  -> product formula / completed boundary gives Reg(u_m)=0
       [OPEN CORE C: source vanishing]
  -> regulator injectivity on the nilpotent relative group
       [PROVED LEAN FOR THE CANONICAL CLASS: truncated logarithm has coefficient one]
  -> u_m=1
  -> m=1
       [PROVED LEAN: localDivisorJetInfinitesimalUnit_eq_one_iff]
  + independently source RHLadder 1
  -> RH
       [PROVED LEAN CONDITIONAL CAPSTONE:
        riemannHypothesis_of_rhLadder_one_of_rightLogUnitVanishing].
```

## Candidate regulators

1. a Goodwillie/Chern-character comparison from nilpotent relative `K1` to negative cyclic or
   truncated de Rham data, retaining the Hodge filtration rather than periodicizing it;
2. a prime--Gamma logarithmic regulator obtained from the completed Euler coefficient stream before
   exponentiation to a determinant;
3. a Whitehead-torsion class of the completed local Koszul complex whose scalar determinant is one
   but whose filtered torsion records `log(1+X)`;
4. an Adams-weight decomposition of the relative unit, with a source theorem killing every
   positive weight.

## Attacks and kill conditions

1. Homotopy `K`-theory and periodic cyclic homology are nil-invariant and therefore deliberately
   blind to `m`; using either without its filtration retires the route.
2. The regular determinant of `u_m` is one for all `m`; determinant-line triviality is not Open
   Core C plus D.
3. Defining the regulator after reading `m` is target-fed unless it is the localization of one
   global source map.
4. A regulator with a nilpotent kernel cannot prove reducedness.
5. The completed product formula must annihilate the same relative class, not an unrelated scalar
   Euler anomaly.
6. Finite-prime jet surjectivity does not supply regulator injectivity; it realizes every local
   class and is therefore neutral.

## Status

- `[PROVED LEAN]` `1+X` is a unit in every local divisor jet;
- `[PROVED LEAN]` for positive depth it is trivial exactly at `m=1`;
- `[PROVED LEAN]` the finite logarithmic regulator of the canonical class vanishes exactly at
  `m=1`;
- `[PROVED LEAN]` local regulator vanishing on right-half fibers plus `RHLadder 1` implies RH;
- `[PROVED NO-GO]` scalar regular determinant is unipotent and multiplicity-blind;
- `[POSITIVE TARGET]` filtered relative-K1/logarithmic regulator before determinant collapse;
- `[OPEN CORE]` global source localization and source vanishing of the now-injective local
  logarithmic regulator;
- `[OPEN]` independent first ladder rung.
