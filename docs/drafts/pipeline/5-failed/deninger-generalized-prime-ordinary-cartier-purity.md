# Generalized prime as an ordinary analytic Cartier divisor

- **ID:** `deninger-generalized-prime-ordinary-cartier-purity`
- **Stage:** 5-failed
- **Type:** RETIRED CONJECTURE / TYPE ERROR
- **Label:** `DAC_GENERALIZED_PRIME_ORDINARY_CARTIER_PURITY`
- **Parent:** `deninger-arithmetic-projection-leray-rost-schmid-resolution`

## Retired conjecture

For every rational prime \(p\), Deninger's generalized function
\([p]\) is an ordinary analytic section on the rational-Witt
suspension, cuts out the \(p\)-packet as an effective Cartier divisor,
and its analytic \(d\log\) class has residue one.

## Failure

Deninger's Proposition 11.7 proves only the set-theoretic
generalized-divisor identity
\[
 \operatorname{div}[p]
 =
 \operatorname{pr}^{-1}V(p).
\]
His generalized functions in §11 are monoid-valued classes, not
sections of the analytic function sheaf.  In §12 Deninger constructs
twisted sheaf sections for invertible regular functions.  He explicitly
says that treating all regular functions would require lifting the
monoid formalism, and does not perform that construction.

Consequently, an ordinary analytic local equation, non-zero-divisor
property, conormal line, and Poincaré residue do not follow from the
zero-set identity.  Using them would assume the missing geometry.

## Positive survivor

`DAC_ARITHMETIC_PRO_LOG_KUMMER_DIVISOR_RESOLUTION` supplies the exact
replacement.

For every finite set \(P\) of primes, the divisor
\[
 D_P=\sum_{p\in P}V(p)\subset\operatorname{Spec}\mathbb Z
\]
is a disjoint strict-normal-crossings Cartier divisor.  Its divisorial
log structure has characteristic sheaf
\[
 \bigoplus_{p\in P}i_{p,*}\mathbb N
\]
and exact groupified valuation sequence.  Pulling this log sequence to
Deninger's space gives the prime normal orientations.  Proposition
11.7 identifies their supports with the generalized divisors
\(\operatorname{div}[p]\).  Rational powers scale valuations, and the
Tate twist cancels that scaling.

This survivor preserves exactly what arithmetic cohomology needs:
Kummer normal lines, disjoint prime residues, and power compatibility,
without asserting that \([p]\) is an ordinary analytic function.

## No-go closure

The strongest valid statement is the generalized-log Cartier
resolution above.  The remaining open gate is purity of Deninger's
Tate--Milnor analytic coefficient with respect to that pulled-back log
divisor, not construction of an ordinary analytic \([p]\).

**Verdict:** `FAILED AS ORDINARY ANALYTIC CARTIER CLAIM; POSITIVE
GENERALIZED-LOG KUMMER RESOLUTION PROVED ON PAPER`.

## Log

- 2026-07-27 — retired after exact audit of Deninger §§11--12;
  extracted and proved the pro-log Kummer survivor.
