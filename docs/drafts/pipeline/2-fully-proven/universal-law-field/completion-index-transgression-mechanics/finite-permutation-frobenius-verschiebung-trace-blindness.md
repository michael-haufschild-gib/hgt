# Finite permutation Frobenius--Verschiebung trace blindness

- **ID:** `ULF-FVBLIND-1`
- **Stage:** 2-fully-proven
- **Type:** unconditional no-go with positive completion survivor
- **Lean:** `GaloisForLFunctions.HTGeometry.FinitePermutationFVTraceBlindness`; verified

## 1. Higher-law interpretation

If horizontal grade is a completion index, it must be invisible at every raw finite integral
formation stage.  Finite cyclotomic Witt Frobenius is a permutation of the stage basis, while
`F V=q` forces `V=q F^{-1}`.  Their squared parity supertrace therefore measures only periodic
orbit count and degree.  It cannot carry analytic rapidity.  Any grade-dependent supertrace must
be an anomaly of infinite/Tate completion: a failure of trace to commute with formation limit.

## 2. Exact theorem

Let `X` be finite, `F` a permutation of `X`, `P(F)` its integral permutation matrix, and `q` an
integer.  Put

`V=q P(F^{-1})`

and define the squared parity supertrace

`STr_2(F,V)=Tr(P(F^2))-Tr(q^2 P(F^{-2}))`.

If `k_2(F)` is the number of points fixed by `F^2`, then

`STr_2(F,V)=(1-q^2) k_2(F)`.

In particular it is an integer determined only by the finite orbit decomposition and `q`; it has
no continuous character or rapidity parameter.

## 3. Proof

Trace of a permutation matrix equals number of fixed points.  A point is fixed by `F^2` exactly
when it is fixed by `F^{-2}`, so both permutation traces equal `k_2(F)`.  Trace is linear under
integer scalar multiplication.  Hence

`Tr(P(F^2))-Tr(q^2 P(F^{-2})) = k_2(F)-q^2 k_2(F)`

`= (1-q^2) k_2(F)`.  QED.

## 4. Corpus specialization

The finite cyclotomic rational-Witt module already proves that arithmetic Frobenius permutes its
monomial basis.  The abstract Frobenius--Verschiebung law already proves `V=q F^{-1}` whenever
Frobenius is invertible and `F V=q`.  Thus the theorem applies to every raw finite permutation
stage of that model.

## 5. Exact RH consequence

This closes one source-model class, not RH.  Finite-stage Lefschetz traces cannot equal the analytic
ledger

`q^(1+a)-q^(1-a)`

as a grade-varying law: the former has no `a` input.  Therefore the bridge needed by all-scale
integral supertrace rigidity cannot be termwise equality with finite-stage trace.

The surviving RH architecture is narrower:

1. finite integral formation complexes carry permutation Frobenius and integral local traces;
2. an unbounded inverse/direct system is formed before analytic realization;
3. completion creates a derived boundary class (`lim^1`, Roos, Tate, or an equivalent exact
   completion defect);
4. a source-native trace theorem identifies the analytic hyperbolic supertrace with the boundary
   index, not with any raw finite trace;
5. the boundary index remains integral at every natural degree `q`;
6. all-scale integral supertrace rigidity then forces `a=0`, hence the corpus grade equivalence
   gives RH.

The next theorem must therefore be a trace-versus-completion transgression identity.  Repackaging a
finite matrix, finite orbit count, normalized trace, or fitted character is ruled out.

## 6. Positive survivor

Finite stages do useful work: they supply the integral lattice, exact `F V=q` relation, and orbit
complexes.  Analytic rapidity can only reside in the derived defect of assembling all stages.  This
turns “completion-born boundary” from a metaphor into the only surviving location of the grade.

## Log

- 2026-09-02 -- theorem extracted from finite Witt permutation action plus abstract
  Frobenius--Verschiebung law; paper proof dependency-closed.
