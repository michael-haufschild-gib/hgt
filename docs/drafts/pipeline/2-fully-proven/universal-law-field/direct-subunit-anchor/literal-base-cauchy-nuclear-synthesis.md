# Literal base-Cauchy nuclear synthesis

- **ID:** ULF-LBCNS-001
- **Stage:** 2-fully-proven
- **Type:** THEOREM
- **Parent:** `1-in-progress/universal-law-field/direct-subunit-anchor/integral-nuclear-prime-mixed-homotopy-defect.md`

## Statement

Put `I = Nat.Primes x Nat` with counting measure and

```text
f_alpha = routePPrimitiveBurnolWindowFeatureLp(alpha, 0) in L2(0,infinity).
```

The field `alpha |-> f_alpha` is Bochner `L2`.  Its synthesis

```text
A_base : L2(I,count) -> L2(0,infinity),
A_base(c) = sum_alpha c_alpha f_alpha
```

is Hilbert--Schmidt and satisfies

```text
||f_alpha||^2 = routePPrimitiveBaseCauchyCubicWeight(alpha),
||A_base||_HS^2 = B_base,
B_base = routePPrimitiveBaseCauchyCubicTraceBudget < 1.       (LBCNS.1)
```

Consequently the covariance

```text
S_base = A_base A_base* : L2(0,infinity) -> L2(0,infinity)
```

is Schatten-1 and

```text
Re Tr(S_base) = B_base < 1.                                  (LBCNS.2)
```

Every entry of the source Gram is the full P-G186 base-Cauchy entry, including unequal primes,
depths, and clocks.  Thus `S_base` is formed from one literal prime-mixed source, not a direct sum
of local prime budgets.

## Proof

P-G186 identifies every finite Gram matrix of the actual Burnol vectors with the primitive
base-Cauchy matrix.  Taking a singleton packet and its diagonal gives

```text
||f_alpha||^2 = routePPrimitiveBaseCauchyCubicWeight(alpha).
```

The right side is summable, with sum `B_base`; the strengthened source-horizontal budget theorem
proves `B_base < 1`.  Hence `alpha |-> f_alpha` belongs to vector-valued `L2(I,count)`.  Bochner
synthesis by this field is Hilbert--Schmidt, and Parseval gives its squared Hilbert--Schmidt norm
as the field's `L2` norm squared, namely `B_base`.  The product of synthesis with its adjoint is
Schatten-1.  The positive covariance trace law gives its trace as the same squared norm.

P-G186's off-diagonal equality, not diagonal summability, supplies prime mixing.  No Xi divisor,
zero coordinate, adjustable scalar, or post-divisor capacity inequality occurs.

## Meaning for ULF-INHD-001

The earlier `1/sqrt(2)` normalization is obsolete.  New corpus theorem
`routePPrimitiveBaseCauchyCubicTraceBudget_lt_one` proves the actual P-G186/P-G194 carrier already
has sub-unit mass.  Source half of the proposed homotopy defect is therefore constructed without
damping:

```text
A_s = L_s U_c A_base tau_s,
||A_s||_HS^2 <= B_base < 1.
```

Only the source-canonical signed landing remains: it must identify the arithmetic--theta horizon
projection difference with `A_s* Gamma_hom A_s`.  This theorem does not assert that identification
and therefore does not prove RH.

## Lean target

```text
RHTower.RoutePPrimitiveBurnolBaseNuclearSynthesis
```

No RH premise or new axiom is permitted.

## Lean status

Completed in `RHTower.RoutePPrimitiveBurnolBaseNuclearSynthesis`.

Target build passes.  Axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.
