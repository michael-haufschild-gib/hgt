# Hypertranscendental horizon function-field core

- **ID:** `hypertranscendental-horizon-function-field-core`
- **Stage:** 3-formalized
- **Type:** THEOREM (LEAN) / GENERIC-POINT TRANSFER CERTIFICATE
- **Scientific status:** `[FORMALIZED CORE] [NOVELTY PROVISIONAL] [SIGNIFICANT PARENT]`
- **Paper parent:** `hypertranscendental-maximal-finite-horizon-galois-law`

## Formalized declarations

In `HypertranscendentalHorizonFunctionField.lean`:

- `finiteDifferentialJet`
- `finiteDifferentialJet_algebraicIndependent_of_hypertranscendentalOver`
- `finiteDifferentialJet_aeval_injective_of_hypertranscendentalOver`
- `hypertranscendentalFiniteJetParametrization`
- `hypertranscendentalFiniteJetParametrization_X`

## Certified content

For a hypertranscendental element `x` over a field `F`, Lean proves that every finite derivative
packet

```text
(x,Dx,...,D^(L-1)x)                                      (1)
```

is algebraically independent over `F`.  It then proves injectivity of the universal multivariate
polynomial evaluation map and constructs the labelled algebra equivalence

```text
Frac(F[X_0,...,X_(L-1)])
  ~= F(x,Dx,...,D^(L-1)x),                                (2)
```

with `X_i` sent exactly to `D^i x`.

Equation `(2)` is the formal reason no specialization collapse occurs when universal rational
horizon coordinates are evaluated in an actual HT source.  Scaling by the nonzero constants `i!`
to the divided-jet coordinates used in the paper is elementary in characteristic zero and is not
wrapped in a second Lean coordinate API.

## Verification

The module passes a targeted direct Lean check.  A scratch `#print axioms` audit reports only the
standard logical axioms inherited from the algebraic-independence and fraction-field libraries.  No
full build is run.

## Formal boundary

This module certifies generic-point transfer, not the complete construction of normal closures and
permutation-group monodromy in Lean.  The exact binomial degree has a separate formal core; the
all-rank `S_D` theorem and its function-field transport remain paper-proved.  No stronger formal
claim is made here.
