# Finite quantum expectation escape–return dichotomy law

- **Status:** Lean-formalized
- **Formal module:** `formal/GaloisForLFunctions/RHTower/FiniteQuantumExpectationEscapeReturnDichotomyLaw.lean`
- **Headline theorem:** `finiteQuantumExpectation_neverExits_or_postExit_return`

## Exact unconditional law

Fix any finite family of scalar quantum expectation histories, any
nonnegative history weights, any chosen synchronization graph \(G\), any
resolution \(Q\), and any positive guard time. Define

\[
R(G,Q)=
2M^{(1)}_{\rm omit}(G)+
2\frac{2\pi}{Q+1}M^{(1)}_{\rm select}(G).
\]

Exactly one of the following exhaustive alternatives is guaranteed:

1. at every nonnegative time, total weighted expectation deviation is at
   most \(R(G,Q)\); or
2. there is a certified time \(t_{\rm exit}\) at which deviation is strictly
   greater than \(R(G,Q)\), followed by a later sampled time
   \(t_{\rm ret}>t_{\rm exit}\) with deviation at most \(R(G,Q)\), and

\[
t_{\rm ret}\le
(t_{\rm exit}+t_{\rm guard})
\,(Q+1)^{d-\#\pi_0(G)}.
\]

## What this closes

The theorem cannot label near-stationarity as recurrence. If an observed
history never leaves the guaranteed radius, that is reported as the first
branch. Every event called a return in the second branch is strictly after an
exit in the identical scalar-history metric.

## Truth boundary

- The return is an existence deadline, hence bounds the first post-exit
  return from above but does not identify its exact time.
- The graph exponent is a universal capacity upper bound. Arithmetic
  relations can make one history recur earlier.
- The scalar coefficient masses are cancellation-resistant upper bounds;
  they are not the exact grouped Bohr-frequency support.
- This theorem is finite-dimensional and closed/unitary. It does not yet
  prove Anderson eigenfunction localization or a thermodynamic limit.

## Verification

Direct foreground compilation passed with

```text
lake env lean GaloisForLFunctions/RHTower/FiniteQuantumExpectationEscapeReturnDichotomyLaw.lean
```
