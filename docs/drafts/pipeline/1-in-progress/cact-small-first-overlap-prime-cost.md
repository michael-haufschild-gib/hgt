# Small actual prime cost beyond touching

## Target

For every fixed nonzero smooth profile supported in the unit interval, prove
one constant `C_phi>0` such that, for `1<=c<=2`, `N>=2`, and all signed vectors,

```
abs(NR(phi_(c/N),N,x)) / mass(phi_(c/N))
  <= C_phi * ((c-1)+1/N) * (poleDefect(N,x)+sum x_n^2).
```

This is an estimate on the literal prime source, including every prime power.
It does not assume cancellation, a prime-pair conjecture, or a spectral model.

## Mechanism

Distinct positive integers with one at most `N` have log gap greater than
`1/(N+1)`. Height control of the actual autocorrelation leaves amplitude
`B^2 * max(0,w-1/(N+1))` at every non-ratio integer lag. Retain that amplitude
through the existing weighted Schur and divisor-row argument. At `w=c/N`,
normalization leaves at most `(B^2/M)*((c-1)+1/N)`. The remaining top-row weight
is paid by the actual prime defect through `sum_top_le_poleDefect_param`.

## Source and status

Corpus search179 and the actual statements in SSHA/TheRowsAtBoundedOverlap,
ALG/TheArchimedeanCrossEnergyIsOneSided, and the programme's height-overlap
theorem supply the inputs. The broad search returned no matching small
overlap/defect estimate; this is not an exhaustive novelty claim.

`IntegerSeparationShrinksTheNonRatioPrimeRows.lean` is drafted but unchecked.
The normalized prime-defect estimate and its uniform smallness corollary are
being formalized. No theorem is yet claimed.

## Remaining complete-form obligation

A small prime correction alone does not prove positivity beyond touching.
Actual overlapping Gram entries and the cancelled archimedean integral still
need a relative comparison with the endpoint form. Separating the singular
cross integral before its diagonal cancellation is invalid in this regime.
