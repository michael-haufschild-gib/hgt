# Route E Ramaré incidence-complement conditional negativity

- **ID:** `ROUTE-E-RAMARE-INCIDENCE-CONDITIONAL-NEGATIVE-001`
- **Stage:** 3-formalized
- **Type:** `[EXACT GRAM DECOMPOSITION]` / `[CONDITIONAL NEGATIVITY]` / `[FRONTIER REDUCTION]`
- **Parent:** `route-e-ramare-recombination-ternary-antiscale-law.md`
- **RH used:** no
- **Computation used:** no
- **Literature used:** no; internal-corpus derivation

## Result

For finite nonempty incidence sets `F_n subset P`, define

```text
C(n,m) = 1 - |F_n inter F_m|/(|F_n| |F_m|),
L_p(c) = sum_(n : p in F_n) c_n/|F_n|.
```

Lean proves the exact complex quadratic identity

```text
sum_(n,m) C(n,m) Re(c_n conj(c_m))
  = normSq(sum_n c_n) - sum_(p in P) normSq(L_p(c)).
```

Hence on `sum_n c_n=0`,

```text
sum_(n,m) C(n,m) Re(c_n conj(c_m))
  = -sum_(p in P) normSq(L_p(c)) <= 0.
```

The centered form vanishes exactly when every normalized prime load vanishes. Specializing
`F_n=primeFactorsIn P n` gives the actual Ramaré active-integer law. Specializing further to the
finite Möbius phases rewrites the prime off-diagonal integrand as total active scalar norm square
minus normalized prime-load energy.

## New scientific content

The incidence-complement kernel is conditionally negative definite, not an arbitrary positive
covariance kernel. This was not present elsewhere in the corpus research index. It changes the
Route E burden: once the sharp physical reporter is centered source-faithfully, its incidence
component requires no positive upper estimate. Remaining positive burden is the scalar mean mode,
plus sharp-cutoff identification and signed moving recurrence seam. Equality classification also
identifies the exact centered escape space: simultaneous cancellation of all normalized prime
loads.

## Lean certificate

Module:

```text
GaloisForLFunctions.RHTower.Sieve.RouteERamareIncidenceConditionalNegative
```

Principal declarations:

```text
routeE_sum_normalizedIncidenceBlock
routeE_offDiagonalBlock_eq_total_normSq_sub_diagonal
routeE_incidenceComplement_decomposition
routeE_centeredIncidenceComplement_eq_neg_energy
routeE_centeredIncidenceComplement_nonpos
routeE_centeredIncidenceComplement_eq_zero_iff
ramareIncidenceComplement_decomposition
ramareCenteredIncidenceComplement_eq_neg_energy
ramareCenteredIncidenceComplement_nonpos
ramarePrimeOffDiagonalIntegrand_eq_total_normSq_sub_primeLoadEnergy
```

Module is imported by `GaloisForLFunctions.RHTower`. Direct `lake env lean` check and targeted
module build pass. Kernel axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, `admit`, new `axiom`, `opaque`, `unsafe`, route premise, or numerical computation
occurs.

## Honest frontier

This theorem does not show the actual sharp cofactor reporter is centered under the physical
finite-volume weights, does not estimate its scalar mean, and does not cross the zero/one-large-
prime or recurrence seams. Route E and RH remain open. Exact next producer is a source-faithful
sharp-cutoff decomposition whose centered coefficient is the `c` above and whose scalar mode has
the affine strict-half moving-range bound.

## Log

- 2026-08-12 — exact Gram decomposition, conditional negativity, radical classification, and
  arithmetic/Möbius specializations proved in Lean; umbrella import and targeted audit passed.
