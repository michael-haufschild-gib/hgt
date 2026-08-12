# Route E Ramaré integer-incidence recombination

- **ID:** `ROUTE-E-RAMARE-INTEGER-INCIDENCE-001`
- **Stage:** 3-formalized
- **Type:** `[EXACT ARITHMETIC RECOMBINATION]` / `[FINITE-VOLUME SIGNED IDENTITY]`
- **Parent:** `route-e-ramare-recombination-ternary-antiscale-law.md`
- **RH used:** no
- **Computation used:** no
- **Literature used:** no; internal-corpus derivation

## Result

Let `P` be a finite prime packet and let `P(n)` denote the primes of `P` dividing `n`. Lean now
proves that each Ramaré block is exactly the ordinary-integer incidence block

```text
mu(p) p^(iw) G_p(w)
  = sum_(1 <= n <= M, p | n) mu(n) n^(iw) / |P(n)|.
```

Reindexing all ordered `p != q` pairs gives the exact multiplicity

```text
|P(n)| |P(m)| - |P(n) inter P(m)|.
```

After cancelling the two normalization factors, the full finite-volume prime off-diagonal is

```text
ramarePrimeOffDiagonal(P,M,W)
  = sum_(n,m active)
      mu(n) mu(m)
      * (1 - |P(n) inter P(m)|/(|P(n)| |P(m)|))
      * ramareMellinPairKernel(W,n,m).
```

The complement coefficient is also proved equal to the normalized number of ordered distinct
prime incidences and lies in `[0,1]`. Thus the formula retains exact recurrence weights, every
alternating finite-volume Möbius sign, shared-prime collisions, and the complete Mellin kernel.

## Lean certificate

Module:

```text
GaloisForLFunctions.RHTower.Sieve.RouteERamareIntegerIncidence
```

Principal declarations:

```text
routeEDistinctIncidenceCount_eq_card_mul_sub_inter
routeEDistinctIncidenceRatio_eq_one_sub_inter
routeE_offDiagonal_incidenceBlock_sum_reindex
ramarePrimeBlock_eq_integerIncidenceBlock
ramarePrimeBlock_eq_activeIndicatorBlock
ramareIncidenceComplement_eq_normalizedDistinctIncidence
ramareIncidenceComplement_nonneg
ramareIncidenceComplement_le_one
ramarePrimeOffDiagonalIntegrand_eq_integerIncidence
ramarePrimeOffDiagonal_eq_integerIncidence
```

Module is imported by `GaloisForLFunctions.RHTower`. Direct `lake env lean` check and targeted
module build pass. Kernel axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, `admit`, new `axiom`, `opaque`, `unsafe`, route premise, or numerical computation
occurs.

## Frontier consequence

The apparent prime-pair residue is now formally identified as an ordinary-integer signed
covariance. Prime labels provide no extra separation: coprime pairs receive coefficient exactly
one, while shared-prime incidence removes only its normalized diagonal fraction. The last finite
recombination seam is therefore closed.

Still open is the genuinely analytic producer: tensor this exact integer-pair kernel with the
sharp-cutoff rough cofactor histories and prove the centered all-reporter strict-half rate in the
moving Gallagher range, compatibly with the physical recurrence seam. Route E and RH remain open.

## Log

- 2026-08-12 — exact block recombination, distinct-incidence complement, coefficient bounds, and
  finite-volume Möbius-sign/Mellin-kernel identity proved in Lean; umbrella import and targeted
  audit passed.
