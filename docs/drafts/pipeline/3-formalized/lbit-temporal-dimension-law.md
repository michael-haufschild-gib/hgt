# L-bit localization–temporal-dimension law

- **ID:** `lbit-temporal-dimension-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Date:** 2026-07-30
- **Formal source:** `formal/GaloisForLFunctions/HTGeometry/LBitTemporalDimensionLaw.lean`

## Exact law

For a finite l-bit Hamiltonian
\[
  E_J(x)=\sum_{S\subseteq I}J_S\chi_S(x),
  \qquad x\in\{0,1\}^I,
\]
let \(\tau(J)\) be the rational dimension of its anchored energy gaps. Then
Walsh inversion gives
\[
  \boxed{\tau(J)=
  \dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}
  \{J_S:S\ne\varnothing\}.}
\]

This is an equality for every coefficient family, not a generic statement.

## Consequences

If \(J_S=0\) for \(|S|>k\), then
\[
  \tau(J)\le
  \sum_{j=0}^{k}\binom{|I|}{j}-1.
\]
In every positive coefficient-\(L^1\) neighborhood of any such Hamiltonian
there is a coefficient family \(K\) with
\[
  \tau(K)=2^{|I|}-1,
\]
and
\[
  \sup_x|E_K(x)-E_J(x)|<\varepsilon.
\]
Both Hamiltonians are diagonal in the same Boolean configuration basis.
Every l-bit charge commutes exactly with every such Hamiltonian, and all
off-diagonal configuration amplitudes vanish.

Thus exact localization and exact temporal dimension are independent:
transport can remain frozen while completed recurrence dimension changes
from a finite-order coefficient ceiling to the full exponential value.

For blocks \(A,B\), the number of supports meeting both blocks is exactly
\[
  (2^{|A|}-1)(2^{|B|}-1),
\]
identifying the mixed l-bit sector with the multiplicative rectangle sector
of the finite-pair recurrence law.

One fixed coefficient assignment on all finite supports of \(\mathbb N\)
has full rank on every finite restriction:
\[
  \tau(I)=2^{|I|}-1
\]
for every finite site type \(I\). This is a simultaneous finite-window law,
not a construction of infinite-volume \(C^*\)-dynamics.

## Physical boundary

This is an exact l-bit fixed-point theorem. It is not yet a theorem for an
ordinary random finite-range Anderson Hamiltonian or a stability theorem for
microscopic many-body localization. Full exponential rank uses the complete
all-order l-bit hierarchy. Strictly bounded interaction order has only the
coefficient-count ceiling above.

## Verification

Target source compilation with cached output passes:

```text
lake env lean GaloisForLFunctions/HTGeometry/LBitTemporalDimensionLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/LBitTemporalDimensionLaw.olean
```

Axiom audit of the load-bearing declarations reports only:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

No `sorry`, `admit`, custom `axiom`, `opaque` or `unsafe` declaration is
used. Final `lake build` module audit is reserved for publication audit.
