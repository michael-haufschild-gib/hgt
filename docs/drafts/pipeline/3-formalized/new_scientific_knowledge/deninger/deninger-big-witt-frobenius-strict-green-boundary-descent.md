# Deninger Big-Witt Frobenius strict Green-boundary descent

- **Status:** Formalized in Lean 4
- **Route:** L
- **Lean:** `RHTower.DeningerBigWittFrobeniusStrictGreenBoundaryDescent`
- **Primary incidence theorem:**
  `deningerBigWittFrobeniusPrimeSeamFiniteIncidenceSource_coordinate`
- **Primary physical theorem:**
  `deningerBigWittFrobeniusPrimeSeamFiniteBVGreenChain_groundReadout`

## Result

Let `a` be a complex prime potential and let `S` be finite. For every ordered
pair `(p,q)`, the first ghost of the Frobenius-transgressed polarized Big-Witt
source is

```text
c_pq(a) = -2 |a_p-a_q|^2/(pq).
```

This module retains `c_pq` before scalar aggregation in two concrete source
complexes.

First, for `p != q`, it constructs the actual ordered Calderón--Witt Milnor
incidence

```text
c_pq(a) * w_pq.
```

The normalized arithmetic incidence matrix is the identity, so every packet
coordinate of the finite source is exactly `c_pq`, with zero diagonal. The
actual Gamma/co-Poisson moving boundary preserves this coefficient and
multiplies it by the genuine modular exterior; the actual reflection defect
preserves it and multiplies it by the genuine reflection-odd exterior.

Second, at ordinary-integer degree `pq`, it constructs the literal Hochschild
one-chain

```text
-2 |a_p-a_q|^2 * (S_pq^* tensor Q S_pq).
```

Its Hochschild boundary is the actual ordinary-integer BV--Green commutator.
The ground diagonal of this boundary is exactly `c_pq`. Summing all ordered
pairs proves the finite identity

```text
d_1(b C_S(a)) = ghost_1(F_2(P_S(a))) = -2 E_W(a,S).
```

No quotient is declared to be a boundary, no cyclic reader is substituted for
the physical diagonal, and no RH-equivalent premise occurs.

## Conjecture loop

1. **Scalar boundary-membership conjecture:** equality of the transgressed
   first ghost with a boundary readout might suffice. **Failure:** that would
   forget ordered source labels and would not compare with the actual
   Gamma/co-Poisson boundary.
2. **Strict dual-landing conjecture:** keep each ordered coefficient on the
   actual Calderón--Witt witness and on a literal degree-`pq` Hochschild chain.
   **Success:** arithmetic packet coordinates recover every coefficient, the
   genuine Gamma/Hodge maps preserve it, and the physical ground reader of the
   literal Hochschild boundary recovers it exactly.
3. **Immediate Stokes-annihilation conjecture:** commutatorhood should kill the
   ground reader. **Failure:** the ground diagonal is not cyclic. Existing
   neutral finite-part results measure the nonzero modular anomaly, and the
   actual Gamma boundary multiplies rather than cancels horizontal fracture.

## Novelty boundary

Big-Witt Frobenius, Hochschild boundaries, and Calderón--Witt incidence
coordinates are existing ingredients. Candidate new knowledge is their
coefficient-faithful weld for the polarized Xi prime-seam source: one explicit
finite source has simultaneously exact ordered Gamma/Hodge incidence
coordinates and exact ordinary-integer Green--BV ground readout. Targeted
corpus and source-paper audits found no previous theorem giving this strict
dual landing.

## Frontier effect

The missing Route-L comparison is no longer an unspecified source-object or
coefficient-provenance problem. The transgressed physical scalar is now an
exact readout of a literal finite Hochschild boundary, and its complete
ordered coefficients already lie in the actual Gamma/co-Poisson incidence
carrier.

Remaining core is narrower and harder: construct a source-derived
cyclic/modular Stokes functional whose comparison with the noncyclic ground
reader has `o(sum 1/p)` error. Neither the old oriented boundary nor the
moving-horizon sum trace proves this: both kill an enlarged two-leg object
while the fixed physical reader selects one Green leg. Proving that comparison
without erasing the leg is the RH-bearing theorem.

## Verification

- direct `lake env lean` on leaf: pass
- targeted leaf build: pass
- declaration axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- leaf forbidden-declaration scan and `git diff --check`: pass
- repository-wide textual lint remains red only on unrelated pre-existing
  umbrella gaps and `HTGeometry/ShiftSumLimits.lean` proof debt
