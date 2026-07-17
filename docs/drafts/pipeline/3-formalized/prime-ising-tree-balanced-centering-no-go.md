# Prime Ising tree balanced centering and scalar-normalization no-go

- **ID:** `prime-ising-tree-balanced-centering-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) `[SOURCE NORMALIZATION] [NO-GO] [RH BRIDGE]`
- **Source:** `../1-in-progress/prime-source-ferromagnetic-ising-lee-yang-limit-rh.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeIsingTreeBalancedCentering.lean`
- **Statement:** Global spin inversion forces an exponential reflection cocycle with exponent the
  total logarithmic prime mass.  Scalar unit-central normalization therefore cannot converge
  locally uniformly to the unit-pointed even germ `XiC(0)^(-1)XiC`; multiplication by the unique
  half-cocycle removes the first-jet obstruction while preserving entireness and the real-zero law.

## Goal

Determine the normalization actually permitted by the finite prime source before attempting the
Lee--Yang comparison with `XiC`.  The result must use no Xi zero and must distinguish an attainable
source comparison from a formally correct RH implication whose premise is impossible.

## The theorem package

For a finite prime-labelled Ising tree `T`, let

```text
M(T) = sum_(vertices v of T) log p_v.
```

Every tree is nonempty, so unconditionally

```text
M(T) >= log 2 > 0.                                             (1)
```

If `Z_T` is its prime-field partition and `N_T(z)=Z_T(0)^(-1)Z_T(z)` is the scalar
unit-central normalization, the attainable target is the pointed germ

```text
XiHat(z) = XiC(0)^(-1) XiC(z),       XiHat(0)=1.              (2)
```

Global spin inversion gives

```text
Z_T(z) = exp(-i M(T) z) Z_T(-z),
N_T(z) = exp(-i M(T) z) N_T(-z).                              (3)
```

Consequently

```text
N_T'(0) = -i M(T)/2.                                          (4)
```

Local-uniform convergence of entire functions propagates to their first derivatives.  Since
`XiHat` is even, `XiHat'(0)=0`; equations `(1)` and `(4)` therefore prove

```text
not TendstoLocallyUniformly (N_(T_n)) XiHat                   (5)
```

for every tree sequence.

Define instead the source-balanced partition

```text
B_T(z) = exp(i M(T) z/2) N_T(z).                              (6)
```

Then `(3)` forces `B_T(-z)=B_T(z)`.  The exponential factor is entire and zero-free, hence `B_T`
is entire, `B_T(0)=1`, and every zero of `B_T` is real.  Therefore

```text
TendstoLocallyUniformly (B_(T_n)) XiHat -> RiemannHypothesis. (7)
```

The implication `(7)` is not an RH proof: the locally uniform source comparison remains open.  It
is the corrected endpoint because `(6)` is forced by the source reflection law and `(5)` kills the
previous scalar-normalized premise.

## Canonicality

Within exponential gauges `exp(a M(T) z) N_T(z)`, evenness and `(2)` force `a=i/2`.  Thus the
half-mass factor is not selected from the target germ.  It is the unique linear exponential gauge
that trivializes the source spin-inversion cocycle.

## Lean certificate

The file proves, without project axioms:

- `log_two_le_treePrimeLeeYangMass`;
- `treeFieldProduct_centered_eq_massExp`;
- `primeIsingTreePartition_reflectionCocycle`;
- `balancedPrimeIsingTreePartition_even`;
- `deriv_centralNormalizedPrimeIsingTreePartition_zero`;
- `unitCentralXiC_zero`;
- `not_tendstoLocallyUniformly_centralNormalizedPrimeIsingTreePartition_unitCentralXiC`; and
- `riemannHypothesis_of_balancedPrimeIsingTreePartition_tendstoLocallyUniformly`.

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 → 1 in-progress: source-pure mass and reflection cocycle identified
- [x] 1 → 2 fully-proven: scalar-normalization contradiction and half-cocycle repair proved
- [x] 2 → 3 formalized: exact module build and axiom audit passed
- [ ] 3 → 4 publication-ready: parent-theory and literature novelty audit still required

## Novelty and significance gate

- **Significance:** passed as a route-level theorem.  It refutes the existing direct normalized-tree
  comparison and replaces it with a source-canonical endpoint.
- **Novelty:** not claimed.  Spin-inversion centering is elementary in finite Ising theory; the
  specialized prime-mass compact-open obstruction has not yet received a literature audit.
- **Anti-theatre verdict:** this does not prove RH and does not reduce the open comparison theorem.
  It prevents an impossible premise from being advertised as the live bridge.

## Open core

Construct a cofinal, source-functorial sequence `T_n` and prove

```text
B_(T_n) -> XiC(0)^(-1) XiC
```

locally uniformly on `C`, or prove a source obstruction to that comparison.  Coefficient matching,
pressure convergence, or scalar normalization is insufficient.

## Log

- 2026-07-17 -- Reflection mass, scalar-normalization no-go, balanced repair, real-zero law, and
  corrected RH capstone proved in Lean; exact module build and axiom audit passed.
