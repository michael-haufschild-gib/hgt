# Logarithmic-derivative meromorphic-order quantization

- **ID:** `logarithmic-derivative-meromorphic-order-quantization`
- **Stage:** 3-formalized
- **Type:** THEOREM / CLASSICAL ANALYTIC BRIDGE
- **Scientific status:** `[PROVED] [FORMALIZED] [SEARCH] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `../../1-in-progress/vanishing-mass-finite-residue-projective-rigidity.md`
- **Formal module:**
  `formal/GaloisForLFunctions/HTGeometry/LogarithmicResidueQuantization.lean`

## Statement

If `f` is meromorphic at `rho` and has integer meromorphic order `n`, then

```text
(s-rho) logDeriv(f)(s) -> n             as s -> rho, s != rho.  (1)
```

Positive `n` records a zero and negative `n` a pole.  For a finite family `F_j` with real
coefficients `c_j`, equation `(1)` gives

```text
(s-rho) sum_j c_j logDeriv(F_j)(s) -> sum_j c_j n_j.            (2)
```

For a pole family indexed by a parameter `p`, the right side of `(2)` is exactly
`finiteQuantizedResidueCorrection coefficient order p` from the vanishing-mass rigidity law.

## Proof

The meromorphic-order normal form factors `f` on a punctured neighborhood as

```text
f(s)=(s-rho)^n g(s),
```

where `g` is analytic and nonzero at `rho`.  Off the center,

```text
logDeriv(f)=n/(s-rho)+logDeriv(g).
```

The analytic-unit logarithmic derivative is continuous at `rho`, so multiplication by `s-rho`
kills its contribution and proves `(1)`.  Finite summation proves `(2)`.

## Role

This closes the analytic-producer gate in the parent theorem.  Finite logarithmic gauge families
do not merely have an assumed finite residue palette: their residues are finite real-linear
combinations of integer meromorphic orders.  If the order functions have finite range, the already
formalized vanishing-mass law screens the correction asymptotically.

## Formal theorem surface

- `logDeriv_residue_of_meromorphicOrder`;
- `finiteLogDeriv_residue_of_meromorphicOrders`;
- `finiteLogDeriv_residue_eq_finiteQuantizedResidueCorrection`.

## Gates

- [x] arbitrary zero and pole orders covered
- [x] punctured-neighborhood factorization transferred to logarithmic derivatives
- [x] finite logarithmic-gauge residue formula proved
- [x] exact interface to the finite quantized correction proved
- [x] targeted module build passed
- [ ] combined axiom and lint audit recorded
