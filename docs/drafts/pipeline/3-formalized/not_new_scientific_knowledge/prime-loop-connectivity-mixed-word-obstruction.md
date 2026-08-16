# Prime-loop connectivity versus mixed-word obstruction

- **ID:** `prime-loop-connectivity-mixed-word-obstruction`
- **Stage:** 3-formalized
- **Type:** `[NO-GO]`, `[POSITIVE SUCCESSOR]`, not new scientific knowledge
- **Source:** `../../0-backlog/moonshot-arithmetic-bulk-hyperbolic.md`
- **Lean bricks:** `FiniteEulerInert.lean`, `IharaBlockSelector.lean`

## Statement

An ordinary positive metric-graph realization of the Riemann Euler product faces a strict
dichotomy.

1. Give each prime `p` an isolated primitive loop of length `log p`. Its repetitions contribute
   exactly the local factor

   ```text
   exp(-s log p)=p^(-s),
   Z_p(s)=(1-p^(-s))^(-1).
   ```

   The disjoint union reproduces every finite Euler product, but has no connected prime--Gamma
   interaction and no mechanism for the nontrivial Xi divisor.
2. Join two nonzero prime loops `p` and `q` at a vertex. The closed word `pq` is then a mixed
   primitive orbit. Its length is `log p+log q=log(pq)` and its nonzero positive amplitude forces an
   additional primitive factor. The Riemann Euler product has no primitive factor indexed by the
   composite `pq`; `p^m` occurs only as a repetition of the `p` loop.

Thus positive connected gluing creates unwanted mixed primitive words, while exact removal of all
mixed words block-diagonalizes the prime sectors back to the disconnected model.

## Proof

For the isolated `p` loop, the standard geometric orbit expansion is

```text
sum_(m>=1) exp(-m s log p)/m = -log(1-p^(-s)),
```

so exponentiation gives the local Euler factor. This is the same exponential local factor
formalized as `eulerInvFactor p s` in `FiniteEulerInert.lean`.

Now take two directed loops with nonzero scalar transition weights `a_p,a_q` at one vertex. Every
finite edge word is closed. The length-two word `pq` uses both colors, so it is not a repetition of
either length-one loop and is primitive. Its weight is `a_p a_q`, which is nonzero. Positive scalar
orbit sums cannot cancel it. Conversely, requiring every mixed length-two amplitude to vanish
gives `a_p a_q=0` for every distinct pair; in an all-prime positive model at most one sector remains
active in each connected scalar block. Decomposing by the active sector yields the disjoint prime
sum. QED.

## Positive successor

The obstruction identifies the minimum nonordinary geometry for a live quantum-graph chain:

```text
prime-log connected graded scattering system
  -> supertrace cancels every mixed primitive word
  -> pure repetitions retain exactly Lambda(p^m)
  -> archimedean vertex/cusp contributes the Gamma factor
  -> a closed self-adjoint superdeterminant equals Xi
  -> spectral reality
  -> RH.
```

The cancellation must be graded or indefinite; scalar positivity cannot do it. It must also occur
before analytic continuation, uniformly over all mixed words, without making the transfer matrices
orthogonal prime blocks. If a construction merely declares the superdeterminant to be Xi, it is
target-fed. If its mixed-word cancellation forces block orthogonality, it returns to the
disconnected no-go.

## Two-ended audit

- `[PROVED]` the prime-length source end reproduces the finite Euler factors exactly;
- `[PROVED]` ordinary connected positive gluing necessarily adds mixed primitive factors;
- `[OPEN CORE]` construct a connected graded scattering category with exact all-word cancellation
  but nontrivial prime--archimedean coupling;
- `[OPEN CORE]` prove unconditional closedness/self-adjointness and identify its superdeterminant
  with the completed Xi source;
- `[PROVED CONSUMER]` a genuine self-adjoint determinant realization would force spectral reality
  and hence RH through the existing Hilbert--Polya endpoints.

The ordinary positive quantum-graph detour is closed. The graded connected successor is a typed
large detour, but its two substantive source theorems are not present in the corpus.

## Classification

The mixed-word observation is elementary symbolic dynamics and the geometric-series identity is
classical. The result is useful route geometry, not new scientific knowledge.

## Lean formalization

`formal/GaloisForLFunctions/RHTower/PrimeLoopMixedWordObstruction.lean`

| Card claim | Lean declaration |
|---|---|
| `∑_{m≥1} exp(-m s log p)/m = -log(1 - p^{-s})` | `hasSum_primeLoopOrbit` |
| exponentiating gives the local Euler factor `(1-p^{-s})^{-1}` | `exp_primeLoopOrbit` |
| the disjoint union reproduces every finite Euler product | `exp_sum_primeLoopOrbit` |
| the mixed word has length `log p + log q = log(pq)` | `mixedWordLength` |
| its amplitude `a_p a_q` is nonzero, so positive orbit sums cannot cancel it | `mixedWordWeight_ne_zero` |
| `pq` is not a prime power, so the Euler product has no such primitive factor | `not_isPrimePow_mul_of_ne` |
| requiring every mixed amplitude to vanish leaves at most one active sector | `eq_of_mixedWordWeight_eq_zero` |
| **the dichotomy** | `primeLoop_connectivity_dichotomy` |

The local factor is the corpus's `eulerInvFactor` (`RHTower/FiniteEulerInert.lean`), and
`eulerInvFactor_eq_one_sub` identifies it with the single-traversal multiplier
`primeLoopMultiplier p s = exp(-s log p)`.

The `[OPEN CORE]` items (a connected graded scattering category with exact all-word cancellation,
and the identification of its superdeterminant with the completed Xi source) are explicitly open
research, not part of the proved theorem.

All declarations audited with `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
