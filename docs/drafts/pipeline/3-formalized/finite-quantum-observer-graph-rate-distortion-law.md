# Finite quantum observer graph rate–distortion law

- **Status:** Lean-formalized
- **Formal module:** `formal/GaloisForLFunctions/RHTower/FiniteQuantumObserverGraphRateDistortionLaw.lean`
- **Headline theorem:** `exists_finiteQuantumObserver_graph_rateDistortion`

## Exact result

For every finite energy list, every finite family of complex matrix records,
every nonnegative record weighting, every resolution integer \(Q\), and every
chosen simple graph \(G\) on the energy sectors, some positive integer \(n\)
satisfies

\[
n\le (Q+1)^{d-\#\pi_0(G)}
\]

and

\[
D_{\rm obs}^2(n)\le
4M_{\rm omit}(G)+
4\left(\frac{2\pi}{Q+1}\right)^2M_{\rm select}(G).
\]

Selected and omitted directed masses partition the complete off-diagonal
observer mass exactly. Diagonal mass is excluded because phase conjugation
fixes it. A threshold-graph specialization and its pointwise omitted-weight
bound are also formalized.

## Truth boundary

- The displayed distortion is an upper bound. Omitted coherences do not
  generally contribute exactly \(4M_{\rm omit}\).
- \(d-\#\pi_0(G)\) is the universal graph-capacity exponent in the deadline,
  not necessarily the exact exponent of one arithmetically resonant energy
  list.
- The result controls Hilbert–Schmidt displacement of complete matrix
  records. It is not, by itself, an exact theorem about a single scalar
  expectation history, where equal Bohr gaps can cancel.
- The theorem is finite-dimensional, deterministic, and stroboscopic. It
  does not yet certify prior exit, a first post-exit return, device
  feasibility, an Anderson ensemble, or a thermodynamic limit.

## Novelty status

`[NOVELTY UNVERIFIED]`. Dirichlet recurrence, incidence rank
\(d-\#\pi_0(G)\), thresholding, and omitted-mass triangle bounds each have
strong antecedents. Candidate novelty is only the completed
observer-record/graph/rate–distortion composition, and it is not a
Nature-level anchor without a non-vacuous post-exit theorem and a genuine
local-Hamiltonian consequence.

## Verification

Direct foreground compilation passed with

```text
lake env lean GaloisForLFunctions/RHTower/FiniteQuantumObserverGraphRateDistortionLaw.lean
```

Headline declarations use only `propext`, `Classical.choice`, and
`Quot.sound`.
