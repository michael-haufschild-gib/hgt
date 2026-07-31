# Finite quantum expectation-sector graph rate–distortion law

- **Status:** formalized
- **Lean module:** `GaloisForLFunctions.RHTower.FiniteQuantumExpectationSectorGraphRateDistortionLaw`
- **Scientific role:** basis-invariant recurrence spine

## Result

For every finite type \(V\) of energy sectors, every family of scalar
expectation histories with ordered-sector coefficients \(c_a(E,F)\), every
nonnegative observer weighting, every graph \(G\) on \(V\), and every
resolution \(Q\), some positive integer \(n\) satisfies
\[
  n\le(Q+1)^{|V|-\#\pi_0(G)}
\]
and
\[
  \sum_a\lambda_a|f_a(n)-f_a(0)|
  \le
  2M_{\rm omit}
  +2\frac{2\pi}{Q+1}M_{\rm select}.
\]
The same metric has an exhaustive non-vacuous alternative: it never exits
the guaranteed neighborhood, or after an exit it returns inside that
neighborhood before the graph deadline.

For supplied complete sector operators \(P_E\),
\[
  c_a(E,F)=\operatorname{Tr}(P_E\rho_aP_FA_a)
\]
reconstructs the physical trace history exactly. These coefficients are
invariant under simultaneous similarity transformations. Thus vertices may
be distinct energy eigenspaces, removing dependence on an arbitrary basis
inside degenerate sectors.

## Formal declarations

- `exists_finiteQuantumExpectationSector_graph_rateDistortion`
- `finiteQuantumExpectationSector_neverExits_or_postExit_return`
- `finiteQuantumExpectationSectorTraceCoefficient`
- `sum_finiteQuantumExpectationSectorBlocks_eq`
- `finiteQuantumExpectationSectorHistory_traceCoefficient_eq_trace`
- `finiteQuantumExpectationSectorInitialValue_traceCoefficient_eq_trace`
- `finiteQuantumExpectationSectorDisplacement_traceCoefficient_eq_trace_sub`
- `finiteQuantumExpectationSectorTraceCoefficient_similarityInvariant`
- `exists_finiteQuantumExpectationSector_trace_graph_rateDistortion`

## Verification

```text
lake env lean \
  GaloisForLFunctions/RHTower/FiniteQuantumExpectationSectorGraphRateDistortionLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/FiniteQuantumExpectationSectorGraphRateDistortionLaw.olean
```

passed. Axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Boundary

The theorem accepts a complete sector-operator family; it does not prove a
spectral theorem for a supplied Hamiltonian or that sector energies are
distinct. Equal Bohr gaps may cancel, and the \(\ell^1\) mass bound remains
conservative. A localization improvement still requires a theorem making
off-graph sector coefficients small.
