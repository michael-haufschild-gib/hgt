# Finite quantum observer post-exit rate–distortion law

- **Status:** Lean-formalized
- **Formal module:** `formal/GaloisForLFunctions/RHTower/FiniteQuantumObserverPostExitRateDistortionLaw.lean`
- **Headline theorem:** `exists_finiteQuantumObserver_postExit_graph_rateDistortion`

For every finite matrix-record observer family and chosen synchronization
graph, a certified observer exit before one positive sampling tick is
followed by a strictly later return candidate no later than

\[
t_{\rm tick}(Q+1)^{d-\#\pi_0(G)}.
\]

At that later time the squared Hilbert–Schmidt record displacement obeys the
selected/omitted graph rate–distortion budget. Full-coherence and
threshold-graph specializations are formalized; the full coherence graph has
exactly zero omitted positive mass.

This result retains a supplied exit certificate. Calling the later event a
return inside the same exit ball additionally requires the displayed
rate–distortion budget not to exceed that ball’s squared radius. The scalar
expectation escape–return dichotomy removes this premise by defining the
neighborhood at the guaranteed budget itself.

Direct foreground compilation and axiom audit passed. Axioms are only
`propext`, `Classical.choice`, and `Quot.sound`.
