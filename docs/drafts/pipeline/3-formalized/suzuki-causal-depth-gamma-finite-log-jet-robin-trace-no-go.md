# Suzuki causal-depth Gamma finite-log-jet Robin-trace no-go

- **ID:** CCM-FU-C29
- **Stage:** 3-formalized
- **Result:** Every fixed exact Wigner--Smith/Robin logarithmic source jet preserves nuclearity of
  the actual causal-depth Gamma feature; no uniformly operator-bounded response in this class can
  semibound the rectangular Ward defect.
- **Module:** `GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaFiniteLogJetRobinTraceNoGo`
- **Terminal theorem:** `no_suzukiCausalDepthGammaFixedLogJetWardProducer`

## Closed chain

`log(p^(e+1))^k=(e+1)^k(log p)^k` and corpus prime-depth decay imply fixed-log-moment `ℓ¹`;
canonical column expansion gives `F_k∈S¹`; trace duality gives an `O(1)` bounded-response
correction; the correction is sublinear; the generic rectangular Ward theorem excludes the
producer class.

Lean also proves exact source fidelity:
`suzukiCausalDepthGammaLogJetFeatureOperator_single_source_eq_smul` and
`suzukiCausalDepthGammaLogJetFactor_eq_wignerSmithCharge_re_pow`.

## Boundary

Killed: every fixed jet order with a uniform response operator-norm ceiling.

Survives: cutoff-growing jet order, super-polynomial/singular functional calculus,
operator-norm/graph-weak blow-up, singular trace, or a moving source that loses `S¹`.

## Audit

- `lake env lean` direct module check: passed.
- Targeted `lake build` of this module: passed.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Formal lint: new module reachable and clean; repository lint remains red only on unrelated
  pre-existing unreachable modules.
- Literature audit through August 2026 found no exact source-specific fixed-log-jet
  nuclearity/producer no-go. General summability and trace-duality ingredients are classical.
