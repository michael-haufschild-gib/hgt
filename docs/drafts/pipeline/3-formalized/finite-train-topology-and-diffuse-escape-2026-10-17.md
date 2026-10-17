# Finite-train topology and diffuse packet escape

- **ID:** finite-train-topology-and-diffuse-escape-2026-10-17
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scope:** Infinite-Grid Tail Rigidity Beyond Trap 5; general signed correlations.
- **Status:** Certified package 13 of 100; counted once. Global lint remains blocked
  by unrelated concurrent drafts, listed below.
- **Paper:** `docs/reports/BiScaleUncertainty/FiniteTrainTopologyAndDiffuseEscape.md`
- **Guide:** `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` (read-only).

## Exact invariant and classification

For an actual compact C² positive-mass seed f, distinct integer sites t_i, and
nonzero finite coefficient data c_i, put G(u)=sum_i c_i f(u-t_i S),
Q=sum_i c_i² and A_k=sum_(t_j-t_i=k)c_i c_j. If the seed correlation vanishes
outside radius D and S>2D, the normalized peak

    L=max({0} union {|A_k|/Q : nonzero realized lags k})

satisfies exactly ||H_G-H_f||_infinity=L. This includes all cancellations and
single-packet data. Local correlations equal H_f on |x|<=S/2, giving

    |E(G)-E(f)|<=2 integral_(S/2,infinity) w_arch.

For S_n>=2D+2 tending to infinity, arbitrary varying counts, coefficients and
integer sites share the explicit ceiling E(f)+2 integral_(1,infinity) w_arch;
their energies converge to E(f). Global uniform correlation convergence,
compact correlation closure and uniform signed logarithmic trace tails are
each equivalent to L_n->0. No exact grid-zero premise is imposed.

The actual source moment computation gives

    P(G)=B(1/2)B(-1/2)P(f)/Q,
    B(beta)=sum_i c_i exp(beta t_i S).

For P(f)!=0, polar convergence to P(f) is exactly convergence of this normalized
symbol product to one. Consecutive integer sites recover the old copyTrain
source and lag coefficients exactly.

## Explicit producer and positive survivor

Equal coefficients at sites 3^i have unique nonzero ordered differences. With
q=n+2 packets, Q=q, every nonzero lag coefficient is one, L=1/q, and each
coefficient contributes the mass fraction 1/q. The first two sites prove
B(1/2)B(-1/2)>=exp(S) for every real S. For S>=q the polar multiplier is >=q/4.

The premise-free theorem `exists_smooth_diffuse_train_polar_escape` constructs
an actual C-infinity seed and family, one nonnegative energy ceiling, exact
correlation distance 1/(n+2), convergent energies, compact correlation closure,
uniform signed trace tails, and P(G_n)>=((n+2)/4)P(f)->infinity. Its spacing is
S_n=8+n and its seed has positive polar moment and source radius one.

The obstruction is polar escape under correlation compactness and energy
convergence. The strongest positive survivors are the exact grouped-peak
classification, count-independent energy estimate and exact polar symbol.
All have dependency-closed paper proofs and Lean certificates. Diffusion across
many equal packets is a distinct mechanism from two-copy amplitude suppression.

Trap 10 is respected: the endpoint is an explicit source producer with proved
unconditional error and growth bounds. No assumed Chebyshev receiver, floor
counterterm subtraction, or exact full-grid blindness is used.

## Corpus and novelty boundary

Initial lexical logs: `/tmp/finite-train-topology-frontier.txt`,
`/tmp/finite-train-topology-frontier-broad.txt`, `/tmp/diffuse-train-frontier.txt`.
Deep search `/tmp/finite-train-topology-deep.json` returned partial source-only
candidates, pending coverage, and no applicable replacement identities, proof
ideas or ingredient sets. Existing finite-source expansion, local energy
comparison and signed compactness APIs were checked directly and reused.
No exhaustive external priority claim is made.

Existing sqrt(n)-weighted polar-copy sample defects belong to package 1.
Existing Nyquist cell and dyadic L2 producer bounds were identified in
`ExplicitNyquistPolarAndChebyshevFactorialProducer` and are not counted anew.
The read-only field guide was read fully after its update (260 lines), SHA256
`dda7a67adbca527a21596c6fb672c28afb5feda594fe3b552a781325df7c3933`.

## Certificates

- [x] Complete paper proof preceded new Lean code; actual diffuse witness audited.
- [x] Eight direct `lake --old env lean` checks pass without diagnostics:
  `FiniteIntegerTrainPackets`, `FiniteIntegerTrainPeak`, `FiniteIntegerTrainEnergy`,
  `FiniteIntegerTrainCompactness`, `FiniteIntegerTrainPolar`, `TernaryPacketTrain`,
  `TernaryPacketPolarGrowth`, `FiniteIntegerTrainProducers`.
- [x] All 77 public declarations (61 theorems, 15 definitions, one structure)
  have exhaustive axiom checks: only `propext`, `Classical.choice`, `Quot.sound`.
- [x] All 77 exact API name/module pairs, eight unique umbrella imports and
  unchanged source hashes verified. Index refresh passed; no umbrella build ran.
- [x] Authoritative formal lint executed. No error concerns this package. The
  global gate failed on four foreign unwired modules: `CellPrefixHilbert`,
  `DivisorCellConstraints`, `HighFrequencyLaplaceEnergyMeanValue`, and
  `UnconditionalLaplaceEnergyAndRoughCollarWeilProducer`; also a foreign `sorry`
  at `HighFrequencyLaplaceEnergyMeanValue.lean:292`, theorem
  `integral_twoSided_atomic_div_sq_le`. No global green lint claim is made.
- [x] Ledger and parent card record 13 certified connected packages.

Leaf logs: `/tmp/finite-train-{packets,peak,energy,compactness,polar,ternary,growth,producers}-leaf.log`.
Audit logs: `/tmp/finite-train-topology-{axioms,index,lint}.log`.
Scratch and complete manifests: `/tmp/finite_train_topology_axioms.lean`,
`/tmp/finite_train_topology_declarations.json`,
`/tmp/finite_train_topology_source_hashes.json`,
`/tmp/finite_train_topology_axiom_coverage.json`.

## Next paper result, uncounted

`../2-fully-proven/nyquist-polar-integrable-residual-2026-10-17.md` proves on paper
that the explicit Nyquist producer has an absolutely summable all-tail residual,
with exact operator norm A_N<=1/sqrt(N). Its actual polar decomposition locates
the diffuse escape in weighted cell averages while the correction is uniformly
stable. Lean formalization has not started. The 100-package goal remains active.
