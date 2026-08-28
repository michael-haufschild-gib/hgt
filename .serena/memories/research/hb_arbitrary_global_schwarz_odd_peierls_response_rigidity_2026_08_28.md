# HC72 — arbitrary-global Schwarz-odd Peierls response rigidity (2026-08-28)

Formal module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingArbitraryGlobalSchwarzOddPeierlsResponseRigidity.lean`

Card: `docs/drafts/pipeline/3-formalized/hb-arbitrary-global-schwarz-odd-peierls-response-rigidity.md`

New results:
- Defined structural properties for an arbitrary complex-linear endomorphism `Delta` of the global finite-support Xi Peierls carrier: Peierls skewness, channel-Schwarz oddness, and universal exact unit BM incidence.
- Proved `d4BMXiSecondHarmonicUnitSourceBoundaryConcomitant_schwarzReal_iff`: literal unit BM target is Schwarz-real iff the Xi copy is on the critical line. Off-line proof uses target = canonical radial weight times nonzero source norm-square and HC71 nonreality of radial weight.
- Proved coordinate-free `hbXiPeierlsGlobalPropagator_sourceResponse_schwarzReal`: pairing Schwarz reality + `S Delta = -Delta S` + Peierls skewness force every same-fibre plus/minus response Schwarz-real. No diagonal, locality, finite-range, boundedness, fibre-preserving, or matrix-support hypothesis.
- Proved local incidence forces criticality and closed endpoint `exists_hbXiPeierlsGlobalPropagator_skew_channelSchwarzOdd_and_universalUnitSourceIncidence_iff_rh n`.
- RH witness is zero weighted propagator; reverse direction applies local rigidity to every Xi copy.

Scope: removes HC71 copy-diagonality loophole completely. Remaining physical burden is to construct/identify actual gauge-fixed Einstein–Teukolsky causal propagator and prove skewness, channel-Schwarz oddness, and literal BM incidence from PDE geometry.

Audit: direct Lean passed; target-only build `12023/12023`; four theorem axiom audits only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired; no module lint finding. Global lint failure only unrelated pre-existing unreachable modules. Frontier map not edited. Scratch removed.