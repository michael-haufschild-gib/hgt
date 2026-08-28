# HB arbitrary-global Schwarz-odd Peierls response rigidity

- **ID:** HC72
- **Stage:** 3-formalized
- **Type:** THEOREM / LEAN-PROVED FULL LINEAR CAUSAL PROPAGATOR OBSTRUCTION / HARD FRONTIER
- **Routes:** HB, FZZ-P, RBH, PW-B
- **Source:** HC71 diagonal obstruction; corpus Peierls skewness; carrier-pairing Schwarz reality;
  canonical Schwarz exchange of literal BM source axes
- **Statement:** Among all complex-linear global propagators on the finite-support Xi carrier—with
  arbitrary cross-fibre and cross-channel mixing—simultaneous Peierls skewness, channel-Schwarz
  oddness, and universal exact unit BM incidence exists if and only if RH.

## Corpus-led conjecture

Remove HC71's copy-diagonal hypothesis. For an arbitrary complex-linear global propagator `Delta`,
assume only the two structural causal laws

`Peierls(Delta; f,g) = -Peierls(Delta; g,f)`

and

`S (Delta f) = -Delta (S f)`.

The corpus gives `S plus = minus`, `S minus = plus`, and
`pairing(Sx,Sy)=star(pairing(x,y))`. Combining these with the two structural laws should prove that
the same-fibre literal source response

`Peierls(Delta; plus(1,q), minus(1,q))`

is Schwarz-real for every `q`, irrespective of all off-diagonal matrix coefficients. Separately
classify the literal BM boundary concomitant as Schwarz-real exactly on the critical line: off the
line it is canonical radial weight times a strictly positive source norm-square, and the radial
weight has nonzero imaginary part.

Conclude the premise-free endpoint

`(exists arbitrary global Delta, skew Delta and SchwarzOdd Delta and universal unit BM incidence)
  <-> RH`.

The RH direction is witnessed by the zero diagonal propagator because all literal BM sources are
then extinct. The reverse direction applies the response-reality law fibrewise.

## Why this is frontier-level

HC71 left open whether non-diagonal Green operators could evade the incompatibility through
cross-fibre mixing. HC72 attacks the full algebraic operator class and, if true, proves they cannot:
the obstruction is coordinate-free at the paired-source level. This removes diagonality, locality,
kernel sparsity, and fibre preservation from the RH receiver.

The theorem still does not construct the actual gauge-fixed Einstein--Teukolsky causal propagator
or prove its physical time-reflection law. It reduces that PDE producer burden to two standard
structural identities—Peierls skewness and Schwarz oddness—plus literal BM source incidence, without
any model-specific matrix ansatz.

## Hostile checks

- Quantify over every complex-linear endomorphism of the global finite-support two-channel carrier.
- No diagonal, local, finite-range, bounded, continuous, reflection-permuting, or kernel hypothesis.
- Derive response reality from exact operator and pairing identities; do not inspect matrix entries.
- Prove BM boundary Schwarz reality iff criticality, including source extinction on the line and
  strict nonreality off it.
- State existence iff RH as a closed theorem; use no physical premise in the endpoint statement.
- Keep frontier map read-only.

## Novelty boundary as of 2026-08-28

Mandatory Lean-corpus search found HC71's diagonal theorem and the older source-fixed reflected
cubic rigidity theorem, but no arbitrary global-linear propagator result deriving same-source
Schwarz reality without fibre preservation or branch-reflection premises. Bounded primary-source
audit covered Peierls/covariant-phase-space symplectic--Poisson equivalence and its PDE hypotheses
(Khavkine, arXiv:1402.1282), Kerr reflection-dependent conserved bilinear forms and QNM projections
(Green--Hollands--Sberna--Toomani--Zimmerman, arXiv:2210.15935), scalar Kerr Green-function
decomposition (Yang--Zhang--Zimmerman--Chen, arXiv:1311.3380), and the July 2026 higher-order QNM
perturbation framework with continuous-spectrum contributions (Lestingi--Sberna--Green,
arXiv:2607.19492). No audited source states this exact full-operator BM Xi response-reality
obstruction or its RH equivalence. Bounded, not exhaustive, priority claim.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened after HC71 left copy-diagonality as its principal algebraic restriction.
  Frontier map left unchanged.
- 2026-08-28 — Proved the full arbitrary-operator result in
  `ThetaCuspHawkingArbitraryGlobalSchwarzOddPeierlsResponseRigidity.lean`. For any complex-linear
  endomorphism of the global Xi carrier, Peierls skewness plus channel-Schwarz oddness forces every
  literal same-fibre plus/minus response to be Schwarz-real. This proof is coordinate-free and uses
  no matrix-support condition. Proved separately that the unit BM boundary concomitant is
  Schwarz-real iff the fibre is critical. Their universal exact incidence is therefore RH-equivalent.
- 2026-08-28 — Verification: direct `lake env lean` passed; target-only
  `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingArbitraryGlobalSchwarzOddPeierlsResponseRigidity`
  passed (`12023/12023`); all four exported theorem axiom audits report only `propext`,
  `Classical.choice`, and `Quot.sound`; umbrella import present. Formal lint reports no finding in
  this module; repository lint remains nonzero only for pre-existing unrelated unreachable modules.
