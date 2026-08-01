# Route G2 source-germ rigidity closure (2026-08-01)

Route G2 from `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` is closed as an exact no-go/classification, not an RH proof.

## Mathematical result

For
- `P = suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta`,
- `R = suzukiAffineSewnIntervalPart alpha beta 0 WAlpha WBeta rightAlpha rightBeta`,
- `M = suzukiShiftedXiMultiplier 0 = XiC'/(z^2 XiC)`,
- `m = suzukiAffineSewnExteriorWeylQuotient ...`,

at every point with `P z != 0`:
`m z = suzukiReflectionOddPart R z / P z - M z`.

Under distinct shifts, entire boundary responses, and real-zero characteristic factors, the local quotient is analytic off the real axis. Xi poles therefore survive exactly: `m` has order -1 at each off-real Xi zero and its Euler defect has order -2.

Strongest survivor:
`RH ↔ ∃ analytic D on UHP and one UHP seed u, E[m] = D as a pointed germ at u`.
Same theorem is formalized after substituting the complete relative-Volterra Euler/Neumann boundary responses. Thus literal Green/CD source weld would itself be the hard RH proof; it is not routine missing Volterra infrastructure.

## Files

- Paper proof: `docs/drafts/pipeline/2-fully-proven/route-g2-relative-volterra-source-germ-weld.md`
- Formal card: `docs/drafts/pipeline/3-formalized/route-g2-relative-volterra-source-germ-weld.md`
- Lean: `formal/GaloisForLFunctions/RHTower/SuzukiVolterraSourceGermWeldRigidity.lean`
- Umbrella import: `formal/GaloisForLFunctions/RHTower.lean`
- Frontier map Route G2 updated to closed no-go.

## Lean declarations

- `suzukiAffineSewnExteriorWeylQuotient_eq_localCorrection_sub_xiMultiplier`
- `analyticAt_suzukiAffineSewnExteriorWeylEulerDefect_of_riemannHypothesis`
- `analyticOnNhd_suzukiAffineSewnExteriorWeylEulerDefect_of_riemannHypothesis`
- `riemannHypothesis_iff_exists_suzukiAffineSewnExteriorWeylEulerDefect_source_germ_weld`
- `riemannHypothesis_iff_exists_suzukiVolterraPhaseEulerDefect_source_germ_weld`

## Verification

Passed:
- `lake env lean GaloisForLFunctions/RHTower/SuzukiVolterraSourceGermWeldRigidity.lean`
- `scripts/formal_tools.py lint` (no output/errors)
- batched `#print axioms` scratch: only `propext`, `Classical.choice`, `Quot.sound`
- `lake build GaloisForLFunctions.RHTower.SuzukiVolterraSourceGermWeldRigidity`; target olean exists and build PIDs exited.

No computations used. No custom axioms, sorry/admit/opaque/unsafe.

## Source audit

Primary sources:
- Suzuki arXiv:2206.03682v4: literal prime-Gamma transform initially only for Im z > 1/2.
- Suzuki arXiv:2606.09096v1: finite selfadjoint/real-zero models unconditional; global limit remains conjectural/conditional.
- Suzuki arXiv:1204.1827: extension across critical parameter range is RH-bearing.
- Derkach-Hassi-Malamud arXiv:1706.07948: boundary triples do not supply Xi source identification.

External novelty remains unverified; do not claim priority.

Related project memories: `mem:core`, `mem:conventions`, `mem:task_completion`.