# Falsification pass over the live-branch open cores (2026-09-04)

- **ID:** RH-OPEN-CORE-FALSIFICATION-2026-09-04
- **Stage:** 1-in-progress (record; no new theorem)
- **Type:** AUDIT / NUMERICAL TEST
- **Source:** `rh-current-frontier-map.md` (live-branch open-core table), Lean corpus via the search tool

## Purpose

Open cores of live branches that are stated as explicit finite inequalities and are only known to be
*sufficient* for their branch can be falsified by a rigorous computation; a failure closes the
branch, a survival isolates a finite target.  Cores that Lean proves *equivalent* to RH cannot be
tested this way (a failure would be a disproof of RH).

## Classification (from Lean declarations)

| Branch | Open core | Lean status | Testable? |
|---|---|---|---|
| CLG/TTF | `thetaCuspC5LikelihoodHomotopyCompensationThree u t λ > 0` on `[0,1]`, `M''(0) ≥ 0`, atom tangent, gate `M(1) > 0` | sufficient chain (`M''' > 0 → convex lift → direct-J → rank-four/Ptolemy → …`); four-face cone proved false | **yes** |
| Q | exterior paired-diagonal nonnegativity / finite paired-value passivity | `continuedPrimeArchPositiveExteriorPairedDiagonalNonnegative_iff_riemannHypothesis`, `positivePairedReducedSourcePassivity_iff_riemannHypothesis` (both directions) | no: it is RH |
| O | finite Gamma–Slepian head inequality at every aperture | failure at one aperture = negative constrained ground energy = ¬RH (`riemannHypothesis_of_polarGroundEnergy_nonneg` + converse under RH) | only aperture pushing (done to `S = 1`) |
| D2 | lower bound of `2 Re(prime flux) − log t` above `141858/10000` | frontier map: unbounded below under ¬RH | no: RH-type |

## CLG/TTF result

`SURVIVES` with large margin: scripts and README in
`2-fully-proven/computations/clg-ttf-c5-homotopy-numerical-test/`; log entry on
`theta-c5-likelihood-homotopy-curvature.md`.  All four statements hold at 861 points of the structural
tail at 120 digits and at 400-digit spot checks to `u = 8`; the homotopy is nearly constant
(`|M(1) − M(0)| ≤ 0.19 M(0)`), which points to a perturbative proof of the gate that avoids the
curvature homotopy.

## Consequence

No live branch was closed.  The only explicit, finite, sufficient-type core in the table is true
numerically; its proof would close the compact seam of CLG/TTF, not the branch (clustered/general
packets and cofinal escape remain).  Future falsification passes should target newly created
sufficient-type cores only.
