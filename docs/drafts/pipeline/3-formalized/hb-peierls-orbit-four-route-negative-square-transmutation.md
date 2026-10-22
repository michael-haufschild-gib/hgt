# HB Peierls-orbit four-route negative-square transmutation

- **ID:** HC68
- **Stage:** 3-formalized
- **Type:** THEOREM / LEAN-PROVED EXACT CAUSAL-CURRENT TRANSMUTATION / HARD FRONTIER
- **Routes:** HB, FZZ-P, RBH, PW-B
- **Source:** HC67 reflected polarized Peierls orbit square law; HC39 shared Ward-energy square;
  exact FZZ-P/PW-B/RBH Ward transmutations on actual Xi support
- **Statement:** The concrete reflected `++/--` BM Peierls causal-current orbit is exactly a
  negative, strictly-positive-coefficient square of the FZZ information force, every-grade PW-B
  partner imbalance, and actual RBH multiplicity-leading imbalance. These are three presentations
  of one causal current, not merely coincident zero loci.

## Corpus-led conjecture

For QNM grade `n`, divisor copy `q`, PW recoil grade `k`, and actual divisor `rho`, define explicit
susceptibilities from the actual Xi height and the already-proved positive Ward multipliers:

1. `S_HB = 2(8n+5) Im(q)^2 / C_HB(n,q)`;
2. `S_FZZ = 2(8n+5) Im(q)^2 / C_FZZ(q)^2`;
3. `S_PW = 2(8n+5) Im(q)^2 / C_PW(k)^2`;
4. `S_RBH = 8(8n+5) Im(rho)^2 / C_RBH(rho)^2`.

Prove each coefficient strictly positive and prove

`PeierlsOrbit = -S_HB * HBPower = -S_FZZ * Force^2 = -S_PW * PWImbalance^2
= -S_RBH * RBHImbalance^2`.

Then derive pointwise extinction equivalences and universal RH equivalences in each route language.

## Why this is frontier-level

HC39 identified a shared passive optical energy, but passive squaring erased orientation. HC67 found
the correct polarized causal-current survivor and proved its negative sign. This conjecture welds
that signed causal object, at exact coefficient level, to three independently constructed route
observables. Success closes the multi-route causal-current seam: HB polarization, nonlinear FZZ
information force, every-grade PW recoil, and actual RBH multiplicity geometry become one exact
negative-square law.

This does not claim the abstract full-cokernel cut equals the concrete BM current; physical source
incidence for that final identification remains a separate producer burden.

## Hostile checks

- Use actual HC67 unit-carrier midpoint orbit cut; no tunable radial point.
- Use actual FZZ force, every-grade PW imbalance, and canonical first RBH divisor copy.
- Prove all conversion coefficients strictly positive, including centre fibres.
- Derive exact identities before zero-locus or RH corollaries.
- Do not replace a hard identity by bounds or numerical optimization.
- Keep frontier map read-only.

## Novelty boundary as of 2026-08-28

Lean-corpus search found pairwise shared Ward-energy identities but no theorem connecting the HC67
polarized Peierls causal current to FZZ-P, PW-B, or RBH squares. Bounded primary-source search
covered FZZ duality (Hikida--Schomerus, arXiv:0805.3931), nonlinear black-hole ringdown and horizon
mode coupling (arXiv:2208.07374; arXiv:2306.11142), and operator-theoretic RH positivity routes
(Connes--Consani, arXiv:1910.14368). No audited source states this completed-zeta Xi-fibre exact
four-route Peierls negative-square transmutation. Bounded, not exhaustive, priority claim.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened from the conjunction of HC67's signed causal-current square and the corpus's
  positive-multiplier Ward transmutations. Frontier map left unchanged.
- 2026-08-28 — Proved four explicit strictly positive susceptibilities and exact identities in
  `ThetaCuspHawkingPeierlsOrbitFourRouteNegativeSquareTransmutation.lean`: the Peierls orbit is a
  negative multiple of canonical HB optical power and negative squares of FZZ force, every-grade
  PW imbalance, and actual RBH imbalance. Proved three pointwise extinction equivalences, three
  universal route equivalences, and two universal RH equivalences.
- 2026-08-28 — Verification: direct `lake env lean` passed; target-only
  `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingPeierlsOrbitFourRouteNegativeSquareTransmutation`
  passed (`12008/12008`); all sixteen exported theorem axiom audits report only `propext`,
  `Classical.choice`, and `Quot.sound`; umbrella import present; formal lint reports no finding in
  this module (only unrelated unreachable modules).
