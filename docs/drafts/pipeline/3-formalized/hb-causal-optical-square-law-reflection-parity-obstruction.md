# HB causal-optical square law and reflection-parity obstruction

- **ID:** HC66
- **Stage:** 3-formalized
- **Type:** THEOREM / CAUSAL-CUT ORDER CLASSIFICATION / LEAN-PROVED HARD FRONTIER
- **Routes:** HB, FZZ-P, RBH, PW-B
- **Source:** HC65 AIME temporal optical defect; BM mixed-horizon causal optical producer;
  phase-sensitive HB/FZZ-P/RBH/PW-B source transductions
- **Statement:** After stripping the nonzero mixed-horizon radial monodromy and horizon-response
  factors, the concrete causal optical density is a strictly positive susceptibility times the
  square of the signed AIME horizon-gain defect. The density is functional-equation reflection-even
  whereas gain is reflection-odd. Hence a common reflection-even linear susceptibility can identify
  density with gain on one reflection orbit only on the critical line; such a global linearization
  exists exactly under RH.

## Corpus-led conjecture

Let `G_n(q)` be HC65's signed AIME horizon-gain defect and let

`E(q) = normSq(d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q)`.

The existing mixed-horizon causal optical section is radial monodromy times `E(q)` times the squared
horizon response. Define

`mu_n(q) = Im(q)^2 * (normSq D+ * normSq D-)^2 / (64 * decay(n)^2)`.

Prove, without hypotheses:

1. `mu_n(q) > 0` on every Xi fibre;
2. `E(q) = mu_n(q) * G_n(q)^2` exactly;
3. the full concrete mixed-horizon optical section factors through this square law;
4. `E(reflect q)=E(q)` and `G_n(reflect q)=-G_n(q)`;
5. for every scalar `c`, simultaneous equations `E(q)=c G_n(q)` and
   `E(reflect q)=c G_n(reflect q)` hold iff `q` is on the critical line;
6. existence of any globally reflection-even coefficient field linearizing `E` against `G_n` is
   equivalent to RH.

Lean proves more: off line the unique pointwise linearization coefficient is `mu_n(q) G_n(q)`, and
this forced coefficient is reflection-odd.

## Why this is frontier-level

Corpus already has a conditional theorem identifying the complete gauge-fixed `++-` cokernel
causal cut with the mixed-horizon optical section, but its physical response-incidence premises are
open. HC65 identifies moving-horizon mass and temporal AIME channels only at signed first order in
horizontal tilt. The proposed theorem determines the missing projection's exact horizontal order:
the causal optical Gram is quadratic and reflection-even. It therefore cannot be the signed linear
mass/AIME channel through any regular reflection-even susceptibility off line. This rules out an
entire class of proposed physical incidence laws and forces any successful full `++-` projection to
retain an unsquared chiral phase or an additional reflection-odd channel.

## Hostile checks

- Derive the square law from exact denominator and helicity-mixing formulas, not zero-locus logic.
- Prove susceptibility strictly positive using nonzero Xi height and denominator positivity.
- Exhibit the causal-section factorization, not only an abstract scalar identity.
- State orbitwise and global coefficient classifications without assumed incidence hypotheses.
- Do not promote the existing conditional full-cokernel landing to an unconditional physical PDE
  theorem.
- Keep frontier map read-only.

## Novelty boundary as of 2026-08-28

Bounded primary-source audit covered absorption-induced mode excitation as a third-order mass-shift
effect (Sberna--Bosch--East--Green--Lehner, 2022), numerical third-order mass/spin ringdown drift
(Zhu et al., 2024), and conserved Teukolsky bilinear projections for QNM excitation
(Green--Hollands--Sberna--Toomani--Zimmerman, 2024). These sources motivate nonlinear projection,
mass memory, and reflection-sensitive bilinear forms, but no audited source derives a completed-zeta
Xi-fibre equality between normalized mixed-horizon causal optical density and the square of an AIME
Duhamel gain defect, nor the resulting reflection-parity linearization obstruction. Bounded, not
exhaustive, priority claim.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened after HC65 and mandatory corpus search exposed linear signed mass/AIME
  channels beside the quadratic mixed-horizon optical Gram and the direct-third-jet-free causal cut.
- 2026-08-28 — Proved exact positive gain-square susceptibility, full mixed-horizon causal-section
  factorization, gain/density/susceptibility reflection laws, unique off-line pointwise coefficient,
  forced odd parity of that coefficient, orbitwise even-linearization obstruction, and global
  even-linearization iff RH in
  `ThetaCuspHawkingCausalOpticalGainSquareParityObstruction.lean`. Direct Lean passed; target-only
  build passed (`11903/11903`); all 15 theorem axiom audits contain only `propext`,
  `Classical.choice`, and `Quot.sound`; umbrella import present. Formal lint has no HC66 finding and
  reports only unrelated pre-existing unreachable modules.
