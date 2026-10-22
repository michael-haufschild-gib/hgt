# HB Schwarz-odd diagonal causal-propagator obstruction

- **ID:** HC71
- **Stage:** 3-formalized
- **Type:** THEOREM / LEAN-PROVED CAUSAL GREEN-JUMP COMPATIBILITY CLASSIFICATION / HARD FRONTIER
- **Routes:** HB, FZZ-P, RBH, PW-B
- **Source:** HC70 diagonal Peierls source-incidence rigidity; canonical antilinear channel
  Schwarz involution; nonzero imaginary height of every Xi divisor copy
- **Statement:** A copy-diagonal global Peierls propagator can simultaneously realize literal unit
  BM source incidence on every Xi fibre and be odd under canonical channel Schwarz transport if and
  only if the Riemann hypothesis holds.

## Corpus-led conjecture

For an arbitrary weight field `w : XiZeroCopy -> C`, define Schwarz-oddness of its two-channel
Peierls propagator by

`S (Delta_w f) = - Delta_w (S f)` for every finite-support packet `f`,

where `S` is the corpus canonical antilinear channel exchange. Prove the exact operator
classification

`Delta_w is Schwarz-odd <-> star (w q) = w q for every q`.

The HC70 incidence classification forces `w(q)` to equal the canonical radial weight at every
tilted fibre. That radial weight has imaginary part `-Im(q)` and every Xi divisor copy has nonzero
imaginary part. Hence a Schwarz-real incident weight cannot exist at a tilted fibre. Prove the
closed endpoint

`(exists w, universal unit BM incidence for w and Delta_w is Schwarz-odd) <-> RH`.

Under RH the zero weight is a witness because every BM source is extinct. Conversely, simultaneous
incidence and Schwarz-oddness force every Xi fibre onto the critical line.

## Why this is frontier-level

HC70 solved diagonal source-incidence uniqueness but left physical causal symmetry untouched. This
conjecture attacks that structural burden: advanced-minus-retarded propagation should reverse under
the canonical Schwarz/time-reflection channel exchange. Exact BM incidence instead demands a
genuinely non-real jump coefficient on every tilted Xi fibre. Their compatibility is therefore not
an adjustable normalization issue but an RH-equivalent obstruction.

This does not prove an Einstein--Teukolsky causal propagator is copy-diagonal or that its physical
time reflection is exactly the corpus channel involution. It proves the full algebraic compatibility
law within the copy-diagonal inverse Green-jump class and isolates those PDE identifications as the
remaining physical burden.

## Hostile checks

- Weight field arbitrary; no continuity, boundedness, nonvanishing, or reflection hypothesis.
- Derive Schwarz reality from operator oddness using a single-copy probe, not coefficient extensionality
  assumed as a premise.
- Prove the converse operator identity for arbitrary two-channel finite-support packets.
- Derive canonical radial-weight nonreality from the corpus exponent imaginary-part theorem and
  `xi_divisor_support_im_ne_zero`; do not add a nonzero-height premise.
- State existence iff RH as a premise-free theorem; zero propagator allowed only in the RH direction,
  where HC70 incidence is source-extinct.
- Keep frontier map read-only.

## Novelty boundary as of 2026-08-28

Mandatory Lean-corpus searches found HC70 arbitrary diagonal incidence rigidity, fixed-scalar
no-go theorems, and the canonical channel Schwarz involution, but no causal Schwarz-oddness
classification or simultaneous-incidence endpoint. Bounded primary-source audit covered the
Peierls/covariant-phase-space hypotheses and symplectic--Poisson equivalence (Khavkine,
arXiv:1402.1282), reflection-dependent conserved Kerr QNM bilinear forms (Green--Hollands--Sberna--
Toomani--Zimmerman, arXiv:2210.15935), and the July 2026 higher-order QNM perturbation framework,
whose spectral decomposition retains continuous-spectrum contributions and whose QNM sum can
diverge (Lestingi--Sberna--Green, arXiv:2607.19492). No audited source states this exact Xi-fibre
Schwarz-odd diagonal Green-jump obstruction or its RH equivalence. Bounded, not exhaustive,
priority claim.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened from HC70's remaining causal-symmetry burden. Frontier map left unchanged.
- 2026-08-28 — Proved the arbitrary-weight operator classification in
  `ThetaCuspHawkingSchwarzOddDiagonalCausalPropagatorObstruction.lean`: a copy-diagonal Peierls
  propagator is channel-Schwarz odd iff every jump weight is Schwarz-real. Proved the canonical BM
  radial weight has imaginary part equal to negative Xi height and is therefore non-Schwarz-real on
  every Xi copy. Combined this with HC70 incidence rigidity to prove existence of a universally
  incident Schwarz-odd diagonal jump iff RH; under RH, the zero jump is valid because all unit BM
  sources are extinct.
- 2026-08-28 — Verification: direct `lake env lean` passed; target-only
  `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingSchwarzOddDiagonalCausalPropagatorObstruction`
  passed (`12022/12022`); all five exported theorem axiom audits report only `propext`,
  `Classical.choice`, and `Quot.sound`; umbrella import present. Formal lint reports no finding in
  this module; repository lint remains nonzero only for pre-existing unrelated unreachable modules.
