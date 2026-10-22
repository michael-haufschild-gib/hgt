# Abstract aperture Morse perturbation and congruence survivor

- **ID:** `ccm-aperture-morse-abstract-exhaustion-survivor`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (Lean), `[POSITIVE SURVIVOR] [BRIDGE]`
- **Source:** failed `ccm-aperture-morse-hardymodel-index-exhaustion-law.md`
- **Statement:** Finite negative subspaces survive coercivity-controlled perturbations, transport
  through linear equivalences, and obey exact finite/cofinal supremum laws; screw packets satisfy the
  stated rank-one and conjugate-pair polarization identities.

## Goal

Bank every exact unconditional lemma exposed by aperture attempt without asserting that ordinary screw
features count analytic zero multiplicity or identify the actual Xi aperture index.

## Exact survivor

Lean proves:

- `screwFeature gamma 0 = 0`, hence every packet has zero base row and column;
- a rank-one feature Gram form is a squared modulus and nonnegative;
- the conjugate-pair packet is algebraically one plus-square minus one minus-square;
- a `k`-dimensional form bounded by `-delta*norm(x)^2` remains negative after perturbation error
  `epsilon*norm(x)^2` whenever `epsilon<delta`;
- real-linear equivalences transport negative subspaces and preserve dimension in both directions;
- bounded cofinal achievable dimensions have exact supremum, while dimensions of every size are
  unbounded;
- every finite set of points strictly right of `Re s=1/2` admits one positive uniform shift.

The difference-of-squares identity is not promoted to “exactly one negative square” without the
required nondegeneracy and independence statements.

## Gates

- [x] 0 → 1: false multiplicity claim isolated
- [x] 1 → 2: exact algebraic and functional-analytic survivor dependency-closed
- [x] 2 → 3: `RHTower/CCM/CCMApertureMorseExhaustion.lean` built, wired, and axiom-audited with only
  `propext`, `Classical.choice`, and `Quot.sound`
- [ ] 3 → 4: publication packaging unnecessary

## Missing stronger theorem

A multiplicity-exact Xi aperture law needs confluent derivative-jet screw features, proof that their
finite Gram carrier realizes analytic multiplicity, the actual Xi screw-series identification, and both
directions of closed aperture exhaustion. None is assumed here.

## Log

- 2026-08-24 — split exact Lean survivor from false ordinary-feature multiplicity transport.
