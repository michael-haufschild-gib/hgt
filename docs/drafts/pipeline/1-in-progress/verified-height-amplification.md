# Verified-height amplification for a first off-line zeta zero

- **ID:** verified-height-amplification
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** user research prompt; Platt--Trudgian verified-height theorem
- **Statement:** `[CONJECTURE]` There is an explicit `T_1 > T_0`, with
  `T_0 = 3 * 10^12`, for which the published verification below `T_0` plus a
  new non-computational analytic theorem imply that every nontrivial zero
  `rho = beta + i gamma` with `0 < gamma <= T_1` has `beta = 1/2`.

## Goal

Produce an actual strict numerical improvement to the unconditional lower
bound for the ordinate of a possible RH counterexample.  The improvement must
come from a proved analytic implication, not from a new zero enumeration,
rounded endpoint recovery, a conditional hypothesis, or a reformulation of
RH.  It must clear both gates:

- **Novel:** the implication and its proof are not already present in the
  literature or elsewhere in this repository.
- **Significant:** after inserting the published Platt--Trudgian certificate,
  the conclusion gives a strict explicit `T_1 > 3 * 10^12`.

## Gates

- [x] 0 -> 1 in-progress: exact target, falsifiers, and competing attack
  routes are stated.
- [ ] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, explicit
  `T_1`, no open dependency.
- [ ] 2 -> 3 formalized: theorem interface and proof formalized in Lean, with
  the external Platt--Trudgian certificate isolated as an explicit input.
- [ ] 3 -> 4 publication-ready: standalone theorem, novelty audit, proof,
  certificate provenance, and Lean certificate.

## Constraint

Let `Gamma` be the least positive ordinate of an off-critical-line zero, if RH
is false.  The published verification gives `Gamma > T_0`.  A successful
amplifier must prove `Gamma > T_1` from zeta-specific analytic structure.  The
functional equation alone gives a quartet at the same absolute ordinate and
therefore cannot increase `Gamma`.  Fixed finite positivity or moment tests are
also excluded: the repository theorem
`finite-degree-reciprocal-tests-height-limited` proves that sufficiently high
off-line pairs evade every prescribed finite degree.

## Candidate moves

1. `[CONJECTURE]` **Minimal-counterexample descent.**  Construct an adaptive
   explicit-formula kernel attached to a hypothetical first off-line quartet
   at height `Gamma` and prove that its negative contribution forces a second
   off-line zero at ordinate at most `Gamma / lambda`, for some explicit
   `lambda > 1`.  Minimality would then give `Gamma > lambda T_0`.
2. `[CONJECTURE]` **Certificate-to-annulus transfer.**  Turn the verified
   boundary zero count at `T_0` into a zero-free annulus above `T_0` using an
   explicit lower bound for the completed zeta function on the top boundary
   and an upper bound for its logarithmic variation.  This succeeds only if
   the published certificate supplies a nonzero quantitative boundary margin;
   openness without an explicit margin is insufficient.
3. `[CONJECTURE]` **First-defect support theorem.**  Prove that a first
   off-line zero at `Gamma` creates a zeta-specific prime-side witness whose
   spectral support lies strictly below `Gamma`; combine that witness with the
   already verified divisor below `T_0`.  The witness must use the Euler
   product essentially, since functional-equation-symmetric fake functions can
   carry an arbitrarily placed first off-line quartet.
4. `[CONJECTURE]` **Integer zero-density exclusion.**  Derive a localized
   upper bound `< 2` for the number of off-line zeros in a window just above
   `T_0`; functional-equation reflection would make any nonempty upper-half
   off-line set have multiplicity at least two.  The bound must remain uniform
   as `beta` approaches `1/2`, where standard zero-density estimates normally
   lose all pointwise force.

## Immediate attacks

- A functional-equation-only descent is false: the symmetry orbit preserves
  ordinate.
- A standard zero-density estimate cannot exclude an off-line zero
  arbitrarily close to the critical line unless it is uniform at
  `sigma = 1/2` and counts only off-line zeros.
- A finite positivity certificate cannot work uniformly in height by the
  repository's finite-degree blindness theorem.
- A qualitative continuity argument yields only an unspecified extension
  `T_0 + epsilon`; without an explicit lower boundary margin it gives no new
  numerical theorem.
- Recovering a larger endpoint already contained in the published computation
  is `[SEARCH]`, not a new theorem.

## Open core

`[OPEN CORE]` Find and prove a zeta-specific descent or quantitative boundary
margin theorem that converts verification through `T_0` into an explicit
strictly larger verified height without enumerating additional zeros.  If all
four mechanisms fail, prove the sharp no-amplification obstruction under the
available certificate data rather than claiming a numerical advance.

## Log

- 2026-07-10 -- created directly in 1-in-progress for the verified-height
  amplification research program.
