# CHMD structural sign conjecture loop

Status: unresolved; no qualifying contribution. Corpus-only research; no external search, numerical experiments,
or novelty audit. Existing concurrent working-tree changes are outside this task.

## Objective

Prove one unconditional structural theorem overcoming a hard CHMD obstacle.
An improved bound, an RH equivalence, or a receiver with an unproved sign premise
does not meet the objective.

## Plan

1. Inspect current CHMD Lean declarations and search the whole Lean corpus for mechanisms.
2. State exact conjectures; attack each for falsity, circularity, and prior corpus coverage.
3. Complete a dependency-closed mathematical proof before formalization.
4. Formalize without unproved premises, computation, or heartbeat increases.
5. Audit the leaf with `lake env lean`, inspect axioms from `/tmp`, run formal lint,
   and wire the finished module into its umbrella without an umbrella build.

## Frontier verified from source

- CHMD converts the actual prime–Gamma functional into a causal Klein–Gordon wave.
- Unrestricted even polar Archimedean positivity is an RH-equivalent target,
  not an available unconditional hypothesis.
- Stage19/20 expose positive and negative hyperbolic packet channels. Completed
  squares and strip restrictions do not discharge their relative sign.
- The working tree changes concurrently. Preserve all changes outside this card.
- `WeilPhiDoobArchimedeanJumpAndHalfLineFolding` gives the exact source identity
  `markovEnergy (Φ v) = archJump(v) + primeJump(v) - coshMass(v²)`.
  Nonnegativity of the two jump energies does not establish the required spectral gap.

## Conjecture ledger

1. **Per-orbit positivity of the completed hyperbolic packet. Rejected.**
   Stage20's two-point difference weight is `2(1 - cos(y u) cosh(y v))`.
   At a full real-phase return, a nonzero imaginary frequency gives a negative real
   weight. Stage15's positive real part of the sech-square weight does not repair
   this. Stage16's reflection identities preserve the real contribution rather
   than cancel it. This observation does not assert an off-line zero exists.

2. **Use the derivative of the positive theta ground state to obtain a positive
   reflected jump kernel. Not established.** The continuous archimedean reflection
   weight is already positive in
   `WeilPhiDoobReflectedKillingPotentialAndDisjointSupportDiagonal`.
   The prime terms involve different loci, `|x-y| = log n` and `x+y = log n`;
   the archimedean monotonicity argument does not compare their atomic measures.
   Therefore source log-concavity alone supplies no proof of the proposed
   reflected-kernel sign. No new no-go theorem is claimed.

3. **Construct negative even polar node tests to control the missing dual sector.
   Already present.** `EvenSectorPoleFreeBlindFarkas` constructs
   `evenPolarMinusTest`; `EvenSectorPoleFreeTwoSidedGrowth` already pays the
   two-sided growth argument. Reimplementing this would not advance the frontier.

4. **Exact spectral synthesis of the causal wave from a short time interval.
   Unproved and insufficient for the requested objective by itself.** A possible
   argument uses Laplace transforms, the locally finite Klein–Gordon pole set,
   and residue extraction. The corpus already has the actual wave's pole and
   growth analysis in `CHMDGrowthPositivityCollapseAndTwoPointCriterion` and
   related restricted-shift density in `WeilWorkDeficitRestrictedXiDensity`.
   A new density statement would still leave the signed quadratic form open;
   it is not being counted as the requested structural sign advance.

No dependency-closed proof of a qualifying new conjecture has been obtained.
In particular, no argument here discharges the negative mass in the exact Doob
identity, or the negative hyperbolic packet channel in CHMD.

## Verification

No new theorem claimed or formalized. No Lean source or umbrella was changed by
this task, and no Lean build was run. The statements above distinguish existing
corpus results, rejected attempts, and unproved ideas.
