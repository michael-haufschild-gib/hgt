# CHMD arithmetic obstruction loop

## Objective

Remove a hard arithmetic obstruction in CHMD by an unconditional structural theorem.
No estimates, RH receivers, spectral results, numerical experiments, or external search.

## Plan

1. Establish the current arithmetic frontier from Lean declarations and corpus search.
2. Form exact conjectures, attack them, and retain the mathematical lessons of failures.
3. Complete a dependency-closed proof before formalizing a surviving contribution.
4. Audit the leaf with `lake env lean`, inspect axioms, wire the umbrella, and run formal lint.

## Verified starting point

`CHMDPrimeChainSourceFactorization` gives a complete positive prime-chain variance
factorization of crossing jumps. `CHMDPrimeDivisorCuts` retains the negative cosh
mass in the full source identity. `CHMDReflectedPrimeSingularPart` excludes local
positive-jump absorption: reflected prime lines are singular relative to the
positive forward-prime and archimedean measures.

## Active investigation

Determine which arithmetic compatibility is lost when the complete prime-chain
source is split into independent nonnegative pieces, and whether an exact
recombination removes that loss. No new theorem claimed yet.

## Conjecture ledger

1. **Independent prime-chain centering absorbs the remaining source mass.**
   Rejected as an unsupported inference: the exact source identity still has
   `-phiDoobCoshMass`; centering within a chain does not implement the global
   polar constraint. The existing `chainVariance_zero_iff` already supplies
   the exact chainwise rigidity. No new sign follows.
2. **Crossing-prime nullspace rigidity without compact support is sufficient.**
   Rejected on significance grounds. Two incommensurable prime periods could
   remove the compact-support hypothesis, but injectivity supplies no
   comparison with the negative mass. Do not spend the task formalizing this.
3. **Use the pointwise theta harmonic identity to cancel the mass.**
   Already present in `CHMDThetaHarmonicIdentity.theta_harmonic_identity`.
   Substitution recovers the signed original Weil operator. It does not
   create positivity. The complete prime source must retain joint arithmetic
   compatibility rather than being treated as independent positive rates.

## Wider corpus leads

`ThetaPrimeShiftNoetherIntegrated` gives a positive complete prime-link boundary
charge and exact prime–Gamma exchange on every half-line. Its whole-line
exchange vanishes, so it does not alone orient arbitrary signed tests.
`ThetaCuspKernelLogConcavity` proves strict global log-concavity; order-two
positivity is available and must not be mistaken for an all-order theorem.
`ThetaCuspLikelihoodPrimeSquareSignWall` shows that prime-square diagonal mass
reverses a prime-shell current near the boundary. Any primewise extension
must account for composite arithmetic compatibility.

## Constraints and workspace

Existing modified and untracked files predate this work and must be preserved.
The task-specific card and any new arithmetic leaf are this task's write scope;
the umbrella receives only the new leaf's import when audited.
`update_plan` and `multi_tool_use.parallel` are unavailable in this session;
this card tracks the plan and independent reads use the available parallel API.
