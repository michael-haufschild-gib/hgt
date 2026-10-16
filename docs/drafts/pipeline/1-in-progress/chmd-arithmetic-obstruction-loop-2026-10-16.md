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

## Further conjecture attacks

### Mixed cuts versus translated sources

The translated two-source Ward current is not the mixed-cut kernel of the original form. Translating its two theta factors separately changes the physical prime displacement. A tail identity for that current therefore does not settle mixed-cut positivity. The existing `ThetaPrimeGammaCutEnergy` already proves the diagonal cut identity; `ThetaTailTwoPointPositivity` already handles the separate first-moment kernel at two nodes. Neither is a new contribution here.

### Global branch subtraction

Rejected as a frontier contribution: `CHMDKleinGordonInverseLightCone` already removes the Bessel tail on the actual wave and restores its meromorphic arithmetic continuation. Reassembling the local logarithmic branch terms would duplicate that mechanism unless a new arithmetic consequence were established. None was established.

### Connectivity of individual divisor cuts

The conjecture that every nonempty divisor cut is connected is false already for distinct primes p < q and log p < u < log q. The only crossing prime-power edges of pq are 1--q and p--pq. More generally, if p is prime, p does not divide M, and M < exp u < p, every divisor of pM is either d or pd for d dividing M, and the crossing graph consists of the disjoint edges d--pd. Thus even arbitrarily large cut nullspaces occur. This is a paper-level counterexample, not a new Lean theorem or a claimed contribution. Existing global compact-source rigidity uses compatibility across indices and does not contradict it.

### One-sided Euler conjugation

A finite divisor-incidence calculation suggests an exact one-sided normal form. Write Z(a,b) = 1 when a divides b, M = Z inverse, and D(a,a) = log a on a divisor-closed finite set. Then (Z D M)(a,b) equals log a on the diagonal and Lambda(b/a) on a proper divisible pair. For r = b/a its coefficient is the divisor sum of log(ad) mu(r/d). The reverse conjugation M D Z instead has negative Lambda off the diagonal. This calculation alone is not a congruence of the reflected signed form.

The full source-level inverse also has a genuine boundary obstruction: `ThetaPrimeDeletionCausalMode` proves local convergence of cofinal deletion while the negative-cusp boundary trace does not commute with that limit. `ThetaPrimeDeletionTerminalCusp` identifies the signed terminal word. Therefore a one-sided conjugacy cannot be promoted silently to the complete CHMD form. No qualifying obstruction removal has been obtained from it.

### Active next conjecture: retain the mixed-prime crossing terms

Investigate the half-line crossing correction of the complete Euler/Mobius translation action before reducing it to its logarithmic derivative. For finite translation sums, the forward/reflected commutator is a crossing Gram integral whose square retains pairs of arithmetic labels. The question is whether the literal theta source equation identifies the resulting full mixed-prime correction with the missing cosh contribution, or leaves an explicit nonzero residual. Establish the exact identity first; reject the candidate if it only creates another sufficient-positivity receiver or changes the source form.

No new Lean module, compiler audit, or qualifying theorem has been produced. Goal remains active. Preserve all pre-existing worktree changes.

#### Crossing-Gram admission check

For a finite sum of forward half-line translations, the boundary commutator expands into the square of the reflected crossing sum. With critical Euler coefficients the unsquared arithmetic sum has a growing boundary component, so the finite identity alone does not justify an infinite Gram integral. The completed Gamma/pole compensation must be included before taking that limit. `MobiusGammaHankelMultiplierCollapse` additionally rules out silently extending coefficientwise Mobius multiplication to the wrong additive completion. Its theorem concerns that completion; it is not a no-go for all source-level inversion.

The exact completed crossing identity, its admission on the original CHMD source class, and its relation to the negative cosh mass remain unproved in this investigation. Next work must attack that literal identity, not infer the desired sign from an auxiliary positive Gram.
