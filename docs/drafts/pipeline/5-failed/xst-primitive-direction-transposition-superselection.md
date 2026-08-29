# XST primitive-direction transposition superselection

Status: `[PROVED HERE] [PROVED IN LEAN] [CORPUS-NOVEL NO-GO] [POSITIVE SURVIVOR FORMALIZED] [TARGETED EXTERNAL NO-MATCH] [GLOBAL NOVELTY UNVERIFIED]`

## Corpus origin

Corpus research before conjecturing found:

- `xiCTaylorThetaTailCore_current_eq_tsum_primitiveDirectionGlobalJoint`: exact decomposition of the RH-bearing core current into complete coprime-direction packets;
- `thetaCuspPrimitiveRayCorePolarKernel_one_sub` and
  `thetaCuspPrimitiveRayAngularSeamIntegrand_one_sub`: transposition is angular reflection, and the unresolved interior seam is reflection invariant rather than anti-invariant;
- `thetaCuspPrimitiveRayCorePairCurrent_swap`: the underlying Hermitian current is symmetric;
- `thetaCuspPrimitiveRayShellBirth`: shell birth is favorable, but individual endpoint currents later change sign.

Exact duplicate searches for complete-direction transpose invariance and transpose-orbit linear
classification returned no theorem.

## Frozen conjecture C-XST-PRT

Let `qᵀ` exchange the two positive coprime coordinates of a primitive direction, and let

`I(q;d,z) = ∫ thetaCuspPrimitiveDirectionCoreIntegrand q d z`

over the positive-quadrant product measure. Then:

1. `q ↦ qᵀ` is an involution;
2. `I(qᵀ;d,z) = I(q;d,z)`;
3. every scalar transpose-orbit aggregate satisfies
   `a I(q) + b I(qᵀ) = (a+b) I(q)`;
4. hence equal-weight pairing doubles the packet and opposite-weight pairing deletes it. No
   transpose-only mixing can create analytic cancellation while retaining the canonical symmetric
   source contribution.

The strongest positive survivor is the exact one-dimensional quotient law: on each transpose
orbit, all source-visible linear information factors through coefficient sum `a+b`; the
antisymmetric line is source-null.

## Paper proof plan

Define the transpose on the coprime subtype using symmetry of `PNat.Coprime`. Prove density
covariance by commuting each common-scale atom product. Combine it with the symmetric core-pair
current. Exchange the two integration variables under the identical restricted-volume factors.
The orbit law is then linear algebra. Transfer the same equality to the shell-born global-joint
radial packet through the existing exact direction bridge.

## Exact RH chain and consequence

The candidate chain being tested was:

transpose-paired primitive-ray cancellation
→ sublinear bound for the global primitive-direction sum
→ `XiCTaylorThetaTailCoreCurrentSublinearUpper D`
→ `riemannHypothesis_of_xiCTaylorThetaTailCoreCurrentSublinearUpper`
→ RH.

If C-XST-PRT is proved, this chain is killed at its first arrow: canonical transposed rays reinforce.
Any surviving XST proof must mix distinct transpose orbits or use a genuinely signed
infinite-support incidence before the primitive-direction sum. This does not prove RH.

## Result

C-XST-PRT is proved in
`GaloisForLFunctions.RHTower.XiCTaylorPrimitiveDirectionTranspositionSuperselection`.

Main theorems:

- `integral_thetaCuspPrimitiveDirectionCoreIntegrand_transpose` proves invariance of the complete
  common-scale direction integral under transposition;
- `xiCTaylorThetaTailPrimitiveDirectionCurrent_orbitMix_eq_zero_iff` classifies every real scalar
  two-orbit cancellation exactly;
- `xiCTaylorThetaTailPrimitiveDirectionCurrent_add_transpose` proves canonical equal-weight
  reinforcement;
- `xiCTaylorThetaTailPrimitiveDirectionCurrent_sub_transpose` proves the antisymmetric channel is
  source-null;
- `integral_thetaCuspPrimitiveDirectionGlobalJoint_transpose` transports invariance to the full
  shell-born reflected radial packet.

The proof uses absolute integrability of each complete ray and Fubini under the identical positive
half-line measures; it does not estimate or separate endpoint and interior seam terms.

## Positive survivor and route decision

The transpose orbit has an exact one-dimensional source-visible quotient: coefficients `(a,b)`
are observed only through `a+b`. The antisymmetric line is its full kernel. Therefore a producer
that keeps canonical positive source mass cannot obtain cancellation inside a transpose orbit.

Route decision: retire transpose-pair cancellation. Continue XST only through genuinely signed
mixing across distinct transpose orbits, or through the already-identified infinite-support
reflection polarization before primitive-direction reassembly.

## Novelty audit

Corpus searches through 2026-08-29 found the pointwise angular covariance and global primitive-ray
reassembly, but no theorem integrating them into complete-direction invariance or classifying all
transpose-orbit scalar mixing.

Targeted external searches through 2026-08-29 found related work on Xi Jensen/Taylor polynomials,
Xi Taylor coefficients, theta-kernel approximations, and semilocal operator approaches, but no
coprime primitive-direction theta-current decomposition or transpose-orbit classification:

- https://arxiv.org/abs/1910.01227
- https://arxiv.org/abs/1907.08984
- https://arxiv.org/abs/1502.06844
- https://arxiv.org/abs/1910.14368

This supports only a targeted no-match claim, not global novelty.

## Lean audit

- direct `lake env lean` check: passed;
- exact leaf build: `9098/9098`, passed;
- printed axioms for complete-direction invariance, orbit classification, and radial transport:
  `[propext, Classical.choice, Quot.sound]` only;
- formal lint: no module-specific error; repository retains unrelated pre-existing umbrella
  reachability failures and large-file warnings;
- umbrella import wired; full umbrella build intentionally not run.
