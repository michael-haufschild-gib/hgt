# Original character mismatch controlled by both transfer losses

- **Stage:** 1-in-progress
- **Parent:** [Selberg conjecturing loop](../../selberg-quarter-conjecturing-loop.md), cycle52.
- **Objective:** Bound the original coherent seam pairing by transfer loss in both its source and radial derivative, connecting the actual seam current to the proved phase-loss Rellich identity.

## Evidence and conjecture

Cycle50-51 source hashes were revalidated unchanged. The previous goal turn made concrete progress:70 new public declarations closed the physical and arithmetic phase-loss Rellich laws. The full Selberg endpoint remains active and unproved.

Current explicit-OR corpus queries for projection mismatch, quadratic domination, bilinear bound, polarization, and golden ratio returned2662 declarations in393 modules; bilinear/quadratic-bound/discriminant/Cauchy-Schwarz returned2120 in818. Counts describe discovery metadata, not all proof bodies read. Inspected the actual character-projector adjoint/orthogonal-corner proofs, ComplexQuadraticPolarization's real polarization/scalar-optimization argument, EventSquarePolarization's finite mixed expansion, and IntegralCauchySchwarz's exact nonnegative-quadratic lemma. Artifacts use `/tmp/selberg_mixed54_`.

For literal upper/lower projectors P,Q, let A(v)=norm(v)^2-norm(QP(v))^2, B=P-Q, a=(Id-P)v, b=(Id-Q)P(v), and phi=(1+sqrt(5))/2. Test the two exact positive identities recorded on the [dilation card](../../selberg-maass-dilation-stress.md). Their proposed consequence is `abs(Re(inner (B(v)) w))^2 <= phi^2*A(v)*A(w)` uniformly in level and both vectors. No angle bound, nonzero-loss condition, or spectral coercivity premise is allowed.

## Proof loop

- [x] Prove both positive square decompositions for the actual finite character projectors.
- [x] Polarize the diagonal bounds and discharge all zero-loss cases through the source quadratic lemma.
- [x] Specialize the mixed estimate to the actual original Maass radial seam derivative.
- [x] Integrate the strengthened physical seam estimate with the exact normalization and original phase Rellich terms.
- [x] Run complete scratch/source/targeted-final/axiom/index/wiring/lint audits with strictly serial foreground Lean commands; record the global lint result separately below.

The full original core–cusp quarter comparison remains the next global target; this card does not assume its conclusion.

## Positive proof and strengthening

Both exact square identities passed the complete Lean scratch. The diagonal absolute bound and real polarization passed next; scaling one argument and applying the corpus's nonnegative-quadratic lemma proves `mismatchPair(v,w)^2 <= phi^2*lossEnergy(v)*lossEnergy(w)`. Zero-loss cases are handled by the same closed quadratic lemma. Its companion Young bound retains every real scaling.

The source specialization now targets an integrated comparison directly with the proved phase Rellich energy. On the modular arc, original mass loss has weight1/y³ and radial derivative loss weight1/y. The physical current is `J=-2*B(F,D_rad F)/y`. Apply the exact Young bound at scale `phi*y²*t`; dividing by the proved positive factor gives a nonnegative quadratic `massLoss + t*J + phi²*y²*radialLoss*t²`. Use y²<=1 and sum both reflected arc points. Source continuity justifies integration, and the same quadratic lemma should yield `(integral J/2)^2 <= (phi²/4)*massPhaseBoundary*radialPhaseBoundary`. This would connect the coherent core–cusp balance to the actual radial phase Rellich law without discarding the original mass factor or inserting a trace estimate.

## Complete original-source theorem

The full source specialization and integrated comparison passed the complete scratch. The actual paired normal current equals `(-2/y)*mismatchPair(F,D_rad F)`. Exact source regularity proves both phase-loss densities continuous on the full arc and all needed integrals exist. Summing the two reflected pointwise quadratics retains the exact factor2 on the paired current; integration and the same nonnegative-quadratic lemma give

`(integral pairedArcCurrent / 2)^2 <= (phi^2/4)*massPhaseBoundary*radialPhaseBoundary`.

The source phase Rellich identity then proves

`seamResponse^2 + (phi^2/4)*lambda*massPhaseBoundary^2 <= (phi^2/4)*massPhaseBoundary*(angularPhaseBoundary+sidePhaseFlux+topPhaseFlux)`.

The exact core–cusp identity substitutes the entire original quarter balance for seamResponse, including coreQuarter, the residue Fourier boundary form, complete Bessel square tails, and the spectral core/tail mass. No physical boundary term, angular derivative, or zero-loss case was removed. New source [SelbergMaassMixedLoss](../../../../../../formal/GaloisForLFunctions/RHTower/SelbergMaassMixedLoss.lean) contains395 lines and26 public declarations. Full scratch and exact source passed cleanly; the targeted final build and all26 axiom/coverage/wiring audits also passed.

The next global comparison must control the actual angular-plus-side/top phase stress by the positive terms in the full core–cusp balance. The newly retained positive spectral phase mass is part of that comparison. The uniform quarter endpoint is not assumed and remains unproved.

## Final audit

`lake env lean` complete scratch and exact source checks passed cleanly. `lake build GaloisForLFunctions.RHTower.SelbergMaassMixedLoss` rebuilt only this module (6.9s). Post-build `#print axioms` covered every one of the26 public declarations, with only standard `propext`, `Classical.choice`, and `Quot.sound`. Source SHA256 is unchanged. Every public declaration appears in the exact module's research results and generated API rows; umbrella import occurs exactly once. Artifacts are `/tmp/selberg_mixed54_manifest.json`, `/tmp/selberg_mixed54_audit.json`, and corresponding names/scratch/source/build/axiom/index/coverage/lint logs.

Repository lint ran and currently reports only two unrelated concurrent HTGeometry additions awaiting umbrella wiring: `GomesPolynomialExponentialIntegrability` and `GomesPolynomialExponentialTails`. No foreign source or umbrella was changed. The earlier pair of unrelated lint failures from cycle51 is historical. All task-owned Lean/check/build handles are terminal; this turn used strictly serial foreground Lean commands. No full or umbrella build, numerical experiment, added axiom, commit, or push. The full Selberg endpoint remains active and unproved.

## Next original-source conjecture

A further explicit-OR stress-flux/boundary-coercivity/Robin/impedance search retrieved242 declarations in44 modules. Inspected SuzukiCausalWeilRobinGreenIdentity's actual algebraic boundary–tail reconstruction (not an analytic Maass result) and the original character projector's exact block commutation proof. The useful requirement is to identify the full physical boundary record before trying to estimate it.

Next derive the complete phase stress tensor as the original stress of F minus that of its fixed inversion transfer, including the mixed horizontal/vertical derivative pairing. Real polarization of the proved exact phase-energy average should give the mixed term. Since the transfer's input is an actual upper-character projection, complete upper-block motion acts by its proved unit-modulus phase; this should make the full aggregate stress unit-periodic. At the vertical sides, the dilation factors differ by exactly one, so the complete sidePhaseFlux should reduce to the integral of the actual horizontal phase stress. Check this exact identity, then connect the side/top record to original cusp Fourier and Bessel data. No side sign or spectral coercivity is to be assumed.

## Cycle53 continuation completed

The complete phase stress, its unit-translation symmetry, and the exact physical side/top flux formulas are now proved. They have been substituted into the full original core–cusp bound. All28 declarations in the new module passed the full source/build/axiom/coverage/wiring/index/lint audit; the latest repository lint is green, so the prior unrelated wiring-error snapshot above is historical. [Complete proof and next arithmetic kernel estimate](../../selberg-phase-stress-side-flux.md). The full quarter endpoint remains unproved.
