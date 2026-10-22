# Actual Maass dilation stress and physical boundary energy

- **Stage:** 1-in-progress
- **Parent:** [Selberg conjecturing loop](../../selberg-quarter-conjecturing-loop.md), cycle50.
- **Goal:** Derive a source-based boundary-to-bulk energy comparison using the original Maass equation, complete physical derivatives, and actual modular seams.

## Corpus-derived conjecture

Previous turn is progress: the core–cusp gluing module and its integrated arithmetic seam bound were completed and audited; its source hash was revalidated unchanged. The full quarter bound remains the objective.

Explicit OR searches for trace inequality, Rellich, boundary energy, ground-state transform, and Dirichlet-to-Neumann retrieved145 declarations in52 modules; virial/Pohozaev/boundary trace/stress tensor retrieved429 in78; stress/Pohozaev/conformal current retrieved128 in17. Artifacts use `/tmp/selberg_bulk52_`. These are matching metadata counts, not claims that every proof body was read. Inspected the actual Sturm–Liouville virial and Sturm-energy product-rule proofs, oscillator windowed virial square expansion, and existing cusp Hardy/source pair-phase identities.

For an original scalar Maass observation u with `Delta u = -lambda*u/y²`, define the physical symmetric stress tensor

`T_ij = 2 Re(D_i u * conjugate(D_j u)) - delta_ij*(|grad u|²-lambda*|u|²/y²)`.

Conjecture: its divergence is `(0,-2*lambda*|u|²/y³)`. Contracting with the actual dilation vector `(x,y)` then cancels this inverse-square forcing against the tensor trace, so the dilation current has zero planar divergence. This should give a boundary energy identity retaining radial and angular derivative squares on the actual modular arc. Every derivative, potential, and observation must be the original source; no assumed stress conservation or trace inequality is allowed.

## Proof loop

- [x] Derive exact original stress derivatives and dilation conservation in scratch.
- [x] Identify the exact circular normal-density term, preserving radial/angular energy and potential mass.
- [x] Integrate the full physical current and split the complete radial/angular/mass boundary energy.
- [x] Prove the original exceptional-source radial-energy bound at unit height.
- [ ] Derive the uniform quarter comparison with the full core–cusp bulk energy.
- [x] Audit all45 public declarations, source hashes, unique umbrella wiring, API/search coverage, and repository lint; record the build scheduling deviation below.

The stress identity is a proposed additional source constraint, not an assumed spectral gap. Keep the cycle49 core–cusp identity and all original mode-square terms intact.

## Positive strengthening

The exact horizontal stress conservation, vertical inverse-square forcing, and dilation conservation have passed scratch. The circular normal-density flux is now identified on paper and in scratch with minus `(radialEnergy-angularEnergy+lambda*mass/y²)/y`. The actual angular energy remains in the identity. Continuously differentiable source stresses provide the regularity needed to integrate these equations.

The next concrete integration uses both actual Fubini descriptions of the compact modular core. A general C¹ current requires a Green formula that retains its side jump; the older scalar-potential formula cancels that jump under a separate matching condition. We are deriving the full side-plus-top-plus-curved-arc formula directly, then instantiating it on the actual dilation current. No side cancellation is assumed.

The complete general-current Green formula has now passed scratch. Horizontal Fubini separates a full side-jump integral from the lower circular slivers; the actual circular substitution maps those slivers to the paired half-arc. Vertical Fubini retains top minus the entire lower boundary. Their sum is the physical divergence integral on ordinary two-dimensional core area. The original stress module and this geometry module are being checked as the two needed dependencies of the actual Maass Rellich specialization.

## Integrated positive theorem

The original full-core identity is now proved in Lean:

`radialBoundary + lambda*massBoundary = angularBoundary + sideFlux(Y) + topFlux(Y)`.

The radial/angular densities are the squared original physical derivatives divided by arc height; mass has the inverse-cube height weight forced by the Maass potential. All integrability follows from the actual source regularity on the entire paired arc. For an exceptional source, positivity of lambda and actual mass yields `radialBoundary <= angularBoundary + sideFlux(1) + topFlux(1)`. Full side and top stresses remain literal source quantities.

The three modules are [stress](../../../../../../formal/GaloisForLFunctions/RHTower/SelbergMaassDilationStress.lean), [general Green](../../../../../../formal/GaloisForLFunctions/RHTower/SelbergModularCurrentGreen.lean), and [Rellich](../../../../../../formal/GaloisForLFunctions/RHTower/SelbergMaassDilationRellich.lean). They contain45 public declarations. Complete scratch/source checks and targeted final builds passed. The Rellich audit was started before the Green handle had been confirmed terminal, causing a duplicate needed-dependency build; both builds completed and all handles then returned terminal. No stale task-owned worker remained. This scheduling deviation is recorded rather than claimed as serial compliance. Post-build axiom/index/lint audits follow.

## Next conjecture: physical phase-loss Rellich identity

The broad explicit-OR corpus query for phase energy, Rellich, quadratic current, and commutator returned2526 matching declarations in637 modules (`/tmp/selberg_bulk52_phase_corpus.json`). Inspected complete finite-phase incidence identities from `PauliUniformCommutatorEnergy`, mixed finite current expansion from `EulerDeletionMixedCurrentGram`, and the actual original-source `triple_displacement_energy`, fixed-observation derivative and phase-gradient proofs. These suggest keeping the complete finite family before taking any worst-channel estimate.

Construct the actual fixed observations `coordinate_q o (Id - tripleWeight(a,b,c)*regularUnitary(deckTriple(a,b,c)))`. Their derivatives are the same observations of the physical source derivative. The complete normalized squared observation sum equals inversion-transfer loss, both for source mass and each physical direction. Summing the proved Rellich identities should therefore produce a radial/angular/mass law for the literal arithmetic loss. All side/top terms must be retained and identified as the corresponding complete phase-stress sums. No new PDE, sign, side cancellation, or spectral bound is assumed.

## Completed cycle50 audit

All45 public declarations passed post-build `#print axioms` with only `propext`, `Classical.choice`, and `Quot.sound`. Source hashes match their pre-audit manifest. Exact-module search covers every public declaration; umbrella imports occur once; generated API includes all names; repository formal lint passed. The final Rellich source has227 lines. Artifacts: `/tmp/selberg_bulk52_manifest.json`, `/tmp/selberg_bulk52_audit.json`, and matching source/build/axiom/index/coverage/lint logs. No full or umbrella build, numerical experiment, commit, or push. The full uniform quarter comparison remains unproved.

## Cycle51 phase-loss strengthening

The complete phase construction and genuine-integral strengthening have passed the full scratch and exact source checks. New source: [SelbergMaassPhaseRellich](../../../../../../formal/GaloisForLFunctions/RHTower/SelbergMaassPhaseRellich.lean),276 lines,25 public declarations. `phaseReadout` is the literal coordinate of `Id-tripleMotion`; `phaseAverage_norm` proves exact normalization against inversion-transfer loss. Physical differentiation commutes with every fixed observation. Finite summation of all source Rellich identities proves `radialPhaseBoundary + lambda*massPhaseBoundary = angularPhaseBoundary + sidePhaseFlux + topPhaseFlux`. Actual source continuity justifies exchanging the complete phase sum and integrals, so all three terms are the genuine radial/angular/mass transfer-loss integrals. `phase_loss_rellich_integral` records the full identity at unit height. Positive exceptional mass yields the radial phase-energy estimate. The final targeted build rebuilt only this module (5.2s). All25 public declarations passed post-build standard-axiom, unchanged-source-hash, API/search, and unique-wiring audits. Global lint currently reports only two concurrently added HTGeometry modules as unreachable; this is being rechecked after the other source changes settle.

A further explicit-OR search for two projections, mixed Gram, operator angle, and golden ratio returned47 declarations in25 modules (`/tmp/selberg_phase53_next_corpus.json`). The entire `HTGeometry.TwoProjectionDeficiency` proof was inspected. Its useful mechanism is retaining both projection energies before Cauchy–Schwarz; its external angle hypothesis is not imported. The next source-derived target is a bilinear mismatch bound using transfer loss in both arguments, so the seam derivative uses precisely the newly controlled radial phase energy.

## Next precise mixed-loss conjecture

Write `P=upperProjection(s)`, `Q=lowerProjection(-r)`, `A(v)=norm(v)^2-norm(Q(P(v)))^2`, `B=P-Q`, `a=(Id-P)v`, and `b=(Id-Q)P(v)`. The corpus already proves `A(v)=norm(a)^2+norm(b)^2`. The candidate sharper positive forms are

`A(v) + Re(inner (B(v)) v) = norm((Id-Q)v)^2 + norm(b)^2`,

and, with `phi=(1+sqrt(5))/2`,

`phi*A(v) - Re(inner (B(v)) v) = (phi-1)*norm(phi*a-b)^2 + norm(Q(a))^2`.

These square expansions suggest a uniform mixed estimate `abs(Re(inner (B(v)) w))^2 <= phi^2*A(v)*A(w)`, proved by polarization and scalar optimization after the actual projection identities are discharged. This would replace the full source derivative norm in the coherent seam bound by its own transfer-loss energy, precisely the quantity in the new radial phase Rellich law. Next loop: check the exact square expansions on paper and in Lean, then prove the mixed bound and specialize to the original radial source derivative. No angle or spectral assumption is proposed. Cycle52 proved both exact square identities, the mixed estimate, and its full original-source integrated/core–cusp strengthening. [Complete proof and current phase-stress target](../../selberg-character-mixed-loss.md). The full quarter comparison remains unproved.

## Cycle51 final audit status

The complete phase proof, exact source, and final single-module build passed; only `SelbergMaassPhaseRellich` rebuilt (5.2s). All25 public declarations passed post-build axiom checks using only standard `propext`, `Classical.choice`, and `Quot.sound`; source hash is unchanged. Exact-module research/API coverage and unique umbrella wiring passed. Artifacts: `/tmp/selberg_phase53_manifest.json`, `/tmp/selberg_phase53_audit.json`, and matching scratch/source/build/axiom/index/coverage/lint logs. These checks, together with cycle50, cover70 public declarations.

Final global lint currently fails only because concurrent HTGeometry additions `GomesDilatonDensityShape` and `GomesDilatonMeasureReconstruction` are not yet reachable from their own umbrella. They are outside this task's write scope; no foreign source or umbrella was changed. Cycle50's earlier global lint passed. All task-owned Lean handles are terminal, and the final process scan found no remaining task-owned worker. Cycle51 obeyed strictly serial Lean execution. No full or umbrella build, numerical experiment, commit, or push. The full Selberg endpoint remains active and unproved.
