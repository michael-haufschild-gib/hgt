# CHMD: exact algebraic inverse and finite-sample generator classification

Status: FORMALIZED. RH remains unproved; goal active.

Previous turn: progress. Automatic mass-domain admission was proved for vanishing
Xi samples, including the explicit polar image. This turn must reach nonzero
spectral packets and their actual operator action, not repeat that result or the
existing Birman--Schwinger count.

## Corpus evidence

The finite-mass and odd-frontier deep queries returned `partial=false`, no
errors/unfinished stages, and 72,875 inventoried files with none pending.
Compiler metadata remains mostly pending/stale. A shorter hybrid query,
`cardinal generator domain --any --module CHMD --per-module 0`, returned the
previous zero-sample admission and existing cardinal graph frames, but no
finite-support generator formula. Source-text search also found no such
CHMD declaration. These are discovery results, not global absence certificates.

Existing results to reuse:

- `CHMDMassMixedExplicitFormula`: arbitrary-mass mixed explicit formula on
  compact C2 operator-core tests.
- `CHMDCompactSmoothOperatorCore`: the actual maximal arithmetic operator core.
- `CHMDMassSamplingCompleteness`: literal mass Fourier kernels and critical band.
- `CHMDMassPolarCompletion`: exact polar generator image.
- `CHMDUniversalCardinalPairing`, `CHMDTranslatedCardinalDetection`: constructed
  actual cardinal graph vectors, including small translations, with universal
  signed pairings against literal cosine/Fourier samples.
- `CHMDOddSectorCriterion`: RH already equivalent to exclusion of odd bound
  states. Do not add another criterion or sharpen a count as the contribution.

## Exact conjecture and attack

Let R be the actual arithmetic resolvent, L its maximal generator, and F_w(z)
the literal Fourier readout of an arbitrary mass vector w. Suppose a finite set
S of actual zeta-zero carrier points contains every carrier rho where either
F_w(gamma_rho) or F_w(-gamma_rho) is nonzero. No graph-domain assumption is made.

For strip point z define K(c,z) by

`<K(c,z),v> = Re(c F_v(z))`;

explicitly `K(c,z)=Re(c) k_z^re - Im(c) k_z^im`, with the existing literal L2
Fourier kernels. Define

`B_S(w) = sum_{rho in S} (m_rho/2) *
  [K(F_w(gamma_rho),-gamma_rho) + K(F_w(-gamma_rho),gamma_rho)] + b_polar(w)`.

Conjecture: `R(2w+B_S(w))=w`; consequently w belongs to D(L),
`Lw=w+B_S(w)`, and its actual full graph lift has signed energy
`<B_S(w),w>`. The formula is independent of any redundant zero support.
The finite sum retains actual zeta multiplicities and all original prime jumps.

Preliminary attack verdict: SURVIVES PRELIMINARY ATTACK. No estimate, RH
equivalence, or assumed operator-domain bridge is the proposed output. The
stronger full infinite-series assertion is not inferred from this finite case.
Nonvacuous applications must compute generator images of the already constructed
cardinal vectors and their translated detectors, including both Fourier phases.
No external novelty audit is performed, as explicitly instructed by the user.

## Dependency-closed paper proof

1. The existing strip kernels represent real and imaginary parts of every
   mass readout. Real bilinearity proves the displayed formula for K(c,z).
2. Evaluate the existing operator-norm-convergent mixed formula at w. Terms
   outside S vanish exactly. The finite remaining terms, and the already
   identified polar term, give `<(L-1)v,w>=<B_S(w),v>` for each compact C2 test v.
3. Approximate any u in D(L) by the proved compact C2 operator core. Both inner
   products converge in the mass norm, giving the same identity for u.
4. Set u=Rz. Since L(Rz)=z-Rz and R is symmetric, the identity gives
   `<w-R(2w+B_S(w)),z>=0` for every z. Therefore `R(2w+B_S(w))=w`.
   This is an explicit range witness for maximal-domain admission. The
   generator definition then gives `Lw=w+B_S(w)`.
5. The actual graph lift is `rieszLift(2w+B_S(w))`. Its defining Riesz equation
   and the source identity give signed pairing `<B_S(w),source(q)>` for every
   graph q, hence the exact signed energy at q equal to the lift.
6. For a known cardinal graph vector, its universal pairing is already a
   mass-continuous literal sample. The same Riesz identity immediately gives
   its actual operator image as the corresponding weighted Fourier kernel.
   Translated frames use the explicit two exponential coefficients in
   `shiftedCosineReadout`, so the construction covers both Fourier directions.

No open analytic input remains in this finite-support argument. Exclusion of
primitive bound states and infinite cardinal synthesis remain separate open
questions; this contribution must not claim either.

## Implementation and validation plan

1. Prove weak compact-test representation gives the explicit resolvent witness.
2. Construct literal finite-sample image, prove exact pairing, domain/action,
   graph lift, energy, and support independence.
3. Prove actual cardinal and translated-cardinal operator action; instantiate
   an unconditional nonzero actual cardinal vector.
4. Targeted foreground builds only, one owned Lean process at a time. Final
   direct checks of every affected leaf, all-declaration axiom audit, API probes
   in /tmp, umbrella wiring, index/lint, and owned scratch cleanup.

## Stronger synthesis conjecture exposed by the operator action

The first four leaves now build: `CHMDMassWeakGenerator`,
`CHMDMassWeightedKernels`, `CHMDFiniteSampleGenerator`, and
`CHMDCardinalOperatorAction`. They provide finite-support admission, exact
energy, all cardinal operator images, and translated detector images. Treat
this as an intermediate operator bridge, then close its algebraic range.

Let V_fin be all mass vectors with finite Xi-sample support. The stronger claim
is the exact range identity

`(L-1)(V_fin) = massSamplingSpan`,

where the right side is the algebraic span of the actual real/imaginary Fourier
kernels at Xi zeros and the two poles. Equivalently, every b in that algebraic
span has a unique w in V_fin orthogonal to the critical band with
`R(2w+b)=w`. This constructs the inverse on the entire algebraic sampling space,
not just selected individual packets. No bounded inverse or infinite synthesis
is asserted.

Paper proof:

1. Finite-support vectors form a real subspace (unions of finite supports under
   addition). Define their signed images by the explicit resolvent relation.
   The proved finite formula puts every such image in massSamplingSpan.
2. Translated cardinal sources retain finite orbit support: their Fourier
   samples are the old cardinal values multiplied by exp(i*z*t). Their proved
   operator images are cardinalOrbitMass(a) times the real/imaginary phase
   kernels. This positive mass can be divided out, so every phase kernel lies
   in the finite-support image space.
3. For fixed a, all phase kernels lie in the span of four literal kernels at
   a and -a. Their own span is therefore finite-dimensional and closed. A vector
   orthogonal to every phase kernel has
   exp(-i*a*t)F(a)+exp(i*a*t)F(-a)=0 throughout the existing small shift interval.
   The already proved exponential-pair separation gives F(a)=F(-a)=0. Double
   orthogonal-complement duality now puts all four literal kernels in the
   phase span itself, not merely its closure. This is the finite-dimensional
   step that avoids an unjustified closed-range assumption for L-1.
4. Negative-real-part zeros reduce to their negatives. The two polar real
   kernels are linear combinations of the signed images of the actual ground
   and odd polar sources; polar imaginary kernels vanish. Hence every generator
   of massSamplingSpan is an actual finite-support signed image.
5. Given a preimage, remove its critical projection. This preserves every
   sample, hence finite support, and preserves its signed image. Two reduced
   preimages differ by an element satisfying Rv=v/2; it lies both in the critical
   band and its orthogonal complement, and is zero. This proves existence and
   uniqueness without assuming any spectral series converges.

Two further deep corpus searches (full-orbit synthesis; finite-kernel rigidity)
completed without partial results or errors. They did not return this CHMD
range identity. The finite-exponential rigidity idea has no usable unconditional
source theorem yet; multiplicities prevent importing full-divisor rigidity from
mere zero values. It is not used in the proof above.

The range proof also forces the converse classification: for every u in the
actual maximal domain, `(L-1)u` belongs to the algebraic sampling span if and
only if u has finite Xi-sample support. For the reverse implication, choose the
constructed finite-support preimage with the same forcing. Their difference is
critical by the resolvent equation, so it has zero samples and cannot change
the finite support. Consequently uniqueness of the reduced inverse holds among
all maximal-domain vectors, without a finite-support restriction on competitors.
This stronger statement uses the same audited corpus ingredients and has a
dependency-closed paper proof; it is included in the capstone closure.

## Final result and audit

Seven leaves, 1,083 lines and 104 declarations, all imported exactly once by
`GaloisForLFunctions/RHTower.lean`:

- `CHMDMassWeakGenerator`: compact-core weak identities give actual resolvent
  preimages and maximal-domain admission (8 declarations).
- `CHMDMassWeightedKernels`: literal mass kernels for complex sample weights
  and translated cosine phases (12).
- `CHMDFiniteSampleGenerator`: arbitrary finite-support mass sources belong to
  the maximal domain, with exact full signed image and divisor energy (18).
- `CHMDCardinalOperatorAction`: actual cardinal and translated-cardinal
  operator action, and an unconditional positive cardinal packet (22).
- `CHMDFiniteSampleRange`: finite-sample images form a submodule; translated
  phase kernels are actual members (16).
- `CHMDPhaseKernelSynthesis`: finite-dimensional phase separation puts every
  literal Xi sampling kernel in that image submodule (13).
- `CHMDAlgebraicSpectralInverse`: exact range equality, source classification,
  and unique reduced inverse among all maximal-domain vectors (15).

The capstone statements are `finiteSampleImageSpace_eq_samplingSpan`,
`finite_sample_generator_image_iff`, and
`exists_unique_reduced_generator_inverse`. The second quantifies over the
actual maximal domain; the third requires only that the forcing vector belong
to the stated algebraic sampling span. No RH, zero simplicity, finite number
of off-line zeros, closed range, or convergent infinite expansion is assumed.

All seven targeted `lake --old build` checks passed. Final plain `lake env lean`
checks of all seven leaves exited 0 with empty logs. Axiom audits covered every
one of the 104 declarations; only `propext`, `Classical.choice`, and `Quot.sound`
occurred. Toolchain API probes passed. The index refresh and authoritative
`scripts/formal_tools.py lint --check-generated` both exited 0. `git diff --check`
passed. No full or umbrella build, heartbeat increase, numerical experiment,
external search, commit, or push was performed.
All 34 owned temporary search, proof-probe, and audit files were deleted and
their absence verified; all owned process handles are terminal.

The user's Birman--Schwinger pointer was checked again with the corpus tool.
`orthonormal_primitive_bound_states_le` is already at
`CHMDBirmanSchwingerBound.lean:471`; its finite-off-line-zero hypothesis and
`k <= 2 * offLineZeros.ncard` conclusion are explicit. The negative compact-test
index argument is at line 382. These existing results are not reproved here.
The broad hybrid query returned useful hits but was partial, with interrupted
text/source retrieval; coverage was 72,890/72,890 inventoried files. An exact
lexical query returned the counting theorem. The six earlier discovery queries
all completed without partial results or errors; compiler metadata still does
not certify global absence or applicability.

This closes exact finite-support operator inversion, rather than only individual
cardinal graph admission. It does not exclude primitive bound states or supply
an infinite cardinal expansion. Those remain the RH-facing frontier. External
scientific novelty was not assessed, following the user's explicit restriction.

SHA256 of the audited sources:

```
CHMDMassWeakGenerator ee2a8ebef54cab58565e8155048a04435216f6aee89e5e60fe98a5b59c5a78f3
CHMDMassWeightedKernels edf445ebd66d469c21dd7d802c9f1396b90ef1ad62c23a3c53d72e1c86805288
CHMDFiniteSampleGenerator 0dcafe09ada4440a25a132016e60da6a1c65047f1c9b6ee3c9e471dc8f4fc657
CHMDCardinalOperatorAction dcd20e4f0cb98c74fb070eb525164ba8463fb52edad0fd847ca5b7fb4f07c104
CHMDFiniteSampleRange a9272684f1a50e33e4846fd6dc2577dd46c63bc41a3ea3b221145d2ff89457e1
CHMDPhaseKernelSynthesis c274e981cc90f762ea3758ab492d09b27d63b5b4b723a13b2253820c73dd24f7
CHMDAlgebraicSpectralInverse da6911aa177624f31a4ead8575de9ab01623e791d6d95cd118b6c53067a90af7
```
