# CHMD: finite spectral samples determine the actual generator image

Status: IN PROGRESS. RH remains unproved; goal active.

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
