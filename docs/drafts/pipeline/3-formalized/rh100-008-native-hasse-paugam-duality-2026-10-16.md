# Contribution 008: native Hasse Hilbert admission and global Paugam duality

Status: formalized; 8/100 contributions audited and counted.
Nine direct leaf audits and 26 standard-axiom audits passed. All nine leaves
are wired into `RHTower.lean`; owned scratch files and jobs are cleaned up.
Repository lint found three unrelated concurrent umbrella omissions, listed
below. No new-module lint error was reported.

Objective: a distinct structural advance combining current frontier routes.
No estimates, conditional receivers, RH equivalences, or routine corollaries
of 001–007 count. Use the current Lean corpus and documented research search;
no web, numerical experiments, external novelty check, or old reports.
One owned foreground Lean build at a time, direct leaf audits only, no raised
heartbeats, added axioms, full builds, umbrella builds, or subagents.

Plan:
1. Inspect source-native Weil/residue duality, prime Euler cohomology, and
   cross-route admission obstructions against the current Lean corpus.
2. Record conjectures, exact failures and positive survivors. Require a
   dependency-closed paper proof of an actual construction before formalizing.
3. Formalize the selected advance, audit every changed leaf and its axioms,
   wire imports, run formal lint, and clean owned scratch. Count only then.

Initial leads: global Meyer Xi synthesis may support an actual, nondegenerate
source pairing, but full Weil trace can lose higher jets at repeated zeros.
Prime dilation inverses modulo actual boundaries may instead require a paid
periodization-surjectivity theorem. Both are questions to test against source,
not asserted conclusions. Broad frontier map checked for other current routes.

## Conjecture loop

- A family of single top-jet Paugam forms is insufficient: the corpus proves
  its common-kernel radical and that dilation mixes lower jets. Use the full
  complementary-jet block, not a top-jet substitution.
- A generic decaying reweighting would make an artificial Hilbert form but
  would not pay native arithmetic admission. Do not pursue that shortcut.
- Euler inversion on literal cohomology is not implied by finite-jet
  invertibility or by global injectivity. The required boundary correction
  for periodization has not been constructed; no Euler theorem claimed.

## Dependency-closed proof: native Hasse admission and global Paugam completion

Let H(rho,j)(g)=M_g^(j)(rho)/j!, for j below the full multiplicity.
The logarithmic source integral and the corpus factorial/exponential law give
one common bound on all Hasse orders, using integral exp(2|t|)|g(t)|.
The actual generator identity M_(Ag)(s)=s M_g(s), differentiated in Hasse
normalization, gives s H_j(g)=H_j(Ag)-H_(j-1)(g), with the last term zero
at j=0. Thus (1+|rho|)|H_j(g)| is controlled by a fixed pair of weighted
source integrals of g and its first derivative, uniformly in j and rho.
The divisor's reciprocal-square summability includes every multiplicity
copy. Consequently the entire Hasse jet packet of every actual source is
square summable, without extra spectral grading or a source-admission premise.
Weighted derivative gauges dominate those integrals, making this a continuous
map in the original strong source topology; boundary descent is already paid.

Global Xi synthesis makes the descended map injective. Exact finite causal
sections realize every finite Hasse packet, including zero at all unselected
zeros, so its image is dense in the canonical jet Hilbert space. This is
actual-source admission, not just an abstract coordinate carrier.

The complementary Hasse Paugam block at an upper-half-plane support point is
the sum H_j(u)H_(m-1-j)(Jv)-H_j(v)H_(m-1-j)(Ju). The two ℓ² packets make
the full sum absolutely convergent. The existing full-jet dilation law yields
weight-one covariance; simultaneous original reflection reverses the form.
Given a nonzero source class, global faithfulness exposes a nonzero jet and
an exact finite causal packet at its reflected complementary slot detects it.
Hence the resulting full-source form has zero radical. No positivity,
semisimplicity, source-selected Hodge metric or canonical arithmetic trace
identification is inferred. The structural result is a faithful dense
Hilbert realization of literal source cohomology supporting one convergent,
nondegenerate, full-multiplicity Paugam form with the original dynamics.

## Final structural result

Every original all-weight Meyer class has its complete multiplicity-bounded
Hasse packet in the unweighted jet Hilbert space. The resulting map is
complex-linear, injective, continuous for the original strong quotient
topology, and dense. The Hilbert upper-half-plane complementary pairing,
antisymmetrized with the exact original reflection, pulls back to one
jointly continuous global alternating form with zero radical. Its entire
coordinate series is absolutely summable. Every local block is precisely
the existing full Paugam block divided by `(multiplicity-1)!`, so the global
form obeys `Omega(F_c u,F_c v)=exp(c) Omega(u,v)` and
`Omega(Ju,Jv)=-Omega(u,v)`.

For RN, take the actual cut-current factor at coordinate `(rho,j)` to be
the Hedenmalm source of order `multiplicity(rho)-j`. The literal native
interior charge factorization is retained. This source class is a nonzero
unit phase times the causal Xi chain generator. Finite causal sections
therefore land in the span of these actual current factors. Every finite
Hasse packet lies in that span, so the span is Hilbert dense. Continuity of
the global form and its zero radical prove that pairing against this one
native-current family separates every literal Meyer class.

Obstacle removed: whole-source analytic admission and global full-jet
duality, including arbitrary non-finite source classes and repeated zeros.
The RN source factors now support global Hilbert and continuous bilinear
methods on faithful HF cohomology, rather than only finite local blocks.
The new construction uses no arbitrary spectral damping or admission
premise. The admission estimates are internal to this structural result.

Not proved: arbitrary Hilbert packets are original Meyer sources; Hilbert
density is density in the original Frechet topology; infinite sums converge
in the native BV norm; the form is the arithmetic cup/trace; positive Hodge
compatibility, SC wall orientation, or RH.

## Exact source inputs

- HF global faithfulness: `DeningerMeyerGlobalXiSynthesis`.
- HF original topology and generator: `DeningerMeyerStrongLogOperatorContinuity`.
- Exact finite full-jet sources: `DeningerMeyerFiniteXiCausalSplitting`.
- Canonical Hilbert carrier: `DeningerArithmeticJetHilbertRigging`.
- Full multiplicity summability: `XiDivisorDiagonalTraceClass`.
- All-order source normalization: `DeningerCollarExchange`.
- Full local forms and original dynamics: `DeningerMeyerPaugamGeneralizedJetPairing`.
- RN native current/source identification: `PaperThetaCutMeyerCurrent` and
  `DeningerMeyerHedenmalmSourceRealization`.

## Final audit

All nine new leaves passed, one foreground Lean process at a time, with
`lake --old env lean -o <leaf.olean> <leaf.lean>` from `formal/`:

1. `DeningerMeyerHasseMoments`
2. `DeningerMeyerHasseHilbertAdmission`
3. `DeningerMeyerHasseHilbertTopology`
4. `DeningerMeyerHasseHilbertDensity`
5. `DeningerHasseHilbertOperators`
6. `DeningerHasseHilbertPairing`
7. `DeningerMeyerHassePaugamBlocks`
8. `DeningerMeyerGlobalHassePaugamPairing`
9. `PaperThetaCutHasseCompletion`

The `/tmp` audit `lake --old env lean /tmp/hgt_rh008_axioms.lean` checked
26 declarations spanning admission, topology, density, reflection, block
normalization, absolute convergence, zero radical, dynamics and RN totality.
All use exactly `[propext, Classical.choice, Quot.sound]`. The separate
Mathlib API scratch audit passed. No added axioms, proof holes, numerical
experiments, raised heartbeats, full builds or umbrella builds.

`scripts/formal_tools.py lint` reported only these unrelated concurrent
unreachable modules, plus existing large-file warnings:

- `RHTower.CHMDFullJumpMoment`
- `RHTower.CHMDJumpGraphContractions`
- `HTGeometry.KleinGordonLightConeBesselKernel`

All nine new imports were checked individually. No unrelated module was
modified to suppress the global lint result. The search index reported full
source inventory but pending/stale compiler metadata; applicability was
checked against source and direct Lean audits. One Hasse search was partial
at filtering; its available source hits were used. The later Weil-bridge
search supplied no applicable identification, so none is asserted.
Owned `hgt_rh008` scratch artifacts were removed after audit completion.
