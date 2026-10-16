# CHMD: spectral silence forces maximal-domain admission

Status: IN PROGRESS. RH remains unproved.

## Corpus boundary

`CHMDNoWeylAboveThreshold`, `CHMDPurePointAboveThreshold`, and
`CHMDSpectralRiemannCriterion` already give spectral discreteness above one half
and the primitive-bound-state criterion. `CHMDBirmanSchwingerBound` additionally
bounds finite primitive eigenfamilies when the off-line zero set is finite.
Do not reconstruct these results or the superseded local-compactness proposal.

`CHMDFullSpectralNullspace` identifies the signed radical on the complete energy
graph. It does not state automatic energy/operator-domain admission for an
arbitrary mass-L2 vector with vanishing divisor and polar samples.

## Conjecture and paper argument

For the actual mass space, the joint kernel of all literal Xi-zero Fourier
samples and the two polar samples is exactly the one-half eigenspace of the
arithmetic resolvent. Thus spectral silence itself supplies maximal-domain
regularity; no hidden energy-domain premise survives.

1. Strip Fourier kernels are uniformly bounded mass-L2 kernels. Extend the
   existing mixed explicit formula to a continuous functional on the mass
   space: compact-test Fourier coefficients are absolutely summable, so the
   zero series converges in operator norm before evaluation.
2. On graph sources, this functional equals pairing with the actual signed
   generator image of a compact C2 test. Source-map density extends that
   identity to every mass vector.
3. A spectrally silent mass vector w is orthogonal to (L-1)v for every compact
   C2 operator-domain test. The proved compact C2 operator core extends this
   identity to every v in the maximal domain. Taking v=Rz and using self-adjoint
   R gives w=2Rw. This proves operator admission, not merely a weak equation.
4. Conversely, Rw=w/2 supplies a graph lift with source w in the signed radical;
   the established full radical theorem makes every divisor/polar sample zero.
5. Extract the strongest completion statement: actual source-map identification
   of the critical band, closed mass-space nullspace, and completeness of the
   literal sampling kernels on its orthogonal complement.

The result does not exclude primitive bound states or prove RH. It removes the
domain restriction from the spectral nullspace/sampling description.

## Plan and verification

- Finish corpus duplicate search, including candidate lemmas and source arguments.
- Prove mass mixed formula and the operator-core admission argument.
- Prove exact critical-space identification and sampling completeness.
- Targeted leaf builds only, final direct `lake env lean` for affected leaves,
  temporary axiom/API audits, root wiring, formal lint, owned scratch cleanup.

No new axioms, RH premise, simplicity premise, finiteness of off-line zeros,
numerical experiments, or heartbeat increases.

## Paper-proof closure and stronger survivor

The joint-kernel argument succeeds. Four new leaves currently pass their
targeted builds: `CHMDMassFourierReadout`, `CHMDMassMixedExplicitFormula`,
`CHMDMassSpectralAdmission`, and `CHMDMassSamplingCompleteness`. The sampling
kernel span closes to the mass-orthogonal complement of `ker(R-1/2)`, and every
mass vector has a unique reduced representative with its original samples.
This is completeness of the literal dual kernels, not a cardinal-series
expansion or an exclusion of primitive bound states.

The proof exposes a stronger statement, now being formalised in
`CHMDMassPolarCompletion`: vanishing Xi-zero samples alone implies maximal
operator-domain admission. Subtract the actual polar graph source matching
both polar samples; the remaining mass vector is critical by the proved
joint-kernel theorem. The mixed graph formula then identifies the signed
generator image as

`b(w) = -Re F_w(i/2) k^- - Re F_w(-i/2) k^+`,

where `k^+` and `k^-` are the actual real mass Fourier kernels at the poles.
Riesz uniqueness gives `R(2w+b(w))=w`, hence `Lw=w+b(w)` on the maximal domain.
All polar coefficients and the critical remainder are explicit and unique.

Final leaf audits, axiom audits, root wiring, lint, and cleanup remain pending.
