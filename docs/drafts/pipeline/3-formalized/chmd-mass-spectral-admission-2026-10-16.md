# CHMD: spectral silence forces maximal-domain admission

Status: FORMALIZED. RH remains unproved.

## Corpus boundary

`CHMDNoWeylAboveThreshold`, `CHMDPurePointAboveThreshold`, and
`CHMDSpectralRiemannCriterion` already give spectral discreteness above one half
and the primitive-bound-state criterion. `CHMDBirmanSchwingerBound` additionally
bounds finite primitive eigenfamilies when the off-line zero set is finite.
Do not reconstruct these results or the superseded local-compactness proposal.

`CHMDFullSpectralNullspace` identifies the signed radical on the complete energy
graph. It does not state automatic energy/operator-domain admission for an
arbitrary mass-L2 vector with vanishing divisor and polar samples.

Corpus queries covered cardinal-generator action, finite-divisor realization,
and `mass L2 zero samples generator critical eigenspace automatic domain admission`.
All three deep searches returned `partial=false`, no unfinished stages, and
72,861/72,861 inventoried files. Compiler metadata was mostly pending or stale;
these search results are discovery evidence, not verification of declarations.

The user's Birman--Schwinger pointer was checked with
`scripts/formal_tools.py research 'primitive bound states offLineZeros Birman Schwinger' --any --json`.
Its top candidate was `CHMDPolar.orthonormal_primitive_bound_states_le`, with
`card_le_two_mul_offLine_of_negative_definite` as the top source argument.
That query reported partial text/source retrieval despite a complete
72,872-file inventory. Its useful hits confirm the existing counting argument;
they do not certify absence of further results. The theorem explicitly assumes
`offLineZeros.Finite` and concludes `k ≤ 2 * offLineZeros.ncard`.

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

## Completed proof steps

- Corpus duplicate search, including candidate lemmas and source arguments.
- Mass mixed formula and the operator-core admission argument.
- Exact critical-space identification and sampling completeness.
- Stronger zero-only admission and explicit rank-two generator action.

No new axioms, RH premise, simplicity premise, finiteness of off-line zeros,
numerical experiments, or heartbeat increases.

## Paper-proof closure and stronger survivor

The joint-kernel argument succeeds. The first four leaves pass their
targeted builds: `CHMDMassFourierReadout`, `CHMDMassMixedExplicitFormula`,
`CHMDMassSpectralAdmission`, and `CHMDMassSamplingCompleteness`. The sampling
kernel span closes to the mass-orthogonal complement of `ker(R-1/2)`, and every
mass vector has a unique reduced representative with its original samples.
This is completeness of the literal dual kernels, not a cardinal-series
expansion or an exclusion of primitive bound states.

The proof exposes a stronger statement, formalised in
`CHMDMassPolarCompletion`: vanishing Xi-zero samples alone implies maximal
operator-domain admission. Subtract the actual polar graph source matching
both polar samples; the remaining mass vector is critical by the proved
joint-kernel theorem. The mixed graph formula then identifies the signed
generator image as

`b(w) = -Re F_w(i/2) k^- - Re F_w(-i/2) k^+`,

where `k^+` and `k^-` are the actual real mass Fourier kernels at the poles.
Riesz uniqueness gives `R(2w+b(w))=w`, hence `Lw=w+b(w)` on the maximal domain.
All polar coefficients and the critical remainder are explicit and unique.

## Lean verification

All five leaves, including `CHMDMassPolarCompletion`, pass targeted
`lake --old build` checks and final direct `lake env lean` checks. The six direct
checks (five new leaves plus the existing `CHMDBirmanSchwingerBound.lean`) each
exit zero with empty diagnostic output. No umbrella build was run.

The temporary API probe passes. `#print axioms` checks all 83 new declarations
and the existing `orthonormal_primitive_bound_states_le`: all 84 depend only on
`propext`, `Classical.choice`, and `Quot.sound`. Full printed theorem signatures
confirm that no RH, zero-simplicity, off-line-finiteness, or prior-domain premise
was introduced. The sample-vanishing hypotheses describe the vectors being
classified; this is not a proof that arbitrary primitive eigenvectors vanish.

Each new leaf is imported exactly once by `GaloisForLFunctions/RHTower.lean`.
`git diff --check` passes. Formal indexes were regenerated. Project-wide lint
reports one unrelated in-progress module, `PaperThetaBoundedForcing`,
unreachable from its umbrella. A final index refresh cleared both stale-index
findings; `lint --check-generated` still exits one solely for that unrelated
module. No owned proof or import failure remains. All 23 owned temporary search
results, API/axiom probes, and build/audit logs were removed; all owned processes
exited. Cross-session memory records the source hashes and audit results.

Principal declarations in namespace `RHTower.CHMDDoobGraph`:

- `mass_silent_iff_resolvent_half`
- `mass_silent_unique_radical_lift`
- `massSamplingSpan_closure`
- `exists_unique_reduced_mass_source`
- `mass_zero_samples_graph_admission`
- `mass_zero_samples_resolvent_identity`
- `mass_zero_samples_mem_arithmetic_domain`
- `arithmeticGenerator_zero_samples`
- `mass_zero_samples_unique_polar_decomposition`

Remaining mathematical frontier: exclude actual primitive eigenvectors above
one half. The new domain/completeness results do not supply that exclusion or a
primal cardinal-series synthesis. Reuse the established Birman--Schwinger
counting bound rather than reconstructing it.
