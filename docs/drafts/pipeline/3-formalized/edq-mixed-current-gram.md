# EDQ full mixed current Gram and finite-channel rigidity

Stage: 3-formalized. Dependency-closed paper proof and new-declaration Lean audit complete.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH.
Objective: retain the modulus-dependent mixed chronological response and determine whether a nonzero finite superposition can cancel its oriented current. RH remains open.

## Paper proof

For a finite set S of positive channel indices p (actual modulus p+1), complex
coefficients c_p, and the literal deletion paths u_p(s), form
`u_c(s,n)=sum_(p in S) c_p*u_p(s,n)` and its complete prefixes P_c(s,N).
The same real reflection weight `w_s(n)=(n+1)^(2*Re(s)-1)` acts on every
channel, hence also on the full complex superposition.

At each finite cutoff, bilinearity expands its chronological difference as
the full quadratic expression in the mixed parameter-variation currents,
with coefficients `c_p*conjugate(c_q)`. No mixed term is discarded.
The existing weighted chronological identity applies to the superposed path:
the difference is the weighted squared endpoint, minus the product of both
reflected endpoints, minus the complete sum of weight increments times
`norm(P_c(s,n+1))^2`.

At an actual nontrivial zeta zero, every constituent endpoint tends to zero.
The explicit tail bound gives
`norm(P_c(rho,N)) <= [sum_p norm(c_p)*A_p(rho)]*(N+1)^(-Re(rho))`.
Consequently the amplified squared endpoint is bounded by the squared bracket
constant divided by N+1, and also tends to zero. The full complex quadratic
current therefore equals the real, genuinely summable signed prefix energy.
Every term is nonnegative on the right and nonpositive on the left.

Strictness requires arithmetic independence, not only nonnegativity. If every
superposed prefix were zero, successive differences and the nonzero Mellin
weight would give `sum_p c_p*a_p(n)=0` at every integer. At n=1 all nontrivial
coefficients equal one, so `sum_p c_p=0`. Strong induction on a channel index p,
evaluating the same relation at n=p+1, then leaves only `-(p+1)*c_p`: every
proper divisor belongs to a smaller index already eliminated. Thus every c_p
vanishes. Every nonzero finite coefficient vector therefore has a nonzero
literal prefix. More precisely, if all channel indices are at most M, the
induction uses only coefficient positions 0 through M, hence only prefixes
of lengths 1 through M+1. A nonzero vector must be detected by one of these
prefixes. Off the critical line, their finite weighted Gram sum already has
strict sign. At an actual zero the full current dominates this positive
finite certificate on the right, with the reversed inequality on the left.

Off the critical line every weight increment is strictly signed, so this
nonzero prefix forces strict sign in the total current. On the line all
increments, and the source reflection difference itself, vanish. The complete
finite-channel nullspace is therefore classified: at an off-line zero only
the zero coefficient vector has zero quadratic current; on the line every
vector does. This establishes the full finite-channel definite response and
prevents hidden cancellation by complex finite superposition.

## Relation to the proof objective

This result concerns the actual mixed arithmetic current, rather than the
modulus-independent horizontal pair of completed halves. It retains its
possible use in an infinite or externally constrained comparison, while
showing precisely what finite mixing can and cannot annihilate. Strict
orientation is not a proof that the current must vanish at every zero. The
independent source law enforcing zero location remains open.

Corpus consulted: EulerDeletionReflectedCurrentEnergy,
EulerDeletionReflectedChronologicalCurrent, EulerDeletionCompletedChronology,
EulerDeletionHolomorphicChronology, EulerDeletionHorizontalContact,
EulerDeletionDirichletGram, EulerDeletionQuasiShuffleConvergence,
CoprimeBlockCarryTransgression, and corpus-wide indexed searches for mixed
current, polarization, coefficient independence, and prefix Gram energy.

## Formal certificate

Leaf: `formal/GaloisForLFunctions/RHTower/EulerDeletionMixedCurrentGram.lean`
(407 lines; 18 public theorems, three definitions, six private helpers).
Namespace: `RHTower.DeletionMixedCurrent`.

- `mixedPath`, `quadraticCurrent`, `mixedEnergy`: literal superposed paths, the entire mixed-current quadratic expression, and its full prefix Gram energy.
- `mixedPath_partner`, `mixed_chronological_tendsto`: actual common reflection weight and ordinary finite-cutoff transport of all cross terms.
- `mixed_endpoint_bound`, `mixed_energy_tendsto`: explicit superposed tail bound, disappearance of both endpoints and the amplified squared endpoint, and full complex Gram convergence.
- `hasSum_mixedEnergy`, `quadraticCurrent_eq_energy`: genuine summability and exact real signed Gram representation of the complete current at every actual zero.
- `deletion_coefficients_independent_initial`, `deletion_coefficients_independent`: complex arithmetic independence, already detected by coefficient positions zero through M for channels of index at most M.
- `exists_nonzero_mixed_prefix_initial`, `exists_nonzero_mixed_prefix`: every nonzero vector has a nonzero actual prefix, with the explicit first-M+1 prefix bound. These statements hold at every complex parameter, without a zero premise.
- `mixed_energy_initial_pos`, `mixed_energy_initial_neg`: the corresponding finite Gram head has strict sign on the appropriate side of the line at every source parameter.
- `mixed_energy_prefix_le_current`, `current_le_mixed_energy_prefix`: each finite Gram prefix bounds the complete current at actual zeros, with the correct orientation.
- `quadraticCurrent_re_pos`, `quadraticCurrent_re_neg`: strict sign for every nonzero finite complex vector at any actual off-line zero.
- `quadraticCurrent_of_re_half`, `quadraticCurrent_eq_zero_iff`: full source vanishing on the line and exact nullspace classification at every actual zero.

Final scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_mixed.lean`, exit 0,
no diagnostics. Final leaf audit:
`LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionMixedCurrentGram`,
exit 0; only the new leaf rebuilt (7.1 seconds). Dependencies cached/replayed.
One umbrella import added; no full or umbrella build.

New-only axiom audit: `lake env lean /tmp/edq_mixed_axioms.lean`, exit 0.
All 21 public declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`; the dependency closure covers all six private helpers.
No added axioms, admissions, numerical premises, or external computation certificates.

No route is retired. The theorem does not assert that any off-line zero exists.
Nor does strict orientation supply an independent law forcing the current to
vanish at every zero. RH remains unproved and unfalsified.

## Repository checks and cleanup

Repository lint ran once. Its sole error is the unrelated unwired HTGeometry
module `PolynomialODEEvenCompactSourceEleven`. It reports no error for this
new leaf. That other work area was left untouched; a global lint pass is not
claimed. The search index was refreshed once, and the new nullspace theorem
is retrievable by exact indexed search.

Scoped whitespace, local links, exact single umbrella wiring, equality with
the checked scratch source, and forbidden-declaration checks passed. No owned
Lean or Lake process remained. The three owned scratch Lean sources were
removed. Audit logs remain under `/tmp/edq_mixed` with `.api.log`, `.check.log`,
`.build.log`, `.axioms.log`, `.lint.log`, and `.index.log` suffixes.
