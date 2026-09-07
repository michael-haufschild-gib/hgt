# EDQ completion transport of the full chronological source

Stage: 3-formalized. Dependency-closed paper proof and Lean verified.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH.
Objective: determine the actual effect of xi completion on chronology, rather than transferring its endpoint functional equation to intermediate prefixes.

## Dependency-closed paper derivation

Use literal modulus p+1, reflection r(s)=1-conjugate(s), chronological cross C_s(N),
harmonic numbers H_N, arithmetic finite part K=finitePart(p+1,p+1), and the already
verified reflection current J(s). Write D_s for the deletion endpoint and
U(s)=-Im(sum_n AbelRemainder(p,p,s,n)); that series is absolutely convergent in the
open strip. The existing finite Abel identity has a real arithmetic middle sum.
Its terminal tends to zero, hence Im C_s(N) tends to U(s).

The full symmetric quasi-shuffle identity and reflection variation give

`C_s+conjugate(C_r)+p*H_N → D_s*conjugate(D_r)-K`,
`C_s-C_r → -J(s)`.

Taking real parts and adding proves the full complex limit

`C_s(N)+p*H_N/2 → L(s)`,
`L(s)=(Re(D_s*conjugate(D_r))-K-Re J(s))/2 + i*U(s)`.

No imaginary component or finite constant is discarded. At an actual zero,
both endpoints vanish, J is real, and U(r(s))=U(s). Thus

`L(s)=(-K-J(s))/2+i*U(s)`, `L(r(s))=(-K+J(s))/2+i*U(s)`.

Multiplying the two literal jump streams by arbitrary scalars a,b multiplies
their cross chronology by k=a*conjugate(b), and the reversed chronology by
conjugate(k). At every finite cutoff the required harmonic subtraction is
therefore `(k-conjugate(k))*p*H_N/2`. The normalized reflected difference tends
to `k*L(s)-conjugate(k)*L(r(s))`. At every actual zero this is exactly

`-Re(k)*J(s)-2*Im(k)*U(s)-i*Im(k)*K`.

For every p>0 throughout the strip, the unrenormalized completed difference
converges if and only if Im(k)=0. In the forward direction, subtracting its
hypothetical finite limit from the proved normalized limit makes the induced
harmonic counterterm converge. Dividing its imaginary part by H_N, which
tends to infinity, gives both zero and the constant p*Im(k), so Im(k)=0.
In the reverse direction k=conjugate(k), the counterterm is exactly zero, and
the proved normalized convergence is ordinary convergence. This is an exact
classification, without a zero premise, not a claimed phase constraint on xi.

For modulus two, K=0; the limit is real but includes the additional phase
potential U. A real scaling retains J; a complex completion also mixes U into
the real part. Neither fact proves vanishing.

The actual xi completion of the literal modulus-p+1 deletion endpoint is
`F_p(s)=s*(1-s)*Gamma_R(s)/(1-(p+1)^(1-s))`.
For p>0 in the strip its denominator and numerator are nonzero, and
`F_p(s)*D_p(s)=xi(s)` by the corpus's exact endpoint and gamma identities.
The preceding transport law applies to the literal completed jumps using
a=F_p(s), b=F_p(r(s)). Endpoint completion does not supply a vanishing equation
for this normalized second level.

## Corpus basis and current gap

Read EulerDeletionReflectedCurrentEnergy, EulerDeletionReflectedChronologicalCurrent,
EulerDeletionReflectedLogarithmicGram, the actual paired-eta completed Gaussian
coupling/symmetry, and RouteRCompletionCountertermBlindnessNoGo. Searches across
the indexed corpus found no existing chronological renormalization/completion
transport theorem. The Route R counterterm theorem concerns another source;
it is not substituted here.

The positive target is a complete finite-to-limit transport law for literal
arithmetic chronology. No route is retired. RH still requires an independent
arithmetic comparison forcing the already oriented J to vanish. A new receiver
or the endpoint equality alone does not close that gap.

## Formal certificate

Leaf: `formal/GaloisForLFunctions/RHTower/EulerDeletionCompletedChronology.lean`
(267 lines; 15 public theorems, eight public definitions, two private lemmas).
Namespace: `RHTower.DeletionCompletedChronology`.

- `reflectedCross_im_tendsto`, `renormalizedPrefix_tendsto`: full complex finite part throughout the strip, with endpoint product, arithmetic finite constant, signed reflection current, and absolutely convergent Abel phase.
- `chronologyLimit_sub_partner`, `abelPhase_partner_at_zero`, `chronologyLimit_at_zero`: exact partner difference and actual-zero specialization.
- `chronologicalCrossPrefix_scale`, `completedDifference_eq`, `completedDifference_tendsto`: actual scalar action on finite chronology, induced harmonic counterterm, and full transport limit.
- `ordinaryDifference_converges_iff`: for every nontrivial modulus in the open strip, ordinary convergence is equivalent to reality of the cross phase, without any zero premise.
- `completed_value_at_zero`: full real/imaginary decomposition of the completed finite part at every actual nontrivial zero.
- `xiFactor_ne_zero`, `xiFactor_mul_endpoint`, `xi_completed_endpoint_tendsto`: genuine nonzero xi completion of the literal arithmetic source throughout the strip.
- `xi_completedDifference_at_zero`, `xi_modulus_two_completedDifference_at_zero`: actual xi-completed second-level limits, retaining the independent Abel phase even when the arithmetic finite constant vanishes.

Final scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_completion.lean`, exit 0,
no diagnostics. Final targeted leaf audit:
`LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionCompletedChronology`,
exit 0. Only the new leaf rebuilt (4.6 seconds); dependencies cached/replayed.
Umbrella import added; no full or umbrella build.

New-only axiom audit: `lake env lean /tmp/edq_completion_axioms.lean`, exit 0.
All 23 public declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`; private lemmas are covered by this dependency closure. No added
axioms, admissions, numerical premises, or external computation certificates.

Repository lint passed once (existing file-size warnings); the search index was refreshed once.
Scoped whitespace, links, exact umbrella wiring, and owned-process checks passed.
Owned scratch Lean sources were removed; audit logs remain available.
Logs retained under `/tmp/edq_completion` with `.api.log`, `.check.log`, `.build.log`,
`.axioms.log`, `.lint.log`, and `.index.log` suffixes. The initial leaf audit's
endpoint eta-expansion error is retained separately in `.build-initial-failure.log`;
the corrected final source passes both scratch and targeted leaf checks.

RH remains unproved and unfalsified. This source-level completion transport is
not a universal current-annihilation law. No route is retired.
