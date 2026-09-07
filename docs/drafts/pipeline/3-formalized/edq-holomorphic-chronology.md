# EDQ holomorphic chronology and completed square splitting

Stage: 3-formalized. Dependency-closed analytic proof and Lean verified.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH.
Objective: place the actual retained chronological current and Abel phase in a holomorphic source, with the precise completion functional equation. RH remains open.

## Dependency-closed paper proof

For r(s)=1-conjugate(s), conjugating the outer reflected kernel gives
`conjugate((n+1)^(-r(s)))=(n+1)^(s-1)`.
Thus every finite chronological cross and every finite Abel remainder is entire
in s. This is an identity of the actual arithmetic coefficients and cutoffs.

The corpus's uniform Abel block bound with initial cutoff zero gives
`norm(X_N(s)) <= 2*p*(1+norm(s)/Re(s))` for every N and Re(s)>0.
On the open box `delta<Re(s)<1-delta`, `norm(s)<R`, each diagonal Abel remainder
is bounded by

`2*p^2*(1+R/delta)*(1+R)*(n+1)^(-1-delta)`.

For delta>0 this is summable. Every strip point lies in such a box, so the
actual Abel sum is holomorphic there, with locally uniform convergence and
valid termwise differentiation. The previously verified parameter-variation
limit identifies the full normalized chronology L(s) with a fixed constant
minus this Abel sum. Hence L is holomorphic throughout the open strip despite
its earlier real/imaginary expression.

Conjugation of literal finite jumps and normalized chronological prefixes,
followed by uniqueness of limits, gives `L(conjugate(s))=conjugate(L(s))`.
The complete symmetric quasi-shuffle then gives

`L(s)+L(1-s)=D(s)*D(1-s)-K`,

where K is the already verified logarithmic arithmetic finite constant.
No endpoint or finite term is dropped.

Let F be the literal xi completion factor already verified, and define
`A(s)=F(s)*F(1-s)*(L(s)+K/2)`.
Every factor is holomorphic in the strip. The exact endpoint completion and
xi functional equation give `A(s)+A(1-s)=xi(s)^2`.
The gamma and arithmetic factors preserve conjugation, so A does as well.
On the critical line, therefore `2*Re(A(s))=norm(xi(s))^2 >= 0`.
This is a boundary identity. It supplies no sign in the strip interior without
an additional source estimate, and it does not force the current to vanish.

The positive result is an analytic realization of the literal retained current,
with its true reflection equation and boundary energy. No arbitrary holomorphic
splitting is substituted for the arithmetic chronology. No route is retired.

## Corpus inspected

EulerDeletionCompletedChronology, EulerDeletionQuasiShuffleCrossDomain,
EulerDeletionQuasiShuffleSecondConvergence, DirichletUniformAbel,
DirichletBddHolo, ArcsineZetaAnalyticFamily, and mathlib's
Analysis/Complex/LocallyUniformLimit. Broader indexed searches for eta Herglotz,
chronological holomorphic, xi square splitting, and completion commutator
located no existing holomorphic theorem for this literal chronology.

At every actual nontrivial zero rho, the analytic half retains precisely the
original EDQ components:

`2*Re(A(rho))=-Re(xiPhase(rho))*Re(J(rho))-2*Im(xiPhase(rho))*U(rho)`.

The two components therefore belong to the same genuine holomorphic source.
The boundary energy identity alone gives neither their required interior
comparison nor universal vanishing of J.

## Formal certificate

Leaf: `formal/GaloisForLFunctions/RHTower/EulerDeletionHolomorphicChronology.lean`
(349 lines; 19 public theorems, two public definitions, 14 private lemmas and
one private definition). Namespace: `RHTower.DeletionHolomorphicChronology`.

- `star_kernel_partner`, `differentiable_abelRemainder`: exact removal of the conjugated reflected exponent and entire finite arithmetic remainders.
- `norm_innerPrefix_le`, `norm_abelRemainder_le`: all-prefix bound without a zero premise and an explicit summable majorant uniform on bounded inner strip regions.
- `differentiableAt_abelSum`, `hasSum_deriv_abelRemainder`: actual holomorphy and justified differentiation of the retained infinite arithmetic series.
- `chronologyLimit_sub`, `chronologyLimit_eq_abelSum`, `analyticOnNhd_chronologyLimit`: the full complex finite part is the constant-minus-Abel-sum analytic realization.
- `chronologyLimit_conj`, `chronologyLimit_add_one_sub`: real structure and holomorphic reflection equation with the entire endpoint product and finite arithmetic constant.
- `xiFactor_conj`, `differentiableAt_xiFactor`, `analyticOnNhd_completedSplit`, `completedSplit_conj`: genuine analytic xi completion and its real structure.
- `completedSplit_add_one_sub`: the two literal arithmetic halves sum to genuine xi squared throughout the strip.
- `completedSplit_critical_energy`, `completedSplit_critical_nonneg`: twice the boundary real part is xi's squared norm at every critical-line point.
- `completedSplit_re_at_zero`: exact connection to the previously retained current and Abel phase at every actual nontrivial zero.

Final scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_holo.lean`, exit 0,
no diagnostics. Final leaf audit:
`LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionHolomorphicChronology`,
exit 0; only the new leaf rebuilt (4.7 seconds). Dependencies cached/replayed.
Umbrella import added without a full or umbrella build.

New-only axiom audit: `lake env lean /tmp/edq_holo_axioms.lean`, exit 0.
All 21 public declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`; private helpers are covered by that dependency closure.
No added axioms, admissions, numerical premises, or external computation certificates.

Repository lint passed once (existing file-size warnings); the search index was refreshed once.
Scoped whitespace, links, exact umbrella wiring, and owned-process checks passed.
Owned scratch Lean sources were removed; audit logs remain available.
Logs retained under `/tmp/edq_holo` with `.api.log`, `.check.log`, `.build.log`,
`.axioms.log`, `.lint.log`, and `.index.log` suffixes.

RH remains unproved and unfalsified. No interior source-sign theorem or universal
current-annihilation theorem is asserted. No route is retired.
