# TG C9.11y — faithful full-response ground admission

- **ID:** tg-full-response-ground-admission
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** P1 `tg-principal-polar-operator-cancellation`; route TG
- **Statement:** The complete native prime–polar response pair and its actual physical ground column control each other in nuclear/L2 norm with constants independent of prime and polar cutoffs.
- **Status:** both final production leaf audits and all 21 public foundation audits pass; wired and indexed; global lint reports eleven unrelated unwired leaves and no finding in either new leaf.

## Hard problem and contribution

The hard arithmetic problem remains cancellation of the complete signed
prime–polar ground tails. Previous work proves two-way control between
that ground column and its physical time-band nuclear source. It did not
establish faithful passage through both time/Fourier channels to the
complete original response. This result closes that passage for the
native symmetric tails.

All operators below act on the actual full physical Sonin L2 space.
Let A and B be its physical and Fourier forbidden projections, Q its
Sonin projection, J its original projection correction, F its Fourier
unitary, U=F^-1, R its physical reflection, and H=AFA its square time-band
operator. The aperture a is positive and fixed.

The result has two parts.

1. For every bounded complex source D, admission of the complete pair
   `(C(D),C(D*))` in genuine Schatten-one is equivalent to admission of
   the four literal source blocks `(DAB,DBA,D*AB,D*BA)`. This holds for
   unconditional sums and for cofinal limits along any filter.
2. For every original symmetric prime–polar tail K, there are fixed
   positive constants c_a and C_a, independent of all its finite prime
   and continuum cutoffs, such that
   `||K f_a|| <= c_a ||(C(K),C(K*))||_(S1 pair)` and
   `||(C(K),C(K*))||_(S1 pair) <= C_a ||K f_a||`.

The second statement proves all native Fourier, adjoint and reflection
identities used in the transport. They are not admission premises.

## Dependency-closed paper proof

### Recovering both original channels

The corpus proves `||BAB||<1`. Thus `1-BAB` is invertible. The elementary
identity transferring invertibility of `1-YX` to `1-XY`, applied first
to `X=AB,Y=B` and then with reversed factors, proves invertibility of
both `1-AB` and `1-BA`. Its explicit inverse is
`1+X(1-YX)^(-1)Y`; multiplication verifies both inverse equations.

Put T=AB+BA. Since A and B are projections,

`T(1-A)B=AB-(AB)^2=AB(1-AB)`.

Consequently the fixed bounded right factors

`R_AB=(1-A)B(1-AB)^(-1)`,

`R_BA=(1-B)A(1-BA)^(-1)`

satisfy `T R_AB=AB` and `T R_BA=BA`. Thus DT determines both DAB and DBA
by bounded right multiplication, for every D. Addition reconstructs DT.
Apply the same maps to D*. The existing bounded response/source recovery
identifies `(C(D),C(D*))` with `(DT,D*T)`. Composition gives bounded maps
between the complete response and all four original channels, with exact
inverse identities on the actual source images. Continuity and preservation
of summable families prove part 1.

### Native Fourier and adjoint transport

The exact full-vector native source consists of its finite prime sum and
the strong polar integral with original density `2 cosh(u/2)/u`.
Fourier transformation sends each normalized dilation D_exp(t) to
D_exp(-t). Its bounded linear map passes through the finite sum and
the Bochner integral. Hence F reverses the direction of the entire source.

The adjoint of D_exp(t) is D_exp(-t). Pairing against arbitrary L2 vectors,
moving the pairings through the same strong integral and using reality
of every original weight proves adjoint reversal for the full source.
Physical reflection commutes with every dilation and therefore with
the full source. Adding the two source directions and subtracting the
two finite stages proves `FK=KF`, `K*=K` and `RK=KR` for every native tail.
Continuity on each finite positive polar interval proves all necessary
integrability; no limiting integral is assumed.

### Bounded full-response reconstruction and recovery

The actual time-band identities are `BA=UH` and `AB=RHF`. The corpus's
correction right factor W satisfies

`J=AB(1-AW)+BAW`.

Using the native commutations gives

`KJ=R(KH)F(1-AW)+U(KH)W`.

Each term is a fixed bounded sandwich map in genuine Schatten-one.
Since K*=K, this recovers both components of the left-source pair from
KH. The existing bounded real-linear forward response map then constructs
the complete response pair from KH.

Conversely, its bounded recovery first returns KJ. Multiply on the right
by `(1+J) R_BA` and on the left by F. The identities
`J(1+J)=T`, `T R_BA=BA`, `FK=KF`, and `FBA=H` show that the result is
exactly KH. Thus both directions are bounded by constants depending only
on a.

The already-audited native estimates bound `||KH||_S1` above by a fixed
constant times `||Kf_a||`, and below by another such constant. Compose
these estimates with the two bounded maps to prove part 2.

## Frontier consequence and limits

For the native symmetric family, nuclear response compression cannot
conceal a nonvanishing physical ground tail, and physical ground decay
supplies the complete response rather than only one time-band channel.
Native Fourier/full-response transport is no longer an independent
admission input by the two final-audited Lean inequalities.

This is not a proof of ground decay. The signed arithmetic covariance,
Gamma completion, Hardy cubic compatibility and strict sub-unit law remain
open. The fixed constants above are finite; no sub-unit estimate follows.
Part 1 covers arbitrary complex sources; part 2 is stated for the actual
native symmetric tails, not an unspecified complex-parameter family.
RH has neither been proved nor falsified.

## Lean and search evidence

The wired channel leaf is
`formal/GaloisForLFunctions/RHTower/SoninTimeBandChannelRecovery.lean`.
Its thirteen public declarations pass the final foreground audit with
empty diagnostics: `/tmp/tg-c911y-channel-final.log`.

The native proof draft retains every original coefficient, both dilation
directions and the entire strong polar integral. Its first audit exposed
dependent rewriting and coercion issues, which were repaired without
altering statements. The full scratch and final production audits now pass
with empty diagnostics. The native leaf is
`formal/GaloisForLFunctions/RHTower/SoninPrimePolarFullResponse.lean`.

Corpus searches `/tmp/tg-c911y-response-factor-search.json` and
`/tmp/tg-c911x-centered-jet-search.json` were nonpartial with snapshot
coverage and background refresh incomplete. Candidate lemmas, source
arguments and ingredient sets were inspected. Relevant original response,
ground recovery and prime-count endpoint statements were checked in their
source files. None of the inspected arithmetic results supplies the
missing signed covariance upper bound.

Both final production audits used foreground `lake --old env lean <leaf>
-o .lake/build/lib/lean/<module>.olean`. Logs:
`/tmp/tg-c911y-channel-final.log` and `/tmp/tg-c911y-native-final.log`.
Both leaves are wired into RHTower. No full or umbrella build was run.
Foundation queries for all 21 public declarations are in
`/tmp/tg-c911y-axioms.lean`; results are recorded below when complete.

All 21 public foundation queries pass with only `propext`,
`Classical.choice`, and `Quot.sound`: `/tmp/tg-c911y-axioms.log`.
Index refresh exits 0 (`/tmp/tg-c911y-index.log`); all thirteen channel
and eight native-response public API names are verified in
`formal/LEAN_API.md`. No new axiom, hole, numerical experiment, heartbeat
increase, full build or umbrella build was used.

Global lint exits 1 with eleven unrelated modules unreachable from their
umbrella and no finding in either new leaf: `/tmp/tg-c911y-lint.log`.
The findings concern six CCM leaves, two MoebiusMollified leaves,
`ThetaCuspCurvatureDefectPrimitiveTransport`,
`ThetaMovingShellFirstOrderPhase`, and `ZetaZeroDensityPowerSaving`.

All owned processes have exited. Superseded owned proof drafts are removed;
production sources, foundation audit scratch, final logs and corpus-search
JSON evidence remain. No commit or push was made. The RH goal remains active
and unmet.
