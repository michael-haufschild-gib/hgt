# SZ: arithmetic phase of the divisor response

- **ID:** sz-divisor-response-phase
- **Stage:** 5-failed (whole-half-plane passivity; positive survivor formalized)
- **Type:** FALSIFIED, with THEOREM (Lean) survivor
- **Source:** docs/reports/rh-current-frontier-map.md, route SZ
- **Statement:** The literal divisor source has a uniform first-mode logarithmic-derivative limit; its proposed passive response has negative real part at unbounded heights on every sufficiently right vertical line.

## Hard problem and conjecture

SZ needs cumulative signed source correlations and Wronskian control at the
original cutoffs. The exact Tatuzawa--Iseki forcing retains Mobius signs;
its known absolute envelope discards the required cancellation. Write B for
divisorSourceEntire and F for criticalStepSourceMellin. The corpus gives
F=B/(s*zeta(s)) on Re s>1. Formally, the logarithmic forcing
-F'-(zeta'/zeta)*F equals (1/s-B'/B)*F. The physical forcing/Mellin
identification still needs a separate exact weld; this card does not claim it.

Conjecture tested: Re(1/s-B'/B)>=0 throughout a right half-plane, allowing
a passive-response argument. Paper result below refutes this conjecture
even arbitrarily far inside absolute convergence.

## Dependency-closed paper proof

Put b(n)=log(n)-tau(n)+2*gamma, c=b(1), and d=-b(2)*log(2)/c.
The corpus proves B=L(b) on Re s>1 and absolute convergence there.
It also proves gamma>1/2, hence c>0. The neighboring harmonic remainder
bound at n=2 gives gamma<=4/3-log(2). The analytic strict inequality
log(1+x)>2*x/(x+2), applied at x=1, gives log(2)>2/3. Therefore
b(2)=log(2)-2+2*gamma<=2/3-log(2)<0, and d>0. No numerical
approximation is used.

Absolute convergence permits differentiation: B'=-L(log*b). This
coefficient family vanishes at n=1. The corpus's uniform first-index
Dirichlet theorem therefore gives 2^s*B'(s)->-b(2)*log(2) as Re s->infinity,
uniformly in Im s. Its index-one case gives B(s)->c. Division by c yields

    2^s * B'(s)/B(s) -> d > 0,

again with no restriction on Im s. This is the positive survivor: the
actual arithmetic response retains the phase exp(-i*t*log(2)); it does
not acquire a fixed sign when translated vertically.

Choose sigma sufficiently large that the real part of the normalized
quotient exceeds d/2 for every height. At t=2*pi*k/log(2), k a natural
number, 2^(sigma+i*t)=2^sigma. Thus Re(B'/B)>d/(2*2^sigma).
In contrast Re(1/(sigma+i*t))=sigma/(sigma^2+t^2) tends to zero as
k tends to infinity. At all sufficiently large such heights the response
has strictly negative real part. This holds on each sufficiently right
vertical line, above every prescribed height. Source nonvanishing in
this half-plane follows from the same uniform limit B->c>0.

## Novelty and applicability audit

Deep corpus searches (partial snapshots 1182294, 1182299, 1182300,
1182304) located the exact Tatuzawa identity, its coarse absolute bound,
the entire/Dirichlet source weld, and HTGeometry.ShiftSpectrumFirstIndex.
Candidate statements and proof bodies were inspected. No matching
literal-source logarithmic phase theorem was found; partial search is
not proof of global novelty. The generic first-index theorem is reused,
not presented as new. The new content is its exact arithmetic coefficient,
normalized logarithmic response, and persistent vertical sign obstruction.

## No-go closure

- **Killing mechanism:** a nonzero arithmetic phase survives arbitrarily far right, whereas the real part of 1/s tends to zero vertically.
- **Strongest positive survivor:** uniform-in-height first-mode phase law with strictly positive exact coefficient d; an eventual zero-free region for the actual B follows.
- **New insight:** any SZ forcing closure must retain phase compensation or a signed integrated law; whole-half-plane passivity is unavailable. No claim is made against a critical-line-specific signed estimate or RH.
- **Status:** dependency-closed paper proof and both Lean leaves complete. Five public theorem axiom audits use only propext, Classical.choice, and Quot.sound. The hard SZ source-paired energy estimate remains open.

## Lean certificate

- `DivisorSourceLogPhase`: `divisorSourceLogPhaseCoefficient_pos`,
  `divisorSourceEntire_right_limit`, `divisorSourceEntire_deriv_first_mode`,
  `divisorSourceEntire_logarithmic_first_mode`.
- `DivisorSourceResponseSign`: `divisorSourceLogResponse_negative_cofinally`.

Both leaves pass direct foreground `lake --old env lean` audits and are
wired into RHTower. API and all five public axiom queries pass in /tmp.
No added axioms, numerical experiment, heartbeat override, full build, or
umbrella build was used. Global lint reports ten pre-existing unrelated
unreachable modules; neither new leaf is unreachable and no forbidden
declaration is reported. Scoped diff whitespace check passes.

## Log

- 2026-10-02 — Paper proof and corpus applicability audit completed; begin targeted Lean formalization.
- 2026-10-02 — Both leaves, API checks and all five public axiom queries pass. Candidate retired with the uniform source phase law fully formalized.
