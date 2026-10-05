# BAG additive rational three-frequency source

- ID: C28.56ag.1, continuation01a5.
- Route: complete signed physical BAG cubic.
- Status: five leaf audits and all41 declaration axiom audits passed.
- Paper proof: ../2-fully-proven/bag-additive-rational-three-frequency-source.md.
- Active parent: ../1-in-progress/bag-three-frequency-ramanujan-source.md.

## Exact result

The finite signed divisor atoms

    nu_(e,P) = sum_(d|rad(P)) mu(d)d^(-e)/d * sum_(a mod d) delta_(a/d)

are compensated as kappa_(e,P)=(nu_(e,P)-nu_(0,P))/e at the SAME prime set.
For every complex Schwartz Phi on R^3, their full three-coordinate tensor
acting on F_Phi(x)=sum_(n in Z^3) Phi(n) exp(2 pi i n.x) tends jointly, with
P ranging over all finite sets and e->0+, to

    sum_(n in Z^3) Phi(n) Lambda(|n1|) Lambda(|n2|) Lambda(|n3|).

The theorem is `tendsto_ramanujanTripleFiniteAtomAction` in
ChiRamanujanThreeFrequencyAtomAction. Every finite rational atom and every
independent integer coordinate is retained. The atom action equals the
Fourier sum exactly before taking limits. Summability is proved for every
Schwartz profile using a finite seminorm; no all-prime atomic total-variation
bound or interchange hypothesis is imposed. The test is FIXED.

The multiplier at n=0 is the product over all retained primes, not D_e(0).
Two retained primes give a bound e log2 log3 after compensation. For n>0,
the coefficient is in [0,log n], uniformly even if P does not contain the
prime factors of n. Eventual coverage and the corpus Wold normal-cone
derivative give the joint one-coordinate limit. The tensor bound and actual
Schwartz lattice summability give the full tested limit. On 1<n<=M,
P=range(M+1) recovers D_e(n)/e exactly throughout the finite physical band.

## Files and audits

- ChiRamanujanFinitePrimeCompensation: 9 public declarations, audit6042 exit0.
- ChiRamanujanThreeFrequencyLattice: 5 declarations, audit71927 exit0.
- ChiRamanujanThreeFrequencySource: 7 declarations, audit66780 exit0.
- ChiRamanujanFiniteRationalAtoms: 11 declarations including Fintype instance,
  audit18211 exit0.
- ChiRamanujanThreeFrequencyAtomAction: 9 declarations, final audit21689 exit0.

Every final leaf command was `lake --old env lean <leaf> -o <olean>`, run in
foreground with no overlapping owned Lean process. No diagnostics remained.
All five imports occur exactly once in RHTower. The /tmp axiom probe9488
exited0; all41 declarations use only propext, Classical.choice and Quot.sound.
The same probe checked the concrete mathlib names used by the construction.

Index50560 exited0 and refreshed all five modules. All40 non-instance public
entries are present in LEAN_API; the Fintype instance was checked directly
by Lean and the axiom audit. Lint80376 exited1 on27 unrelated unreachable
modules, with no proof-debt or reachability finding for these five leaves.
Global lint is not clean. No full or umbrella build, numerical experiment,
added axiom, heartbeat increase, subagent, commit or push occurred.

## Remaining frontier and next conjecture

This closes fixed-test ADDITIVE rational source/interchange. The existing
six-zeta trace uses MULTIPLICATIVE positive-rational dilation modes; its
finite-height prime-net/integral transfer has not been identified with this
new representation. Stationary equations of the literal pq/r phase suggest
the surface z=x*y, but all near-resonant and growing-test errors remain.

Prime powers also remain in the limit. The corpus exact squarefree-Mangoldt
identity suggests convolving each retained local source with delta_0-h_(p^2).
Its proposed local factor is

    delta_0-p^(-e)h_p-(1-p^(-e))h_(p^2),

which agrees with delta_0-h_p at e=0 and kills p^2-divisible Fourier
coordinates at every damping. This keeps the arithmetic prime-only filter
in the measure, leaving a smooth physical test. Its literal finite atom
identity and joint prime-only limit are the NEXT conjecture, not claimed
formalized here. The full signed physical cubic at o(N/log^2 N), growing
moments, moving cofactors, positive common-height self-return and RH remain
open. This result is source construction, not a cubic cancellation saving.

Subsequent continuation01a6 closed the prime-only source extension above;
see `bag-prime-only-rational-three-frequency-source.md` (C28.56ag.2).
The complete signed growing physical cubic remains open.
