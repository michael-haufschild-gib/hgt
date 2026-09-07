# CCM-FU: source-supplied quadratic first-prime reserve

- **Stage:** 3-formalized
- **Type:** [BRIDGE], unconditional arithmetic theorem (Lean).
- **Parent:** [complete reserve-extension induction](../1-in-progress/ccm-fu-reserve-extension-induction.md).
- **Theorem:** Universal constants c>0 and T>=1 satisfy `c*M^2/p <= Q_empty(M)-Q_{p}(M)` for every prime p and every cutoff with `M/p>=T`.

The complete pairing identity in `MobiusDivisorPrimePairEnergy.lean` says
that the released energy is exactly

`2*sum_(d<=M, p does not divide d) mu(d)^2*K_d(M)*K_(pd)(M)`.

This is an unconditional arithmetic lower bound for that release.
It does not assume source diagonal dominance, bound the geometric defect
after pairing, or supply an exhaustive order.

The proof uses the actual unit-channel floor and exact clipped
interpolation to obtain one A>=1 such that
`M/d>=A -> K_d(M)>=sqrt(M)/32` for every positive d.
For `N=floor(M/(p*A))`, every d<=N has both relevant quotient scales above A.

The corpus's coprime squarefree window estimate has error `2R+N/R` and
density `D*p/(p+1)`, where `D=6/pi^2`. This density is at least one quarter.
For N>=1024, choosing `R=floor(N/32)+1` gives `N<=R^2` and
`2R+N/R<=N/16+34<=N/8`. Hence the complete coprime squarefree prefix mass
is at least N/8, uniformly in p.

Each retained pair contributes at least `mu(d)^2*M/1024`. Thus release is
at least `M*N/4096`. Since `M<=2*p*A*N` when N>=1, this is at least
`M^2/(8192*p*A)`. The proof uses `c=1/(8192*A)` and `T=1024*A`.
All discarded pair terms are nonnegative by the existing unsigned source
orientation theorem.

The cofactor pairing sum is formally identified with the literal retained
energy `Q_{p}`. Nonzero terms correspond bijectively to prime-factor labels
by their squarefree product. Terms outside the cutoff vanish, and nonsquarefree
cofactors vanish by the Möbius factor. The identity holds at every cutoff,
including when p is not an active source prime.

For every fixed prime this gives a quadratic original-energy credit at all
sufficiently large cutoffs. This credit differs from the previously bounded
linear release of an initial late-prime head-balancing block. It does not
bound `2*sqrt(G_{p}*D_{p})` or prove that even the first geometric certificate
meets the original budget. Spending the reserve through all subsequent
mergers, complete PE4, the signed Abel bound and RH remain open.

The module is `RHTower/MobiusDivisorFirstPrimeReserve.lean`. Its four public
theorems are `exists_divisorUnsignedDilationChannel_quotient_lower`,
`exists_mobiusDivisorFirstPrime_quadratic_release`,
`mobiusDivisorSelectionEnergy_singleton_eq_primePair`, and
`exists_mobiusDivisorSelectionEnergy_first_prime_reserve`.

Scratch and exact-file `lake env lean` checks pass. Only the new module's
olean was emitted. All four new public declarations were axiom-audited once:
only `propext`, `Classical.choice`, and `Quot.sound`. The module is wired
into `RHTower.lean`; the index was refreshed and formal lint passed.
A module-only Lake preflight earlier in the same work
found stale dependency traces without compiling; no dependency-rebuilding
Lake audit, full build or umbrella build was run. This analytic proof uses
no empirical premise, and no numerical experiment was run for it.
