# SZ: unbounded negative actual nonlinear prime discrepancy

- **ID:** SZ-PRIME-MOMENT-POTENTIAL-ESCAPE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** P1:sz-nonlinear-prime-forcing-sign; P3:sz-prime-moment-first-contact.
- **Statement:** For every real B and integer N, some n>=N has
  primeMassHalf(n)+primeMassHalf(n)^2/4-psi(n)<-B, unconditionally.

## Actual objects and result

All von Mangoldt prime powers are retained. Put

    M_n = primeMassHalf(n),
    U_n = sqrt(n)*(M_n+2)-n-psi(n)-1,
    D_n = M_n+M_n^2/4-psi(n).

`ccmPrimeMomentDiscrepancy_negative_escape` proves

    forall B : Real, forall N : Nat, exists n>=N, D_n < -B.

The continuous and integer potentials are also unbounded below on every
tail. The theorem has no RH, sign, zero-location, or growth assumption.
It does not prove eventual negativity, a critical normalized forcing
bound, or the canonical-head Gamma--prime--polar inequality.

## Dependency-closed paper proof

1. Let E(T)=(psi(exp T)-exp T)*exp(-T/2), J(T)=integral_0^T E(t) dt,
   and U(T)=exp(T/2)*(1+J(T)/2)-1. The exact critical Mellin source
   identity gives

       U(T)=sqrt(exp T)*(primeMassHalf(exp T)+2)-exp T-psi(exp T)-1.

   E is locally integrable, so U is continuous. The elementary Chebyshev
   envelope admits U in every real Laplace half-plane s>1. Integration
   by parts for J keeps J(0)=0 and proves the terminal term vanishes.
   Substituting the actual E transform and cancelling the initial terms
   gives, with G(s)=(s-1)*zeta(s) extended at1,

       L_U(s)=-logDeriv G(s)/(s*(2*s-1)), s>1.

2. Source functional-equation identities and the critical-line real
   logarithmic derivative of xi give the exact central residue

       Re(-logDeriv G(1/2))=2+gammaHardyPhaseRate(0)<0.

   G has no positive real zero. For arbitrary B, the density
   g(T)=(U(T)+B)*exp(-T/4) has transform

       -logDeriv G(z+1/4)/(2*(z+1/4)*(z-1/4))+B/(z+1/4).

   This is analytic at every real z>1/4, with the same negative residue
   at1/4. The corpus's negative-real-residue Landau theorem, including
   its compact-head correction, rules out an eventually nonnegative g.
   Hence U(T)<-B occurs beyond every real cutoff. No complex zero-free
   half-plane or interchange across a possible off-axis zero is assumed.

3. For x in [n,n+1), primeMassHalf(x) and psi(x) are constant. Thus
   U(log x) is a concave quadratic in sqrt(x). The left limit at n+1
   equals the post-entry U_(n+1), because sqrt(n+1)*Delta M=Delta psi.
   Therefore

       min(U_n,U_(n+1)) <= U(log x).

   Continuous negative escape transfers to integer negative escape
   without discarding prime jumps or inserting a cutoff error.

4. Generalize the source first-contact law to an arbitrary real A.
   A strict descent below A-1 forces a later D<A. Otherwise a subsequent
   valley would have D<U+w^2/4<U+1<A, since 0<=w<=2. The potential must
   descend forever. The identity D=U+(1+M/2-sqrt(n))^2, together with the
   descent, forces displacement below -1. Every entry then dissipates
   at least half its weight from D; D+M/2 is nonincreasing. This
   contradicts D>=A and unconditional divergence of M.

   Consequently D>=A on a tail forces U>=min(U_start,A-1) there.
   Integer negative escape contradicts this bound for every A. Set
   A=-B to obtain the main unconditional theorem.

## Lean audit

- `CCMPrimeMomentPotentialLaplace.lean`: final foreground audit38295,
  exit0, no diagnostics.
- `CCMPrimeMomentFirstContact.lean`: arbitrary-level extension checked
  in scratch89827, then final foreground audit37824, exit0, no diagnostics.
- `CCMPrimeMomentPotentialEscape.lean`: final foreground audit87799,
  exit0, no diagnostics. Earlier95916 caught a tactic-style cleanup
  regression; explicit two-goal branches fixed it before this final audit.
- Every final leaf command used `lake --old env lean <module> -o <olean>`
  in `formal`. The two new leaves each have one RHTower umbrella import.
  No full or umbrella build, heartbeat increase, numerical experiment,
  subagent, or custom axiom was used.
- Full24-public-declaration axiom audit16658 exited0. Every declaration
  depends only on `propext`, `Classical.choice`, `Quot.sound`. The audit
  used `lake --old env lean /tmp/sz_potential_escape_axioms.lean`; no
  axiom query was inserted into a production source file.
- Global lint44412 exited1 on14 other modules unreachable from umbrellas;
  no error named these three leaves. Global lint is not claimed green.
- Deep searches1221960 and1222173 were partial/source-only or had pending
  compiler coverage; the latter reported a semantic-retrieval timeout.
  The lexical negative-residue search found the exact theorem but had
  no freshness metadata. Sources and Lean determined applicability;
  search misses establish neither absence nor novelty.

## Remaining hard frontier

The original eventual-sign candidate for the normalized nonlinear forcing
is open. The exact physical balance is

    action + bulkDissipation + 2*exp(-T/2)*D
      = ageMoment + terminalEntropy.

Unbounded negative unnormalized D controls none of the other terms and
supplies no bound for exp(-T/2)*D. The next attack must control this joint
physical balance with the original prime cutoff and positive quadratic
correction retained, then connect it to the canonical-head joint sign.
The active RH goal is unresolved.

Lint44412's14 unrelated unreachable modules were RHTower's
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MertensProductDiamondPintz, MoebiusMollifiedCriticalMoment,
MoebiusMollifiedErrorThreeLines, ThetaFinitePairBoundaryCurrent,
ThetaFinitePairBoundaryPackets, ThetaMovingShellFirstOrderPhase,
ZetaZeroDensityPowerSaving, and HTGeometry.CompactMonoidMeasureAlgebra.
Their sources and wiring were outside this change.

Closure: all owned processes terminated; all8 exact scratch/search/lint
files removed. Three audited production oleans retained, three unique
umbrella imports checked, targeted whitespace clean. Memory:
`rhtower/sz-prime-moment-negative-escape-2026-10-04`. No RH proof or
falsification is claimed; the goal remains active.
