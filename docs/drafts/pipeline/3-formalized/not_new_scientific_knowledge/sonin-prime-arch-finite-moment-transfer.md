# Finite Sonin moment-block convergence transfers to RH

- **ID:** `sonin-prime-arch-finite-moment-transfer`
- **Stage:** 3-formalized
- **Type:** THEOREM / TOP-DOWN SOURCE-VALUE CHAIN
- **Scientific status:** `[FORMALIZED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/SoninPrimeArchFiniteMomentTransfer.lean`

## Statement

Let `T_a=K_a^*K_a` be the unconditional positive trace-class all-prime Sonin residual energy and
write

\[
S_r(a)=\operatorname{Tr}(T_a^{r+1}).
\]

Let `M_r` be the fixed centered prime--Gamma moment obtained from the normalized Taylor germ of the
continued prime--Gamma source.  Assume that for every finite cutoff `N` there is one explicit
positive aperture sequence `a_{N,j}` such that all moments below the cutoff converge
simultaneously:

\[
S_r(a_{N,j})\longrightarrow M_r
\qquad (0\le r<N).
\]

Then RH follows.

In Lean the schedules are packaged as one function `aperture : Nat -> Nat -> Real`.  The predicate
`SoninPrimeArchFiniteMomentCoupling aperture` requires positivity and the displayed finite-block
convergence.  The capstone is

```text
SoninPrimeArchFiniteMomentCoupling aperture
  -> SoninPrimeArchPerTestTraceHankelCoupling
  -> PrimeArchSourceTraceHankelIntNonnegative
  -> RiemannHypothesis.
```

## Proof

For a coefficient vector `c : Fin n -> Real`, Lean first proves the exact finite identity

\[
\mathcal Q_a(c)
=\sum_{i,j<n}c_i c_j S_{i+j}(a).
\]

The left side is the squared Hilbert--Schmidt norm of the source-built probe
`K_a p(T_a)`, hence is nonnegative.  To handle a polynomial of degree `d`, choose the single
schedule for cutoff `2(d+1)`.  Every moment appearing in its quadratic value then converges on that
same schedule.  Finite-sum continuity gives convergence to the corresponding prime--Gamma
trace-Hankel value.  Closedness of the nonnegative half-line supplies its sign, and the existing
countable integer-polynomial criterion gives RH.

## Non-circularity audit

The premise contains no Xi zero, zero ordering, real-rootedness, anti-Herglotz condition, Weil
positivity, limiting divisor measure, or sign assertion.  It is a source-to-source value relation:

\[
(M_0,\ldots,M_{N-1})
\in
\overline{\{(S_0(a),\ldots,S_{N-1}(a)):a>0\}}
\qquad\text{for every }N.
\]

This is not known to follow from RH, so the formal theorem is an implication rather than a disguised
equivalence.  It is also substantially stronger than matching each moment along an unrelated
aperture sequence: synchronization inside every finite block is what preserves positivity of all
mixed polynomial tests.

## What the newest corpus does not discharge

The polynomial Calkin boundary and the finite Sonin-word normal form live in the noncompact
principal grade.  The moments `S_r(a)` live in the Hilbert--Schmidt/trace-class residual grade.
Passing to the Calkin quotient kills precisely the compact data whose traces occur here.  Therefore
maximal essential alignment, finite-word tropical normal forms, and the universal boundary
character do not imply the finite-moment coupling.

The marked transverse Frostman profile retains prime labels but presently supplies no identity for
the trace moments of `T_a`.  It may help identify the arithmetic content of a future limit, but it
does not establish convergence.

## Open core

`[OPEN CORE]` Prove or refute the simultaneous finite-block closure relation above from the explicit
Sonin residual kernel and the continued prime--Gamma source formula.  A valid proof must exhibit the
aperture schedules before reading any Xi divisor and must control mixed moments on one common
schedule per cutoff.

The first structural attack should classify all possible finite-block cluster points of

\[
a\longmapsto(S_0(a),\ldots,S_{N-1}(a)).
\]

If an aperture-independent algebraic relation holds among these coordinates and fails for the
prime--Gamma vector, the route is false.  If the curve has a source-defined cofinal boundary whose
moments equal the prime--Gamma germ, that boundary is the missing weld.

## Lean certificate

The module proves:

- `soninAllPrimeTraceHankel_ofFn`;
- `SoninPrimeArchFiniteMomentCoupling`;
- `soninPrimeArchPerTestCoupling_of_finiteMomentCoupling`;
- `riemannHypothesis_of_soninPrimeArchFiniteMomentCoupling`.

## Gates

- [x] finite coefficient-vector Sonin moment identity
- [x] simultaneous finite-block coupling implies per-test coupling
- [x] formal chain from finite moment coupling to RH
- [x] separate the Calkin principal grade from the trace-class moment grade
- [ ] classify finite Sonin moment-block cluster points
- [ ] construct the prime--Gamma boundary point or prove it is excluded
- [ ] RH
