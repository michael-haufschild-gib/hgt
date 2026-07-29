# An involution canonically selects a minimal complementary event record

- **ID:** `involution-selects-minimal-event-record`
- **Stage:** 2-fully-proven
- **Type:** SPECTRAL-FRACTURE CLASSIFICATION / SOURCE-NATURAL RECORD BRIDGE
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [REDISCOVERED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent no-go:** `../../5-failed/albert-hessian-as-rank-six-event.md`
- **Physics parent:** `../../1-in-progress/actuality-creates-future-law.md`
- **Lean target:** `formal/GaloisForLFunctions/HTGeometry/EventInvolutionComplement.lean`

## Exact theorem

Let \(V\) be a finite-dimensional complex vector space and let \(A:V\to V\) be an involution:

\[
A^2=1.
\]

Define the continuation and record projections

\[
C_A=\frac{1+A}{2},\qquad R_A=\frac{1-A}{2}.                    \tag{1}
\]

Then:

\[
C_A+R_A=1,\qquad C_AR_A=R_AC_A=0,                             \tag{2}
\]

\[
C_A^2=C_A,\qquad R_A^2=R_A,                                  \tag{3}
\]

\[
\ker C_A=\operatorname{im}R_A,\qquad
\ker R_A=\operatorname{im}C_A.                               \tag{4}
\]

The combined map

\[
(C_A,R_A):V\longrightarrow V\oplus\operatorname{im}R_A        \tag{5}
\]

is injective. The quotient reporter induced by \(R_A\) is a canonical linear isomorphism

\[
V/\operatorname{im}C_A
\xrightarrow{\;\sim\;}
\operatorname{im}R_A.                                        \tag{6}
\]

Thus \(R_A\) is simultaneously:

- the exact information erased by \(C_A\);
- a faithful complementary record on \(\ker C_A\);
- a canonical realization of \(\operatorname{coker}C_A\); and
- minimal, with dimension \(\dim\ker C_A\).

If \(V=\mathbb C^{10}\) and \(\operatorname{tr}A=2\), then

\[
\dim\operatorname{im}R_A=4,\qquad
\dim\operatorname{im}C_A=6.                                  \tag{7}
\]

Hence the trace-two involution itself selects a canonical `4/6/4` continuation-record fracture.

## Proof

Adding the definitions in `(1)` gives \(C_A+R_A=1\). Multiplication and \(A^2=1\) give

\[
C_AR_A
=\frac14(1+A)(1-A)
=\frac14(1-A^2)
=0,
\]

and identically \(R_AC_A=0\). Expanding \(C_A^2\) and \(R_A^2\) proves `(3)`.

If \(x\in\ker C_A\), then by `(2)`

\[
x=(C_A+R_A)x=R_Ax,
\]

so \(x\in\operatorname{im}R_A\). Conversely, \(C_AR_A=0\) implies
\(\operatorname{im}R_A\subseteq\ker C_A\). This proves the first equality in `(4)`; the second is
symmetric.

If `(5)` sends \(x\) and \(y\) to the same pair, then

\[
x=(C_A+R_A)x=(C_A+R_A)y=y,
\]

so it is injective.

Define the map in `(6)` by

\[
[x]\longmapsto R_Ax.
\]

It is well defined because \(R_A\) vanishes on \(\operatorname{im}C_A\). It is surjective because
every \(y\in\operatorname{im}R_A\) obeys \(R_Ay=y\). If \(R_Ax=0\), then
\(x=C_Ax\in\operatorname{im}C_A\), so `[x]=0`; hence it is injective. This proves `(6)`.

Finally, the negative spectral projection of an involution satisfies

\[
\operatorname{tr}A
=\dim V-2\dim\operatorname{im}R_A.
\]

With \(\dim V=10\) and \(\operatorname{tr}A=2\), its range has dimension four. Equations `(2)` and
`(4)`, or rank--nullity, give \(\dim\operatorname{im}C_A=6\). \(\square\)

## Sharpness and uniqueness

For a fixed involution \(A\), the polynomial functional calculus uniquely determines the two
spectral projections `(1)`. No complement, basis, record isomorphism, or environment unitary is
chosen.

This does not contradict the bare-map noncanonicity theorem in
`noninvertible-event-complementary-record-boundary.md`. A bare noninjective \(C\) cannot select a
record. The additional involution \(A\), with \(C=(1+A)/2\), supplies precisely the missing
source structure.

## Hostile novelty audit

`[NOT NEW MATHEMATICS]`

The theorem is elementary spectral decomposition of an involution. The relevant physical-source
fact is also literature: a compatible pure-spinor pair determines commuting complex structures
whose product yields the `6+4` product structure.

Primary source:

- K. Krasnov, *Geometry of Spin(10) Symmetry Breaking*, J. Math. Phys. **65** (2024),
  arXiv:2209.05088.

No novelty may be claimed for complementary projectors, their kernel/range identities, quotient
equivalence, or the pure-pair product structure.

## Exact scientific delta

The earlier event programme assumed an arbitrary maximal-rank intertwiner \(T\). The theorem shows
that if the compatible pure-pair product involution is the physical source datum, no arbitrary
rank-six choice is needed:

\[
\text{source involution}
\longmapsto
\big(\text{six-continuation},\text{four-record}\big)
\]

is canonical.

This closes only the finite algebraic selection problem. It does not establish that the
four-record becomes spacetime.

## Physical open core

`[OPEN CORE: SPECTRAL RECORD BECOMES CAUSAL OBSTRUCTION]`

Derive, rather than stipulate, that:

1. elementary quantum actualization selects Krasnov's compatible pure pair;
2. the positive projector is the locally continuable quantum channel;
3. the negative projector is transported into a distinct outgoing record, not relabelled on one
   fixed carrier;
4. the Albert Hessian equips that record with the nested \(1+3\) Lorentz form and positive time
   cone;
5. event composition globalizes these records without forcing universal weak--tangent bundle
   equality;
6. one source connection yields gravity and exactly the Standard Model forces; and
7. the construction predicts a finite observable beyond GR plus the Standard Model.

## Gates

- [x] exact theorem and dependency-closed paper proof
- [x] hostile novelty audit: elementary spectral algebra
- [x] failed Hessian route and positive survivor recorded
- [x] exact theorem formalized unconditionally in Lean
- [ ] compatible pure pair derived as physical actualization
- [ ] outgoing record identified with causal geometry

## Log

- 2026-07-29 — extracted the source-natural complementary spectral projectors after the direct
  Albert-Hessian event was falsified.
- 2026-07-29 — completed paper proof of exactness, minimality, quotient realization, and `6+4`
  specialization.
- 2026-07-29 — formalized the complete spectral complement and exact `4/6/4` specialization in
  Lean; targeted module build, formal lint, and axiom audit passed.
