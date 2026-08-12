# Noncommutative reciprocal fusion, Jordan history, and tracial erasure law

- **ID:** ULF-RFTM-2
- **Stage:** 2 — fully proven on paper
- **Type:** NONCOMMUTATIVE FORMATION-LAW / FUSION / HISTORY / OBSERVER NO-GO
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN FORMALIZED] [BRIDGE]`
  `[EXACT NONCOMMUTATIVE FUSION] [DOUBLE-COMMUTATOR HISTORY] [EXACT ASSOCIATOR]`
  `[TRACIAL ERASURE] [NOT RH]`

## 1. Mathematical delta

ULF-RFTM-1 left one precise open core: find a noncommutative direct/reflected fusion law that
recovers scalar reciprocal work on every flat and retains ordering history away from flats.

The correct operation is not ordinary multiplication of positive coordinates. It is quadratic
congruence. If `r` is a half-formation and `q` is a second formation, the direct and reflected
outputs are

\[
 D_r(q)=rqr,
 \qquad
 D_r^\rho(q)=rq^{-1}r.
\tag{NRF.1}
\]

Their reciprocal works obey one exact identity. Its noncommutative term is a sum of double
commutators. That term vanishes on every commutative flat but can be nonzero for positive matrices.
Every trace erases it exactly. Thus scalar trace work is not an incomplete estimate of ordering
history; it is structurally blind to it.

## 2. Algebraic setup

Let `A` be a unital associative ring and let `A^times` denote its group of units. For `u in A^times`
define the reciprocal work element

\[
 w(u)=u+u^{-1}-2\,1_A.
\tag{NRF.2}
\]

For `r in A^times` and `z in A`, define the reciprocal congruence action

\[
 \mathcal C_r(z)=rzr+r^{-1}zr^{-1}.
\tag{NRF.3}
\]

No commutativity, topology, positivity, or trace is assumed in Sections 2--4.

## 3. Exact noncommutative fusion

### Theorem 3.1 — congruence fusion identity

For every `r,q in A^times`,

\[
 \boxed{
 w(D_r(q))+w(D_r^\rho(q))
 =\mathcal C_r(w(q))+2w(r^2).}
\tag{NRF.4}
\]

### Proof

The two inverse laws are

\[
 (rqr)^{-1}=r^{-1}q^{-1}r^{-1},
 \qquad
 (rq^{-1}r)^{-1}=r^{-1}qr^{-1}.
\]

Hence the left side of `(NRF.4)` is

\[
 r(q+q^{-1})r+r^{-1}(q+q^{-1})r^{-1}-4.
\]

Insert `q+q^{-1}=w(q)+2`:

\[
 \mathcal C_r(w(q))+2(r^2+r^{-2}-2)
 =\mathcal C_r(w(q))+2w(r^2).
\]

This is `(NRF.4)`. QED.

## 4. Two exact history decompositions

### 4.1 One-sided commutator form

Define

\[
 \kappa_R(r;z)=
 r(zr-rz)+r^{-1}(zr^{-1}-r^{-1}z).
\tag{NRF.5}
\]

Then

\[
 \boxed{
 \mathcal C_r(z)=(r^2+r^{-2})z+\kappa_R(r;z).}
\tag{NRF.6}
\]

Indeed, subtract the first term on the right and factor each difference on the left. Therefore

\[
\boxed{
 w(D_r(q))+w(D_r^\rho(q))
 =w(r^2)w(q)+2w(r^2)+2w(q)+\kappa_R(r;w(q)).}
\tag{NRF.7}
\]

If `r` commutes with `w(q)`, then `r^{-1}` also commutes with it and `kappa_R=0`. Equation
`(NRF.7)` becomes exactly the scalar fusion law of ULF-RFTM-1.

The one-sided decomposition is algebraically cheap but does not preserve self-adjointness term by
term. The symmetric form below is the intrinsic positive-cone version.

### 4.2 Jordan/double-commutator form

Now assume `A` is a rational algebra. Write

\[
 a\circ b=\frac12(ab+ba),
 \qquad
 [a,b]=ab-ba,
\]

and define

\[
 \boxed{
 \kappa_J(r;z)=
 -\frac12\left([r,[r,z]]+[r^{-1},[r^{-1},z]]\right).}
\tag{NRF.8}
\]

### Theorem 4.1 — Jordan fusion with retained history

For every `r,q in A^times`,

\[
 \boxed{
 \begin{aligned}
 w(D_r(q))+w(D_r^\rho(q))
 &=w(r^2)\circ w(q)+2w(r^2)+2w(q)\\
 &\quad+\kappa_J(r;w(q)).
 \end{aligned}}
\tag{NRF.9}
\]

### Proof

For arbitrary `a,z in A`, direct expansion gives

\[
 aza=(a^2\circ z)-\frac12[a,[a,z]].
\tag{NRF.10}
\]

Apply `(NRF.10)` to `a=r` and `a=r^{-1}`, add, and use bilinearity of the Jordan product:

\[
 \mathcal C_r(z)=(r^2+r^{-2})\circ z+\kappa_J(r;z).
\]

Since `r^2+r^{-2}=w(r^2)+2`,

\[
 \mathcal C_r(z)=w(r^2)\circ z+2z+\kappa_J(r;z).
\]

Substitute `z=w(q)` in `(NRF.4)`. QED.

### Corollary 4.2 — exact flat restriction

If `r` and `q` commute, then `kappa_J(r;w(q))=0`, the Jordan product is ordinary multiplication,
and `(NRF.9)` is

\[
 w(rqr)+w(rq^{-1}r)
 =w(r^2)w(q)+2w(r^2)+2w(q).
\]

For `r=e^{x/2}` and `q=e^y`, this is exactly

\[
 \omega(x+y)+\omega(x-y)
 =\omega(x)\omega(y)+2\omega(x)+2\omega(y).
\]

Thus ULF-RFTM-1 is the flat restriction of `(NRF.9)`, not an analogy to it.

## 5. Ordered composition and exact associator

Quadratic congruence is not associative. This failure is typed rather than hidden. For

\[
 D_r(q)=rqr,
\]

one has

\[
 \boxed{
 D_s(D_r(q))-D_{sr}(q)
 =srq(rs-sr).}
\tag{NRF.11}
\]

### Proof

The left side is

\[
 srqrs-srqsr=srq(rs-sr).
\]

QED.

The associator vanishes when successive half-formations commute. Away from a flat, `(NRF.11)`
records ordered history. No claim that it is a cohomologically nontrivial curvature class is made.

## 6. Positive matrices and the trace-erasure theorem

Take `A=M_n(C)` and let `r,q` be positive-definite Hermitian matrices. Both congruence outputs in
`(NRF.1)` are positive definite. Moreover `w(u)` is positive semidefinite for every positive
invertible `u`, since functional calculus gives

\[
 w(u)=(u^{1/2}-u^{-1/2})^2.
\tag{NRF.12}
\]

For self-adjoint `r,z`, the Jordan history `(NRF.8)` is self-adjoint.

### Theorem 6.1 — every trace erases Jordan history

For the matrix trace,

\[
 \boxed{\operatorname{Tr}\kappa_J(r;z)=0.}
\tag{NRF.13}
\]

### Proof

Cyclicity gives `Tr[a,b]=0` for every pair of matrices. Each summand in `(NRF.8)` is itself a
commutator. QED.

This erasure is strict: the history operator can be nonzero. Let

\[
 r=\begin{pmatrix}2&0\\0&1\end{pmatrix},
 \qquad
 q=\begin{pmatrix}2&1\\1&2\end{pmatrix}.
\]

Both are positive definite, and

\[
 w(q)=\frac23\begin{pmatrix}1&1\\1&1\end{pmatrix}.
\]

A direct substitution into `(NRF.8)` gives

\[
 \boxed{
 \kappa_J(r;w(q))=
 \begin{pmatrix}0&-5/12\\-5/12&0\end{pmatrix}\ne0,}
\tag{NRF.14}
\]

while its trace is zero.

### Corollary 6.2 — tracial observer no-go

No observer that factors only through a trace of the fusion identity can reconstruct
noncommutative formation history. Such an observer sees precisely the flat/Jordan-radial part of
`(NRF.9)` and annihilates `kappa_J` for every packet.

This predicts a sharp failure mode in any spectral-trace organ: if the formation mechanism is
genuinely ordered, a nontracial packet observer or an operator-valued reporter is necessary.
Adding more scalar trace moments of the same commutator term does not restore the lost first-order
operator coordinate automatically.

## 7. Multi-organ fusion ledger

One law now couples five previously separate organs:

1. **exact recovery:** units retain inverse semantic/lineage factors;
2. **functional reversal:** `q -> q^{-1}` exchanges direct and reflected formation;
3. **positive geometry:** quadratic congruence preserves the positive cone;
4. **formation composition:** `(NRF.11)` records order-sensitive associator history;
5. **observer theory:** trace scalarization erases exactly the double-commutator sector.

This is the first exact answer to the Stage-1 request for a noncommutative fusion identity with a
flat restriction and a separately typed commutator history. It does not yet prove the global
compactness criterion for an operator ideal.

## 8. Conjecture-to-proof/failure loops

### Loop A — ordinary product is the noncommutative formation operation

**[FALSIFIED].** A product of positive Hermitian matrices need not be Hermitian.

**Survivor.** Quadratic congruence `q -> rqr` preserves positivity and yields `(NRF.4)`.

### Loop B — scalar fusion extends unchanged

**[FALSIFIED].** Away from commuting flats, the scalar product term misses `kappa_J`.

**Survivor.** The exact replacement is Jordan fusion plus double-commutator history `(NRF.9)`.

### Loop C — trace work retains the correction

**[FALSIFIED].** Equation `(NRF.13)` annihilates it identically.

**Survivor.** Operator-valued or nontracial observation is load-bearing.

### Loop D — nonassociativity is an untyped obstruction

**[FALSIFIED].** Equation `(NRF.11)` gives the exact associator and its commuting-flat vanishing
locus.

**Survivor.** Ordered commutator history is a concrete formation coordinate.

### Loop E — the correction is already an RH selector

**[FALSIFIED].** No literal arithmetic source has yet been shown to produce a nonzero bounded
`kappa_J`, and no global ideal properness theorem has been attached to it.

**Survivor.** The next gate is precise: construct a source-generated positive congruence packet,
prove its double-commutator history lies in a compactly controlled ideal, and show bounded amplified
fusion forces both radial and commutator histories to vanish.

## 9. Collision audit and scope

Quadratic congruence `P(r)z=rzr` is the matrix model of the quadratic representation in Euclidean
Jordan algebras and symmetric-cone theory. Matrix-valued d'Alembert equations and spherical
functions are established. Double commutators and tracial commutator erasure are classical
operator-algebra mechanisms.

The theorem is therefore a `[BRIDGE]`: its value is the exact formation interpretation and the
single fusion ledger, not an external priority claim.

The result is algebraic and finite. It supplies no compactness ideal, recurrence theorem,
hypertranscendence theorem, arithmetic source realization, Xi landing, or RH consequence.

## 10. Lean formalization

Module

`GaloisForLFunctions.HTGeometry.ConstitutiveNoncommutativeReciprocalFusion`

formalizes unconditionally:

1. ring-level congruence fusion `(NRF.4)`;
2. one-sided commutator decomposition `(NRF.6)--(NRF.7)`;
3. rational-algebra Jordan/double-commutator fusion `(NRF.9)`;
4. exact associator `(NRF.11)`;
5. genuine matrix units producing the concrete nonzero `2x2` history witness, positive witness
   forms, and trace erasure.

It is imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`. Stage-3 certificate:

`../../../3-formalized/universal-law-field/reciprocal-fusion-topology-mechanics/noncommutative-reciprocal-fusion-jordan-history-and-tracial-erasure-law-formalized.md`.

## Log

- 2026-08-12 — scalar fusion open core pivoted to quadratic congruence.
- 2026-08-12 — exact ring-level fusion and commutator decomposition proved.
- 2026-08-12 — Jordan/double-commutator form and associator proved.
- 2026-08-12 — strict positive `2x2` witness and tracial erasure proved.
- 2026-08-12 — complete algebraic theorem, associator, positive witness forms, genuine unit landing,
  strict history, and tracial erasure formalized in Lean and wired into the field umbrella.
- 2026-08-12 — foreground umbrella build passed (`11842` jobs). Scratch axiom audit of eight
  capstones reported only `propext`, `Classical.choice`, and `Quot.sound`; scoped forbidden-token
  scan found no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
