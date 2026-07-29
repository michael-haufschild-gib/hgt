# Fixed-carrier spatial change is reciprocal-spectrally invisible

- **ID:** `fixed-carrier-spatial-reciprocal-blindness`
- **Stage:** 2-fully-proven
- **Type:** exact connection no-go / positive representation boundary
- **Scientific status:** `[PAPER-PROVED] [REDISCOVERED] [BRIDGE]`
- **Parents:** `../1-in-progress/source-generated-ternary-reciprocity-law.md`,
  `../1-in-progress/purity-boundary-theory-of-everything.md`

## Exact theorem

Let

\[
D\in M_{m,n}(\mathbb C),\qquad
A\in M_m(\mathbb C),\qquad
B\in M_n(\mathbb C)
\]

with

\[
A^\dagger=-A,\qquad B^\dagger=-B.
\]

Define a two-sided spatial variation of the rectangular transfer by

\[
E=AD+DB.
\tag{1}
\]

For the reciprocal squares

\[
Q=D^\dagger D,\qquad G=DD^\dagger,
\]

their first algebraic variations are

\[
\delta Q=E^\dagger D+D^\dagger E,\qquad
\delta G=ED^\dagger+DE^\dagger.
\]

Then

\[
\boxed{\delta Q=QB-BQ}
\tag{2}
\]

and

\[
\boxed{\delta G=AG-GA.}
\tag{3}
\]

Consequently every cyclic power reporter is blind to the spatial variation:

\[
\operatorname{tr}(Q^kB-BQ^k)=0,\qquad
\operatorname{tr}(AG^k-G^kA)=0
\tag{4}
\]

for every \(k\in\mathbb N\).

In complex dimension one, every real rate \(r\) defines

\[
\delta_r(z)=irz
\]

on the scalar ternary product

\[
[x,y,z]=x\overline y z.
\]

The maps \(\delta_r\) are pairwise distinct ternary derivations, while

\[
\overline{\delta_r(z)}z+\overline z\,\delta_r(z)=0.
\tag{5}
\]

Thus reciprocal positive observation cannot reconstruct even a one-dimensional phase connection.

## Paper proof

Taking the conjugate transpose of `(1)` and using skew-adjointness gives

\[
E^\dagger
=D^\dagger A^\dagger+B^\dagger D^\dagger
=-D^\dagger A-BD^\dagger.
\]

Hence

\[
\begin{aligned}
E^\dagger D+D^\dagger E
&=(-D^\dagger A-BD^\dagger)D+D^\dagger(AD+DB)\\
&=-D^\dagger AD-BD^\dagger D+D^\dagger AD+D^\dagger DB\\
&=QB-BQ,
\end{aligned}
\]

proving `(2)`.  Similarly,

\[
\begin{aligned}
ED^\dagger+DE^\dagger
&=(AD+DB)D^\dagger+D(-D^\dagger A-BD^\dagger)\\
&=ADD^\dagger+DBD^\dagger-DD^\dagger A-DBD^\dagger\\
&=AG-GA,
\end{aligned}
\]

proving `(3)`.

Cyclicity of finite matrix trace gives

\[
\operatorname{tr}(Q^kB)=\operatorname{tr}(BQ^k),
\qquad
\operatorname{tr}(AG^k)=\operatorname{tr}(G^kA),
\]

which proves `(4)`.

For `(5)`,

\[
\begin{aligned}
\delta_r(x\overline y z)
&=irx\overline y z,\\
\delta_r(x)\overline y z
+x\overline{\delta_r(y)}z
+x\overline y\delta_r(z)
&=(ir-ir+ir)x\overline y z
=irx\overline y z.
\end{aligned}
\]

Thus \(\delta_r\) is a ternary derivation.  Evaluation at \(1\) distinguishes the rates, while

\[
\overline{irz}z+\overline z(irz)
=-ir\overline z z+ir\overline z z
=0.
\]

Every dependency is closed.

## External parent and hostile verdict

Pluta--Russo prove that every derivation on a TRO is spatial.  Equations `(2)`--`(4)` are the
finite-matrix coefficient-algebra shadow of that standard operator-algebra mechanism.  Unitary
orbit geometry and gauge theory already interpret inner commutators as vertical change, while
Gauss--Codazzi--Ricci and brane constructions already split tangential, normal, gauge, and
gravitational data.

Verdict: `REDISCOVERED / BRIDGE`.

This is not new physics and does not identify a normal defect with gravity.

## Strongest positive survivor

The theorem kills the proposal that time or gravity can be reconstructed from the cyclic
reciprocal spectra of an endomorphism derivation of one fixed ternary carrier:

```text
fixed-carrier ternary derivative
  -> spatial left/right action
  -> coefficient commutators
  -> reciprocal spectral blindness.
```

This is not a proof that every spatial variation is physically gauge.  Eigenvectors, matrix
elements relative to a source frame, or interference with a reference carrier can detect changes
that cyclic spectra forget; even the scalar phase in `(5)` is detectable relative to another
phase.  Calling the spatial directions gauge therefore requires an independent operational
quotient declaring them source-invisible.

After such a quotient is defined, a candidate source-normal object is the class

\[
\mathcal N_{\rm src}(D)
=
\bigl[\nabla_{\rm src}D\bigr]\!
\mod
\{AD+DB:A^\dagger=-A,\ B^\dagger=-B\}.
\tag{6}
\]

This **source-normal defect** is the obstruction to horizontalizing change inside the present
reciprocal law.  The exact representation lesson is conditional and narrower:

> fixed-carrier spatial change cannot create reciprocal-spectral novelty; if the physical source
> quotients precisely those spatial directions as gauge, surviving novelty lies in the
> source-normal class.

The corpus's exceptional pure-spinor results independently select a colour-preserving normal
four-carrier.  Connecting `(6)` canonically to that exceptional normal channel is an open theorem,
not part of this card.

The stronger physical target is therefore not merely a normal quotient.  It must construct the
source-relative comparison that decides which spatial changes are gauge, which are observable
orientations, and how information absent from each isolated positive square survives between
successive carriers.

## Lean target

Create
`GaloisForLFunctions.HTGeometry.FixedCarrierSpatialReciprocalBlindness` proving:

1. the matrix identities `(2)` and `(3)`;
2. cyclic trace blindness `(4)` for every power;
3. scalar phase ternary Leibniz identity;
4. scalar reciprocal-square blindness;
5. injectivity of the real phase-rate family.

## Gates

- [x] exact statement frozen
- [x] paper proof dependency-closed
- [x] hostile status `REDISCOVERED / BRIDGE`
- [x] strongest positive representation survivor recorded
- [ ] exact Lean formalization
- [ ] axiom and lint audit
