# Two-scale local-rotation de-aliasing law

## Status

- Paper proof: dependency-closed.
- Lean formalization: complete; source and axiom audits pass.
- Novelty status: not assessed; used as an internal bridge, with no novelty claim.

## Statement

Let (R) be a unital ring. Let (A,B,J,X\in R) satisfy

\[
A^2=B^2=1,\qquad AB=BA,\qquad J^2=-1,
\]

and let (J) commute with (A,B,X). Put

\[
H=A+B,\qquad S=AB,
\]

and, for (t\in\{1,2\}),

\[
T_{t,+}=1+tJH-t^2S,
\qquad
T_{t,-}=1-tJH-t^2S,
\]
\[
\Delta_t(X)=T_{t,+}XT_{t,-}-T_{t,-}XT_{t,+}.
\]

Then, for every (X),

\[
\boxed{\;12[H,X]=J\bigl(\Delta_2(X)-8\Delta_1(X)\bigr).\;}
\]

No parity, spectral, differentiability, genericity, or limiting premise occurs.

## Proof

For arbitrary central scalar (t), set (E_t=1-t^2S). Since

\[
T_{t,+}=E_t+tJH,
\qquad
T_{t,-}=E_t-tJH,
\]

direct expansion gives

\[
\Delta_t(X)
=2t\bigl(JH X E_t-E_tXJH\bigr).
\]

At (t=1) and (t=2), therefore,

\[
\Delta_1=2\bigl(JHX(1-S)-(1-S)XJH\bigr),
\]

\[
\Delta_2=4\bigl(JHX(1-4S)-(1-4S)XJH\bigr).
\]

Subtracting eight copies of the first identity from the second cancels every
term containing (S):

\[
\Delta_2-8\Delta_1=-12(JHX-XJH).
\]

Because (J) commutes with (H) and (X), and (J^2=-1),

\[
J(JHX-XJH)=-[H,X].
\]

Multiplying the preceding cancellation identity by (J) proves the claim.

## Quantum specialization

For a one-site Pauli involution (P) on each of two replicas, take

\[
A=P\otimes I,\qquad B=I\otimes P,\qquad J=iI.
\]

Then (H=A+B) generates the physical collective commutator. Moreover

\[
T_{t,+}=(I+tiA)(I+tiB),
\qquad
T_{t,-}=(I-tiA)(I-tiB).
\]

Thus each raw term is a nonzero scalar multiple of conjugation by the local
unitary ((I+tiP)/\sqrt{1+t^2}), doubled across the replicas. The law therefore
recovers the exact infinitesimal collective commutator from four finite local
rotations at the two fixed scales (t=1,2). The second scale removes the
relative-even frequency alias left by Clifford quarter turns alone.

Writing `R_2` for doubled conjugation by the normalized scale-two rotation
and `C` for doubled Clifford quarter-turn conjugation, scalar normalization
gives the exact physical identity

\[
[H,X]=\frac{i}{12}\left(
25(R_2X-R_2^{-1}X)-32(CX-C^{-1}X)\right).
\]

The coefficients `25` and `32` are forced by the inverse normalizations:
the scale-two doubled inverse contributes `1/25`, whereas each doubled
quarter turn contributes `1/4`.

## Hall-obstruction closure consequence

Let `U` be the canonical greatest defect maximizer for the full two-replica
q-local collective-commutator family on any finite qubit register. Exact
weight preservation proves that `U` is fixed by both doubled rotations in the
identity above. Product-Clifford covariance proves the same for both quarter
turns. Since `U` is a complex subspace, the displayed identity therefore
implies, for every site `j`, Pauli axis `a`, and `X in U`,

\[
[P_{j,a}\otimes I+I\otimes P_{j,a},X]\in U.
\]

This removes the relative-odd character premise from the earlier
first-order interpolation theorem. Every one-site collective generator now
acts internally on the canonical obstruction.

## Dependency audit

- Pure ring expansion.
- No analytic differentiation.
- No computation or asymptotics.
- No unproved premise.

## Hostile check

- One scale cannot recover the full commutator: at (t=1), the (S)-even
  contribution is annihilated. The second scale is essential.
- q-local span covariance, Hall-maximizer invariance, and first-order internal
  closure are now discharged separately; none is inferred from the raw ring
  identity alone.
- Physical-unitary interpretation uses only scalar normalization; conjugation
  is unchanged because normalizing factors cancel with their inverses.

## Formal sources

- `TwoReplicaTwoScaleCommutatorDealiasing.lean`: universal ring identity.
- `TwoReplicaRationalLocalRotationCovariance.lean`: exact rational gate,
  inverse, Pauli-weight preservation, q-local span covariance, and fixed-point
  theorem for the canonical greatest maximizer.
- `TwoReplicaTwoScaleLocalCommutatorClosure.lean`: physical two-scale identity
  and unconditional one-site commutator closure.

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` on
the matrix-level consequences; the pure ring identity uses only `propext` and
`Quot.sound`.
