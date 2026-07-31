# Scalar suspension cannot realize the Poisson--zeta transfer

- **ID:** `deninger-scalar-suspension-poisson-transfer-no-go`
- **Stage:** 2-fully-proven
- **Type:** SOURCE NO-GO WITH POSITIVE SURVIVOR
- **Label:** `DAC_SCALAR_SUSPENSION_POISSON_TRANSFER_NO_GO`
- **Parent:** `deninger-poisson-relevant-complex-comparison`
- **Statement:** Meyer's zeta operator cannot descend from ordinary
  deck pullback on Deninger's scalar leafwise sheaf; its summands are
  instead ordinary pullbacks by the discrete positive-time flow.
- **Lean status:** algebraic deck-sum collapse and normalized
  suspension-flow identities drafted in
  `DeningerArithmeticPoissonTransfer.lean`; direct check deferred
  while unrelated Lean builds saturate the shared machine.

## Source setup

Deninger's suspension cover is
\[
 \widetilde X=\check X(\mathbb C)\times\mathbb R_{>0},
\]
with right action
\[
 r_q(P,u)=(F_qP,q^{-1}u),\qquad q\in\mathbb Q_{>0},
                                                               \tag{1}
\]
and quotient \(X=\widetilde X/\mathbb Q_{>0}\).  A scalar section on
\(X\) pulls back to a function \(a\) on \(\widetilde X\) satisfying
\[
 a\circ r_q=a.                                                   \tag{2}
\]

Meyer's zeta operator is
\[
 Zf(u)=\sum_{n\ge1}f(nu)
      =\sum_{n\ge1}\lambda_n^{-1}f(u).                            \tag{3}
\]
The tempting source interpretation is to regard the summands in
`(3)` as scalar pullbacks along the Frobenius deck transformations
`(1)`.

## No-go theorem

`[PROVED HERE] [DAC_SCALAR_SUSPENSION_POISSON_TRANSFER_NO_GO]`

For every descended scalar section \(a\) and every \(n\ge1\),
\[
 r_n^*a=a.                                                        \tag{4}
\]
Consequently its \(N\)-term Frobenius sum is
\[
 \sum_{n=1}^{N}r_n^*a=N\,a.                                      \tag{5}
\]
Over characteristic zero, `(5)` has no limit that can equal Meyer's
operator `(3)` on a nonzero scalar section in any Hausdorff locally
convex topology in which the scalar ray
\(\{Na:N\ge1\}\) is unbounded.  In particular, ordinary scalar
pullback on the quotient cannot produce the closed injective map
\[
 Z:H_\cap\longrightarrow H_-.
\]

### Proof

Equation `(4)` is exactly the descent equation `(2)` with \(q=n\).
Summing `(4)` for \(1\le n\le N\) gives `(5)`.  If \(a\ne0\), choose
a continuous linear functional \(\ell\) with \(\ell(a)\ne0\), as
available in a Hausdorff locally convex space.  Then
\[
 \ell(Na)=N\ell(a)
\]
is unbounded, so the partial sums do not converge.  Meyer's
\(Z\), by contrast, is a continuous non-scalar operator on its
weighted Schwartz domain.  Thus the proposed identification is
impossible.

## Strongest positive survivor

`[POSITIVE SURVIVOR] [DAC_DENINGER_FLOW_POISSON_DILATION]`

Deck action and flow action must be kept separate.  Deninger's flow is
\[
 \phi^t[P,u]=[P,e^tu].
\]
For every integer \(n\ge1\),
\[
 [F_nP,u]=[P,nu]=\phi^{\log n}[P,u],                              \tag{6}
\]
because the deck transformation \(n\) sends \((P,nu)\) to
\((F_nP,u)\).  Thus a descended scalar function need not be fixed by
the discrete flow.  On any descended radial coordinate \(x\) satisfying
\(x(\phi^t y)=e^t x(y)\),
\[
 (\phi^{\log n})^*(f\circ x)
 =(z\mapsto f(nz))\circ x.                                       \tag{7}
\]
Consequently Meyer's operator is the convergent flow sum
\[
 Z=\sum_{n\ge1}(\phi^{\log n})^*                                 \tag{8}
\]
on its source-defined Schwartz domain.

`DAC_DENINGER_HILBERT_KUMMER_RADIAL_SUSPENSION` constructs a canonical
global \(x\) on the dense Hilbert--Kummer refinement of Deninger's
generic character space.  The relevant coefficient remains necessary
to encode its refined topology, real endpoint conditions, nonradial
derived directions, and cup/Hodge structure.  It is not needed to
invent a non-scalar replacement for each summand in `(8)`.

## Local logarithmic radial realization

`[PROVED HERE] [DAC_VERSCHIEBUNG_LOG_RADIAL_DILATION]`

The required analytic formula is already exact on every
one-coordinate punctured-disk collar.  Put
\[
 \ell(z)=-\log|z|,\qquad 0<|z|<1.
\]
Then \(\ell(z)>0\), and for \(\pi_n(z)=z^n\),
\[
 \ell(\pi_n(z))
 =-\log|z^n|
 =-n\log|z|
 =n\ell(z).                                                       \tag{10}
\]
Therefore every function \(f:\mathbb R_{>0}\to\mathbb C\) satisfies
\[
 \pi_n^*(f\circ\ell)(z)
 =f(\ell(z^n))
 =f(n\ell(z))
 =(\lambda_n^{-1}f)(\ell(z)).                                    \tag{11}
\]
For \(f\) in Meyer's right-decaying domain, his convergence theorem
then gives on this collar
\[
 \sum_{n\ge1}\pi_n^*(f\circ\ell)
 =(Zf)\circ\ell.                                                  \tag{12}
\]

This is the coordinate restriction of `(7)`.  The corresponding global
gluing is supplied by the norm of the full bounded Kummer functional in
`DAC_DENINGER_HILBERT_KUMMER_RADIAL_SUSPENSION`; what remains open is
the derived sheaf comparison and strict \(H_\cap\to H_-\) topology.

The survivor reduces
`DAC_DENINGER_POISSON_RELEVANT_COMPLEX_COMPARISON` to four source
obligations:

1. sheafify the dense Hilbert--Kummer refinement and its radial
   Schwartz cosheaf;
2. derive the two real endpoint conditions defining \(H_\cap\);
3. prove the global strict locally convex convergence `(8)`;
4. identify the resulting flow-sum cokernel with
   \(H_-/Z(H_\cap)\), compatibly with cup and flow.

## Scope

- This theorem does not use a zeta zero, RH, CCM, or numerical
  computation.
- It does not rule out Deninger's scalar sheaf for \(H^0\); it rules
  out using scalar deck pullback as the middle Poisson differential.
- It does not rule out Frobenius/Verschiebung correspondences elsewhere
  in the coefficient theory.  It proves that no conjectural
  coefficient transfer is needed for the individual Poisson dilation
  terms.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  equation defining the \(G\times\mathbb Q_{>0}\)-action on the
  suspension cover and §12:
  https://arxiv.org/abs/1807.06400
- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann
  zeta function*, Definition 3.1 and Theorem 3.3:
  https://arxiv.org/abs/math/0412277

## Log

- 2026-07-27 — Extracted from the exact suspension deck relation and
  Meyer's source-defined zeta operator.
- 2026-07-27 — Corrected the positive survivor after separating deck
  action from flow: fixed-height Frobenius is discrete positive-time
  flow and realizes each Poisson dilation on scalar radial sections.
