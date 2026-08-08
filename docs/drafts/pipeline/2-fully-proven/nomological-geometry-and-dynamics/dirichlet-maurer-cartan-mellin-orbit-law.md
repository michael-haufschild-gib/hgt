# Dirichlet Maurer--Cartan and Mellin-orbit law

- **ID:** `ngd-dirichlet-maurer-cartan-mellin-orbit`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper)
- **Status:** `[PAPER-PROVED] [SOURCE-PURE] [NOT RH] [NO LEAN WRITTEN]`
- **Statement:** The differential Dirichlet gauge algebra has flat source current
  `M * delta(E) = Lambda`; its Mellin orbit is the Julia von-Mangoldt orbit.

## Setup

Let `A` be the complex algebra of all arithmetic functions under Dirichlet convolution

\[
 (f*g)(n)=\sum_{d\mid n}f(d)g(n/d).
\]

Let `epsilon(1)=1`, `epsilon(n)=0` for `n>1`, and define

\[
 E(n)=1,\qquad M(n)=\mu(n),\qquad
 (\delta f)(n)=(\log n)f(n).
 \tag{1}
\]

Adjoin a central formal one-form `du` and define a differential graded calculus by

\[
 \Omega^0=\mathcal A,\qquad \Omega^1=\mathcal A\,du,
 \qquad \Omega^k=0\ (k\ge2),
 \qquad d_Df=(\delta f)du,
 \qquad d_D(gdu)=0.
 \tag{1a}
\]

Then `d_D^2=0` and the graded Leibniz rule holds because `du wedge du=0`. Thus `delta` is only the
coefficient derivation; it is not incorrectly asserted to be square-zero.

For real `a`, set `sigma_a f(n)=n^(-a)f(n)`, and write
`E_a=sigma_aE`, `M_a=sigma_aM`.

## Theorem

1. `delta` is a derivation, `d_D` is a differential, `E*M=epsilon`, and the logarithmic
   Maurer--Cartan form is

   \[
   \boxed{\boldsymbol\Theta_E:=M*d_DE=-(d_DM)*E=\Lambda\,du.}
   \tag{2}
   \]

   Write `Theta_E=M*delta E=Lambda` for its coefficient.

2. `sigma_a` is an algebra automorphism and

   \[
   \partial_a\sigma_af=-\sigma_a\delta f.
   \tag{3}
   \]

3. With `Theta_a=sigma_aTheta_E`,

   \[
   \boxed{-M_a*\partial_aE_a=\Theta_a,
   \qquad \partial_aM_a=\Theta_a*M_a.}
   \tag{4}
   \]

4. If the Julia--Mellin orbit is defined by
   `J_u(n)=Lambda(n)n^(-1-u)`, then

   \[
   \Theta_a=J_{a-1}.
   \tag{5}
   \]

Consequently the source connection `partial_a-Theta_a*` is pure gauge on the invertible section
`M_a`; equivalently the form in `(2)` obeys the Maurer--Cartan equation, trivially in degree two.
It has zero one-parameter curvature. Any NGD curvature involving this source must arise
from comparison with another reduction, not from `Theta_E` alone.

## Proof

For every divisor `d|n`,

\[
 \log n=\log d+\log(n/d).
\]

Substitution in the convolution sum proves
`delta(f*g)=delta(f)*g+f*delta(g)`. Möbius inversion gives `E*M=epsilon`. Applying `delta` and using
`delta epsilon=0` yields

\[
 (\delta E)*M+E*(\delta M)=0.
\]

The algebra is commutative, so multiplication by `E` and `M=E^(-1)` gives the coefficient identity
underlying `(2)`. Definition `(1a)` then gives the displayed one-form equality. Its
Maurer--Cartan equation lies in `Omega^2=0`.

It remains to compute coefficients. For `n>=1`,

\[
 (M*\delta E)(n)=\sum_{d\mid n}\mu(d)\log(n/d).
 \tag{6}
\]

If `n=p^k`, only `d=1,p` survive and `(6)=k log p-(k-1)log p=log p`. If `n` has at least two
distinct prime divisors, expand each logarithm into prime valuations. For a fixed prime `p|n`, its
coefficient is an alternating sum over subsets of the other distinct prime divisors and equals

\[
 -\sum_{T\subseteq P(n)\setminus\{p\}}(-1)^{|T|}=0.
\]

For `n=1`, `(6)=0`. Thus `(6)=Lambda(n)`, proving `(2)`.

Since `n^(-a)=d^(-a)(n/d)^(-a)`, `sigma_a(f*g)=sigma_af*sigma_ag`. Coordinate differentiation
gives `(3)`. Apply `(3)` to `E`:

\[
 -M_a*\partial_aE_a=M_a*\sigma_a\delta E
 =\sigma_a(M*\delta E)=\Theta_a.
\]

Differentiate `M_a*E_a=epsilon` or apply `(3)` to `M`; either route gives the second formula in
`(4)`. Formula `(5)` is coefficientwise:

\[
 \Theta_a(n)=\Lambda(n)n^{-a}=J_{a-1}(n).
\]

Finally `(4)` says `(partial_a-Theta_a*)M_a=0`. This is the gauge transform of the trivial
one-parameter connection by the invertible element `M_a`; in one parameter its curvature 2-form
vanishes. `square`

## Exact significance for NGD

One source object already couples arithmetic inversion, spectral weights `log n`, positive
von-Mangoldt flow, and Mellin time. The theorem also enforces the GR correction:

\[
 \text{source charge}\ne\text{full reduction curvature}.
\]

The source is flat; curvature can occur only in Fourier reflection, completion, admission,
polarization, boundary, or capacity comparisons.

## Circularity audit

Definitions use only Möbius inversion and arithmetic functions. No Xi zero, RH-equivalent
positivity, central-line substitution, or divisor-dependent normalization occurs.

## Gates

- [x] dependency-closed coefficient proof
- [x] source flow and gauge identity proved
- [x] Julia--Mellin orbit identified
- [x] flatness scope stated
- [ ] formalized in Lean 4

## Lean-return note

No Lean code was written or built. A later formalization should first search existing arithmetic
function/convolution declarations and the formalized Möbius--von-Mangoldt weld before choosing a
module path.

## Log

- 2026-08-08 — paper proof closed and split from the open reduction-comparison problem.
