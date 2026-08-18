# Prime--archimedean Bernstein Legendre double-source kernel

- **ID:** `prime-arch-bernstein-legendre-double-source-kernel`
- **Stage:** 2-fully-proven
- **Type:** exact value relation / reflection law / top-down interface
- **Status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean status:** paper theorem; its one-variable parents are formalized, but the double functional
  and algebraic kernel are not yet formalized

## General identity

Let `m : N -> R`, let `L_m` be its polynomial moment functional, and write

\[
 B_{n,i}(x)=\binom ni x^i(1-x)^{n-i},\qquad
 b_{n,i}=L_m(B_{n,i}),\qquad
 \Pi_n=\sum_{i=0}^n b_{n,i}^2.
\]

Let `L_m tensor L_m` be the bivariate polynomial functional determined by

\[
 (L_m\otimes L_m)(x^j y^k)=m_jm_k.
\]

Put

\[
 A(x,y)=1-x-y+2xy,qquad D(x,y)=1-x-y
\]

and choose the square-root branch equal to `1` at `t=0` in

\[
 K(t;x,y)=
 \frac{1}{\sqrt{1-2tA(x,y)+t^2D(x,y)^2}}.                 \tag{1}
\]

Then, as a formal power series in `t`,

\[
 \boxed{
 \sum_{n\ge0}\Pi_n t^n=(L_m\otimes L_m)K(t;x,y).
 }                                                               \tag{2}
\]

The right side is unambiguous formally: the coefficient of `t^n` in `K` is a polynomial in
`x,y`, so the ordinary polynomial functional is applied coefficientwise.

## Proof

Introduce the degree-`n` Bernstein row kernel

\[
 S_n(x,y)=\sum_{i=0}^n B_{n,i}(x)B_{n,i}(y).              \tag{3}
\]

Linearity gives immediately

\[
 (L_m\otimes L_m)S_n
 =\sum_{i=0}^n L_m(B_{n,i})L_m(B_{n,i})=\Pi_n.            \tag{4}
\]

It remains to sum `S_n`.  Equivalently, if `CT_w` denotes the constant Laurent coefficient in
`w`, then

\[
 S_n(x,y)=\operatorname{CT}_w
 \bigl((1-x+xw)(1-y+yw^{-1})\bigr)^n.                    \tag{5}
\]

Write

\[
 a=(1-x)(1-y)+xy=A(x,y),\quad
 b=x(1-y),\quad c=(1-x)y.
\]

Summing the geometric series before extracting the constant term gives

\[
 \sum_{n\ge0}S_n(x,y)t^n
 =\operatorname{CT}_w\frac1{1-t(a+bw+cw^{-1})}
 =\frac1{\sqrt{(1-at)^2-4bc\,t^2}}.                     \tag{6}
\]

For completeness, the coefficient of `a^m(bc)^k t^(m+2k)` on both sides is

\[
 \frac{(m+2k)!}{m!\,k!^2}.
\]

Finally,

\[
 a^2-4bc=(1-x-y)^2=D(x,y)^2,                             \tag{7}
\]

so `(6)` is exactly `(1)`.  Combining `(4)` and `(6)` proves `(2)`.

## Exact reflections

The kernel has both symmetries

\[
 K(t;x,y)=K(t;y,x)=K(t;1-x,1-y).                         \tag{8}
\]

The second follows because `A(1-x,1-y)=A(x,y)` while
`D(1-x,1-y)=-D(x,y)`.  Thus simultaneous complement reflection is a static constraint of the
whole purity germ, not a degree-by-degree evolution law.

The conjugate-reflected specialization contains the orientation datum.  For `u in C`, define

\[
 B_+(u)=|u|+|1-u|,\qquad B_-(u)=|u|-|1-u|.
\]

Since

\[
 A(u,\bar u)=|u|^2+|1-u|^2,qquad
 D(u,\bar u)^2=(1-2\operatorname{Re}u)^2,
\]

one has the exact factorization

\[
 \boxed{
 1-2tA(u,\bar u)+t^2D(u,\bar u)^2
 =(1-B_+(u)^2t)(1-B_-(u)^2t).
 }                                                               \tag{9}
\]

Hence the first positive-real algebraic branch point of the reflected atom kernel is

\[
 t=B_+(u)^{-2}.                                           \tag{10}
\]

This is exactly the reciprocal square of the already formalized endpoint Bernstein atom
amplitude

```text
xiEndpointBernsteinAtomAmplitudeBase q
  = ||u_q|| + ||1-u_q||.
```

Under false RH, the current Lean corpus proves that a maximal amplitude `B>1` is attained and that
the complete positive susceptibility has exact radius `R_A=B^(-2)`.  Equation `(9)` therefore
identifies the abstractly selected radius with the positive reflected-kernel pinch of a maximizing
source atom.  It does not infer a full-series singularity from one summand; noncancellation of the
maximal exponential mode is supplied by the existing formal theorem.

## Prime--Gamma specialization

Take

\[
 m_n=
 \frac{\texttt{normalizedPrimeArchMoment}(n)}
 {\texttt{primeArchEndpointHausdorffRadius}^n}.
\]

Then `Pi_n` is exactly `primeArchEndpointBernsteinPurity n`, so `(2)` is an unconditional
source-value formula for the complete Abel susceptibility.  Moreover the ordinary moment germ

\[
 M_R(v)=\sum_{n\ge0}m_nv^n                              \tag{11}
\]

is determined by the already formalized even prime--Gamma germ
`normalizedPrimeArchMomentGerm`: locally,

\[
 M_R(v)=
 \texttt{normalizedPrimeArchMomentGerm}\!\left(\sqrt{v/R}\right), \tag{12}
\]

where the right side is independent of the local square-root choice because that germ is even.
Thus the whole susceptibility germ is determined by two copies of one continued prime--Gamma
source germ and the universal algebraic kernel `(1)`.

## What this changes

The source problem no longer has to be stated as control of every finite coefficient vector.  It
may instead be stated as regularity of one explicit double source evaluation of `K`.  In the
divisor-resolved false-RH geometry already formalized in Lean, the critical positive-axis
obstruction is the attained reflected algebraic pinch `(9)`.

This is not itself an RH proof.  Extending `(L_m tensor L_m)K` by defining it through its Taylor
coefficients would merely restate the Abel criterion.  A useful continuation must be obtained
independently from the continued prime--Gamma or theta source formula.

The companion pole--residue law
`prime-arch-moment-pole-residue-pinch-law.md` makes the same obstruction entirely source-local:
the ordinary moment germ has simple poles `p=1/u` with residue exactly `-R` times the divisor-fibre
multiplicity, and the pole position and residue determine both the pinch radius and its nonzero
half-order coefficient.

## Formalization target

1. Define a bivariate polynomial moment functional and prove `(4)`.
2. Formalize `S_n` and its constant-term or direct binomial generating identity `(6)`.
3. Prove the kernel reflections `(8)` and conjugate factorization `(9)`.
4. Specialize `(2)` to `primeArchEndpointBernsteinPurity`.
5. Connect `(10)` to `PrimeArchEndpointBernsteinAttainedExactThreshold` and the exact Abel radius.
6. Only after targeted Lean verification is permitted, wire the resulting module into
   `RHTower.lean`.

## Literature calibration

The algebraic square root is the classical Legendre generating function; see NIST DLMF
[18.12.11](https://dlmf.nist.gov/18.12.E11).  The constant-term derivation above supplies the exact
Bernstein-row specialization needed here.  No novelty is claimed for the abstract generating
identity.  The project contribution is its exact splice to the formal prime--Gamma moment
functional, the endpoint amplitude, and the RH-critical Abel radius.

## Gates

- [x] double-source kernel identity proved on paper
- [x] simultaneous complement reflection proved on paper
- [x] conjugate reflected-pinch factorization proved on paper
- [x] endpoint prime--Gamma specialization identified
- [x] exact-radius splice identified
- [ ] Lean formalization
- [ ] independent source continuation across the Abel collar
- [ ] RH

## Half-order maximal-packet refinement

The companion theorem
`prime-arch-bernstein-half-order-pringsheim-singularity.md` combines this reflected factorization
with the formal maximal-packet and ellipse-phase rigidity laws. Under false RH it proves the exact
local decomposition

\[
 \chi(t)=H(t)+\frac{A(t)}{\sqrt{1-B^2t}},\qquad A(B^{-2})>0,
\]

and hence the positive asymptotic

\[
 \Pi_n\sim \kappa B^{2n}n^{-1/2},\qquad \kappa>0,
\]

so the `(1-B^2t)^(-1/2)` term has nonzero monodromy in the complete susceptibility. Therefore
a single-valued **meromorphic**, rather than holomorphic, source continuation through the thin
collar already implies RH.
