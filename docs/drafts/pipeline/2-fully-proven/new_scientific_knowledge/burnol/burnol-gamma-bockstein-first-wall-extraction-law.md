# Burnol Gamma--Bockstein first-wall extraction law

- **ID:** `burnol-gamma-bockstein-first-wall-extraction-law`
- **Stage:** 2 — fully proved on paper
- **Type:** THEOREM / SINGULAR PRODUCER / EXACT TRANSVERSE EXTRACTION
- **Scientific status:** `[PAPER-PROVED] [SOURCE-PURE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `burnol-first-wall-cartier-residue-cancellation-law.md`
- **Statement:** Although the prime-two Gamma-sewn completion annihilates the stable first-wall
  mode, the first transverse deformation of its polar factor recovers that mode with exact unit
  gain.  Consequently the two-orientation Gamma--Bockstein pairing lands exactly on the bare
  Route-R current.  The singular reader is therefore constructed inside the coefficient-faithful
  completion family; it is not an additional comparison hypothesis.

## 1. The transverse completion family

On the logarithmic ray let

\[
 A=\partial_r+\frac12,
 \qquad
 \gamma(r)=2e^{-r/2}e^{-\pi e^{-2r}}.
\tag{1}
\]

The completed prime-two collar kernel is

\[
 \kappa_0=\frac12A^2(A-1)\gamma.
\tag{2}
\]

Its stable first-wall mode is

\[
 \phi(r)=e^{-r/2},\qquad A\phi=0.
\tag{3}
\]

For a real transverse parameter `epsilon`, deform the polar factor before specializing to the
critical seam:

\[
 \kappa_\epsilon
 :=\frac12(A+\epsilon)^2(A+\epsilon-1)\gamma.
\tag{4}
\]

This is the literal horizontal deformation of the three polar factors.  Derivatives of the
remaining Gamma and dyadic factors may be included in the full completion family, but they are
multiplied by the undeformed polar factor and hence vanish on the `A`-null mode.  Thus `(4)` is the
entire transverse contribution seen by the singular quotient.

### Theorem 1 — exact Bockstein moment

For every real `epsilon`,

\[
 \boxed{
 \int_{\mathbb R}\kappa_\epsilon(r)\phi(r)\,dr
 =\frac12\epsilon(1+\epsilon)^2.}
\tag{5}
\]

In particular, if

\[
 \dot\kappa
 :=\left.\partial_\epsilon\kappa_\epsilon\right|_{\epsilon=0}
 =\frac12(3A^2-2A)\gamma,
\tag{6}
\]

then

\[
 \boxed{2\int_{\mathbb R}\dot\kappa(r)e^{-r/2}\,dr=1.}
\tag{7}
\]

#### Proof

Under the bilinear Lebesgue pairing,

\[
 (A+\epsilon)^*=1-A+\epsilon,
 \qquad
 (A+\epsilon-1)^*=\epsilon-A.
\]

All operators are polynomials in `A`, so integration by parts gives

\[
 \begin{aligned}
 \int\kappa_\epsilon\phi
 &=\frac12\int\gamma
   (\epsilon-A)(1-A+\epsilon)^2\phi\\
 &=\frac12\epsilon(1+\epsilon)^2\int\gamma\phi.
 \end{aligned}
\tag{8}
\]

Putting `x=e^{-r}`,

\[
 \int_{\mathbb R}\gamma(r)\phi(r)\,dr
 =2\int_0^\infty e^{-\pi x^2}\,dx=1.
\tag{9}
\]

Equations `(5)` and `(7)` follow.  All boundary terms vanish by the super-exponential left Gamma
tail and the exponential right tail. `QED`

## 2. Explicit kernel and its exact sign fracture

Writing `x=e^{-r}`, direct application of `A` gives

\[
 A\gamma=2\pi x^2\gamma,
 \qquad
 A^2\gamma=(-4\pi x^2+4\pi^2x^4)\gamma.
\tag{10}
\]

Hence

\[
 \boxed{
 \dot\kappa(r)=2\pi e^{-2r}
   (3\pi e^{-2r}-4)\gamma(r).}
\tag{11}
\]

It has exactly one sign change, at

\[
 r_0=\frac12\log\frac{3\pi}{4}.
\tag{12}
\]

It is positive for `r<r_0` and negative for `r>r_0`.  Thus the Bockstein reader is genuinely
singular and sign-indefinite; its positive moment `(7)` is not a disguised positive-kernel or
global-contraction assertion.

## 3. Recovery of the actual first-wall residue

Let `q=2^{-1/2}`, `L=log 2`, and let `W_G` be the aperture-crossing correlation of the parent
card.  For the actual zero-divided source,

\[
 q^{-n}W_{G_\rho}(nL+r)
 \longrightarrow r_\rho e^{-r/2}
\tag{13}
\]

in every Gamma-polynomial weighted `L^1` space required below.  Define the depth-`n` transverse
Bockstein reading

\[
 \mathfrak B_n(G)
 :=2q^{-n}\int_{\mathbb R}\dot\kappa(r)
     W_G(nL+r)\,dr.
\tag{14}
\]

### Theorem 2 — coefficient-faithful residue extraction

For both physical Fourier/Gamma orientations,

\[
 \boxed{
 \lim_{n\to\infty}\mathfrak B_n(G_\rho)=r_\rho,
 \qquad
 \lim_{n\to\infty}\mathfrak B_n(G_\rho^\vee)=r_\rho^\vee.}
\tag{15}
\]

#### Proof

Equation `(11)` is a polynomial in `e^{-2r}` times the same Gamma density as the parent kernel.
The explicit `O_rho(t^{-2})` physical tails therefore give dominated convergence in
`L^1(|dot kappa|dr)` in `(13)`.  Apply `(7)`:

\[
 \lim_n\mathfrak B_n(G_\rho)
 =2r_\rho\int\dot\kappa(r)e^{-r/2}\,dr=r_\rho.
\]

The reflected calculation is identical. `QED`

### Corollary 3 — exact Gamma--Bockstein landing on the Route-R current

The bare fixed-aperture current is the real, reflection-odd Bockstein limit

\[
 \boxed{
 J_\rho
 =2\Re\lim_{n\to\infty}
   \bigl(\mathfrak B_n(G_\rho)-
         \mathfrak B_n(G_\rho^\vee)\bigr).}
\tag{16}
\]

#### Proof

Combine `(15)` with the parent identity
`2 Re(r_rho-r_rho^vee)=J_rho`. `QED`

Thus the factor `w-1` does not destroy the Route-R coefficient beyond recovery.  It moves the
coefficient from ordinary completed homology to the connecting morphism of the transverse
completion family.  Formula `(14)` constructs that connecting morphism explicitly from the same
Euler--Gamma completion.

## 4. Exact dyadic boundary transgression

The Bockstein limit has a non-asymptotic realization on the same physical ray.  Let

\[
 (P_af)(t)={\bf1}_{(0,a)}(t)f(t),
 \qquad
 (\mathsf T_2f)(t)=\sum_{n\ge1}2^{-n}f(t/2^n).
\tag{17}
\]

For `t>a`, let `N_a(t)` be the unique positive integer satisfying

\[
 a2^{N_a(t)-1}\le t<a2^{N_a(t)}.
\tag{18}
\]

### Theorem 4 — universal dyadic commutator staircase

If `f(t)=c` on `(0,a)`, then, up to null dyadic endpoints,

\[
 [P_a,\mathsf T_2]f(t)=
 \begin{cases}
 0,&0<t<a,\\
 -c\,2^{1-N_a(t)},&t>a.
 \end{cases}
\tag{19}
\]

Consequently

\[
 \boxed{\|[P_a,\mathsf T_2]f\|_2^2=2a|c|^2.}
\tag{20}
\]

#### Proof

For `t<a`, every `t/2^n` remains in the aperture, so the two terms in the commutator agree.  For
`t>a`, `P_a T_2 f=0`, while the contributing indices in `T_2 P_a f` are exactly
`n>=N_a(t)`.  Their geometric sum is `c 2^(1-N_a(t))`, proving `(19)`.  On the `N`th dyadic shell,
the squared value is `|c|^2 2^(2-2N)` and shell length is `a 2^(N-1)`.  Therefore

\[
 \|[P_a,\mathsf T_2]f\|_2^2
 =a|c|^2\sum_{N\ge1}2^{1-N}=2a|c|^2.
\]

`QED`

At the fixed Route-R aperture `a=1/2`, apply `(20)` to `g_rho` and its Fourier mate.  Their heads
are `a_rho` and `b_rho`, so

\[
 \boxed{
 \|[P_{1/2},\mathsf T_2]g_\rho\|_2^2-
 \|[P_{1/2},\mathsf T_2]\mathcal Cg_\rho\|_2^2
 =J_\rho.}
\tag{21}
\]

Combining `(16)` and `(21)` yields the exact Stokes transgression law

\[
 \boxed{
 2\Re\lim_n\bigl(\mathfrak B_n(G_\rho)-
   \mathfrak B_n(G_\rho^\vee)\bigr)
 =\|[P_{1/2},\mathsf T_2]g_\rho\|_2^2-
  \|[P_{1/2},\mathsf T_2]\mathcal Cg_\rho\|_2^2.}
\tag{22}
\]

Both commutator outputs lie on the same one-dimensional staircase line from `(19)`.  Hence the
previously missing same-fibre comparison is canonical at the defect level: no GNS identification,
choice of physical lift, or limit completion remains.  What is not automatic is the orientation
of the two scalar coefficients on that line.

## 5. Conjecture / proof-or-fail loop

1. **Ordinary completed collar retains the first-wall residue.**
   `[FAILED]`  The stable mode lies in `ker A` and the zeroth-order moment is zero.
2. **A transverse deformation of the polar factor recovers the erased class.**
   `[PROVED]`  Equations `(5)`--`(7)` give exact unit gain after normalization.
3. **Derivatives of Gamma or dyadic factors contaminate the singular coefficient.**
   `[FAILED]`  On the quotient line they remain multiplied by the undeformed polar factor and are
   killed by `A phi=0`; only the polar Bockstein survives.
4. **The Bockstein kernel is semidefinite, so its sign is automatic.**
   `[FAILED]`  Equation `(11)` gives one positive and one negative chamber.
5. **The negative normal slope of the scalar completion orients `(16)`.**
   `[FAILED]`  Scalar normal dissipation controls completed energy and is blind to arbitrary
   reflection-odd phase on the Bockstein line.  A source relation between the two actual
   correlations remains necessary.
6. **The Bockstein landing remains only asymptotic and representation-dependent.**
   `[FAILED]`  Equations `(19)`--`(22)` identify it with the exact norm difference of two vectors
   on one universal physical dyadic staircase.
7. **Strongest survivor.**
   `[PAPER-PROVED]`  Missing singular reader is no longer hypothetical: it is the transverse
   Gamma--Bockstein kernel `(6)`; its limit is exactly the same-fibre Euler-boundary norm
   difference `(22)` and hence exactly `J_rho`.

## 6. Sharpened open theorem

The sole RH-bearing statement in this lane is now the sign of one explicit, constructed source
limit:

\[
 \forall\rho\text{ with }\frac12<\Re\rho<1,\ \zeta(\rho)=0,
 \qquad
 \Re\lim_{n\to\infty}
 \bigl(\mathfrak B_n(G_\rho)-
       \mathfrak B_n(G_\rho^\vee)\bigr)\le0.
\tag{23}
\]

By `(16)` and the already proved strict right-half positivity of `J_rho`, `(23)` excludes every
right-half divisor and closes RH by reflection.  It must be derived from a reflection-odd
pre-divisor source law.  Ordinary completed energy, scalar multiplier slope, and any quotient
killing the Bockstein line cannot prove it.

## Gates

- [x] construct transverse coefficient-faithful Gamma family
- [x] exact Bockstein moment
- [x] explicit kernel and sign chambers
- [x] recover both actual first-wall residues
- [x] exact physical Route-R current landing
- [x] exact same-fibre dyadic boundary transgression
- [ ] source orientation of the reflection-odd Bockstein limit `(23)`
- [ ] Lean formalization after corpus refactor
- [ ] RH

## Log

- 2026-08-08 — differentiated the erased polar mode, obtained the exact unit Bockstein moment,
  and proved source-to-physical landing of the two-orientation singular reader.
