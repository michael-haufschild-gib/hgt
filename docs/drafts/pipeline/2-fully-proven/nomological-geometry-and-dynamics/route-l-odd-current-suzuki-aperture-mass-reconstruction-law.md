# Route-L odd current, Suzuki aperture, and Mass reconstruction law

- **ID:** `ngd-route-l-suzuki-aperture-mass-reconstruction`
- **Stage:** 2 — fully proved on paper
- **Status:** `[PAPER-PROVED] [NORMAL-DERIVATIVE/D/P INVERTIBLE COEFFICIENT TRANSFORM]`
  `[PRIMITIVE-PRIME PROJECTION] [NOT RH]`
  `[NO LEAN WRITTEN]`
- **Purpose:** prove that the full Suzuki prime-torque aperture profile is the hinge transform of
  the Route-L odd current and reconstructs its prime-power coefficients, including the Mass
  half-density prime current.

## 1. Objects

Let

\[
 a_n=\log n,
 \qquad
 w_n=\frac{\Lambda(n)\log n}{\sqrt n},
\]

and define the order-zero locally finite signed Radon measure

\[
 D=XK_{\rm pr}
 =-\sum_{n\ge2}w_n(\delta_{a_n}-\delta_{-a_n}).
\tag{1}
\]

For `L>0`, define the odd compactly supported hinge

\[
 \phi_L(t)=-\frac12(L-|t|)_+\sinh t.
\tag{2}
\]

The established Suzuki prime torque is

\[
 P(L)=\sum_{n\ge2}w_n(L-a_n)_+\sinh(a_n).
\tag{3}
\]

For each fixed `L`, only `n<=e^L` contributes, so every sum is finite. The hinge `phi_L` is
continuous and compactly supported but not smooth. Pairings below use the canonical Radon-measure
pairing with `C_c(R)`, not the action of an arbitrary distribution on a test function.

## 2. Exact hinge transform

### Theorem 2.1

For every `L>0`,

\[
 \boxed{P(L)=\langle D,\phi_L\rangle.}
\tag{4}
\]

#### Proof

For `a>0`, oddness of `(2)` gives

\[
 \phi_L(a)-\phi_L(-a)
 =-(L-a)_+\sinh a.
\]

Pairing `(1)` with `(2)` therefore yields

\[
 \langle D,\phi_L\rangle
 =-\sum_{n\ge2}w_n
   \bigl(\phi_L(a_n)-\phi_L(-a_n)\bigr)
 =P(L).
\]

This is `(4)`. ∎

## 3. Inversion in aperture

### Theorem 3.1 — normalized coefficient-space isomorphism

Let `A` be the vector space of locally finite odd atomic measures

\[
 D_w=-\sum_{n\ge2}w_n(\delta_{a_n}-\delta_{-a_n})
\]

supported on `{+-log n}`. Let `P` be the vector space of continuous locally piecewise-linear
functions on `(0,infinity)` whose knots lie in `{log n}` and which vanish on
`0<L<=log 2`. The hinge transform

\[
 D_w\longmapsto P_w(L)=\sum_{n\ge2}w_n\sinh(a_n)(L-a_n)_+
\]

is a bijection `A->P`.

As a distribution on the positive aperture line,

\[
 \boxed{
 P''(L)=\sum_{n\ge2}w_n\sinh(a_n)\,\delta_{a_n}.}
\tag{5}
\]

Its inverse is `(5)`, so the full normalized function `P(L)` determines `D` coefficientwise.

#### Proof

For fixed `a>0`, the distributional second derivative of `(L-a)_+` is `delta_a`. Applying this
termwise to the locally finite sum `(3)` gives `(5)`. Since the locations `a_n=log n` are distinct
and `sinh(a_n)!=0`, the mass at `a_n` recovers

\[
 w_n=\frac{\operatorname{mass}_{a_n}(P'')}{\sinh(a_n)}.
\]

Equation `(1)` then reconstructs `D`. Conversely, every function in `P` is reconstructed from its
slope jumps and zero initial affine part. The normalization is essential because second
differentiation alone has an affine kernel. ∎

### Corollary 3.2 — Mass prime coefficient

For a prime `p`, let

\[
 t_p=\frac{\log p}{\sqrt p}.
\]

Then

\[
 \operatorname{mass}_{\log p}(P'')
 =t_p\log p\,\sinh(\log p),
\tag{6}
\]

so

\[
 \boxed{
 t_p=
 \frac{\operatorname{mass}_{\log p}(P'')}
      {(\log p)\sinh(\log p)}.}
\tag{7}
\]

#### Proof

At a prime, `Lambda(p)=log p`, hence
`w_p=(log p)^2/sqrt(p)=t_p log p`. Substitute in `(5)`. ∎

## 4. Cross-route statement

Combining this theorem with the half-density weld gives the exact coefficient chain

\[
 \text{Route-L half-density normal derivative }
 \dot\kappa_0=\left.\partial_a\kappa_a\right|_0
 \longleftrightarrow
 \text{odd distribution }D
 \longleftrightarrow
 \text{Suzuki aperture profile }P
 \longrightarrow
 \text{Mass prime coefficients }(t_p).
\tag{8}
\]

The first two arrows are bijections between the normalized coefficient objects above. Formula
`(7)` is the primitive-prime quotient and kills every higher prime-power grade; it is not injective
on the full current. This is a cross-route coefficient transform, not a common scalar analogy.

## 5. Exact scope and no-gos

1. The theorem reconstructs Suzuki's arithmetic prime-torque term, not the independent
   archimedean term, Gamma normalization, aperture recurrence carrier, or final selector.
2. It reconstructs Mass half-density coefficients, not the full Mass outgoing `T dF` bulk or its
   capacity geometry.
3. It uses no Xi zero and proves no critical-line statement.
4. The hinge transform is not the LTG field theorem: it joins three arithmetic/spectral charts but
   does not construct a common stability filtration, positive real form, or topology.
5. Any proposed common lawspace must reproduce `(4)--(7)` exactly. Failure is a direct falsifier.
6. These maps identify a common arithmetic coefficient skeleton. They prove neither isomorphism
   nor nonisomorphism of full Route-L, Suzuki/G, and Mass organs. Untransported structures include
   the Route-L parameter connection and horizontal collar, Suzuki archimedean and recurrence data,
   and Mass incidence/capacity geometry.

## 6. Corpus imports

- The odd current `(1)` is imported from `critical-euler-mass-weil-stokes-shadow-law.md`,
  Theorem 3, equations (10)--(11).
- Its Route-L origin as the normal derivative is imported from
  `half-density-route-l-odd-weil-connection-weld.md`, Corollary 2.2, equations (4)--(6).
- Formula `(3)` is imported from
  `../new_scientific_knowledge/suzuki/suzuki-weil-position-torque-recurrence.md`, equations
  (7)--(10).
- The Mass coefficient `t_p` is imported from `critical-euler-mass-weil-stokes-shadow-law.md`,
  Theorem 2.

## 7. Lean boundary

No Lean was written or built. A later proof can formalize finite aperture truncations and the
piecewise-linear second-derivative identity after declaration research. No formal work is
authorized at this stage.
