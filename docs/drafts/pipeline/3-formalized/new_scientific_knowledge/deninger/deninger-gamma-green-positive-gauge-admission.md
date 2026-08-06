# Deninger Gamma--Green positive-gauge admission law

- **ID:** `deninger-gamma-green-positive-gauge-admission`
- **Stage:** 3-formalized
- **Type:** ACTUAL SOURCE COMPARISON / CONSERVATIVE HORIZONTAL DETECTOR / NO-GO
- **Scientific status:** `[PROVED HERE] [NEW SOURCE IDENTIFICATION] [NOT RH]`
- **Parents:**
  - `deninger-all-cross-prime-incidence-koszul-exactness.md`;
  - `deninger-cross-prime-arithmetic-source-completion.md`;
  - `deninger-meyer-gaussian-cohomology-wronskian-green-comparison.md`;
  - `../../../4-publication-ready/riemann-hellinger-hodge-green-descent/main.tex`.

## Statement

Let (i_0=(2,3)) be the canonical ordered Calderón--Witt witness.  Write

\[
 A_0=alpha_{2,0}\alpha_{3,0}(h_{2,0}-h_{3,0}),
 \qquad
 R_0=r_{2,0}+r_{3,0},
\]

where (alpha_{p,n}>0) is the promoted critical Gamma amplitude,
(h_{p,n}>0) is the Euler half-height, and (r_{p,n}=-2h_{p,n}) is the
modular rate.  Since (h_{2,0}<h_{3,0}),

\[
 A_0<0,qquad R_0<0,qquad A_0R_0>0.                 \tag{1}
\]

The actual Gamma/co-Poisson polarized boundary reflection defect evaluated
on (i_0) is

\[
 \Gamma_0(a)=A_0\sinh(aR_0).                         \tag{2}
\]

Define the derivative-filled quotient

\[
 g_\Gamma(a)=
 \begin{cases}
 A_0R_0,&a=0,\\[1mm]
 A_0\dfrac{\sinh(aR_0)}a,&a\ne0.
 \end{cases}                                         \tag{3}
\]

Then, for every real (a),

\[
 g_\Gamma(a)>0,qquad \Gamma_0(a)=a,g_\Gamma(a).   \tag{4}
\]

At an actual Xi-divisor copy (q), let
(kappa(q)=2\operatorname{Re}\rho_q-1).  Equations `(2)`--`(4)` give the
source-exact factorization

\[
 \Gamma_{\rm CW}(q)=\kappa(q),g_\Gamma(\kappa(q)),
 \qquad g_\Gamma(\kappa(q))>0.                       \tag{5}
\]

The fixed Gaussian cohomology Wronskian already has

\[
 \Omega_G(q)=\kappa(q)s_G(q),qquad s_G(q)>0.
\]

Consequently the two independently constructed source observations obey
the division-free comparison

\[
 \Gamma_{\rm CW}(q)s_G(q)=
 \Omega_G(q)g_\Gamma(\kappa(q)).                     \tag{6}
\]

Thus actual Gamma/co-Poisson Hodge boundary and actual Gaussian/Meyer Green
transport carry the same **oriented** horizontal fracture, not merely the
same zero set.  Both gauges are strictly positive.  Gamma boundary therefore
reinforces the Green orientation and cannot be its arithmetic
null-homotopy.

## Completed admission operator

Let

\[
 P_{\rm CW}=\ell^2(\operatorname{Div}\Xi;\ell^2(I)),
 \qquad
 (\Phi x)(q)=x(q)\eta,
\]

be the genuine all-cross-prime packet completion and its isometric Xi
comparison.  Normalize `(5)` without changing its zeros:

\[
 m(q)=\frac{\Gamma_{\rm CW}(q)}{1+|\Gamma_{\rm CW}(q)|},
 \qquad |m(q)|\le1.
\]

Fibrewise multiplication

\[
 (A_\Gamma z)(q)=m(q)z(q)                            \tag{7}
\]

is a bounded complex-linear operator on (P_{\rm CW}).  Its exact kernel on
the comparison range is

\[
 A_\Gamma\Phi(x)=0
 \quad\Longleftrightarrow\quad
 \operatorname{supp}(x)\subseteq
 \{q:\operatorname{Re}\rho_q=\tfrac12\}.            \tag{8}
\]

Every completed Green provenance vector (G(a)) has the complementary
support law

\[
 G(a)(q)=0
 \quad\text{whenever}\quad
 \operatorname{Re}\rho_q=\tfrac12,                  \tag{9}
\]

because its coefficient contains the fracture (kappa(q)).  Combining
`(8)` and `(9)` gives exact Green-sector conservativity:

\[
 A_\Gamma\Phi(G(a))=0
 \quad\Longleftrightarrow\quad G(a)=0.                \tag{10}
\]

For the fixed reflected-Gaussian source vector (g_G), the existing exact
classification (g_G=0\Longleftrightarrow\mathrm{RH}) yields

\[
 A_\Gamma\Phi(g_G)=0
 \quad\Longleftrightarrow\quad\mathrm{RH}.            \tag{11}
\]

All implications are unconditional.  Equation `(11)` classifies the
missing source-null-homotopy; it does not assert it.

## Proof

The modular exterior is

\[
 \alpha_i\alpha_j e^{a(r_i+r_j)}(h_i-h_j).
\]

Taking its reflection-odd part produces `(2)`.  Positivity in `(4)` follows
by signs.  If (a>0), then (aR_0<0), so
(sinh(aR_0)/a<0); if (a<0), both numerator and denominator have opposite
signs and the quotient remains negative.  Multiplication by (A_0<0) is
strictly positive.  At (a=0), positivity is `(1)`.

Equation `(5)` follows because the completed Green fracture is the real
complex scalar (kappa(q)).  Substitution of the already-proved positive
Gaussian pair scale proves `(6)`.

For `(8)`, evaluate (A_\Gamma\Phi(x)) at the canonical packet coordinate.
The horizon coordinate is nonzero, and (m(q)=0) exactly on the critical
line, so off-line coefficients (x(q)) must vanish.  The converse is
pointwise.  Equations `(9)`--`(11)` then follow by complementary support.

## Anti-theatre audit

This theorem does not close Route L.  It does three frontier-relevant things
that another comparison or zero-set equivalence does not:

1. identifies actual Gamma boundary response and actual Meyer/Gaussian
   Green Wronskian as the same **signed** horizontal defect through positive
   source gauges;
2. constructs a bounded operator on the genuine arithmetic packet
   completion and determines its kernel exactly; and
3. proves the requested Gamma-kernel membership of the fixed Green vector is
   equivalent to RH, so it cannot be inserted as compatibility or inferred
   from old vertical exactness.

The elementary identity (\sinh x=x(\sinh x/x)) is parent analysis.  New
project-specific content is its source-exact identification with the actual
Calderón--Witt Gamma boundary, the positive division-free comparison `(6)`,
and completed Green-sector kernel theorem `(10)`.

## Remaining open core

Construct a genuinely horizontal, source-derived arithmetic null-homotopy
which makes the left side of `(11)` vanish without assuming critical-line
support.  The positive-gauge law proves that neither the actual Gamma
reflection boundary by itself nor any positive rescaling of it can do this.

- 2026-08-06 — Formalization re-verified on this toolchain: the named Lean module exists, is wired into `GaloisForLFunctions.RHTower`, builds, uses no `native_decide`, and every audited declaration depends only on `propext, Classical.choice, Quot.sound`.  Every gate this card states is closed; what the card lists as still open is its declared successor core, not this theorem.  Card moves to `3-formalized`.
