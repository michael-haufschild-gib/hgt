# Deninger failure-nerve mixed dagger coboundary no-go

- **ID:** `deninger-failure-nerve-mixed-dagger-coboundary-no-go`
- **Route:** L / finite filtered source mate
- **Status:** fully proved on paper; RH not proved
- **Inputs:** actual normalized failure-nerve transition; unique purified face
  metric; Deninger tensor-square mate curvature

## Result

Fix a prime `p`, depth `m >= 1`, finite face `F` with `p` not in `F`, and
`Re(s)>0`.  Write

\[
 \lambda_{p,m}(s)=p^{-m(s-1/2)},\qquad
 R_{p,m}(s)=\lambda_{p,m}(s)Q_{p,m}(s),
\tag{1}
\]

and equip the face vertices with the forced metric

\[
 h_F=|Q_F|^{-2},\qquad h_{F\cup\{p\}}=h_F|Q_{p,m}|^{-2}.
\tag{2}
\]

### 1. Concrete source reversal and analytic dagger

Algebraic source reversal of the edge and its Hermitian adjoint for `(2)`
have coefficients

\[
 S_{p,m}=R_{p,m}^{-1}
   =Q_{p,m}^{-1}\lambda_{p,m}^{-1},
\tag{3}
\]

and

\[
 A_{p,m}=\frac{h_{F\cup\{p\}}}{h_F}\overline{R_{p,m}}
   =Q_{p,m}^{-1}\overline{\lambda_{p,m}}.
\tag{4}
\]

Indeed, with the convention
`<z,w>_F=h_F conjugate(z) w`, equation `(4)` is characterized by

\[
 \langle R_{p,m}z,w\rangle_{F\cup\{p\}}
 =\langle z,A_{p,m}w\rangle_F.
\tag{5}
\]

The Euler gauge is common to both reverse laws.  Their modular ratio is

\[
 S_{p,m}A_{p,m}^{-1}=|\lambda_{p,m}|^{-2},
\tag{6}
\]

and their linear mate defect is

\[
 \boxed{
 \Delta_{p,m}=S_{p,m}-A_{p,m}
 =Q_{p,m}^{-1}
   (\lambda_{p,m}^{-1}-\overline{\lambda_{p,m}})
 =Q_{p,m}^{-1}\overline{\lambda_{p,m}}
   (|\lambda_{p,m}|^{-2}-1).}
\tag{7}
\]

Since `p^m>1`,

\[
 \Delta_{p,m}=0
 \Longleftrightarrow |\lambda_{p,m}|=1
 \Longleftrightarrow \Re(s)=\frac12.
\tag{8}
\]

This is the concrete finite source transpose--analytic dagger comparison;
neither reverse law is defined from the Xi zero set.

### 2. Mixed Bianchi law and exactness classification

For two composable edge transitions, source reversal and metric dagger are
contravariantly multiplicative.  Hence their difference satisfies the mixed
Leibniz law

\[
 \Delta_{21}=S_1\Delta_2+\Delta_1A_2.
\tag{9}
\]

For two distinct prime edges `p,q`, commutativity of the actual face
transitions gives the square Bianchi identity

\[
 S_p\Delta_q+\Delta_pA_q
 =S_q\Delta_p+\Delta_qA_p.
\tag{10}
\]

More strongly, if the mixed cobar differential on a vertex cochain `H` is

\[
 (\delta_{S,A}H)_e=S_eH_{t(e)}-H_{s(e)}A_e,
\tag{11}
\]

then the constant identity cochain satisfies

\[
 \boxed{\Delta=\delta_{S,A}{\bf1}.}
\tag{12}
\]

Thus the linear source-inverse/analytic-dagger defect is always mixed-Bianchi
closed and mixed-cobar exact, including at every off-critical parameter where
it is nonzero.

### 3. Gamma curvature is a secondary norm transgression

The uniquely purified relative squared gains of source reversal and analytic
dagger are respectively `|lambda|^(-2)` and `|lambda|^2`.  Their difference is

\[
 \boxed{
 |\lambda_{p,m}|^{-2}-|\lambda_{p,m}|^2
 =K_{p^m}(s).}
\tag{13}
\]

At the actual ordered `(2,3)` witness, the companion comparison theorem gives

\[
 b_\Gamma(q)=c_{23}K_6(\rho_q),\qquad c_{23}>0.
\tag{14}
\]

Therefore actual Gamma reporter is a secondary norm transgression of the
linear mixed-exact defect.  Linear cobar exactness does not annihilate this
quadratic reporter.

## Proof

Equation `(3)` follows by inverting `(1)`.  For a one-dimensional weighted
Hermitian edge, the adjoint coefficient is
`(h_target/h_source) conjugate(R)`.  Substitute `(1)` and `(2)`:

\[
 \frac{h_{F\cup\{p\}}}{h_F}\overline{R}
 =|Q|^{-2}\overline{\lambda Q}
 =Q^{-1}\overline\lambda,
\]

which proves `(4)` and `(5)`.  Division of `(3)` by `(4)`, using
`lambda^(-1)/conjugate(lambda)=|lambda|^(-2)`, proves `(6)`.  Subtraction
gives `(7)`.  All factors outside `|lambda|^(-2)-1` are nonzero.  The existing
half-density unitarity theorem then gives `(8)`.

For a composite path, expand

\[
 S_1S_2-A_1A_2
 =S_1(S_2-A_2)+(S_1-A_1)A_2,
\]

which is `(9)`.  Applying it to the two orders around a commuting prime square
proves `(10)`.  Equation `(12)` is immediate from `(11)` with both endpoint
values equal to one.  Finally the two relative reverse gains are the inverse
and direct radial squared gains, so `(13)` is exactly the already identified
Deninger tensor-square curvature; `(14)` is the actual Gamma comparison.

## Hostile audit and frontier consequence

Not new:

- adjoint of a scalar map between weighted Hermitian lines;
- inverse-versus-adjoint mixed Leibniz identity;
- a difference of two representations as a mixed coboundary;
- scalar half-density unitarity criterion.

New Route-L classification is their forced simultaneous realization on the
actual prime-winning Euler gauge metric and its exact connection to the
independently constructed Gamma reporter.  It invalidates a previously live
research shortcut:

> A source Bianchi identity or mixed-cobar null-homotopy of the linear mate
> defect cannot prove RH.  Both hold identically off line.

The missing theorem must instead kill or control the secondary norm
transgression `(13)` after strict singular Cartier transport.  Equivalently,
it needs a Stokes/trace pairing with a boundary condition strong enough to
annihilate `K`, not merely exactness of `Delta`.  Imposing `Delta=0`, declaring
the identity homotopy zero, or defining the pairing from the Xi divisor is
circular.

This theorem does not produce that secondary Stokes law and does not prove
RH.  It removes linear Bianchi/null-homotopy as an eligible hard core and
replaces it by:

`[SECONDARY_CARTIER_NORM_TRANSgression_STOKES]`

> Construct the source-canonical pairing on the conormally renormalized
> singular Cartier completion and prove its boundary term is the actual
> Gamma curvature while its source Stokes term vanishes for structural,
> non-divisor-fitted reasons.

## Formalization target

Lean should formalize unconditionally:

- weighted Hermitian adjunction identity for the actual edge;
- closed formulas `(3)`--`(8)`;
- mixed Leibniz/Bianchi law `(9)`--`(10)`;
- tautological mixed coboundary `(12)`;
- reverse-gain difference `(13)` and actual Gamma specialization `(14)`.
