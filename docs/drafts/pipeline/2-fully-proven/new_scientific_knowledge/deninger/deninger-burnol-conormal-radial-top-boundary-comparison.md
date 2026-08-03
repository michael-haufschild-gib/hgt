# Deninger--Burnol conormal radial top-boundary comparison

- **ID:** `deninger-burnol-conormal-radial-top-boundary-comparison`
- **Route:** L — Deninger/Hodge/cohomological realization
- **Status:** `[PAPER-PROVED] [CROSS-CORPUS IDENTIFICATION] [NOT RH]`
- **Date:** 2026-08-03
- **Exact advance:** actual multiplicity-exact Burnol co-Poisson Mellin jets supply the physical
  source character whose reflected radial discriminant is exactly the Deninger cofinal
  top-boundary coefficient.  At clock six this is the actual Gamma/Calderón--Witt defect and its
  completed incidence value.  The same theorem proves that the conormal jet itself is nonzero at
  every Xi divisor, so Mellin differentiation cannot be the missing annihilator.

## 1. Actual source conormal

For logarithmic window length (L>0), the literal Burnol sub-window has uncompleted Mellin germ

\[
 B_L(w)=\zeta(w)\frac{e^{Lw}-1}{w}.
 \tag{1}
\]

Let ρ be a point of the Xi divisor and let (m) be its exact zeta multiplicity.  The already
proved exact-jet theorem gives

\[
 B_L^{(m)}(\rho)
   =(e^{L\rho}-1)\frac{\zeta^{(m)}(\rho)}{\rho}.
 \tag{2}
\]

Every factor on the right is nonzero: (\zeta^{(m)}(\rho)\ne0) by exactness of (m),
(\rho\ne0) in the open strip, and (e^{L\rho}\ne1) because (L\operatorname{Re}\rho>0).
Consequently

\[
 B_L^{(m)}(\rho)\ne0.
 \tag{3}
\]

The nested-window ratio cancels only the common nonzero conormal lead:

\[
 \frac{B_{2L}^{(m)}(\rho)}{B_L^{(m)}(\rho)}-1=e^{L\rho}.
 \tag{4}
\]

After forced half-density centering, define the actual source character

\[
 u_L(\rho)
 :=e^{-L/2}\left(\frac{B_{2L}^{(m)}(\rho)}{B_L^{(m)}(\rho)}-1\right)
 =e^{L(\rho-1/2)}.
 \tag{5}
\]

This is constructed from a literal co-Poisson source before taking any horizontal zero-location
condition.

## 2. Radial discriminant equals Deninger gain

Fix an ordinary-integer clock (n\ge2) and put (L=\log n>0).  The squared norm of `(5)` is

\[
 |u_{\log n}(\rho)|^2
 =e^{2\log n(\operatorname{Re}\rho-1/2)}
 =e^{(2\operatorname{Re}\rho-1)\log n}
 =\chi_\rho(n),
 \tag{6}
\]

where (\chi_\rho(n)) is the Deninger half-density mate gain.  Let

\[
 \rho^\#=1-\overline\rho.
 \tag{7}
\]

Functional-equation/Schwarz reflection preserves the Xi divisor and inverts the radial gain, so

\[
 |u_{\log n}(\rho^\#)|^2=\chi_\rho(n)^{-1}.
 \tag{8}
\]

Therefore the **actual Burnol radial reflection defect** is

\[
 \begin{aligned}
 E_n^{\mathrm B}(\rho)
 &:=|u_{\log n}(\rho)|^2-|u_{\log n}(\rho^\#)|^2\\
 &=\chi_\rho(n)-\chi_\rho(n)^{-1}\\
 &=K_n(\rho),
 \end{aligned}
 \tag{9}
\]

the Deninger tensor-square mate curvature.

This is not the Burnol quadratic cover's complex discriminant
((u_L(\rho)-u_L(\rho^\#))^2).  It is its dagger/radial discriminant.  That distinction is
load-bearing: the complex phase survives, whereas Deninger's unique contribution is the
source-versus-dagger norm comparison.

## 3. Exact top-boundary, Gamma, and incidence comparison

Let (\mathfrak B_s(n,m;e_m)) be the concrete relative cofinal Tate defect and let
ε_m read its newly created top coordinate.  The previous top-boundary theorem gives

\[
 \varepsilon_m\!\left(
   \mathfrak B_{\rho^\#}(n,m;e_m)-\mathfrak B_\rho(n,m;e_m)
 \right)=K_n(\rho).
 \tag{10}
\]

Combining `(9)` and `(10)` yields the source-native comparison

\[
 \boxed{
 \varepsilon_m\!\left(
   \mathfrak B_{\rho^\#}(n,m;e_m)-\mathfrak B_\rho(n,m;e_m)
 \right)=E_n^{\mathrm B}(\rho).}
 \tag{11}
\]

At forced clock (n=6=2\cdot3), the existing positive Gamma calibration (c_{23}>0) gives

\[
 b_\Gamma(\rho)=c_{23}E_6^{\mathrm B}(\rho).
 \tag{12}
\]

For any distinct source primes (p,q), the decoded completed Calderón--Witt incidence landing is

\[
 \operatorname{src}_{p,q,\rho}(\iota_{p,q}x_{\rho,m})
 =E_6^{\mathrm B}(\rho)\,w_{p,q},
 \qquad w_{p,q}\ne0.
 \tag{13}
\]

Thus actual Burnol conormal, Deninger relative top boundary, actual Gamma/co-Poisson boundary, and
completed cross-prime incidence all carry one coefficient without loss.

## 4. Exact zero set and no-go

For (n\ge2), strict monotonicity of the exponential gives

\[
 E_n^{\mathrm B}(\rho)=0
 \quad\Longleftrightarrow\quad
 \operatorname{Re}\rho=\frac12.
 \tag{14}
\]

Equation `(3)` simultaneously says that the exact conormal jet never vanishes on the Xi divisor.
The vertical zeta-zero relation kills the zeroth Mellin value, while its first nonzero Bockstein
retains the full horizontal coordinate.  Hence the proposed shortcut

```text
differentiate the common zeta factor at a zero
  + invoke a generic mixed Stokes square
  = horizontal annihilation
```

is false.  Differentiation changes a horizontally mute zero relation into a coefficient-faithful
detector; it supplies no reason for `(14)`'s left side to vanish.

More generally, a bicomplex identity (d_vd_h+d_hd_v=0) and (d_vx=0) imply only that (d_hx)
is a vertical cycle.  Here the exact conormal Bockstein is nonzero and faithful on that cycle.
Declaring it zero, compact, or a boundary after divisor specialization is exactly the missing
RH-selecting premise.

## 5. Novelty and hostile audit

1. Burnol's co-Poisson formula, exact zero evaluators, and Sonine spaces are parent mathematics.
2. The existing corpus already proved exact conormal jets, doubled-window tomography, the
   Deninger cofinal top boundary, Gamma calibration, and completed incidence landing separately.
3. New content is equation `(11)`: physical multiplicity-exact Burnol source jets realize the
   radial coefficient of the Deninger top-boundary class, with `(12)`--`(13)` fixing normalization
   and target.
4. No source Stokes vanishing is asserted.  Equation `(14)` proves that such vanishing on every Xi
   divisor is RH, not a formal consequence of conormal differentiation.
5. Literal additive source splitting cannot supply it: the retired arithmetic rig--Stokes route
   proves parity splitting is compatible with every complex exponent.
6. Principal conormal-to-Calkin lifting cannot supply it: the retired Burnol prime-seam route
   proves rank-one conormal data cannot generate the independent prime-labelled Calkin frame.

Verdict: **valid compatibility theorem and sharp no-go**.  It closes one named comparison clause
without claiming the annihilation clause.

## 6. Remaining Route-L core

`[OPEN CORE — ORDINARY_INTEGER_GREEN_STOKES_ANNIHILATION]`

Construct a pre-specialization ordinary-integer relation on the global completed/cofinal Xi Green
primitive whose image under `(11)` is zero.  It must be nonseparable and packet/operator-valued,
retain prime-labelled provenance, and remain strict through source completion.  Its proof may not
assume (E_6^{\mathrm B}(\rho)=0), Gamma/Hardy kernel membership, compactness equivalent to RH,
reflection-oddness equivalent to RH, static capacity, positivity equivalent to RH, or RH.

The Green primitive, actual co-Poisson conormal, Deninger top-boundary class, Gamma boundary, and
Calderón--Witt incidence target are now fixed.  Only arithmetic annihilation remains.

