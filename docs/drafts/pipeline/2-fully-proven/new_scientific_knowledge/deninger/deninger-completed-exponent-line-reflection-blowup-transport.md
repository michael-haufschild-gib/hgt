# Completed-exponent line-reflection blow-up transport

- **Stage:** 2 — dependency-closed paper proof
- **Route:** L — Deninger/Green/Hodge source descent
- **Status:** [PAPER-PROVED] [PROJECT-SPECIFIC SYNTHESIS] [PRIORITY UNVERIFIED] [NOT RH]
- **Date:** 2026-08-11
- **Exact advance:** functional-equation reflection is lifted from the Xi divisor to an explicit
  involution of the two-variable completed exponent source. Its exceptional-fibre action is forced,
  transports the marked pole exactly, preserves analytic multiplicity, and conjugates the full
  exceptional profile. This constructs the missing local singular transport without assuming a
  critical-line condition. It does not transport the complete shell-amplified Möbius remainder.

## 1. Completed exponent source and forced reflection

Put

\[
  \mathcal E_\Xi(z,s)=\frac{\xi(s)}{\xi(zs)}.
\]

On the regular source chart (s\ne0,1), define

\[
  \mathfrak J(z,s)=
  \left(
    \overline{\frac{1-zs}{1-s}},\;1-\overline s
  \right).
\tag{1}
\]

If ((z',s')=\mathfrak J(z,s)), then

\[
 z's'=1-\overline{zs}.
\tag{2}
\]

The functional equation and Schwarz reality therefore give

\[
 \mathcal E_\Xi(z',s')
 =\frac{\xi(1-\overline s)}{\xi(1-\overline{zs})}
 =\frac{\overline{\xi(s)}}{\overline{\xi(zs)}}
 =\overline{\mathcal E_\Xi(z,s)}.
\tag{3}
\]

Applying (1) twice returns ((z,s)): the second base coordinate is (s), while (2) makes the
second numerator (1-z's'=\overline{zs}), whose conjugate divided by (s) is (z). Thus
(\mathfrak J) is an anti-birational involution of the regular completed exponent source.

## 2. Exact chart transport

Write

\[
 z=1+t,\qquad s=\rho+tw,
\]

and set (\rho^\#=1-\overline\rho). Direct substitution in (1) gives

\[
 t'=-\overline t\,
       \frac{\overline\rho+\overline t\,\overline w}
            {1-\overline\rho-\overline t\,\overline w},
 \qquad
 w'=\overline w\,
       \frac{1-\overline\rho-\overline t\,\overline w}
            {\overline\rho+\overline t\,\overline w},
\tag{4}
\]

so that (s'=\rho^\#+t'w') exactly. On the exceptional divisor (t=0),

\[
  \boxed{\quad w\longmapsto
  \mathfrak j_\rho(w)=\overline w\frac{1-\overline\rho}{\overline\rho}.\quad}
\tag{5}
\]

Every nontrivial Xi divisor point lies in (0<\Re\rho<1), hence both factors in (5) are nonzero.
The map is forced already by its degree-one anti-linear form and the marked-pole condition:
if (w\mapsto a\overline w) sends (-\rho) to (-(1-\overline\rho)), then
(a=(1-\overline\rho)/\overline\rho).

Equation (5) sends the divisor direction (0) to (0) and the marked pole (-\rho) to
(-\rho^\#). Applying it at (\rho^\#) returns (w), so it is an involution over the line-reflected
Xi divisor.

## 3. Multiplicity-exact exceptional equivariance

Let (d_\rho=\operatorname{ord}_\rho\xi). Functional equation and Schwarz reflection imply
(d_{\rho^\#}=d_\rho). For the exponent exceptional profile

\[
 P_\rho(w)=\left(\frac{w}{w+\rho}\right)^{d_\rho},
\]

substitution of (5) gives

\[
 \frac{\mathfrak j_\rho(w)}{\mathfrak j_\rho(w)+\rho^\#}
 =\frac{\overline w}{\overline w+\overline\rho}
 =\overline{\frac{w}{w+\rho}}.
\]

Therefore

\[
 \boxed{\quad
 P_{\rho^\#}(\mathfrak j_\rho(w))=\overline{P_\rho(w)}.
 \quad}
\tag{6}
\]

This transports the complete multiplicity profile, not only its pole support. Since the constant
leg (6^m) is real, marked tame exponents remain ((-m,m)); the horizontal Deninger character is
inverted by (5), so its oriented Gamma-six readout changes sign exactly as required.

## 4. Frontier consequence and limitation

Equations (1)--(6) close the local singular reflection transport before divisor scalarization.
They rule out treating reflection of the exceptional profile as an additional missing choice.
They do **not** prove simultaneous critical-edge admission: (5) exchanges the two edge exponents
(1-\delta) and (1+\delta), but does not place either one in the projective trace domain. Nor do
they control the trace-order remainder of the corrected Möbius tensor source. Route L still needs
the global ideal-preserving extension of this forced local involution, followed by the independent
fixed-reader cyclicity identity.

## 5. Hostile audit

1. No RH premise or zero-location estimate is used.
2. The transport is not defined from the desired critical-edge domain; it is forced by the two
   exact Xi symmetries and the two-variable exponent source.
3. It does not claim that covariance implies selection. Off-line divisor pairs are transported
   just as faithfully as critical-line points.
4. The advance over the bare functional equation is the explicit lift through the exponent
   deformation and its multiplicity-exact exceptional divisor action. Parent functional-equation
   symmetry itself is not claimed as novel.
