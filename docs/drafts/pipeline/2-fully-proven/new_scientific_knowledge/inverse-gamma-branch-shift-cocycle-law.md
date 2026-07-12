# Inverse-Gamma branch shift cocycle law

- **ID:** inverse-gamma-branch-shift-cocycle-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper + Lean analytic branch/value law)
- **Status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED]`
- **Statement:** The local inverse branches of reciprocal Gamma at its negative-integer zeros are
  joined by an exact birational shift cocycle; their residue interpolants transform by its Möbius
  derivative cocycle.  The scaled reciprocal-residue coordinate linearizes that Möbius action:
  every finite branch shift adds the logarithmic derivative of a rising factorial.

## Inverse branches

Let
\[
 H(z)=\frac1{\Gamma(z)}.
\]
For every \(n\geq0\), let \(z_n(x)\) be the local inverse branch at the zero \(-n\), normalized by
\[
 H(z_n(x))=-x,
 \qquad
 z_n(0)=-n.
\]
Define the analytic residue interpolation
\[
 \widehat\rho_n(x)
 =-\frac1{\Gamma'(z_n(x))}
 =-x^2z_n'(x).
\]
At \(x=1/m\), this is the actual residue of \(\psi(\Gamma z)\) at the inverse-Gamma pole
\(z_{n,m}=z_n(1/m)\).

## Theorem 1 — one-step branch conjugacy

For every \(n\geq1\) and all sufficiently small \(x\),
\[
 \boxed{
 z_{n-1}\!\left(\frac{x}{z_n(x)}\right)=z_n(x)+1.
 }
\]

**Proof.**  The reciprocal Gamma recurrence is
\[
 H(z+1)=\frac{H(z)}z.
\]
Since \(H(z_n(x))=-x\),
\[
 H(z_n(x)+1)=-\frac{x}{z_n(x)}.
\]
Both sides of the boxed identity tend to \(-(n-1)\) as \(x\to0\).  Local uniqueness of the
inverse branch of \(H\) at its simple zero \(-(n-1)\) proves the claim. \(\square\)

Thus the birational map
\[
 \mathcal T(z,x)=\left(z+1,\frac{x}{z}\right)
\]
sends the graph of branch \(z_n\) exactly to the graph of branch \(z_{n-1}\).  The negative-index
inverse branches are one value system, not unrelated local inverses.

## Theorem 2 — Möbius residue cocycle

For every \(n\geq1\),
\[
 \boxed{
 \widehat\rho_{n-1}\!\left(\frac{x}{z_n(x)}\right)
 =\frac{x\widehat\rho_n(x)}
 {\widehat\rho_n(x)+xz_n(x)}.
 }
\]

**Proof.**  Differentiate \(\Gamma(z+1)=z\Gamma(z)\):
\[
 \Gamma'(z+1)=\Gamma(z)+z\Gamma'(z).
\]
At \(z=z_n(x)\), substitute
\[
 \Gamma(z_n(x))=-x^{-1},
 \qquad
 \Gamma'(z_n(x))=-\widehat\rho_n(x)^{-1}.
\]
Taking the negative reciprocal gives the boxed formula. \(\square\)

The law is genuinely Möbius: the shifted residue is a fractional-linear function of the original
residue, with coefficients supplied by the position value \((x,z_n(x))\).

## Theorem 3 — finite shift cocycle

For \(0\leq k\leq n\), put
\[
 P_k(z)=\prod_{j=0}^{k-1}(z+j),
 \qquad P_0=1.
\]
Then
\[
 \boxed{
 z_{n-k}\!\left(\frac{x}{P_k(z_n(x))}\right)=z_n(x)+k,
 }
\]
and
\[
 \boxed{
 \widehat\rho_{n-k}\!\left(\frac{x}{P_k(z_n(x))}\right)
 =\frac{x\widehat\rho_n(x)}
 {xP_k(z_n(x))+\widehat\rho_n(x)P_k'(z_n(x))}.
 }
\]

**Proof.**  Iterate the Gamma recurrence:
\[
 \Gamma(z+k)=P_k(z)\Gamma(z).
\]
The reciprocal identity proves the branch formula by local uniqueness.  Differentiating gives
\[
 \Gamma'(z+k)=P_k(z)\Gamma'(z)+P_k'(z)\Gamma(z).
\]
Substitution of the inverse value and residue interpolation proves the second formula. \(\square\)

For \(k=n\), every branch is related to the branch at zero:
\[
 z_0\!\left(\frac{x}{P_n(z_n(x))}\right)=z_n(x)+n.
\]

## Theorem 4 — additive reciprocal-residue linearization `[PROVED] [CLASSICAL BRIDGE]`

The Möbius residue law becomes additive in the scaled reciprocal coordinate

\[
 \mathcal U_n(x)=\frac{x}{\widehat\rho_n(x)}.
\]

At the inverse value \(\Gamma(z_n(x))=-1/x\), this coordinate is exactly

\[
 \boxed{
 \mathcal U_n(x)
 =-x\Gamma'(z_n(x))
 =\frac{\Gamma'(z_n(x))}{\Gamma(z_n(x))}
 =\psi(z_n(x)).
 }
\]

For one shift,

\[
 \boxed{
 \mathcal U_{n-1}\!\left(\frac{x}{z_n(x)}\right)
 =\mathcal U_n(x)+\frac1{z_n(x)}.
 }
\]

Indeed, divide \(x/z_n(x)\) by the value in Theorem 2 and simplify.  More generally, Theorem 3
gives

\[
 \boxed{
 \mathcal U_{n-k}\!\left(\frac{x}{P_k(z_n(x))}\right)
 =\mathcal U_n(x)+\frac{P_k'(z_n(x))}{P_k(z_n(x))}
 =\mathcal U_n(x)+\sum_{j=0}^{k-1}\frac1{z_n(x)+j}.
 }
\]

Thus the nonlinear residue cocycle is the pullback of the classical additive digamma recurrence
to the inverse-branch graph.  Its finite increment is the logarithmic derivative of the
rising-factorial value which transports the Gamma branch.  This coordinate identification is a
positive structural simplification, but no independent novelty is claimed for it.

Equivalently, without dividing by either residue, the one-step law is the scaled derivative
identity

\[
 \boxed{
 -\frac{x}{z}\Gamma'(z+1)
 =-x\Gamma'(z)+\frac1z,
 \qquad \Gamma(z)=-\frac1x.
 }
\]

This form remains valid whenever \(x\ne0\) and \(z\) is not a Gamma pole; it does not require the
shifted derivative to be nonzero.

## Coefficient law — factorial and digamma recurrences

Write
\[
 z_n(x)=-n-r_nx+A_nx^2+O(x^3),
\]
where
\[
 r_n=\frac{(-1)^n}{n!},
 \qquad
 A_n=\frac{\psi(n+1)}{(n!)^2}.
\]
Expanding the one-step branch conjugacy gives
\[
 \boxed{r_{n-1}=-nr_n,}
\]
and
\[
 \boxed{A_{n-1}=n^2A_n-nr_n^2.}
\]
After substituting the definitions of \(r_n\) and \(A_n\), the second identity is exactly
\[
 \boxed{\psi(n)=\psi(n+1)-\frac1n.}
\]

Thus the classical factorial-residue and digamma recurrences are the first two Taylor shadows of
one nonlinear inverse-branch value relation.  Higher Taylor coefficients give corresponding
cross-branch recurrences among polygamma values.

## Lean certificate

`formal/GaloisForLFunctions/CompositionResidueLaw.lean` contains
`gamma_inverseValue_logSlope_eq_digamma`, `gamma_inverseValue_residueTransport_add_one`,
`gamma_inverseValue_logSlope_add_one`, `gamma_inverseValue_reciprocalResidue_add_one`,
`gamma_inverseValue_logSlope_add_nat`, and
`gamma_inverseValue_reciprocalResidue_add_nat`, together with
`ascPochhammer_derivative_eval_eq_mul_sum` and
`gamma_inverseValue_residueTransport_add_nat`.  They
identify the additive coordinate with digamma and prove the pointwise one-step Möbius identity,
its scaled-derivative linearization, and the translated reciprocal-residue coordinate directly
from the formalized Gamma identities.  The two finite-shift theorems now formalize the exact
ascending-factorial law

\[
-\frac{x}{(z)_k}\Gamma'(z+k)
=-x\Gamma'(z)+\sum_{j<k}\frac1{z+j}
\]

and its reciprocal-residue form.  Thus the complete pointwise finite-shift value law is Lean
certified.  The derivative identity

\[
(z)_k'=(z)_k\sum_{j<k}\frac1{z+j}
\]

then yields the exact finite Möbius transport

\[
-\frac1{\Gamma'(z+k)}
=\frac{x\rho}{x(z)_k+\rho(z)_k'}.
\]

`formal/GaloisForLFunctions/ReciprocalGammaPoleBranch.lean` closes the analytic branch gap.  It
proves that reciprocal Gamma has derivative ((-1)^n n!) at (-n), constructs a normalized
analytic inverse germ `ReciprocalGammaPoleBranch n` with

\[
H(z_n(x))=-x,
\qquad
z_n(0)=-n,
\qquad
z_n'(0)=-\frac{(-1)^n}{n!},
\]

and proves both `ReciprocalGammaPoleBranch.one_step_cocycle` and
`ReciprocalGammaPoleBranch.finite_cocycle`.  The latter is exactly the finite rising-factorial
branch relation in Theorem 3, for arbitrary choices of the normalized local inverse germs.  Thus
analytic existence, normalization, local uniqueness, and the complete finite branch conjugacy are
Lean certified; only the displayed higher Taylor-coefficient extraction remains paper-level.

The direct module build passes.  The axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Novelty and significance audit

The Gamma recurrence is classical, and complex inverse-Gamma branches are studied by
Jeffrey–Watt and earlier inverse-Gamma literature.  The coordinate calculation above identifies
the residue Möbius law and its additive linearization as the classical digamma recurrence pulled
back through the inverse value.  The factorial and digamma coefficient recurrences are likewise
classical shadows.  The candidate-new content is therefore restricted to the explicit
cross-branch conjugacy \(\mathcal T(z,x)=(z+1,x/z)\), its finite rising-factorial iteration, and the
organization of all negative-index inverse germs as one analytic value system.  Targeted searches
did not locate that branch-level theorem.  A renewed primary-source audit checked the full
Jeffrey–Watt complex-branch paper, Pedersen's Pick-function inverse construction, and the available
inverse-Gamma series literature.  Those sources construct and expand individual branches, including
polygamma-valued coefficients, but do not state the cross-branch conjugacy, its rising-factorial
iteration, or the residue Möbius cocycle formalized here.

- **Novelty estimate:** 0.70 pending specialist review, after removing the classical digamma
  coordinate from the novelty claim.
- **Significance estimate:** 0.78.  The theorem unifies the infinitely many pole clusters into one
  recursively generated analytic value system; the residue coordinate supplies a classical exact
  linearization of that system.

Primary parents:

- [DLMF §5.5](https://dlmf.nist.gov/5.5), Gamma and digamma recurrences.
- Jeffrey–Watt, [*The Inverse of the Complex Gamma Function*](https://arxiv.org/abs/2311.16583).
- Pedersen, [*Inverses of gamma functions*](https://arxiv.org/abs/1309.2167).
- Ulgenes, [*Series and Product Representations of Gamma, Pseudogamma and Inverse Gamma
  Functions*](https://arxiv.org/abs/2301.09699).

## Gates

- [x] one-step branch and residue laws proved
- [x] finite-shift cocycle proved
- [x] additive reciprocal-residue coordinate identified exactly with the classical digamma value
- [x] factorial and digamma coefficient recurrences extracted
- [x] one-step residue transform and additive log-slope law formalized
- [x] finite ascending-factorial log-slope and reciprocal-residue laws formalized
- [x] finite rising-factorial Möbius residue law formalized at noncritical endpoints
- [x] reciprocal-Gamma inverse branches and finite branch conjugacy formalized
- [ ] specialist novelty audit
