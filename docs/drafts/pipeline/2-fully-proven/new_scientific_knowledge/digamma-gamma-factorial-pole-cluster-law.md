# Factorial pole-cluster velocity law for \(\psi\!\circ\!\Gamma\)

- **ID:** digamma-gamma-factorial-pole-cluster-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) · CANDIDATE NEW SCIENTIFIC KNOWLEDGE
- **Status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Statement:** Near every pole \(-n\) of the inner Gamma function, the poles of
  \(\psi(\Gamma z)\) are reciprocal-integer samples of an analytic inverse-Gamma curve;
  the interpolated residue is exactly \(-x^2\) times the derivative of its position germ, and
  its first two coefficients recover
  \(\operatorname{Res}_{-n}\Gamma\) and \(\psi(n+1)=H_n-\gamma\).

## The values

Fix \(n\geq 0\), and put
\[
 a_n=-n,
 \qquad
 r_n=\operatorname{Res}_{z=a_n}\Gamma(z)=\frac{(-1)^n}{n!},
 \qquad
 A_n=\frac{\psi(n+1)}{(n!)^2}.
\]
The reciprocal Gamma function is entire, has a simple zero at \(a_n\), and satisfies
\[
 \frac1{\Gamma(a_n+t)}
 =\frac{t}{r_n}-\frac{\psi(n+1)}{r_n}t^2+O(t^3).
\]
Let \(\kappa_n\) be its local inverse at zero, normalized by \(\kappa_n(0)=a_n\).  For
small \(x\), define the pole-position germ
\[
 z_n(x)=\kappa_n(-x).
\]
Then
\[
 \Gamma(z_n(x))=-\frac1x,
 \qquad
 z_n(x)=a_n-r_nx+A_nx^2+O(x^3).
\]
For \(x\neq0\), define the analytic residue interpolation
\[
 \widehat\rho_n(x)=-\frac1{\Gamma'(z_n(x))}.
\]
At a reciprocal-integer sample \(x=1/m\), the value \(-1/x=-m\) is a digamma pole and
\(\widehat\rho_n(1/m)\) is the actual residue of \(\psi(\Gamma z)\) at \(z_n(1/m)\).

## The law

### Theorem 1 — exact analytic position-residue velocity

For every sufficiently small nonzero \(x\),
\[
 \boxed{\widehat\rho_n(x)=-x^2z_n'(x).}
\]
Consequently,
\[
 \widehat\rho_n(x)=r_nx^2-2A_nx^3+O(x^4).
\]

**Proof.**  The digamma function has a simple pole of residue \(-1\) at every nonpositive
integer.  At \(x=1/m\), composition with the locally biholomorphic map \(\Gamma\) gives
\[
 \operatorname{Res}_{z=z_n(1/m)}\psi(\Gamma z)
 =-\frac1{\Gamma'(z_n(1/m))}=\widehat\rho_n(1/m).
\]
Differentiating \(\Gamma(z_n(x))=-x^{-1}\) gives
\[
 \Gamma'(z_n(x))z_n'(x)=x^{-2}.
\]
Combining the derivative identity with the definition of \(\widehat\rho_n\) proves the boxed
formula; its reciprocal-integer samples are the actual residues above.  Differentiating the
displayed Taylor series for \(z_n\) gives the second assertion. \(\square\)

### Theorem 2 — the discrete factorial cluster

For every sufficiently large positive integer \(m\), there is a distinguished solution
\(z_{n,m}=z_n(1/m)\) of
\[
 \Gamma(z_{n,m})=-m
\]
near \(-n\).  It is a simple pole of \(\psi(\Gamma z)\), with residue
\(\rho_{n,m}=\widehat\rho_n(1/m)\), and
\[
 z_{n,m}
 =-n-\frac{r_n}{m}+\frac{A_n}{m^2}+O(m^{-3}),
\]
\[
 \rho_{n,m}
 =\frac{r_n}{m^2}-\frac{2A_n}{m^3}+O(m^{-4}).
\]
Hence the cluster recovers two classical Gamma/digamma values:
\[
 \boxed{
 \lim_{m\to\infty}m(z_{n,m}+n)=-\frac{(-1)^n}{n!},
 \qquad
 \lim_{m\to\infty}m^2\rho_{n,m}=\frac{(-1)^n}{n!},
 }
\]
and the balanced next-order value is
\[
 \boxed{
 \psi(n+1)
 =-(n!)^2\lim_{m\to\infty}
 \left(m^2(z_{n,m}+n)+m^3\rho_{n,m}\right).
 }
\]

**Proof.**  Substitute \(x=1/m\) into Theorem 1 and the Taylor series for \(z_n\).  In the
balanced expression, the order-\(m\) terms \(-r_nm\) and \(r_nm\) cancel, leaving
\(A_n-2A_n=-A_n\). \(\square\)

### Theorem 3 — all-order coefficient transport

Write the convergent position germ as
\[
 z_n(x)=a_n+\sum_{j\geq1}b_{n,j}x^j.
\]
Then the complete analytic residue interpolation is
\[
 \boxed{
 \widehat\rho_n(x)=-\sum_{j\geq1}j\,b_{n,j}x^{j+1}.
 }
\]
Thus the pole positions and the analytic interpolation of their residues are a single datum:
either germ determines the other, and every coefficient of the inverse-Gamma branch becomes a
value law for the reciprocal-integer samples forming the composite pole cluster.

**Proof.**  Expand the exact identity \(\widehat\rho_n=-x^2z_n'\) term by term. \(\square\)

## Positive algebraic consequence

### Corollary — algebraic independence from the local digamma field

The function \(\psi(\Gamma z)\) is transcendental over \(\mathbb C(z,\psi(z))\).

**Proof.**  Near \(a_n=-n\), the field \(\mathbb C(z,\psi(z))\) embeds into the meromorphic
germ field \(\mathbb C((z-a_n))\), because \(\psi\) has a simple pole there.  Every algebraic
extension germ becomes a Puiseux germ after finite ramification, and therefore has only the
central singularity in some punctured neighborhood.  Theorem 2 supplies infinitely many poles
\(z_{n,m}\to a_n\) of \(\psi(\Gamma z)\) in every such neighborhood.  The composite therefore
does not belong to that algebraic closure. \(\square\)

This gives the correct proof of the algebraic statement formerly derived from a uniform
logarithmic model.  The exact positive structure is richer: generic sectors retain the familiar
large-argument logarithmic asymptotic, while the inverse-Gamma pole ray carries the factorial
position-residue cluster above.

## Relation to hypertranscendence

The theorem determines a new infinite family of exact local values for \(\psi\!\circ\!\Gamma\)
and proves its algebraic transcendence over \(\mathbb C(z,\psi(z))\).  Hypertranscendence asks
for a stronger conclusion: that no finite algebraic differential relation can coordinate all
jets of these clusters.  The all-order transport law identifies the concrete data such a relation
would have to preserve: the inverse-Gamma coefficient sequence \((b_{n,j})\), simultaneously for
every \(n\).

The all-order outer differential tower generated by these residues is proved in
`inverse-gamma-polygamma-principal-part-power-law.md`: at every sampled pole,
\[
\lim_{z\to z_{n,m}}(z-z_{n,m})^{q+1}\psi^{(q)}(\Gamma z)
=q!\rho_{n,m}^{q+1}.
\]
Thus the leading principal-part tower has rank one; nonlinear separation begins with subleading
Laurent values.

The different inner-pole branches are linked by the shift cocycle proved in
`inverse-gamma-branch-shift-cocycle-law.md`:
\[
z_{n-1}\!\left(\frac{x}{z_n(x)}\right)=z_n(x)+1,
\qquad
\widehat\rho_{n-1}\!\left(\frac{x}{z_n(x)}\right)
=\frac{x\widehat\rho_n(x)}{\widehat\rho_n(x)+xz_n(x)}.
\]
Its first Taylor coefficients recover both the factorial residue recurrence and the digamma
recurrence.

## Novelty and significance audit

### Known parents

- The local inverse-Gamma expansion, including the displayed coefficients through order three,
  is part of the inverse-Gamma literature; see Camargos Couto–Jeffrey–Corless, *The Gamma
  function and its inverse*, and Jeffrey–Watt,
  [*The Inverse of the Complex Gamma Function*](https://arxiv.org/abs/2311.16583).
- The residue \(-1\) of \(\psi\) at the nonpositive integers and the residue-pullback formula
  under a local biholomorphism are classical.

### Candidate-new package

Targeted searches for `digamma(Gamma) poles`, `psi(Gamma(z)) poles`, inverse-Gamma residues, and
position-residue laws found the parent ingredients but no statement of:

1. the analytic pole-position germ of \(\psi\!\circ\!\Gamma\);
2. the exact interpolation law \(\widehat\rho_n=-x^2z_n'\), sampled by the actual residues at
   \(x=1/m\);
3. the balanced limit recovering \(\psi(n+1)\); or
4. the resulting accumulating-pole proof of algebraic transcendence over
   \(\mathbb C(z,\psi(z))\).

The package therefore remains `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED]` pending
an expert-level full-text search in the composition and inverse-special-function literature.

### Significance

- **Novelty estimate:** 0.72 before expert full-text audit.
- **Significance estimate:** 0.78.  The result converts a qualitative singularity picture into an
  exact differential law, recovers two arithmetic special values from composite pole data, and
  supplies an all-order value target for the \(\psi\!\circ\!\Gamma\) HT problem.

## Formalization surface

The formal core is in `formal/GaloisForLFunctions/CompositionResidueLaw.lean`:

1. `residue_comp_of_hasDerivAt`: generic residue pullback by a noncritical value map;
2. `digamma_comp_Gamma_residue`: the actual composite residue \(-1/\Gamma'(z_0)\);
3. `reciprocalPosition_velocity`: differentiation of \(g(z(x))=-1/x\);
4. `reciprocalPosition_residueInterpolation`: the exact identity
   \(-1/d=-x^2z'(x)\).
5. `principalPart_comp_of_hasDerivAt` and `polygamma_comp_Gamma_principalPart`: the all-order
   principal-part power law.

The module builds directly.  Each theorem has only the standard Mathlib axioms
`propext`, `Classical.choice`, and `Quot.sound`.

`formal/GaloisForLFunctions/ReciprocalGammaPoleBranch.lean` now formalizes the analytic existence,
normalization, first derivative, and finite rising-factorial conjugacy of the inverse-Gamma pole
branches.  The displayed second- and third-order Taylor coefficients remain paper-level.

## Gates

- [x] 0 → 1: exact values and relation isolated
- [x] 1 → 2: complete complex-analytic proof, no computational dependency
- [ ] 2 → 3: formal core and branch existence complete; higher Taylor coefficients remain
- [ ] 3 → 4: expert novelty audit and standalone exposition
