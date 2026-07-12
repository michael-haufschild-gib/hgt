# Inverse-Gamma pole-jet determinant conjecture for \(\psi\!\circ\!\Gamma\)

- **ID:** psi-gamma-ht-singularity-arithmetic
- **Stage:** 1-in-progress
- **Type:** CONJECTURE · HYPERTRANSCENDENCE VALUE CERTIFICATES
- **Status:** `[CONJECTURE] [SEARCH]`
- **Statement:** Every finite ADE complexity for \(\psi(\Gamma z)\) is separated by a nonzero
  determinant of Laurent-coefficient values sampled at finitely many inverse-Gamma poles.

## Exact value array

Put
\[
 f(z)=\psi(\Gamma z).
\]
For every \(n\geq0\) and every sufficiently large integer \(m\), let \(z_{n,m}\) be the
distinguished solution near \(-n\) of
\[
 \Gamma(z_{n,m})=-m.
\]
These are simple poles of \(f\).  Write
\[
 f(z_{n,m}+t)=\sum_{\ell\geq-1}c_{n,m,\ell}t^\ell.
\]
The first values are proved in
`../2-fully-proven/new_scientific_knowledge/digamma-gamma-factorial-pole-cluster-law.md`:
\[
 z_{n,m}
 =-n-\frac{(-1)^n}{n!m}
 +\frac{\psi(n+1)}{(n!)^2m^2}+O(m^{-3}),
\]
\[
 c_{n,m,-1}
 =\frac{(-1)^n}{n!m^2}
 -\frac{2\psi(n+1)}{(n!)^2m^3}+O(m^{-4}).
\]
More exactly, if \(z_n(x)\) is the analytic position curve
\(\Gamma(z_n(x))=-1/x\), then
\[
 \widehat\rho_n(x)=-\frac1{\Gamma'(z_n(x))}=-x^2z_n'(x),
 \qquad
 c_{n,m,-1}=\widehat\rho_n(1/m).
\]
This is the base layer of the pole-jet value array.  Every higher
\(c_{n,m,\ell}\) is determined by the Gamma jets at \(z_{n,m}\) and the universal Laurent
coefficients of \(\psi\) at \(-m\).

## Finite determinant attached to an ADE bound

Fix derivative order \(r\), differential degree \(D\), and coefficient degree \(E\).
Let
\[
 \mathcal C_{r,D,E}
 =\{(q,\alpha):0\leq q\leq E,\ |\alpha|\leq D\},
 \qquad
 \alpha\in\mathbb N^{r+1}.
\]
For a pole \(z_{n,m}\), a Laurent index \(\ell\in\mathbb Z\), and
\(u=(q,\alpha)\in\mathcal C_{r,D,E}\), define
\[
 \mathcal M_{r,D,E}((n,m,\ell),u)
 =
 [t^\ell](z_{n,m}+t)^q
 \prod_{j=0}^{r}\left(f^{(j)}(z_{n,m}+t)\right)^{\alpha_j}.
\]

The proved finite-certificate law in
`../2-fully-proven/not_new_scientific_knowledge/meromorphic-pole-jet-finite-certificate-law.md`
gives the exact equivalence
\[
 \boxed{
 f\text{ is HT over }\mathbb C(z)
 \iff
 \forall r,D,E\ \exists\text{ a square row minor of }\mathcal M_{r,D,E}
 \text{ with nonzero determinant}.
 }
\]

## Conjecture

For every \(r,D,E\), rows can be chosen from finitely many reciprocal-integer samples
\((n,m)\) and finitely many Laurent grades so that the resulting
\(|\mathcal C_{r,D,E}|\times|\mathcal C_{r,D,E}|\) determinant is nonzero.

Equivalently, the inverse-Gamma pole-jet value array has full finite algebraic-differential rank
at every complexity.

If proved, the finite-certificate theorem gives
\[
 \operatorname{dtrdeg}_{\mathbb C(z)}
 \mathbb C(z)\langle\psi(\Gamma z)\rangle_D=1.
\]

## First determinant layers

### Algebraic layer

The accumulating poles \(z_{n,m}\to-n\) prove that \(f\) is transcendental over
\(\mathbb C(z,\psi(z))\).  This is the degree-zero differential layer and is fully settled.

### Linear differential layer

A linear ODE over \(\mathbb C(z)\) has only finitely many finite singular points.  The infinite
family \(\{z_{n,m}\}\) therefore proves that \(f\) is not D-finite.  All linear determinant
bounds are settled.

### Nonlinear layers

For nonlinear monomials, the leading Laurent grades can tie because
\[
 \operatorname{ord}_{z_{n,m}}f^{(j)}=-(j+1).
\]
The determinant must therefore retain subleading pole values.  The factorial position-residue
law supplies the first two such grades:
\[
 \frac{(-1)^n}{n!},
 \qquad
 \frac{\psi(n+1)}{(n!)^2}.
\]
Higher inverse-Gamma coefficients introduce polygamma values at \(n+1\).  The concrete theorem
target is a triangular asymptotic expansion in \(m^{-1}\) whose diagonal is a nonzero product of
these coefficient values and a reciprocal-integer Vandermonde.

The leading-grade tie is now exact at every outer derivative order.  The theorem in
`../2-fully-proven/new_scientific_knowledge/inverse-gamma-polygamma-principal-part-power-law.md`
gives
\[
\lim_{z\to z_{n,m}}(z-z_{n,m})^{q+1}\psi^{(q)}(\Gamma z)
=q!\rho_{n,m}^{q+1}.
\]
Hence the normalized leading coefficients form a rank-one Hankel sequence.  This proves that the
first separating determinant must consume at least one subleading Laurent grade; it also fixes the
complete leading block that the triangular expansion must remove.

The same theorem now classifies every pole grade through the analytic germ
\[
R_{n,m}(t)=-\frac{t}{\Gamma(z_{n,m}+t)+m}.
\]
For \(0\leq j\leq q\),
\[
[t^{-(q+1-j)}]\psi^{(q)}(\Gamma(z_{n,m}+t))
=q![t^j]R_{n,m}(t)^{q+1}.
\]
In particular, the first subleading coefficient \(B_{n,m,q}\) satisfies
\[
\frac{B_{n,m,q}}{(q+1)C_{n,m,q}}
=-\frac{\Gamma''(z_{n,m})}{2\Gamma'(z_{n,m})},
\]
independent of \(q\).  Thus the determinant problem has been reduced from unrelated Laurent
coefficients to cross-sample finite jets of the single value germ \(R_{n,m}\).

The branch index \(n\) is also constrained.  The shift cocycle in
`../2-fully-proven/new_scientific_knowledge/inverse-gamma-branch-shift-cocycle-law.md` gives
\[
z_{n-1}\!\left(\frac{x}{z_n(x)}\right)=z_n(x)+1
\]
and a Möbius transform for \(\widehat\rho_n\).  Hence the determinant rows across different inner
Gamma poles are recursively related rather than independent samples.  A successful rank proof
must use the resulting cross-branch coefficient recurrences, not assume genericity in \(n\).

## Positive research target

For each fixed \((r,D,E)\):

1. expand every matrix column in powers of \(m^{-1}\) using the inverse-Gamma branch;
2. group columns by equal principal pole weight;
3. use successive inverse-Gamma coefficients to split each tied group;
4. choose finitely many \(m\)-samples so the final reciprocal-integer Vandermonde is nonzero.

A successful all-degree triangularity theorem proves the conjecture and therefore the
hypertranscendence of \(\psi\!\circ\!\Gamma\).

## Proof boundary

The factorial position-residue values and the finite determinant equivalence are proved.
The all-degree triangularity assertion is `[CONJECTURE]`.  Its key unresolved value question is
whether distinct differential monomials can retain identical complete inverse-Gamma Laurent
signatures at every \((n,m)\).  The finite-certificate formulation makes this a precise equality
problem rather than a qualitative singularity claim.

## Lean surface

Already formalized:

- `digamma_comp_Gamma_residue`: actual residue of the composite at every noncritical inverse-Gamma
  pole;
- `reciprocalPosition_velocity`: derivative of the inverse-value position curve;
- `reciprocalPosition_residueInterpolation`: exact interpolation
  \(-1/d=-x^2z'(x)\).
- `polygamma_comp_Gamma_principalPart`: all-order factorial-power leading block.

Next formal objects:

- Laurent coefficient arrays of differential monomials at a simple pole;
- the finite row-minor certificate;
- the first nonlinear tied-weight separation using the two proved cluster coefficients.

## Gates

- [x] Exact pole positions and residues isolated
- [x] Algebraic and linear differential layers settled
- [x] HT converted to finite pole-jet determinant certificates
- [ ] Nonlinear tied-weight triangularity proved for arbitrary \((r,D,E)\)
- [ ] Full determinant family formalized in Lean
