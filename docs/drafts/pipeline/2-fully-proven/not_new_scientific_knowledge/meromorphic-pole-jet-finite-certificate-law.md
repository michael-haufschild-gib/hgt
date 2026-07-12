# Meromorphic pole-jet finite certificate law

- **ID:** meromorphic-pole-jet-finite-certificate-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) · STRUCTURAL BRIDGE
- **Status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Differential transcendence of a meromorphic function is equivalent to the
  existence, at every finite ADE complexity, of one nonzero finite determinant made from Laurent
  coefficients of its differential monomials at any chosen pole.

## Setup

Let \(f\) be meromorphic on a connected domain \(U\subseteq\mathbb C\), and fix a pole
\(a\in U\).  For integers \(r,D,E\geq0\), define the finite column set
\[
 \mathcal C_{r,D,E}
 =\{(q,\alpha):0\leq q\leq E,\ 
 \alpha=(\alpha_0,\ldots,\alpha_r)\in\mathbb N^{r+1},\ |\alpha|\leq D\}.
\]
The column function indexed by \((q,\alpha)\) is
\[
 F_{q,\alpha}(z)=z^q\prod_{j=0}^{r}\bigl(f^{(j)}(z)\bigr)^{\alpha_j}.
\]
For every Laurent index \(\ell\in\mathbb Z\), put
\[
 M_{r,D,E}(\ell,(q,\alpha))
 =[t^\ell]F_{q,\alpha}(a+t).
\]

## Theorem — finite pole-jet certificate

The following are equivalent.

1. \(f\) is hypertranscendental over \(\mathbb C(z)\).
2. For every \(r,D,E\), the columns of the infinite Laurent matrix \(M_{r,D,E}\) are linearly
   independent over \(\mathbb C\).
3. For every \(r,D,E\), there are
   \(N=|\mathcal C_{r,D,E}|\) Laurent indices
   \(\ell_1,\ldots,\ell_N\) such that
   \[
   \boxed{
   \det\left(M_{r,D,E}(\ell_i,c)\right)_{
      1\leq i\leq N,\ c\in\mathcal C_{r,D,E}}\neq0.
   }
   \]

The same equivalence holds if rows are drawn from Laurent coefficients at any nonempty family of
poles, rather than at one fixed pole.

## Proof

A polynomial ADE over \(\mathbb C(z)\) can be cleared of denominators and written
\[
 \sum_{(q,\alpha)\in\mathcal C_{r,D,E}}
 c_{q,\alpha}F_{q,\alpha}(z)=0
\]
for some finite \(r,D,E\) and a nonzero coefficient vector \(c\).  Thus hypertranscendence is
equivalent to linear independence of every finite family \((F_{q,\alpha})\).

The Laurent expansion at \(a\) is injective on meromorphic functions: if all coefficients of a
meromorphic function vanish, it vanishes on a punctured neighborhood of \(a\), hence on \(U\) by
the identity theorem.  Therefore a coefficient vector lies in the kernel of the Laurent matrix
exactly when it gives a global ADE relation.  This proves \((1)\iff(2)\).

For a matrix with \(N\) columns, column independence is equivalent to the existence of an
invertible \(N\times N\) row minor.  Indeed, the descending intersection of the kernels of all
finite row truncations stabilizes in the finite-dimensional coefficient space; if the full
kernel is zero, some finite truncation already has zero kernel, and an \(N\)-row submatrix has
nonzero determinant.  This proves \((2)\iff(3)\). \(\square\)

## Specialization to \(\psi\!\circ\!\Gamma\)

For
\[
 f(z)=\psi(\Gamma z),
\]
the poles
\[
 a=z_{n,m},\qquad \Gamma(z_{n,m})=-m,
\]
give a two-index family of certificate rows.  The exact values from
`../new_scientific_knowledge/digamma-gamma-factorial-pole-cluster-law.md` begin with
\[
 z_{n,m}=-n-\frac{(-1)^n}{n!m}
 +\frac{\psi(n+1)}{(n!)^2m^2}+O(m^{-3}),
\]
\[
 \operatorname{Res}_{z=z_{n,m}}f(z)
 =\frac{(-1)^n}{n!m^2}
 -\frac{2\psi(n+1)}{(n!)^2m^3}+O(m^{-4}).
\]
All higher Laurent rows are algebraic expressions in the jets of \(\Gamma\) at \(z_{n,m}\) and
the universal Laurent coefficients of \(\psi\) at \(-m\).  Consequently, the full HT question
has a positive finite-value form:
\[
 \boxed{
 \forall r,D,E\ \exists\text{ a finite inverse-Gamma pole-jet minor with nonzero determinant}.
 }
\]

## Classification

The equivalence is a direct synthesis of the identity theorem, Laurent uniqueness, and
finite-dimensional linear algebra.  It is therefore a structural bridge, not new scientific
knowledge.  Its value is that it makes every bounded ADE claim decidable by one finite determinant
and identifies the exact entries supplied by the factorial pole-cluster law.

## Gates

- [x] 0 → 1: coefficient matrix and ADE bounds defined
- [x] 1 → 2: equivalence and finite-minor proof complete
- [ ] 2 → 3: formal Laurent-series infrastructure and determinant criterion
- [ ] 3 → 4: include only as a supporting lemma in a publication
