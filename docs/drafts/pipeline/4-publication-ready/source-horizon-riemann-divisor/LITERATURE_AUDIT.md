# Literature and priority audit

Search date: 2026-08-02.

## Result under audit

The priority candidate is the exact combination:

1. a positive, coefficient-disjoint, divisor-faithful complete Riemann source \(E_K(s)\);
2. finite-stage injectivity but cofinal \(\ell^1\) collapse \(E_K(s)\to e_0\);
3. source-internal extraction of \(q^{1/2-s}\) for every prime by exact finite Möbius peeling;
4. affine-centre-independent Vandermonde rank at every finite prime level;
5. maximal verticality of every product-topology closed relation retaining the countable
   reader:
   \[
   \operatorname{mul}\mathcal R=\mathbb C^\mathbb N,\qquad
   \mathcal R=\operatorname{dom}\mathcal R\times\mathbb C^\mathbb N.
   \]

No novelty is assigned to the ingredients separately.

## Established prior art

| Ingredient | Status |
|---|---|
| \(1/\zeta(s)=\sum_{n\ge1}\mu(n)n^{-s}\) on \(\Re s>1\) | Classical |
| Integral tail bound for Dirichlet series | Classical |
| Largest prime-valuation exponent and its average order | Classical; Niven (1969) |
| Vandermonde determinant and interpolation | Classical |
| Linear relations, multivalued part, closure of nonclosable graphs | Classical; Arens (1961), Hassi--de Snoo--Szafraniec (2009) |
| Spectral realizations of zeta zeros | Established broad literature; Connes, Meyer, Connes--Consani, Hedenmalm, Suzuki |
| A sequence with surjective finite projections is dense in product topology | Standard product-topology fact |

The manuscript explicitly gives these components zero novelty credit.

## Theorem-level searches

Search families included:

- `"reciprocal zeta" Möbius finite prefix asymptotic prime`
- `"1/zeta(s)" Möbius finite Dirichlet polynomial remainder prime asymptotic`
- `"q^s" "1/zeta(s)" Möbius`
- `Riemann zeta prime characters Vandermonde q^{-s} interpolation`
- `closed linear relation graph convergence vertical multivalued part`
- `Riemann source cofinal collapse prime-normal reader`
- `positive divisor-replicating Dirichlet partition linear relation`

Results recovered the classical reciprocal-zeta Dirichlet series and established linear-relation
theory, but no theorem matching the five-part combination above.

Primary or authoritative comparison sources:

- Richard Arens, *Operational calculus of linear relations*, Pacific J. Math. 11 (1961),
  9--23, DOI 10.2140/pjm.1961.11.9.
- S. Hassi, H. S. V. de Snoo, F. H. Szafraniec,
  *Componentwise and Cartesian decompositions of linear relations*,
  Dissertationes Math. 465 (2009), DOI 10.4064/dm465-0-1.
- E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed. (1986).
- I. Niven, *Averages of exponents in factoring integers*, Proc. AMS 22 (1969),
  DOI 10.1090/S0002-9939-1969-0241373-5.
- A. Connes and C. Consani, *The scaling Hamiltonian*, J. Operator Theory 85 (2021).
- H. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494 (2026).
- M. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096 (2026).

## Collision analysis

### Reciprocal-zeta peeling

For a prime \(q\),
\[
R_q(w)=\zeta(w)^{-1}-\sum_{m<q}\mu(m)m^{-w}
\]
has first remaining coefficient \(-q^{-w}\).  The resulting asymptotic is an elementary
consequence of the classical series.  It is not novel in isolation.

No source found packages all \(q\) into the normal reader
\((q^{1/2-s})_q\), proves its internal recovery from the complete positive Riemann source, and
then derives maximal verticality at the cofinal source horizon.

### Linear relations

The facts that a graph closure may be multivalued and that
\(\operatorname{mul}\mathcal R=\{y:(0,y)\in\mathcal R\}\) are standard.
The abstract one-line closure argument receives no novelty credit.

Candidate novelty is the arithmetic forcing data: affine-independent prime-normal packets at
all finite ranks arise from one collapsing divisor-faithful source.  Product-topology closedness
then turns this exact arithmetic rank into the full domain-product classification.

### Product topology

A referee may argue that \(\mathbb C^\mathbb N\) with product topology is weak.  This is true but
not a collision.  Product topology is the initial topology of all finite-prime observers, which
is exactly the theorem's scope.  The result does not claim maximal verticality in \(\ell^2\),
\(\ell^\infty\), or a weighted Rees topology.  Indeed \(P_0=(1,1,\ldots)\) excludes an
unweighted \(\ell^2\) target.

## Priority verdict

No exact collision found.

Honest wording:

> The classical ingredients are not new. The priority candidate is the simultaneous exact
> Riemann realization and its maximal-vertical domain-product consequence. Search failure is
> not proof of priority; independent analytic-number-theory and linear-relation experts should
> verify it before submission.

Forbidden wording:

- “new theory of linear relations”;
- “new Vandermonde law”;
- “new asymptotic for \(1/\zeta\)” without the complete-source context;
- “proof of RH”;
- “no Hilbert--Pólya approach can work”;
- “all relation-valued approaches fail.”
