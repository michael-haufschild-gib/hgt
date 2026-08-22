# Transported prolate relative-resolvent corner

- **ID:** transported-prolate-relative-resolvent-corner
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CONTROL MODEL (paper)
- **Scientific status:** BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Sources:** Connes--Moscovici, *Prolate spheroidal operator and Zeta*, arXiv:2112.05500;
  Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*, arXiv:2310.18423v2;
  Ramis--Richard-Jung--Thomann, *New eigenfunctions for the negative part of the
  Connes--Moscovici prolate spectrum*, 2025

## Statement

Fix a cutoff `lambda>0` and a prime `p`, and put `P={p}`. Let `W_(lambda,infinity)` be the unique
archimedean self-adjoint prolate extension commuting with the physical and Fourier cutoffs. Let

`theta_P:H_infinity->H_P`

be the source bounded isomorphism carrying the archimedean Sonin space onto the semilocal Sonin space.
Define the transported closed prolate control

`W_(lambda,P)^theta=theta_P W_(lambda,infinity) theta_P^(-1)`. (1)

Then:

1. `W_(lambda,P)^theta` is closed, similar to a self-adjoint operator, and its resolvent is trace
   class at every nonreal `z`;
2. the semilocal Sonin space reduces its resolvent;
3. for the cyclic transition `eta_P`, the exact relative-resolvent Sonin corner

   `C_(P,lambda)(z)
    =(1-Q_(lambda,P))
      ((W_(lambda,P)^theta-z)^(-1)eta_P
       -eta_P(W_(lambda,infinity)-z)^(-1))
      Q_(lambda,infinity)`                                  (2)

   is trace class and nonzero for every nonreal `z`.

Thus prolate resolvent smoothing really does convert the noncompact Euler metric crossing into a
nonzero trace-class exact-Sonin corner, uniformly at the level of existence for every positive cutoff.

## Archimedean spectral input

Connes--Moscovici prove that `W_(lambda,infinity)` is the unique self-adjoint extension commuting with
both cutoffs, that its spectrum is discrete and unbounded in both directions, and that every negative
eigenfunction belongs to the Sonin space. The Sonin restriction has at most finitely many positive
exceptions; the orthogonal complement carries the classical positive prolate spectrum and its Fourier
replica.

Ramis--Richard-Jung--Thomann construct spectral determinants for the classical and nonclassical
spectra which are entire of order at most `1/2`. The exponent of convergence of their zeros is therefore
at most `1/2`; in particular the reciprocal eigenvalue sequence is summable. Together with the finite
multiplicities, this gives

`(W_(lambda,infinity)-z)^(-1) in Schatten_1`                (3)

for every nonreal `z`.

Similarity by the boundedly invertible `theta_P` preserves closedness and the trace-class ideal, proving
items 1--2.

## Relative-corner proof

The source relation between the cyclic and Sonin transitions is

`eta_P=theta_PG_P`,

where `G_P` is the positive inverse Euler metric/cyclic-density multiplier. Pulling (2) back through
`theta_P` and applying `sonin-relative-resolvent-sylvester-factorization.md` gives, up to a bounded
invertible quotient map,

`R_complement(z)H_P-H_PR_Sonin(z)`,                         (4)

where

`H_P=(1-Q_(lambda,infinity))G_PQ_(lambda,infinity)`.

The inverse Euler corner `H_P` is noncompact for every `lambda>0`, hence nonzero. Both restricted
resolvents in (4) are trace class by (3), so (4), and therefore (2), is trace class.

It remains to prove nonvanishing. Let `E_-` be the negative spectral projection of the archimedean
Sonin restriction. Its complement inside the Sonin space is finite dimensional. If `H_PE_-=0`, then

`H_P=H_P(Q-E_-)`

would be finite rank, contradicting noncompactness. Hence `H_PE_-!=0`.

The spectrum of `W_(lambda,infinity)` on `E_-` is strictly negative, while its spectrum on the Sonin
orthogonal complement is strictly positive. The resolvent images of these two real spectral sets under
`x |-> (x-z)^(-1)` are disjoint for nonreal `z`. A nonzero operator cannot intertwine the two spectral
calculi. Therefore

`R_complement(z)H_PE_- - H_PE_-R_-(z) !=0`.

This is a restriction of (4), so the full relative corner is nonzero.

## Attack and route boundary

- `[PROVED]` Exact Sonin compression, cofinal cutoff size, and trace-class regularity are mutually
  compatible once a closed prolate realization is supplied.
- `[PROVED]` The survival mechanism is spectral separation, not a finite coefficient accident.
- `[PROVED]` The result holds for every one-prime enlargement `{infinity,p}`. The same proof applies
  to a finite prime set once noncompactness of its full inverse-product Euler corner is established;
  that product statement is not asserted here.
- `[DECISIVE LIMIT]` `W_(lambda,P)^theta` is an isospectral transport of the archimedean prolate
  operator. Its grading is `theta_PN_infinitytheta_P^(-1)`, not the source cyclic grading `N_P`.
  Therefore it is not the formal semilocal prolate candidate
  `-D_P^2+lambda^2N_P`.
- `[DECISIVE LIMIT]` The theorem proves a control corner, not an arithmetic spectral deformation.
  Any Route B promotion must compare the genuine `N_P`-graded extension against this transported
  control and isolate a nontrivial difference.
- `[LIMIT]` Nonzero trace class alone supplies no canonical scalar determinant boundary and no Weil
  positivity.

## Novelty audit

The source-specific theorem does not appear in the cited papers, but it follows from their prolate
spectral results, the source `theta_P/eta_P` relation, and standard Sylvester/trace-ideal theory. More
importantly, the operator is an isospectral transported control rather than the arithmetic semilocal
candidate. It fails the significance gate for new scientific knowledge and is classified as BRIDGE.
