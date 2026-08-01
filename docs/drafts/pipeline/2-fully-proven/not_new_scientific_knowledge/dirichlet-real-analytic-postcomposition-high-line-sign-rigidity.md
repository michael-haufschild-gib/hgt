# Real-analytic postcomposition preserves Dirichlet high-line sign obstruction

- **ID:** `dirichlet-real-analytic-postcomposition-high-line-sign-rigidity`
- **Stage:** `2-fully-proven`
- **Type:** `THEOREM (paper) / NO-GO CLASSIFICATION`
- **Scientific status:** `[PAPER-PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Route:** Route I, scalar passive-response pivots

## Theorem

Let

```text
D(s)=sum_(n>=1) a(n)n^(-s)
```

be an ordinary Dirichlet series with real coefficients and finite absolute-convergence abscissa.
Assume `m>=2` is the first nonconstant index with `a(m) != 0`: `a(n)=0` for `2<=n<m`.
Put `c=a(1)`.

Let `Phi` be complex analytic near the real point `c`, real-valued on a real neighborhood of `c`,
and not locally constant at `c`.  Then for every `H>0` there are points `z_+` and `z_-` satisfying

```text
Im(z_+)>H,  Im(z_-)>H,
Im(Phi(D(1-i z_+)))>0,
Im(Phi(D(1-i z_-)))<0.
```

Consequently no nonconstant real-analytic scalar postcomposition of the raw Dirichlet response is
Herglotz or anti-Herglotz on any upper half-plane tail.

## Proof

Set

```text
h(w)=Phi(w)-Phi(c).
```

Analyticity and failure of local constancy give a finite vanishing order `k>=1` at `c`.  Analytic
factorization supplies an analytic function `g`, nonzero at `c`, such that near `c`

```text
h(w)=(w-c)^k g(w).                                      (1)
```

Because `Phi` is real on a real neighborhood of `c`, equation `(1)` on real `w!=c` shows that
`g(w)` is real there.  Continuity gives

```text
A=g(c) in R\{0}.                                        (2)
```

Let

```text
tau = pi/(2k log m)>0.                                  (3)
```

First-coefficient extraction for ordinary Dirichlet series gives, as `sigma -> +infinity`,

```text
D(sigma-i tau)-c
  = a(m)m^(-sigma) exp(i tau log m)+o(m^(-sigma)),

D(sigma+i tau)-c
  = a(m)m^(-sigma) exp(-i tau log m)+o(m^(-sigma)).      (4)
```

Substitute `(4)` into `(1)` and use continuity of `g`.  Since `k tau log m=pi/2`,

```text
Phi(D(sigma-i tau))-Phi(c)
  =  i A a(m)^k m^(-k sigma)+o(m^(-k sigma)),

Phi(D(sigma+i tau))-Phi(c)
  = -i A a(m)^k m^(-k sigma)+o(m^(-k sigma)).            (5)
```

The real number `A a(m)^k` is nonzero.  Thus the two imaginary parts in `(5)` are eventually
strict and opposite.  If their displayed orientation is reversed because `A a(m)^k<0`, exchange
the labels.

Finally set

```text
z_+(sigma)= tau+i(sigma-1),
z_-(sigma)=-tau+i(sigma-1).
```

Then `1-i z_+(sigma)=sigma-i tau` and `1-i z_-(sigma)=sigma+i tau`.  Taking `sigma>H+1` after the
eventual sign threshold proves the claim.

## Hostile audit

- The theorem does not assume a half-plane sign, analytic continuation past the convergence
  domain, Xi zero information, or RH.
- Constant germs are excluded because they erase the source and are not a response realization.
- Infinite-order flat holomorphic germs do not exist unless locally constant; analytic
  factorization exhausts every nonconstant analytic germ.
- The argument is not restricted to Möbius, rational, polynomial, univalent, or locally injective
  transformations.
- Dependence of the transformation on `s`, matrix-valued lifts, and coefficient-nonlocal
  operations lie outside the theorem and remain separate pivots.

## Literature and novelty boundary

Samaris, *Dirichlet series with positive real part*, Bull. Austral. Math. Soc. 46 (1992), 159--166,
DOI `10.1017/S000497270001176X`, owns parent positive-real generalized-Dirichlet theory.  Standard
analytic vanishing-order factorization and first-term Dirichlet asymptotics supply the ingredients.
The exact conjunction above was not located in the targeted audit, but it is a routine synthesis
of those parent theories and is not claimed as publication-level new knowledge.

## Positive survivor

The analytic germ order multiplies the first logarithmic Dirichlet frequency but cannot orient its
conjugate phase pair.  This is the exact invariant missed by the earlier Möbius-only no-go.
Therefore every surviving Route-I pivot must be coefficient-nonlocal, matrix/indefinite, or
explicitly dependent on the spectral parameter.  The source-pure positive-excess energy pivot is
not killed by this theorem.

## Gates

- [x] exact theorem and quantifiers fixed
- [x] complete dependency-closed paper proof
- [x] hostile falsity and circularity audit
- [x] parent-theory literature audit
- [ ] exact unconditional Lean formalization
