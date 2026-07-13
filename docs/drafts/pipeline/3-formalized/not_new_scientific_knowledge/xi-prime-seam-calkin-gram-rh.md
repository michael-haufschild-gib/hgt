# Xi prime-seam Calkin Gram compactness criterion

- **ID:** `xi-prime-seam-calkin-gram-rh`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[FORMALIZATION]`, `[BRIDGE]`, `[CONTRADICTION ENDPOINT]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiPrimeSeamCalkinGram.lean`
- **Arithmetic endpoint:** `xi-prime-seam-coherence-collapse.md`
- **Operator parents:** `sonin-prime-quadratic-calkin-matrix-injectivity.md`;
  `finite-prime-sonin-gram-matrix-injectivity.md`
- **Paper continuation:**
  `../../2-fully-proven/not_new_scientific_knowledge/sonin-two-particle-prime-coherence.md`

## Statement

For a positive Sonin cutoff `a`, rational primes `p,q`, and an open-strip point `rho`, let

```text
c_p(rho)=log(p)(p^(-conj(rho))-p^(-(1-rho)))
```

and weight the literal two-prime archimedean Euler Gram entry by its seam difference:

```text
G_(p,q)(rho)=(c_p(rho)-c_q(rho)) C_(p,q)(a).               (1)
```

The exact Calkin norm is

```text
||G_(p,q)(rho)||_ess
  = |c_p(rho)-c_q(rho)|/(sqrt(p)sqrt(q)).                  (2)
```

Since every unweighted `C_(p,q)(a)` is noncompact,

```text
G_(p,q)(rho) is compact
  iff
c_p(rho)=c_q(rho).                                        (3)
```

Therefore

```text
all G_(p,q)(rho) compact
  iff Re(rho)=1/2                                         (4)
```

on the open strip, and globally on the Xi divisor,

```text
all Xi-fibre prime-pair seam Gram corners compact
  iff RH.                                                  (5)
```

The contradiction form is formalized as a positive witness:

```text
not RH
  -> exists rho in the Xi divisor, exists primes p,q,
       G_(p,q)(rho) is noncompact.                         (6)
```

False RH is thus detected by survival of one canonical prime-pair Gram class in the Calkin
algebra, rather than only by a nonzero scalar seam or by divergent finite energy.

## Proof

Equation `(2)` is scalar homogeneity of the essential norm combined with the already formalized
identity

```text
||C_(p,q)(a)||_ess=1/(sqrt(p)sqrt(q)).
```

For `(3)`, the reverse implication is immediate.  For the forward implication, if the coefficient
were nonzero, compactness of its scalar multiple would imply compactness of `C_(p,q)(a)` after
multiplication by the inverse scalar.  This contradicts the existing literal Sonin quadratic-corner
noncompactness theorem.

All-pair compactness is therefore exactly prime-seam coherence.  Cofinal prime decay collapses a
coherent seam family to zero, and the prime-two seam vanishes exactly at `Re(rho)=1/2`.  Applying
this fibrewise on the Xi divisor gives `(5)` and classical negation gives `(6)`.

## Contradiction chain and exact open core

The new detour changes the sufficient source target from a uniform norm estimate to ideal
membership:

```text
[OPEN CORE] source-completed relative Sonin Gram identity
  -> every canonical seam-weighted principal Gram corner is compact
  -> every seam difference vanishes by Calkin rigidity
  -> all prime seams are coherent
  -> cofinal decay kills the common seam
  -> every Xi zero lies on the critical line
  -> RH.                                                    (7)
```

This chain can be shorter than the tensor-square uniform-bound route because compactness is an
exact yes/no invariant.  It is also stricter: a bounded but noncompact principal component does not
suffice.  The existing Hilbert--Schmidt principal-subtracted relative defects show that compact
correction terms are available, but they do not establish the missing full-source identity or prove
that its remaining principal term is `(1)`.

Functional-equation symmetry alone does not provide the open implication.  Identifying the
FE-reflected and Schwarz-reflected fibres is already the critical-line equation, so inserting that
identification into a compactness proof would be circular.

## Literature audit

`[SEARCH]` Connes--Consani's
[*Weil positivity and Trace formula, the archimedean place*](https://arxiv.org/abs/2006.13771)
locates positivity in compression of the scaling action to the Sonin complement and develops a
compact correction operator controlled through prolate functions and Hermitian Toeplitz matrices.
It also states that the ingredients extend to the semilocal setting where Weil positivity would
imply RH.  This supports the shape "source principal operator plus compact correction", but the
paper does not identify the seam-weighted two-prime Calkin class `(1)` or prove its compactness.

`[SEARCH]` Connes--Consani--Moscovici's
[*Zeta zeros and prolate wave operators*](https://arxiv.org/abs/2310.18423) constructs stable
semilocal Sonin spaces and a semilocal prolate candidate.  It proposes comparison of an
automatically positive operator trace with the Weil functional as the route to semilocal
positivity.  No prime-pair seam Gram compactness identity matching `(7)` was located.

`[SEARCH]` Connes--Moscovici's
[*Prolate spheroidal operator and Zeta*](https://arxiv.org/abs/2112.05500) places the negative
prolate spectrum on the Sonin space and matches its ultraviolet counting to zeta zeros.  This
supplies the correct archimedean carrier but no source-pure finite-prime compactness theorem.

`[POSITIVE NO-GO]` Connes--Consani's
[*The Scaling Hamiltonian*](https://arxiv.org/abs/1910.14368) proves that the direct local
inner-function mechanism fails: the finite-prime and archimedean local-factor ratios are not
bounded inner functions, and the corresponding local inequality is false in general.  Positively,
the missing identity in `(7)` must preserve the global Poisson normalization and the two Weil
moment constraints; independent local contractions cannot produce the required compactness.

`[OPEN CORE]` No located primary source proves that a globally normalized semilocal source
completion has `(1)` as its sole principal Calkin class with all other terms compact.  That exact
principal-symbol extraction, not Calkin coefficient rigidity, is now the missing theorem.

## Principal declarations

```text
orbitwisePrimeSeamCalkinGramCorner
OrbitwisePrimeSeamCalkinGramCompact
essentialNorm_orbitwisePrimeSeamCalkinGramCorner
orbitwisePrimeSeamCalkinGramCorner_isCompactOperator_iff
orbitwisePrimeSeamCalkinGramCompact_iff_re_eq_half
XiPrimeSeamCalkinGramCompact
xiPrimeSeamCalkinGramCompact_iff_riemannHypothesis
exists_noncompact_primeSeamCalkinGramCorner_of_not_riemannHypothesis
```

## Gates

- [x] exact seam-weighted essential norm
- [x] compactness iff equality of the two canonical seam charges
- [x] fibrewise compactness iff critical-line equation
- [x] global compactness iff RH
- [x] positive noncompact witness from false RH
- [x] Lean proof
- [x] targeted primary-literature audit
- [ ] construct the globally normalized source-completed relative Gram operator
- [ ] identify `(1)` as its only principal Calkin class
- [ ] prove all remaining source terms compact without using Xi zero locations
- [ ] complete RH proof
