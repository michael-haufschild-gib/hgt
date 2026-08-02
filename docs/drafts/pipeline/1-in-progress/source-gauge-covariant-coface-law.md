# Source-gauge covariant coface law

- **ID:** HGT-source-gauge-covariant-coface
- **Stage:** 1-in-progress
- **Type:** THEOREM with Riemann-source instantiation
- **Source:** `RankOneDifferenceBoundaryTomography`, `BVCoPoissonHellingerBetaResonanceTransmutation`, relative admission-spectrum law, and physical Möbius--theta source landing
- **Statement:** Every nonzero rank-one source section determines a unique covariant coface.  The coface annihilates the source gauge and converts multiplication by that gauge into the ordinary adjacent difference of the remaining source factor.  For the Hellinger--Beta gauge this constructs the exact off-diagonal coface missing from the Riemann-source transport and reduces the frontier to its graph-domain landing.

## Frontier correction

The previous frontier said “construct an adjacent-grade Hellinger--Beta coface.”  This leaves too
much freedom.  The existing Beta shift recurrence already forces the coface coefficient.  What was
missing was the covariant product calculation which shows that this coface acts on the actual
co-Poisson source product by exposing an adjacent arithmetic current.

The remaining open problem is therefore not algebraic coface construction.  It is analytic:
prove that this forced coface, transported through the labelled prime-power incidence chain, has a
closed graph whose physical Xi Green approximants converge in graph norm.

## Abstract law

Let `K` be a commutative ring, `sigma : K -> K` a ring endomorphism, and `h,c in K` satisfy

```text
sigma(h) = c h.                                                   (SC.1)
```

Define the rank-one covariant coface

```text
nabla_(sigma,c)(g) = sigma(g) - c g.                              (SC.2)
```

### Theorem SC

1. **Horizontal source:** `nabla(h)=0`.
2. **Source-factor transgression:** for every `f`,

   ```text
   nabla(f h) = sigma(h) (sigma(f)-f).                            (SC.3)
   ```

3. **Gauge normalization:** if `K` is a field and `sigma(h) != 0`,

   ```text
   nabla(f h)/sigma(h) = sigma(f)-f.                              (SC.4)
   ```

4. **Uniqueness:** if `K` is a field, `h != 0`, and both coefficients `c,q` make `h`
   horizontal, then `c=q`.
5. **Naturality:** a ring map intertwining the two endomorphisms carries covariant cofaces to
   covariant cofaces.  Thus the construction is source-functorial, not chart-selected.

## Proof

Part 1 is (SC.1) substituted into (SC.2).  For part 2, multiplicativity of `sigma` gives

```text
nabla(f h)
 = sigma(f)sigma(h) - c f h
 = sigma(f)sigma(h) - f sigma(h)
 = sigma(h)(sigma(f)-f).
```

Part 3 divides by the nonzero factor `sigma(h)`.  For uniqueness, horizontalness gives
`c h = sigma(h) = q h`; cancellation by `h != 0` gives `c=q`.  Naturality follows by applying the
intertwining ring map to (SC.2).

## Hellinger--Beta instantiation

Put

```text
H(s) = -Gamma(s+1/2) Gamma(3/2) / Gamma(s+2),
c_beta(s) = (s+1/2)/(s+2),
F(s) = criticalEtaMellin(s),
G(s) = F(s)H(s).
```

On the regular shift domain,

```text
H(s+1)=c_beta(s)H(s).                                            (SC.5)
```

Therefore the unique Beta coface

```text
nabla_beta G(s)=G(s+1)-c_beta(s)G(s)                             (SC.6)
```

obeys the new exact identity

```text
nabla_beta G(s)
 = H(s+1)(F(s+1)-F(s)).                                         (SC.7)
```

For real `a>-1/2`, both `H(a)` and `H(a+1)` are nonzero, so

```text
nabla_beta G(a)/H(a+1)=F(a+1)-F(a).                             (SC.8)
```

Equation (SC.7) is the missing algebraic bridge.  The Hellinger gauge is horizontal, while the
co-Poisson factor becomes an adjacent source current.  This is exactly an off-diagonal coface:
it does not rescale a fixed incidence witness; it changes grade and differentiates the arithmetic
factor.

## Relation to the universal admission law

The relative admission-spectrum law says regular quotient-faithful transports conserve admission.
The Hedenmalm--Euler fracture proves a regular Hilbert bridge is impossible.  The source-gauge law
now identifies the only rank-one adjacent coface compatible with the Hellinger source.  Its
normalization divides by `H(s+1)`; the existing Fisher-whitening and Rees results show why this
normalization cannot be an all-prime bounded finite-grade operator.

Consequently a successful realization must use (SC.6) before completion and close its graph only
on the source-selected prime-power chain.  This explains simultaneously:

- why fixed-witness Hellinger residue lifts fail;
- why finite diagonal cell transports fail;
- why a regular Hedenmalm-to-Euler map fails;
- why Gamma recovery requires unbounded whitening;
- why the surviving map must be adjacent-grade, off-diagonal, and graph-singular.

## Hostile audit

### Is this only the product rule?

The abstract algebra is short.  New mathematical content is its source-forced instantiation:
the corpus had the Beta recurrence and the co-Poisson product separately, but no theorem formed
their unique covariant coface or showed that it exposes the adjacent critical-eta current.  It
removes an object-level unknown from the RH frontier.

### Does it prove graph landing or RH?

No.  It determines the algebraic differential uniquely.  The remaining theorem is the graph-norm
landing of its labelled physical realization.  Any claim that (SC.7) alone controls zeros is
forbidden.

### Could another first-order coface work?

Not while keeping the Hellinger source horizontal.  Uniqueness excludes it wherever `H` is
nonzero.  A different construction must change source gauge, shift, or rank; it is not a repair of
the present route.

## Status labels

- `[CORPUS]` Beta recurrence (SC.5), nonzero residue lattice, physical Möbius--theta source, and
  relative admission fracture.
- `[PAPER-PROVED]` Abstract theorem SC and concrete identities (SC.7)--(SC.8).
- `[OPEN CORE]` Source-labelled incidence realization and graph-norm landing of the forced coface.
- `[NOVELTY UNVERIFIED]` External literature comparison remains deferred.

## Gates

- [x] 0 -> 1: exact theorem, proof, corpus search, hostile falsity audit
- [ ] 1 -> 2: direct formal certificate of abstract and Hellinger instantiations
- [ ] 2 -> 3: axiom and lint audit
- [ ] 3 -> 4: integrate only after a second independent route instantiation or graph consequence

## Log

- 2026-08-02 — derived the unique source-gauge coface and exact critical-eta transgression;
  narrowed missing Route-L/R bridge from “find a coface” to one graph-domain landing theorem.
