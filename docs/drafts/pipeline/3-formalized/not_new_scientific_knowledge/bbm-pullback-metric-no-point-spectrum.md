# The BBM pullback metric contains no Hurwitz point eigenstate

- **ID:** `bbm-pullback-metric-no-point-spectrum`
- **Stage:** 3-formalized
- **Type:** DIRECT HILBERT--PÓLYA ROUTE VERDICT / POSITIVE DOMAIN SPECIFICATION
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Route status:** The Bender--Brody--Muller metric `eta=Delta^* Delta` is closed as a
  Hilbert-space point-spectrum realization. A different arithmetic two-ended rigging remains open.
- **Statement:** In the proposed BBM metric, every formal Hurwitz eigenstate is sent by `Delta` to
  a Mellin monomial `x^(-z)`. Its squared metric density is `x^(-2 Re z)`, which is integrable near
  zero exactly for `Re z<1/2` and at infinity exactly for `Re z>1/2`. Hence no spectral parameter
  produces a Hilbert vector. A viable BBM-type Hilbert--Pólya realization must replace the pullback
  dilation metric by a source-selected two-ended arithmetic domain with genuine discrete point
  spectrum and an infinite prime-phase carrier preserved through completion.

## 1. The proposed operator and metric

Bender, Brody, and Muller define on the positive half-line the formal operator

```text
Delta=1-exp(-i p),
H=Delta^(-1)(x p+p x)Delta.                                  (1)
```

Its formal eigenfunction at `z in C` is

```text
psi_z(x)=-zeta(z,x+1),
H psi_z=i(2z-1)psi_z,
Delta psi_z=x^(-z).                                          (2)
```

The boundary condition `psi_z(0)=0` is exactly `zeta(z)=0`. Their proposed positive metric is,
up to an irrelevant positive scalar normalization,

```text
eta=Delta^* Delta=sin^2(p/2).                                (3)
```

Thus the putative Hilbert norm of the formal eigenstate is

```text
||psi_z||_eta^2
  =||Delta psi_z||_L2(0,infinity)^2
  =integral_0^infinity |x^(-z)|^2 dx
  =integral_0^infinity x^(-2 Re z) dx.                       (4)
```

No assumption on the zeta divisor has entered `(4)`.

## 2. Two-ended incompatibility theorem

Write `beta=Re z`. The standard power-integrability criteria give

```text
integral_0^1 x^(-2 beta) dx < infinity  iff beta<1/2,        (5)
integral_1^infinity x^(-2 beta) dx < infinity iff beta>1/2. (6)
```

The two inequalities are incompatible. At `beta=1/2`, both ends diverge logarithmically. Therefore

```text
integral_0^infinity x^(-2 Re z) dx=infinity
for every z in C.                                            (7)
```

Consequently none of the formal states `psi_z` is a vector in the Hilbert completion defined by
`(3)`. In particular, the boundary condition `psi_z(0)=0` selects zeta zeros only among
distributional dilation eigenfunctions; it does not produce Hilbert-space point eigenvectors of a
self-adjoint operator in the proposed metric.

This conclusion is stronger than checking only `Re z=1/2`: moving off the critical line repairs one
Mellin end only by destroying the other.

## 3. Lean theorem surface

`formal/GaloisForLFunctions/RHTower/BBMMetricObstruction.lean` defines

```text
bbmMellinMetricDensity z x=x^(-2 Re z)
```

and proves

```text
integrableOn_bbmMellinMetricDensity_near_zero_iff
integrableOn_bbmMellinMetricDensity_at_infinity_iff
not_integrableOn_bbmMellinMetricDensity.
```

The exact module compiles and is wired into `RHTower.lean`. The proof uses mathlib's sharp
real-power integrability theorems; no operator-domain premise, zeta zero, or RH hypothesis is
introduced. `#print axioms` on the three theorems returns only `propext`, `Classical.choice`,
`Quot.sound`.

The remaining open box — constructing a source-selected two-ended arithmetic domain satisfying
clauses 1--6 of §5 — is a forward research target, not debt of the theorem proved here.

## 4. Why the formal BBM metric cannot be the Hilbert--Pólya producer

Equation `(3)` makes the metric map exactly the transformation to the ordinary dilation
eigenfunction `x^(-z)`. The standard dilation generator on `L2(R_+,dx)` has generalized Mellin
eigenfunctions, not these functions as normalizable point states. Therefore the formal similarity
to `x p+p x` does not establish a discrete Hilbert spectrum.

The original paper explicitly leaves the domain of `H` open, notes that its eigenstates have
infinite norm, and uses distributional biorthogonality. The present theorem isolates the exact
reason no choice of horizontal zero location repairs that particular norm.

The theorem does **not** exclude an unbounded similarity with a different completed domain, a
rigged-Hilbert generalized spectrum, or a new operator whose secular determinant is `Xi`. It shows
that such a construction is additional mathematics, not a completion of `(3)` by domain closure.

## 5. Positive BBM domain-incidence law

A successful BBM-type realization must construct all of the following as one arithmetic object.

1. **Two-ended rigging.** A canonical graph/form norm controls both `x->0` and `x->infinity` and
   contains the candidate zeta states as actual vectors. It cannot be the pullback norm `(4)`.
2. **Closed arithmetic domain.** The zeta boundary condition is a continuous trace or boundary
   relation on the closed domain, rather than an evaluation imposed on formal nonvectors.
3. **Discrete spectral mechanism.** The realization has compact resolvent, a proved discrete
   spectral measure, or an exact relative determinant. A subset of the continuous dilation
   generalized spectrum is not point spectrum.
4. **Metric production.** Positivity and self-adjointness follow from the completed source and the
   domain before zero localization; they are not reconstructed from biorthogonal zero states.
5. **Infinite arithmetic phase carrier.** The domain or boundary system explicitly contains the
   prime-log character module. At prime cutoff `N`, its phase dimension is at least `pi(N)` and the
   cofinal maps preserve those directions.
6. **Archimedean transport.** The finite Gamma completion weights and reflects the arithmetic
   carrier without collapsing it. The normalized determinant then equals `Xi`, locally uniformly
   and with multiplicity.

Clause 5 is forced by
`finite-archimedean-gamma-product-boundary-law.md`: a commensurable finite Gamma product contributes
one upper projective valuation direction, while every recurrent object DA over its differential
field has finite rational phase rank. The infinite prime phase module must therefore enter through
the arithmetic domain/boundary carrier and survive completion separately.

Together, `(7)` and the finite-Gamma boundary law sharpen the Hilbert--Pólya target:

```text
ordinary dilation pullback metric     -> no Hilbert point states,
finite archimedean completion         -> one valuation direction,
successful BBM-type realization       -> two-ended arithmetic domain
                                         + unbounded prime-phase dimension
                                         + exact Xi determinant.             (8)
```

## 6. Relation to the critical-disc fibre theorem

The required domain topology must also be stronger than compact-open FE--Schwarz germ convergence.
On every fixed-divisor regular-germ fibre, genuine finite Euler-unit orbits are dense and every
Hausdorff continuous invariant is constant. Adding the full `M_0` weighted tail gives a product
closure modulo the single Mertens class, while retaining all reciprocal-square trace moments
recovers the divisor and turns positivity into an RH-equivalent endpoint.

Therefore the BBM repair cannot be a compact-open continuous scalar metric attached to the Hurwitz
germ. It must be a pointed global incidence structure coupling the weighted all-prime tail,
archimedean completion, closed two-ended domain, and distinguished divisor/trace data.

## 7. Scope and scientific status

- This closes the explicit metric `eta=Delta^*Delta` as a Hilbert point-spectrum implementation,
  not the Hilbert--Pólya conjecture or every BBM-inspired domain.
- A new source-built two-ended arithmetic realization satisfying clauses 1--6 would remain viable
  and would constitute the missing proof mechanism.
- Cofinal finite-prime determinant families that carry the `Xi` divisor locally uniformly and
  cross the logarithmic boundary layer are outside this verdict.
- CCM, Sonin, prolate, and finite-Weil constructions are outside this card.

The scalar theorem is a direct application of classical Mellin power integrability. Bender,
Brody, and Muller already state that their eigenstates have infinite norm; Bellissard emphasizes
the lack of ordinary square integrability, and the authors reply that a different pseudo-Hermitian
inner product/domain is required. The exact all-`z` two-ended contradiction and its use as a domain
specification are rigorous and useful, but do not clear the novelty gate.

## References

1. C. M. Bender, D. C. Brody, M. P. Muller, *Hamiltonian for the Zeros of the Riemann Zeta
   Function*, Phys. Rev. Lett. 118 (2017), 130201, DOI `10.1103/PhysRevLett.118.130201`.
2. J. V. Bellissard, *Comment on "Hamiltonian for the Zeros of the Riemann Zeta Function"*,
   arXiv `1704.02644`.
3. C. M. Bender, D. C. Brody, M. P. Muller, *Comment on 'Comment on "Hamiltonian for the zeros of
   the Riemann zeta function"'*, arXiv `1705.06767`.

## Gates

- [x] BBM metric norm reduced to the Mellin power density.
- [x] exact near-zero and infinity thresholds proved.
- [x] global nonintegrability proved in Lean.
- [x] point-spectrum conclusion separated from distributional spectrum.
- [x] finite-Gamma one-direction law integrated into the positive domain specification.
- [x] wired into the shared `GaloisForLFunctions.RHTower` umbrella (line 125), targeted build green, axiom audit clean.
- [ ] construct a source-selected two-ended arithmetic domain satisfying clauses 1--6.
