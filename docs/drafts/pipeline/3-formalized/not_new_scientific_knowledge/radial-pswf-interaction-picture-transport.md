# Radial PSWF remainders possess an exact interaction-picture transport law

- **ID:** `radial-pswf-interaction-picture-transport`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`
- **Scientific status:** `[PROVED] [LEAN] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theory:** one-dimensional scattering/Jost variation of constants
- **Lean:** `formal/GaloisForLFunctions/RHTower/RadialPSWFInteractionPicture.lean`
- **Statement:** Every solution of the Liouville-transformed exterior radial PSWF equation has an
  exact two-phase decomposition whose amplitudes are transported only by the short-range
  potential. This replaces the invalid operation of factoring an additive asymptotic remainder
  through an oscillatory exponential.

## Exact theorem

Let `W,V,psi : R -> C`, let `c!=0`, and assume

```text
W'=V,
V'=(psi-c^2)W.                                                  (1)
```

Define

```text
a_+(x)=1/2 exp(-i*c*x)[W(x)+V(x)/(i*c)],
a_-(x)=1/2 exp( i*c*x)[W(x)-V(x)/(i*c)].                        (2)
```

Then

```text
W(x)=a_+(x)exp(i*c*x)+a_-(x)exp(-i*c*x),                        (3)

a_+'(x)= exp(-i*c*x)psi(x)W(x)/(2*i*c),
a_-'(x)=-exp( i*c*x)psi(x)W(x)/(2*i*c).                         (4)
```

No asymptotic statement or remainder hypothesis enters `(3)`--`(4)`.

## Proof

Equation `(3)` follows by substituting `(2)` and cancelling the two velocity terms. Differentiate
`(2)`, insert `(1)`, and use `i^2=-1`; the free terms `c^2 W` and the two copies of `V` cancel,
leaving `(4)`.

Lean proves these identities as:

- `radialInteraction_reconstruct`;
- `hasDerivAt_radialInteractionPlus`;
- `hasDerivAt_radialInteractionMinus`.

## Exterior radial consequence

Dunster's Liouville transformation gives exactly

```text
W''+c^2 W=psi_sigma W                                           (5)
```

on the radial interval. On every fixed exterior sector `z>=1+delta`, his explicit potential
satisfies, uniformly for fixed mode and `0<=sigma<=sigma_0<1`,

```text
|psi_sigma(xi)|<=C_delta(1+xi)^(-2),
integral |psi_sigma(xi)| dxi<=C_delta.                          (6)
```

Equations `(4)` and `(6)`, followed by Gronwall, give

```text
sup |a_+|+sup |a_-|<=C,
Var(a_+)+Var(a_-)<=C/c.                                        (7)
```

Thus the exact radial solution, including its Olver remainder, has a phase-preserving
bounded-variation representation. The conclusion comes from the ODE, not from treating the
printed additive `O(c^(-p))` error as a relative error.

## CCM route correction

The existing exterior off-diagonal and high-radial first-row arguments require precisely `(7)`.
Their earlier justification by a complex-domain Cauchy estimate was insufficient: Cauchy's
estimate controls the derivative of the additive remainder, while factoring out `exp(+/-i*c*xi)`
can itself create a derivative of order `c`. The interaction-picture law removes that gap.

After the elementary geometric prefactor in the radial PSWF is restored and `z=r*x` is inserted,
`(7)` yields the symbol and bounded-variation estimates used by:

- `ccm-exact-radial-nonstationary-sector-bound.md`;
- `ccm-exact-high-radial-first-row-bv-bound.md`;
- `ccm-countable-log-chirp-renormalization-law.md` on the exterior branches.

The pole-uniform `r=1` Bessel endpoint still requires its separate endpoint-coordinate estimate;
this theorem does not conceal that input.

## Novelty and significance

The interaction-picture transform is standard one-dimensional scattering theory. Its application
repairs a load-bearing CCM proof step, but it fails the parent-theory novelty gate and is honestly
classified as a bridge.

## References

- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699,
  equations `(2.10)`--`(2.21)`.
- F. W. J. Olver, *Asymptotics and Special Functions*.

## Gates

- [x] exact reconstruction formalized
- [x] exact amplitude derivatives formalized
- [x] no axioms, `sorry`, or hidden radial asymptotic assumptions
- [x] short-range exterior consequence proved on paper
- [ ] pole-uniform endpoint BV estimate formalized analytically
- [ ] full radial PSWF realization in Lean
