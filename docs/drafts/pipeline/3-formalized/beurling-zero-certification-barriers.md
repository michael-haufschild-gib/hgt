# Geometric-lattice discrepancy and convergent Euler-product nonvanishing

- **ID:** `BEURLING-ZERO-CERTIFICATION-BARRIERS-001`
- **Stage:** 3-formalized
- **Type:** Existing elementary theorems; corrected application scope
- **Parent:** [Thin-deletion audit](../1-in-progress/thin-random-deletion-beurling-alpha-beta.md)
- **RH used:** no
- **Status:** `[NARROW LEAN RESULTS] [NO EXHAUSTIVE CONSTRUCTION CLASSIFICATION]`

The Lean file proves the following exact statements. It does not exclude all self-similar
systems, all prime perturbations, or every construction with prescribed counting exponents.

## Fixed geometric lattice

For q>1, a>0, and N constant on `[q^n,q^(n+1))`, some x in that interval satisfies

```
|N(x)-a*x| >= a*(q-1)/(4*q)*x.
```

The proof compares the left endpoint and midpoint. If the constancy holds for every n, these
lower bounds preclude `N(x)=a*x+o(x)`. The declaration is
`RHTower.BeurlingBarriers.lattice_no_power_saving`.

Generalized integers supported on powers of a fixed q satisfy the hypothesis. Arbitrary
self-similarity and nonlattice fractal constructions are not classified by this theorem.
The explicit discrepancy lower bound is the positive survivor.

## Modification inside its convergence region

For q_i>1, sigma>0, and `sum_i q_i^(-sigma)<infinity`, Lean proves

```
product_i (1-q_i^(-s)) != 0               when Re(s)>=sigma.
```

The proof bounds the complex terms by a summable positive family and uses the convergent
logarithm product theorem. The declarations are `tprod_one_sub_ne_zero` and
`modification_factor_ne_zero` in `RHTower.BeurlingBarriers`.

If a separately proved analytic comparison identifies a modified zeta with the base zeta
times this factor or its inverse, their zero divisors agree within that region. A rescaling
requires convergence estimates for both old and new factors. Boundary zeros and continuation
beyond this region are not covered.

The parent card's general `beta>=gamma` inference was unsupported. It cannot replace the
convergence assumption by an integer-counting error exponent below 1/2. A logarithmic
singularity can exponentiate to an analytic zero, as the published deletion construction
also explains. [Broucke–Debruyne–Révész, section 5](https://arxiv.org/html/2309.01567v2#S5).

## Formal status

All three declarations belong to
`GaloisForLFunctions.RHTower.BeurlingLatticeAndModificationBarriers`, already imported by the
RHTower umbrella. Their bodies are unchanged. The scratch axiom audit found only `propext`,
`Classical.choice`, and `Quot.sound`; source-comment checks and narrow build results are
recorded in the current corpus architecture audit.

The proposed universal uncertainty principle and claim that all construction regimes were
exhausted are withdrawn as conclusions of these results. This card proves neither that
principle nor its negation, and supplies no RH architecture or novelty claim.
