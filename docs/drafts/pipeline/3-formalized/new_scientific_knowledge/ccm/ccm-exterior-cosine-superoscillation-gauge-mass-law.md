# CCM exterior cosine superoscillation gauge-mass law

- **ID:** ccm-exterior-cosine-superoscillation-gauge-mass-law
- **Stage:** 3-formalized
- **Type:** exact construction / quantitative obstruction
- **Route:** CCM exterior-measure gauge quotient
- **Status:** [LEAN-PROVED] [NOVELTY-PLAUSIBLE]
- **RH used:** no
- **Computation used:** no

## Audited frontier

[CORPUS] `CCMActualHeadExteriorCosineMeasureGauge.lean` proves every finite measure supported beyond
physical aperture diameter gives a null quadratic gauge. A pointwise nonnegative corrected-symbol
representative for every aperture would imply RH.

[CORPUS] `CCMActualHeadExteriorGaugeCoerciveCompactReduction.lean` proves corrected symbol is a
coercive Gamma backbone modulo bounded prime/polar and finite-measure Fourier–Stieltjes channels.
Every fixed representative is positive outside some compact core, but its lower bound loses total
mass of positive and negative gauge measures.

[CORPUS] Search found no construction of exterior measures reproducing lower-frequency behavior and
no coefficient/mass law governing that construction.

[LITERATURE] Classical binomial superoscillation constructs band-limited exponential polynomials
converging locally uniformly to frequencies outside their band; exponential energy or coefficient
cost is known. The literature audit found no Riemann-Weil/CCM aperture-null interpretation, no
Jordan decomposition into the project measures, and no identification of coefficient variation
with the exact mass term in the corrected-symbol coercive bound. Novelty claim is limited to this
project-specific synthesis and exact formal theorem package.

## Conjecture loop

### C1 — exterior frequencies cannot reproduce a lower cosine

[FALSIFIED] Explicit packet

~~~text
P_N(x) = exp(i H x) ((1-c) + c exp(-i δ x/N))^N
~~~

has frequencies `H-kδ/N`. If `H-δ ≥ H₀`, every atom is exterior, while
`P_N(x) → exp(i(H-cδ)x)`. Its real part therefore reproduces a lower cosine pointwise.

### C2 — abstract signed polynomials may not belong to the physical gauge ideal

[FALSIFIED] Split each real coefficient `q_k` canonically as
`max(q_k,0)-max(-q_k,0)` and put both parts at lag

~~~text
h_k = (H-kδ/N)/(2π).
~~~

This constructs two honest finite positive measures. Their cosine-transform difference equals the
real packet exactly. When `H-δ ≥ 4πa`, both measures are almost-everywhere supported on `h ≥ 2a`,
so the packet is an exact null gauge for every state in the Suzuki aperture Hilbert space.

### C3 — compact lifting can be made harmless by taking `N` large

[FALSIFIED FOR THE CANONICAL PACKET] For `c ≥ 1`, exact binomial algebra gives

~~~text
sum_k |q_k| = (2c-1)^N.
~~~

Lean proves this is also exactly

~~~text
mu_N.real univ + nu_N.real univ,
~~~

the mass loss appearing in the coercive corrected-representative lower bound. Strict downshift below
the exterior band forces `c>1`; hence mass diverges exponentially even though net coefficient mass
is always one. Taking `N` large improves local approximation while worsening the certified global
tail budget without bound.

## Scientific conclusion

Exterior-frequency gauges have full qualitative local expressive power: they can simulate lower
frequencies while remaining physically invisible to the aperture quadratic form. This eliminates
lack of compact expressivity as the obstruction.

The true obstruction is quantitative and global. Superoscillatory cancellation concentrates a net
mass-one signed measure inside exponentially large positive and negative Jordan parts. The CCM tail
proof sees precisely their combined mass. Thus the earlier compact-core reduction and exterior
gauge quotient are two shadows of one principle:

> locality beyond aperture is bought by cancellation, while global positivity is charged at total
> variation rather than net mass.

This does **not** prove RH. It sharply changes the open core: either construct a noncanonical
exterior lift with a tail-compatible mass/error law, prove an unavoidable lower bound ruling such a
lift out, or use a gauge channel whose positive tail grows with its cancellation cost.

## Lean certificate

Module:

~~~text
GaloisForLFunctions.RHTower.CCMActualHeadExteriorCosineSuperoscillation
~~~

Lean proves:

1. exact binomial exponential and cosine expansions;
2. exterior support for every packet atom;
3. finite positive/negative atomic measure construction and finite-measure instances;
4. exact cosine-transform difference and corrected-representative identity;
5. exact aperture support and null quadratic-form theorem;
6. exact positive, negative, and combined measure mass identities;
7. total variation `(2c-1)^N`, net mass one, and exponential divergence for `c>1`;
8. pointwise convergence to arbitrary prescribed lower-frequency cosines.

Verification:

- `lake env lean GaloisForLFunctions/RHTower/CCMActualHeadExteriorCosineSuperoscillation.lean`
  passed;
- targeted `lake build GaloisForLFunctions.RHTower.CCMActualHeadExteriorCosineSuperoscillation`
  passed; no umbrella/full build was run;
- all 29 public theorem/instance axiom audits report only `propext`, `Classical.choice`, and
  `Quot.sound`;
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration occurs in module;
- module is imported by `GaloisForLFunctions.RHTower` umbrella.
