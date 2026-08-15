# Route P primitive Burnol aperture defect first flux

- **ID:** `route-p-primitive-burnol-aperture-defect-first-flux`
- **Stage:** 3-formalized
- **Label:** `P-G189`
- **Source:** P-G188, P-G162, Route-P Gamma-sewn recovery first-jet no-go
- **Statement:** P-G188's primitive aperture defect opens linearly with a globally summable
  arithmetic flux. The deleted hard-edge interval is first-order flat; the distributed tail
  cocycle carries the entire flux. Any Hilbert realization of that tail channel is necessarily
  nondifferentiable at the aperture wall.

## Conjecture, hostile audit, and pivot

P-G188 supplied an exact positive colligation, but that alone did not show which defect component
could interact with completion. A first conjecture treated the hard-edge interval as the likely
Gamma--polar boundary current. It fails at the first jet.

For primitive cell `(p,e)`, write

```text
lambda_(p,e) = log(p^(e+1)),
w_(p,e)      = routePPrimitiveBaseCauchyCubicWeight(p,e),
M_c(p,e)     = (1-exp(-2c lambda_(p,e))) w_(p,e).                  (1)
```

Then

```text
M'_0(p,e) = J(p,e) := 2 lambda_(p,e) w_(p,e) > 0.                 (2)
```

But every primitive Burnol feature vanishes linearly at `L=0`, so its squared density vanishes at
the hard edge. The fundamental theorem of calculus gives

```text
E(B_c F_(p,e,kappa))/c -> 0.                                      (3)
```

Subtracting `(3)` from P-G188's exact energy colligation proves

```text
E(D_c F_(p,e,kappa))/c -> J(p,e).                                 (4)
```

Thus the initial loss is not boundary-interval mass. It is entirely the cocycle defect spread
over the surviving aperture tail.

## Arithmetic and global flux law

Lean reduces `(2)` to the exact primitive arithmetic density

```text
J(p,e)
 = 1/2 * 1/[p log p] * p^(-e) * (e+1)^(-2).                       (5)
```

One aperture derivative removes exactly one inverse logarithm and one inverse depth factor from
the cubic source mass. Prime sparsity still makes the result summable:

```text
sum_(p,e) J(p,e) < infinity.                                      (6)
```

The proof dominates `(5)` by
`(1/2)[p log p]^(-1) 2^(-e)` and uses the already-formalized prime theorem
`sum_p 1/[p(log p)^s]<infinity` for every `s>0`.

Moreover, `1-exp(-x)<=x` gives the uniform domination

```text
0 <= M_c(p,e)/c <= J(p,e),     c>0.                               (7)
```

Dominated convergence therefore closes the global first variation:

```text
[sum_(p,e) M_c(p,e)]/c -> sum_(p,e) J(p,e)                        (8)
```

as `c->0+`. This is a trace-finite, source-defined aperture current, not an atomwise formal
derivative with uncontrolled total mass.

## Square-root/Wold singularity

Suppose a Hilbert-valued channel `v(c)` satisfies `v(0)=0` and either

```text
||v(c)||^2 = M_c(p,e)
```

or, more sharply, `||v(c)||^2=E(D_c F_(p,e,kappa))` for `c>0`. Equations `(2)` and `(4)` give a
strictly positive limit for `||v(c)||^2/c`. If `v` had a finite derivative at zero, differentiating
its squared norm would instead give derivative zero. Lean proves the contradiction
unconditionally for every primitive cell.

Hence the actual defect amplitude is intrinsically `sqrt(c)` scale. This is not a technical
regularity loss: it is the exact Wold/noise behavior required to store a linear energy flux in a
new orthogonal channel.

## Big-picture reinterpretation

P-G162 and `RoutePGammaSewnRecoveryFirstJetNoGo.lean` showed that differentiable scalar
completion cannot cancel the Xi Ward first jet; synchronized Gamma-sewn recovery is itself
first-order transparent. P-G189 identifies the complementary source geometry. An unconditional
positive completion channel can carry the required order-one energy only by being singular as a
vector at the wall, even while its total energy current is trace finite.

The earlier obstruction was therefore a shadow of a higher principle:

```text
first-order energy transport + zero boundary vector
  forces square-root amplitude regularity.                         (9)
```

The completed producer cannot be an ordinary differentiable block interpolation. It must retain a
pre-scalar Wold/rigged channel whose energy, not vector amplitude, has a finite first boundary jet.
P-G189 constructs the exact source-side candidate current but does not yet identify its
coefficientwise Gamma--polar phase or map it to Xi divisor nodes.

## Novelty and theatre audit

Internal corpus search found:

- P-G162's target-side linear Julia loss versus quadratic differentiable tangent;
- Gamma-sewn recovery's first-jet transparency;
- general Sonin lost-layer aperture defects;
- P-G188's finite-time Burnol colligation.

It found no theorem concentrating P-G188's first variation in the tail cocycle, no arithmetic law
`(5)`, no global dominated-convergence identity `(8)`, and no unconditional nondifferentiability
theorem for this primitive defect channel.

Primary-source audit found general weighted translation semigroup models and Wold/Sz.-Nagy defect
theory, including [Phatak--Sholapurkar](https://arxiv.org/abs/1804.08981) and the earlier
[operator-weighted translation semigroup study](https://acta.bibl.u-szeged.hu/14936/1/math_046_249-260.pdf).
Those sources motivate weighted shifts, positive defect operators, and isometric dilations, but
the audited material does not state `(1)`--`(9)` for Burnol conormal features and primitive Euler
weights. No external priority claim is made beyond the exact Route P synthesis.

Every new claim above is a closed theorem. No numerical cutoff, Xi zero, RH premise, abstract
postulated contraction, or differentiability assumption enters the positive flux construction.
The card does not claim Gamma--polar identification or RH.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveBurnolApertureDefectFirstFlux.lean
```

Capstones:

- `hasDerivAt_routePPrimitiveBurnolApertureDefectMass_zero`;
- `tendsto_routePPrimitiveBurnolApertureBoundaryDefectEnergy_div_zero`;
- `tendsto_routePPrimitiveBurnolApertureTailDefectEnergy_div_zero`;
- `routePPrimitiveBurnolApertureDefectFlux_eq`;
- `summable_routePPrimitiveBurnolApertureDefectFlux`;
- `tendsto_routePPrimitiveBurnolApertureTotalDefectMass_div_zero`;
- `not_hasDerivAt_of_norm_sq_eq_routePPrimitiveBurnolApertureTailDefectEnergy`.

Verification:

- `/tmp/pg189.lean`: `lake env lean /tmp/pg189.lean` passed cleanly;
- exact leaf build passed;
- `/tmp/pg189_audit.lean`: capstones depend only on `propext`, `Classical.choice`, `Quot.sound`;
- targeted forbidden-declaration scan: clean;
- umbrella import wired; umbrella not built.

## Gates

- [x] hostile prior-corpus audit
- [x] hard-edge conjecture falsified
- [x] strongest tail-flux survivor extracted
- [x] atomwise exact first variation
- [x] global summability and dominated-convergence law
- [x] unconditional square-root regularity obstruction
- [x] scratch verification
- [x] exact leaf build
- [x] axiom and forbidden-declaration audit
- [x] umbrella wired without umbrella build
- [ ] identify `J(p,e)` as literal coefficientwise Gamma--polar current
- [ ] construct matrix-complete boundary transport to Xi divisor nodes
- [ ] unconditional RH
