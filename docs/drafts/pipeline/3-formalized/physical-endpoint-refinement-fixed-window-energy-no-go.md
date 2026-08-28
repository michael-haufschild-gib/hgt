# Physical endpoint refinement fixed-window energy no-go

- **ID:** `physical-endpoint-refinement-fixed-window-energy-no-go`
- **Stage:** 3 — formalized in Lean 4
- **Source route:** CCM-FU / PPM / completed physical endpoint response
- **Theorem status:** Lean-proved

## Claim

Bare cofinal upper or lower boundedness of completed physical endpoint Dirichlet energy on
translated fixed-width prime-log packets is unconditional and therefore cannot distinguish RH.

The completed unit--double refinement kernel depends only on prime-log displacement. Existing
unconditional completed-seam estimates on `Re(s)=1` and `Re(s)=2` bound that kernel polynomially
in displacement. A fixed logarithmic window keeps every displacement bounded independently of
translation scale; Mertens keeps total endpoint mass bounded; physical aperture geometry bounds
every squared carrier distance. These three bounds give an absolute, scale-uniform estimate for
refinement energy. Loop 82's valuation-correction estimate then gives the same result for fully
completed endpoint energy.

## Gates

- [x] Exact paper statement and proof
- [x] Corpus conjecture search before construction
- [x] Targeted literature novelty audit through 2026-08-27
- [x] Direct Lean check
- [x] Umbrella wiring
- [x] Targeted module build and built-module axiom audit
- [ ] Publication-ready exposition

## Exact theorem

Write

```text
K12(x,y)=2 S(2+i(x-y))-S(1+i(x-y)),
```

where `S=-xi'/xi` is completed seam flux. Existing unconditional line bounds imply that some
`C12>=0` satisfies

```text
||K12(x,y)|| <= C12 (1+|x-y|)^9.                            (1)
```

For the exact support packet

```text
P_m={p : m-A < log p <= m+c},
```

every two members obey

```text
|log p-log q| <= A+c.                                       (2)
```

More generally, if the sampled real refinement kernel is bounded by `K>=0` on a finite packet
`P`, then the true centered physical-aperture Hilbert distance and endpoint weights give

```text
|D_ref(P,A,m,k)| <= 4 A K [sum_(p in P) log(p)/p]^2.        (3)
```

Mertens supplies

```text
sum_(p in P_m) log(p)/p <= A+c+C_M                           (4)
```

whenever `A>0`, `c>=0`, and `2<=exp(m-A)`. Combining `(1)--(4)` gives

```text
|D_ref(P_m,A,m,m+c)|
 <= 4 A C12 (1+A+c)^9 (A+c+C_M)^2.                          (5)
```

Loop 82 proves the valuation contribution is at most

```text
4 A M_corr (A+c+C_M)^2.
```

Hence

```text
|D_end(P_m,A,m,m+c)|
 <= 4 A [C12 (1+A+c)^9+M_corr] (A+c+C_M)^2,                 (6)
```

uniformly in scale `m`. Lean closes the universal statement for every `A>0,c>=0`, plus
premise-free unit-window absolute and two-sided capstones.

## Proof

The completed unit--double kernel is exactly the difference of two completed flux evaluations.
Triangle inequality combines the corpus global line-one and line-two bounds into `(1)`. Window
membership gives both upper and lower bounds for each prime log, so `abs_le` proves `(2)`.

The exact kernel-distance form of refinement energy removes diagonal completion. Termwise absolute
values bound its real kernel coefficient by `K`; every positive endpoint-weight pair remains
positive; every squared Hilbert distance is at most `4A`. Factoring the resulting double sum gives
`(3)`. Equation `(4)` is the exact fixed-width Mertens increment already established in Loop 82.
This proves `(5)`.

The completed energy is refinement energy plus valuation-correction energy. Applying `abs_add_le`
to that exact decomposition and the Loop 82 bound proves `(6)`. `D<=|D|` and `-|D|<=D` then give
unconditional upper and lower cofinal bounds.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalEndpointRefinementFixedWindowEnergyNoGo.lean`
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean`
- Direct check: PASS
- Targeted build: PASS (`11798/11798`)
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Capstones:
  `exists_norm_xiUnitDoubleCompletedOffDiagonalResponseKernel_global_le`,
  `abs_xiUnitDoubleCompletedRefinementApertureDirichletEnergy_supportPacket_le`,
  `exists_uniform_abs_xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy_fixedWidth`,
  `unitPhysicalEndpointCompletedFixedWindowEnergyUniformAbsoluteBound`,
  `unitPhysicalEndpointCompletedFixedWindowEnergyTwoSidedBound`

## No-go closure and positive survivor

Fixed-width scale translation cannot provide RH-strength through bare upper boundedness, lower
boundedness, or even absolute boundedness of this energy. The response kernel only sees bounded
relative prime-log frequency while Mertens keeps endpoint mass finite. Refining valuation tails,
sharpening the polynomial seam bound, or improving the fixed-width Mertens constant cannot repair
this loss of information.

The strongest positive survivor is the compact-frequency Dirichlet law `(3)--(6)`. Any viable
replacement must defeat at least one compactness mechanism. Candidate RH-strength burdens are:

1. let logarithmic width or aperture grow cofinally, forcing unbounded seam frequency;
2. require positivity/coercivity rather than boundedness;
3. impose a vanishing or sharp normalized asymptotic that a generic bounded kernel cannot satisfy;
4. couple packet translation to the pole-crossing prime-source criterion from Loop 81.

## Novelty audit

Primary literature on Weil forms studies positivity, lower-bounded selfadjoint convolution forms,
finite-prime spectral triples, and large-window spectral limits. The newest compact-window result
explicitly treats positivity and lowest spectral values, not this ordinary-prime endpoint-weighted
unit--double response energy. Searches through 2026-08-27 found no exact kernel-distance estimate
`(3)`, no scale-uniform route-specific laws `(5)--(6)`, and no formal no-go showing that both
cofinal bounds hold unconditionally. Candidate-new content is restricted to this exact synthesis.

Primary comparison points:

- A. Connes and C. Consani, [*The Scaling Hamiltonian*](https://arxiv.org/abs/1910.14368):
  semilocal Weil positivity and compactly supported tests.
- A. Connes and W. van Suijlekom,
  [*Quadratic Forms, Real Zeros and Echoes of the Spectral Action*](https://arxiv.org/abs/2511.23257):
  lower-bounded finite-interval convolution forms with an isolated simple ground state.
- A. Connes, C. Consani, and H. Moscovici,
  [*Zeta Spectral Triples*](https://arxiv.org/abs/2511.22755): finite-prime operators and a
  conjectural scaling limit.
- M. Suzuki, [*Weil's quadratic form via the screw function*](https://arxiv.org/abs/2606.09096):
  unconditional finite-interval operators whose growing-window limit remains conjectural.
- M. Chuk,
  [*Weil positivity in compact windows: certified two-sided bounds and a Landau--Widom decay law*](https://arxiv.org/abs/2608.24827):
  unconditional positivity certificates at fixed support and decay questions as support grows.

## Verification log

- 2026-08-27: mandatory corpus searches isolated the line-one/line-two compact-frequency route.
- 2026-08-27: conjectured absolute scale-uniform refinement bound; scratch proof passed.
- 2026-08-27: promoted generic kernel-energy law, exact support-packet estimate, and completed-energy
  absolute bound to Lean.
- 2026-08-27: targeted primary-literature novelty audit completed, including literature posted
  2026-08-25.
- 2026-08-27: direct check, umbrella wiring, targeted build, and standard-axiom audit passed.
- 2026-08-27: global lint reached the wired module but remains blocked by five unrelated,
  concurrently edited unwired Sieve/HTGeometry modules.
