# Route J Julia coherent-energy diagonal floor

- **ID:** `route-j-julia-coherent-energy-diagonal-floor`
- **Stage:** 3-formalized
- **Type:** `[FORMALIZED]` / ROUTE-LEVEL NO-GO WITH POSITIVE SURVIVOR
- **Route:** J in `rh-current-frontier-map.md`
- **RH used:** no
- **Computation used:** no
- **Active claim:** For sixth-power first-clock apertures, literal bad-channel Julia coherent
  energy has an aperture-independent lower bound growing at least logarithmically. Consequently
  no unrenormalized Julia bad-energy budget can give Route A's uniform lower floor.

## Exact frontier

`[CORPUS]` `CCMFirstClockJuliaTwoPacketCapacity.lean` already proves full admitted-prime
enumeration, pointwise zero-aperture recovery of the published source, and the negative-excursion
bound

```text
attenuated completed source < 0
  -> attenuated completed source^2 <= bad coherent energy.
```

`[CORPUS]` `CCMFirstClockJuliaEquilibriumGram.lean` proves the kernel is strictly positive, has
unit diagonal, and packages the bad energy as

```text
E(x,L)=sum_(p,q) B_L(p) R(x(log q-log p)) B_L(q),
B_L(p)>=0, R(0)=1, R(y)>0.
```

`[CORPUS]` `CCMFirstClockPrimePowerTowerCollapse.lean` identifies every one-mode outer prime as a
nonpositive literal tower and hence a positive bad coefficient. `SuzukiMangoldtMacroscopicPrimeBlock.lean`
gives a symbolic Chebyshev lower bound for prime log mass in `(2n,5n]`.

`[LOCAL-RESEARCH]` The generic anchored Gram inequality was already classified as standard
Cauchy--Schwarz/Schur-complement bookkeeping in
`../3-formalized/not_new_scientific_knowledge/ccm-first-clock-julia-equilibrium-coherent-capacity.md`.
It cannot count as frontier progress. The exact unresolved Route-J premise is a uniform or
sufficiently small arithmetic upper budget for the literal full-window energy.

## External frontier

`[LITERATURE]` Jurek--Yor, *Selfdecomposable Laws Associated with Hyperbolic Functions*,
<https://arxiv.org/abs/1009.3542>, supplies parent hyperbolic characteristic-law theory.

`[LITERATURE]` Hiai--Kosaki--Petz--Ruskai, *Families of completely positive maps associated with
monotone metrics*, <https://arxiv.org/abs/1212.1337>, supplies positive-definite and infinitely
divisible hyperbolic-kernel mechanisms.

`[LITERATURE]` Montgomery--Vaughan, *Hilbert's Inequality*,
<https://doi.org/10.1112/jlms/s2-8.1.73>, supplies classical off-diagonal Dirichlet-polynomial
control. Such control does not remove a nonnegative kernel's diagonal.

`[LITERATURE]` Connes--Consani--Moscovici, *Zeta Spectral Triples*,
<https://arxiv.org/abs/2511.22755>, leaves rigorous cofinal convergence to zeta zeros open.
Kim et al., <https://arxiv.org/abs/2607.24830>, is numerical/archimedean and explicitly supplies
no arithmetic RH proof. No located primary source bounds the literal CCM Julia bad energy or
removes its arithmetic diagonal.

Exact residue: parent theory controls positivity and oscillatory off-diagonal terms; neither
local corpus nor external literature audits the unavoidable diagonal mass of Route J's actual
one-mode prime block.

## Pre-freeze competing conjectures and hostile verdicts

1. A source-faithful schedule `x(L)L -> 0` might still decohere the packet.
   `FALSE AS A MECHANISM`: continuity gives `R(x(log q-log p))->1` uniformly on the bandwidth,
   so energy becomes rank one rather than diagonal.
2. A mesoscopic schedule `x(L)L -> infinity` might make energy bounded and then be de-attenuated.
   `CIRCULAR`: it loses uniform identity recovery on the literal prime band; recovering the
   discarded signed tail is the Route-A source problem again.
3. Montgomery--Vaughan off-diagonal cancellation might control bad energy.
   `FALSE FOR THIS CARRIER`: every bad coefficient and every Julia kernel entry is nonnegative;
   the diagonal survives every aperture and off-diagonal terms cannot cancel it.
4. Prime-dependent Julia apertures might preserve source fidelity and suppress coherence.
   `INSIGNIFICANT/INVALID`: it destroys the stationary positive-definite difference kernel that
   proves the negative-excursion inequality.

Given this exact frontier, the strongest falsifiable claim is the arithmetic diagonal obstruction
below.

## Frozen conjecture

`[CONJECTURE]` Put, for a natural number `m`,

```text
L_m = 6 log m,
P_m = { primes p : 2 m^4 < p <= 5 m^4 }.
```

For all sufficiently large `m`, every `p in P_m` is admitted at aperture `L_m`, has exactly one
admitted prime-power mode, and its first-clock phase lies in `(4pi/3,3pi/2]`. Hence

```text
B_(L_m)(p)^2 >= (1/4) (log p)^2 / p.
```

For every real Julia aperture `x`,

```text
E_bad(x,L_m)
 >= sum_(p in P_m) B_(L_m)(p)^2
 >= (log m)/20.                                      (JDF)
```

In particular,

```text
forall C : R, exists m, forall x : R, C < E_bad(x,L_m).
```

The exact constant `1/20` is expendable; aperture-independent divergence is not.

## Why claim could fail

- full admitted-packet enumeration might not transport the block sum without multiplicity loss;
- `p.log floor(exp L_m)` might fail to be one because of a floor/cast seam;
- phase lower bound might not survive the exact first-clock totalization;
- Chebyshev log-mass lower bound might not convert to the weighted square floor with the claimed
  constant.

Any failure must be isolated exactly before changing statement.

## `[PAPER-PROVED]` dependency-closed proof

Assume `25 <= m` and `exp(20) <= m^4`; put `L=6 log m`. Since `m>0`,

```text
exp L=exp(6 log m)=m^6,
floor(exp L)=m^6.                                      (JDF1)
```

Take `p in P_m`. Then `p<=5m^4<=m^6`. Also `p>2m^4`, hence

```text
p^2>4m^8>m^6.
```

The exact natural-log characterization

```text
p.log(m^6)=1 <-> p<=m^6<p^2
```

therefore shows that `p` has exactly one admitted mode. The reduced bad coefficient is thus the
negative of its one-mode tower. The literal tower identity gives

```text
B_L(p)
 =-(log p) p^(-1/2) sin(2pi log p/L).                    (JDF2)
```

The phase is source-forced. From `p>2m^4`, strict monotonicity of `log`, and `m>1`,

```text
4pi/3 < 2pi log p/L.
```

From `p<=5m^4`, `m>=25`, and `log 5 <= (log m)/2`,

```text
2pi log p/L
 <=(pi/3)(4+log 5/log m)
 <=3pi/2.                                                (JDF3)
```

Write the phase as `pi+u`. Then `pi/3<u<=pi/2`; sine monotonicity on
`[-pi/2,pi/2]`, together with `sin(pi/6)=1/2`, gives

```text
-sin(2pi log p/L)=sin u>=1/2.                            (JDF4)
```

The exact critical radius identity `(p^(-1/2))^2=1/p` now yields

```text
B_L(p)^2 >= (1/4)(log p)^2/p.                            (JDF5)
```

Every bad coefficient is nonnegative. The Julia kernel is pointwise strictly positive and has
`R(0)=1`. Hence every term of `E_bad` is nonnegative and its diagonal is exactly `B_L(p)^2`:

```text
E_bad(x,L)>=sum_(p admitted)B_L(p)^2
           >=sum_(p in P_m)B_L(p)^2.                     (JDF6)
```

This step is independent of `x`; no off-diagonal estimate or prime cancellation is used.

For `p in P_m`, `4 log m<=log p` and `p<=5m^4`. Positivity gives

```text
(log p)^2/p >= [4 log m/(5m^4)] log p.                   (JDF7)
```

The corpus's symbolic Chebyshev theorem applied with `n=m^4` states

```text
sum_(p in P_m)log p>=m^4/4.                              (JDF8)
```

Combining `(JDF5)`--`(JDF8)` proves

```text
E_bad(x,L)>=1/4 * 4log(m)/(5m^4) * m^4/4
          =log(m)/20,
```

which is `(JDF)`. Since `log m` is unbounded on the natural numbers, the uniform-in-`x`
unboundedness corollary follows.

There is a second exact boundary law. For fixed `L`, the admitted packet is finite and
`R(x(log q-log p))->R(0)=1` as `x->0`. Termwise passage through the finite double sum gives

```text
E_bad(x,L)->(sum_p B_L(p))^2.                            (JDF9)
```

Thus zero-aperture source recovery restores maximal rank-one coherence; it cannot erase the
diagonal obstruction.

## Hostile proof and priority attack

- **False?** Exact floor, natural-log, phase, radius, enumeration, and Chebyshev seams are all
  discharged above. No asymptotic prime theorem or RH premise occurs.
- **Circular?** No source lower floor, Xi divisor, zero location, or RH-equivalent proposition is
  assumed. Only unconditional finite prime sums and Chebyshev bounds enter.
- **Rediscovered?** The abstract diagonal inequality is routine nonnegative-matrix algebra and is
  `[BRIDGE]`, not novelty. Targeted primary-source and corpus searches found no statement applying
  it to the literal CCM one-mode block with the aperture-uniform logarithmic floor `(JDF)`.
  Priority remains unverified.
- **Insignificant?** The theorem falsifies Route J's first unresolved premise: a uniform upper
  budget for the exact unrenormalized bad energy. It does not prove or disprove RH.

Verdict: `SURVIVES PRELIMINARY ATTACK` as a route-closing no-go and positive classification;
`[NOVELTY UNVERIFIED]` scientifically.

## Relentless interrogation and representation change

**Based on what killed this idea, what stronger conjecture is not killed by the research?**

The immediate replacement, subtracting the diagonal after forming positive bad energy, is false.
For a one-node packet with unit mass at the origin, normalized-kernel energy and diagonal are both
one, while squared anchor correlation is one. Therefore

```text
anchor correlation^2 <= energy-diagonal
```

would read `1<=0`. No post hoc diagonal renormalization preserves the capacity inequality.

The subsequent principal-relative audit tested that structural replacement directly. Positive
channel-linear and globally positive kernels lose every coupling incident to a cancelled
diagonal; anchored Schur residuals lose the source correlation; the diagonal-null positive-Julia
Krein current has quartically divergent off-diagonal energy; and the existing sign-changing
Julia--Euler exterior seam scalarizes to zero. The unrestricted capacity existential is exactly
Route A's eventual lower-floor property, while the explicit singular completed Julia/Ward source
transport is Route R's open core.

Strongest positive survivor is the exact two-boundary classification `(JDF)` and `(JDF9)`:

```text
every aperture retains an arithmetically unbounded diagonal;
zero aperture additionally restores full rank-one coherence.
```

Insight delta: Julia coherence cannot simultaneously serve as a positive capacity certificate and
as a removable regularizer for the literal first clock. Positive good/bad projection occurs too
early; any successor must be relative before that projection.

## Route verdict

The original unrenormalized Route-J energy-budget handoff is `FALSE`: its bad energy cannot have a
uniform upper budget at any aperture. Formalized positive survivor is a sharp classification:

```text
zero aperture     -> rank-one total bad mass;
positive aperture -> still carries an unbounded arithmetic diagonal;
source fidelity   -> restores rank-one coherence.
```

No independent Julia descendant remains. A representation-free capacity assertion is Route A;
the exact nontrivial completed preprojection source object is Route R. Route J is retired after
that ownership transfer without claiming the remaining Ward sign.

## Lean realization

Generic kernel infrastructure is in
`formal/GaloisForLFunctions/HTGeometry/NonnegativeKernelDiagonalCapacity.lean`:

- `realKernelPacketDiagonal_le_energy_of_nonneg` proves diagonal persistence;
- `realKernelPacketEnergy_scale_tendsto_mass_sq` proves the rank-one zero-scale law;
- `normalizedKernel_anchor_sq_not_le_energy_sub_diagonal` kills post hoc subtraction.

Exact arithmetic specialization is in
`formal/GaloisForLFunctions/RHTower/CCMFirstClockJuliaCoherentEnergyDiagonalFloor.lean`:

- `ccmFirstClockJuliaSixthPower_cutoff` proves `(JDF1)`;
- `ccmFirstClockJuliaSixthPower_block_primePowerLength_eq_one` proves the one-mode seam;
- `ccmFirstClockJuliaSixthPower_block_phase` and
  `ccmFirstClockJuliaSixthPower_block_badTerm_sq_lower` prove `(JDF2)`--`(JDF5)`;
- `ccmFirstClockJuliaSixthPower_block_diagonal_lower` proves the Chebyshev block floor;
- `ccmFirstClockJuliaFullBadCoherentEnergy_sixthPower_lower` proves `(JDF)`;
- `ccmFirstClockJuliaFullBadCoherentEnergy_unbounded_uniformly_in_scale` proves its uniform
  unboundedness corollary;
- `tendsto_ccmFirstClockJuliaFullBadCoherentEnergy_zero` proves `(JDF9)`.

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for all load-bearing
declarations. No computation, `sorry`, `admit`, added axiom, `opaque`, or `unsafe` declaration is
used.

## Gates

- [x] internal route and failed-mechanism audit
- [x] current primary-literature audit
- [x] exact conjecture frozen before Lean work
- [x] hostile falsity/rediscovery audit of `(JDF)`
- [x] dependency-closed paper proof
- [x] strongest positive survivor and representation lesson
- [x] exact unconditional Lean theorem
- [x] umbrella and axiom audits
- [x] final lint and module-build audit
