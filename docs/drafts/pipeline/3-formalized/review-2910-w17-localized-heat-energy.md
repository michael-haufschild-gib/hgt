# Localized heat-zero energy evolution

- **ID:** review-2910-w17-localized-heat-energy
- **Stage:** 3-formalized
- **Type:** THEOREM / integration
- **Source:** W17 of the obstacles summary; [heat-flux formulation](wd-heat-localized-energy-flux.md).

## Statement

Let w≥0 vanish outside (−1,1), with derivative v, bounds w≤W, |v|≤V,
and Lipschitz constant M for v. For actual heat zeros, counted with multiplicity, set

`E_w(X,t)=Σ_z mult(H_t,z) w(Re z−X)(Im z)²`,
`N_w(X,t)=Σ_{Im z≠0} mult(H_t,z) w(Re z−X)`.

Let η be the continuous tent cutoff equal to one on [−2,2] and zero outside
[−3,3]. There are constants C>0 and X₀≥4096, independent of w and time, such
that for X≥X₀, 0≤a≤b≤1/8 and b log X≤1, N_w is interval integrable and

`E_w(X,b)−E_w(X,a)+2∫_a^b N_w(X,s) ds`
`≤ (2M+2V+4W) C log X ∫_a^b E_η(X,s) ds`.

At every 0≤t<1/8 with t log X<1, the upper right slope is at most

`−2N_w(X,t)+(2M+2V+4W) C log X E_η(X,t)`.

The slope statement means that every strictly larger real number eventually
bounds all positive difference quotients. Both conclusions include collisions
and heat time zero. No separation, root-path or simplicity input is assumed.

## Paper proof

The actual radius-two zero packet S has total multiplicity at most C log X.
Its real-symmetric exterior logarithmic derivative Q satisfies
`|Q|≤C log X` and `|Im Q(z)|≤C log X |Im z|` on the inner window.
At a simple time each zero has velocity
`z'=2Σ_{b∈S,b≠z}(z−b)⁻¹+2Q(z)`.

Choose disjoint isolating balls around the finite packet. Local zero-count
conservation supplies unique actual branches at simple zeros. Compact-open
continuity excludes extra zeros on the compact complement. Thus the actual
weighted zero sum equals a finite branch sum for short positive increments;
its derivative follows from the product and chain rules.

Symmetrize the pair forces before estimating. A pair's horizontal cutoff error
is at most `2M(y²+y'²)`; its remaining interaction is nonpositive. Each nonreal
conjugate pair contributes exactly `−4w(x)`. Summation gives the full term
`−2N_w`, with error at most `2M card(S) Σ_S y²`. The exterior field contributes
at most `(2V+4W) C log X Σ_S y²`. Since η=1 on S, their sum is bounded by the
claimed outer energy. These estimates contain no inverse zero gap.

For collision passage use `u_n(y)=min(1,((n+1)y)²)`. The actual observable
`Σ mult w u_n` is continuous through collisions. Compact forward simplicity
provides a short punctured interval of simple configurations after every
positive time. A continuous function satisfying the derivative comparison on
these intervals satisfies its integrated comparison everywhere: subtract the
integral majorant and propagate the local right-monotonicity using continuity.
The initial endpoint follows by continuity, including time zero. This argument
does not require finitely many collision times.

At each fixed time the finite packet makes u_n eventually equal to the full
nonreal indicator. The truncated sums are uniformly bounded by W C log X
throughout [a,b]. Dominated convergence therefore proves integrability and the
integrated full-count inequality. For the upper right slope, fix one truncation
already exact at the initial packet. Its continuous integral majorant gives the
claimed slope with the full initial count, including at a multiple zero.

## Lean declarations

In `RHTower/Heat/HeatLocalizedEnergyDissipation.lean`:

- `RHTower.DeBruijn.exists_uniform_heatLocalizedVerticalEnergy_evolution`
- `RHTower.DeBruijn.exists_uniform_heatLocalizedVerticalEnergy_right_slope`

Supporting leaves: `LocalizedHeatPacketFlux`, `HeatZeroSumContinuity`,
`HeatLocalizedEnergyEvolution`, `HeatLocalizedZeroObservables`, and
`HTGeometry/ForwardRegularIntervalComparison`. The last also proves bounded
limit integration and the right-slope consequence of a continuous majorant.

## Audit

All six changed leaves passed final `lake --old env lean` checks. Fifteen
terminal transitive-axiom checks returned only `propext`, `Classical.choice`,
and `Quot.sound`. No placeholders or raised limits occur in these leaves.
Supporting oleans were built only for direct imports; the capstone needed none.
The RHTower and HTGeometry umbrella imports and heat README are wired;
umbrellas were not compiled.

## Boundary

The estimate controls localized evolution. It supplies neither a uniform bound
on the total nonreal count as t decreases to zero nor the arithmetic absorption
needed for extinction. Those remain the WD obstruction.
