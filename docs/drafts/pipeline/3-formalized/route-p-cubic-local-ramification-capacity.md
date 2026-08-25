# Route P cubic local ramification-capacity obstruction

## Status

- Pipeline stage: formalized in Lean 4
- Conjecture label: `CUBIC-LOCAL-RAMIFICATION-CAPACITY`
- Scope: coefficient-generated irregular microlocal Riemann--Hilbert/Stokes landings of the first odd prime/Gamma wall--Xi cubic residual
- Frontier-map status: read-only; no ledger edit made

## Exact theorem

Let `d` be global Puiseux--orbit coarea data, let all multi-Rees parameters be nonnegative, and let `x` be a cubic Xi Malgrange landing.  Write

- `c` for the unique global physical-rank coefficient,
- `r` for the common physical rank,
- `x_a(i)` for the orbit charge at marked point `a`,
- `e_a(i)` for its positive ramification multiplicity,
- `M_a = ∑_i e_a(i)^2` for local squared ramification capacity.

Then, for every marked point `a`,

`1 < (-c) M_a`.

For a genus-zero one-puncture model this becomes the sharp normalized Puiseux-slope obstruction

`1 + 1 / M_0 < (K(0)+1)/N(0)`.

This strengthens the already-formalized bare slope bound `(K(0)+1)/N(0) > 1` by a positive, data-dependent gap.

## Dependency-closed proof

Let `P` be the global Rees-positive form and `T_a = ∑_i x_a(i)^2` local terminal orbit energy.

1. Cubic landing negativity and the one-rank Witt decomposition give
   `P < (-c) r^2`.
2. Nonnegative Rees parameters and nonzero landing charge give `0 < P`; the same landing forces `c < 0`.
3. Compatibility and orbit descent identify
   `r = ∑_i x_a(i)e_a(i)` at every marked point.
4. Finite Cauchy--Schwarz gives
   `r^2 ≤ T_a M_a`.
5. Local Rees energy is `T_a` plus nonnegative block energy.  Every other local Rees term is nonnegative, hence `T_a ≤ P`.
6. Since `-c > 0` and `M_a ≥ 0`,
   `P < (-c)r^2 ≤ (-c)T_aM_a ≤ (-c)PM_a`.
   Divide by `P > 0` to obtain `1 < (-c)M_a`.
7. On a one-puncture sphere, the coefficient identity is
   `-c = (K(0)+1)/N(0) - 1`.
   The capacity inequality forces `M_0 > 0`; division yields
   `1 + 1/M_0 < (K(0)+1)/N(0)`.

No existence premise is asserted.  Landing membership and nonnegative-Rees conditions define the theorem's variable domain; no conjectural axiom or analytic hypothesis is introduced.

## Hostile audit

- `M_a = 0` cannot be an exceptional case: the proved strict product inequality forces `M_a > 0`.
- Zero local charge cannot evade the argument: compatibility would make common rank zero, contradicting cubic landing rigidity.
- Additional marked points cannot absorb the bound: their energies are nonnegative, so every chosen local terminal energy is individually bounded by `P`.
- Threshold contraction cannot evade the bound: terminal energy survives at Rees parameter zero.
- Raw-Euler source incidence is not used; the result applies to every cubic Malgrange landing.
- Result does not prove landing existence or RH.  It removes all local data whose squared ramification capacity is at most the reciprocal global Lorentz debt.

## Novelty audit

Corpus searches found physical-rank descent, terminal energy, global Rees positivity, and cubic Witt-signature rigidity, but no theorem combining them into a pointwise ramification-capacity obstruction or the strengthened one-puncture slope gap.

Literature audit covered generalized irregular Riemann--Hilbert existence, irregular holonomic `D`-module correspondence, wild harmonic bundles/twistor `D`-modules, and Hurwitz-space irregular Riemann--Hilbert constructions.  These sources supply parent theory, not this completed-Xi cubic landing inequality.  Absence is an audit inference, not a universal priority claim.

Primary sources checked:

- Bolibruch--Malek--Mitschi, *On the generalized Riemann-Hilbert problem with irregular singularities*, arXiv:math/0410483.
- Mochizuki, *Wild Harmonic Bundles and Wild Pure Twistor D-modules*, arXiv:0803.1344.
- Kashiwara, *Riemann-Hilbert correspondence for irregular holonomic D-modules*, arXiv:1512.07723.
- Shramchenko, *Riemann-Hilbert problem associated to Frobenius manifold structures on Hurwitz spaces: irregular singularity*, arXiv:0707.0696.

## Lean formalization

Implemented in `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicLocalRamificationCapacity.lean`:

1. local terminal energy is bounded by global Rees-positive energy;
2. ramification-weighted physical-rank Cauchy--Schwarz;
3. pointwise local ramification-capacity inequality;
4. genus-zero one-puncture inverse-capacity slope bound.

Only two application results are public; terminal-energy and finite Cauchy--Schwarz bookkeeping remain private.

Targeted module check passed.  Both public declarations have trust base exactly
`[propext, Classical.choice, Quot.sound]`; no project axiom, `sorry`, `admit`, `opaque`, or
`unsafe` declaration was introduced.
