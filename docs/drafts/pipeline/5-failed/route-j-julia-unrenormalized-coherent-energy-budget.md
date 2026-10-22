# Route J unrenormalized Julia coherent-energy budget

- **ID:** `route-j-julia-unrenormalized-coherent-energy-budget`
- **Stage:** 5-failed
- **Type:** RETIRED ROUTE J / UNIFORM DIAGONAL-CAPACITY NO-GO
- **Scientific status:** `[PAPER-PROVED] [FORMALIZED] [NOVELTY UNVERIFIED] [NO COMPUTATION]`
- **Formalized positive survivor:**
  `../3-formalized/route-j-julia-coherent-energy-diagonal-floor.md`
- **Positive survivor:** a principal-relative current defined before good/bad projection would be
  a new route; the existing singular joint-depth/Ward realization is Route R
- **Endpoint attempted:** Route A's eventual first-clock lower floor

## Intended chain

The Julia compound-Poisson construction proves a normalized pointwise-positive equilibrium
kernel, full admitted-prime enumeration, zero-scale recovery of the literal first-clock source,
and the capacity implication

```text
negative attenuated completed source
  -> squared negative excursion <= literal bad coherent energy.
```

Route J proposed completing this chain with a uniform or sufficiently small upper budget for the
full unrenormalized bad energy, followed by removal of attenuation and handoff to Route A.

## Exact falsification

Put

```text
L_m = 6 log m,
P_m = {p prime : 2m^4 < p <= 5m^4}.
```

For `25 <= m` and `exp 20 <= m^4`, every `p in P_m` is admitted at `L_m`, has exactly one
prime-power mode, and has first-clock phase in `(4pi/3,3pi/2]`. Therefore its reduced bad
coefficient satisfies

```text
B_(L_m)(p)^2 >= (log p)^2/(4p).
```

The Julia kernel is strictly positive with unit diagonal, so no aperture or off-diagonal estimate
can cancel these squares. The unconditional Chebyshev block estimate then gives, for every real
Julia scale `x`,

```text
E_bad(x,L_m)
  >= sum_(p in P_m) B_(L_m)(p)^2
  >= log m/20.
```

Consequently

```text
forall C : R, exists m : N, forall x : R, C < E_bad(x,L_m).
```

The proposed unrenormalized global budget is false uniformly in Julia scale.

## Lean status

Formalized in:

- `formal/GaloisForLFunctions/HTGeometry/NonnegativeKernelDiagonalCapacity.lean`;
- `formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockJuliaCoherentEnergyDiagonalFloor.lean`.

Load-bearing declarations:

- `realKernelPacketDiagonal_le_energy_of_nonneg`;
- `normalizedKernel_anchor_sq_not_le_energy_sub_diagonal`;
- `ccmFirstClockJuliaSixthPower_block_primePowerLength_eq_one`;
- `ccmFirstClockJuliaSixthPower_block_badTerm_sq_lower`;
- `ccmFirstClockJuliaFullBadCoherentEnergy_sixthPower_lower`;
- `ccmFirstClockJuliaFullBadCoherentEnergy_unbounded_uniformly_in_scale`;
- `tendsto_ccmFirstClockJuliaFullBadCoherentEnergy_zero`.

All are unconditional and use only standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`). No numerical computation enters statement or proof.

## Dead mechanisms

1. **Source-faithful zero-scale schedule.** It restores the kernel to one across every fixed
   packet, producing rank-one energy `(sum_p B_p)^2`, not cancellation.
2. **Mesoscopic decoherence.** It loses identity recovery on the literal prime band; restoring the
   discarded signed tail is the original Route-A source problem.
3. **Montgomery--Vaughan off-diagonal cancellation.** Every bad coefficient and Julia kernel entry
   is nonnegative; the diagonal cannot cancel.
4. **Prime-dependent apertures.** They destroy the stationary difference kernel used by the
   capacity inequality.
5. **Post hoc diagonal subtraction.** The normalized one-node unit packet makes the desired anchor
   inequality read `1 <= 0`.

## Strongest positive survivor

`JULIA TWO-BOUNDARY CLASSIFICATION`:

```text
every aperture -> arithmetically unbounded diagonal persists;
zero aperture  -> full rank-one coherence is restored.
```

Julia coherence cannot be both the positive capacity certificate and a removable regularizer for
the literal first clock. The subsequent principal-relative audit closes the advertised Julia
implementations and proves the representation-free residual capacity exactly RH-equivalent. It
does not class-completely exclude every source-defined symmetric sign-changing completed/nonlinear
current, but such a pre-projection object changes the primitive and is not Route J. Route J is
retired; the existing singular Ward construction is Route R, and any different survivor requires
new route ownership.

## No-go closure audit

- [x] exact negative theorem proved
- [x] strongest positive boundary law extracted
- [x] positive survivor dependency-closed on paper
- [x] survivor and no-subtraction law formalized in Lean
- [x] prior failed mechanisms audited
- [x] no RH-equivalent premise used
- [x] no computation used
- [x] pre-projection positive survivor separated from retired Route J and assigned new-route status
