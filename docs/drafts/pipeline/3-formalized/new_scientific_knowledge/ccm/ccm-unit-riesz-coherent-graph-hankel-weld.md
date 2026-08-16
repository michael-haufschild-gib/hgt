# Unit-Riesz coherent graph energy as exact CCM-HG boundary slope

- **ID:** `ccm-unit-riesz-coherent-graph-hankel-weld`
- **Stage:** 3-formalized
- **Type:** SOURCE-FAITHFUL OPERATOR CONNECTOR / SHARP NORM IDENTIFICATION
- **Scientific status:** `[UNCONDITIONALLY PROVED IN LEAN]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [EXTERNAL PRIORITY UNVERIFIED] [NOT AN RH PROOF]`
- **Formal module:**
  `formal/GaloisForLFunctions/RHTower/CCMUnitRieszCoherentGraphHankelWeld.lean`
- **Parent modules:**
  `CCMUnitRieszExponentialCoherentTrace.lean`,
  `CCMUnitRieszCoherentPolarSamplingNoGo.lean`, and
  `CCMBoundaryRelativeTrace.lean`.

## Result

For the compact four-lag coherent third-difference response `g_{a,h}`, let `d_{a,h}` be its
piecewise classical derivative on the three lag cells and define the complex leak profile

```text
ell_{a,h}(u) = 2 d_{a,h}(u) + i g_{a,h}(u).
```

Lean proves measurability, the finite first leakage moment, and the pointwise density identity

```text
|ell_{a,h}(u)|^2 = 4 d_{a,h}(u)^2 + g_{a,h}(u)^2.
```

For `a >= 0`, `h >= 0`, the half-line leakage energy is therefore exactly the coherent generator
energy and source Gram:

```text
integral_(0,infinity) |ell_{a,h}(u)|^2 du
  = G(a,h)
  = 4 Q(a,h).
```

The generic Hankel boundary theorem then becomes a literal source identity:

```text
boundaryRelativeTrace(ell_{a,h},u) / u  -->  4 Q(a,h)    as u -> 0+.
```

Thus the CCM-HG four-unit infinitesimal condition on this coherent packet family is sharp and
equivalent to the source-Gram unit ball:

```text
every boundary-density limit is <= 4  <->  Q(a,h) <= 1.
```

For the fixed sample `a=1-h`, `0<h<=1`, Lean further proves that an explicit positive multiple of
the HG boundary difference quotient converges to `g_{1-h,h}(1)^2`. Fixed coherent evaluation lost
by bare polar `L2` energy is recovered exactly by boundary graph flux.

## Why this advances frontier

Previous theorem showed a hard obstruction: no finite constant controls fixed source evaluation by
bare polar energy, even inside actual finite unit-Riesz coherent source span. It also exposed graph
energy as positive survivor, but did not place that survivor inside a CCM carrier.

This theorem supplies missing carrier. Map `g -> 2g' + i g` retains both derivative and amplitude
channels in one complex Hankel leak profile; it is source-faithful at norm level and gives exact HG
initial slope. Consequently Route O, CCM-GS, and CCM-EP cannot use polar `L2` convergence, while
CCM-HG has a concrete graph-norm receiver rather than an abstract request for “boundary flux.”

## Claim-to-Lean closure

| Claim | Declaration |
|---|---|
| weak generator and complex graph leak | `unitExponentialThirdDifferenceWeakGenerator`, `unitExponentialThirdDifferenceGraphLeakProfile` |
| measurability | `measurable_unitExponentialThirdDifferenceWeakGenerator`, `measurable_unitExponentialThirdDifferenceGraphLeakProfile` |
| modulus equals graph density | `leakDensity_unitExponentialThirdDifferenceGraphLeakProfile` |
| admissible HG leak profile | `leakProfile_unitExponentialThirdDifferenceGraphLeakProfile` |
| total leakage equals generator energy | `integral_leakDensity_unitExponentialThirdDifferenceGraphLeakProfile` |
| initial HG slope equals `4Q` | `tendsto_boundaryRelativeTrace_div_unitExponentialThirdDifferenceGraphLeakProfile` |
| four-unit condition iff `Q<=1` | `unitExponentialThirdDifferenceGraphLeakProfile_density_le_four_iff` |
| fixed sample recovered from boundary slope | `tendsto_unitExponentialThirdDifference_fixedSample_boundaryDensity` |

## Theatre and novelty audit

Identity `|2g'+ig|^2=4|g'|^2+|g|^2` and Green/Sobolev interpretations of exponential kernels are
classical by themselves and are not claimed as new mathematics. Candidate novelty is exact
composition of three corpus-specific objects:

1. literal unit-Riesz coherent increment source packet;
2. its sharp graph/source-Gram identity after bare-polar domination fails;
3. CCM Hankel boundary relative trace, yielding exact four-unit/source-unit-ball equivalence and
   fixed-evaluation recovery.

Targeted corpus search and primary arXiv searches around Connes--Consani Weil positivity,
semi-local trace formulas, exponential-kernel RKHS graph norms, and Hankel boundary traces found no
statement of this exact connector. Search failure does not establish priority; external novelty
remains unverified.

## Open core

This packet theorem does not prove arithmetic four-unit contractivity. Remaining hard theorem is a
linear/cofinal extension from codiagonal coherent packets to literal completed prime-minus-polar
source, preserving signed source provenance and proving its graph-leak boundary slope is at most
four. The already-formal divisor-side theorem would then exclude every finite strict-right divisor
packet. No normalization chosen after seeing packet may substitute for that literal source bound.

## Gates

- [x] paper proof
- [x] unconditional Lean proof
- [x] actual coherent source-span instantiation
- [x] exact HG boundary-slope identity
- [x] four-unit/source-unit-ball equivalence
- [x] fixed-sample recovery
- [ ] independent mathematical audit
- [ ] external priority audit
- [ ] cofinal extension to literal completed source
- [ ] arithmetic source-Gram bound `Q<=1`
- [ ] divisor-preserving source-to-RH endpoint

## References

- A. Connes, C. Consani, M. Marcolli, *The Weil proof and the geometry of the adeles class space*,
  arXiv:math/0703392.
- A. Connes, C. Consani, *The Scaling Hamiltonian*, arXiv:1910.14368.
- A. Connes, C. Consani, *Weil positivity and Trace formula, the archimedean place*,
  arXiv:2006.13771.

## Log

- 2026-08-16 -- Derived complex graph leak `2g'+ig` from coherent-packet obstruction survivor.
- 2026-08-16 -- Proved leak admissibility and exact total-energy/source-Gram identity in Lean.
- 2026-08-16 -- Proved HG initial slope `=4Q`, sharp four-unit equivalence, and fixed-sample
  recovery in Lean.
