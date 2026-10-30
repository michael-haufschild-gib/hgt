# Complete Weil defect reserve at every fixed overlap

- **ID:** complete-weil-defect-reserve-at-every-fixed-overlap
- **Stage:** 3-formalized
- **Type:** THEOREM

## Theorem

For the explicit unit-supported boosted cubic spline `φ`, every `c>0` admits
`b_c>0`, `C_c`, and `N_c` such that, for `N≥N_c`, `w=c/N`, and every real packet,

`W(f_x)/(w∫φ²) ≥ b_c D_N(x)-C_c Σx_n²`.

This is a reserve for the complete signed source, including both poles and
all non-ratio prime powers. It is not a claim of positivity.

## Proof

Write `G=w∫φ²`, `S=Σx_n²`, and choose a fixed integer `L` large enough.
Split at `M=floor(N/L)` into `f_low` and `f_high`. The two supports are ordered
and disjoint once `w≤atomSpacing(M)/2`.

1. The sharp prime counterterm and directed non-ratio estimate, together with
   the formalized infinitesimal pole estimate, give
   `log(N)S+(pole-prime)/G ≥ (1-η)D_N-C_(c,η)S` for every `η>0` eventually.
2. The established unit-coefficient self-energy and cross-penalty estimate give
   `Gamma(f_low)/G ≥ (log N-C)S_low-32e²(wM)D_M`.
3. The boosted-spline high-band target gives
   `Gamma(f_high)/G ≥ (a_c log N-B_c)S_high`, with `a_c>0`.
4. Ordered-support Gamma interaction costs at most
   `2π(1+2ce^c)GS`, by the established boundary estimate and the verified Gram bound.
5. The formalized cutoff estimate gives
   `log(N)S_high ≤ (1+1/u)D_N+C_(L,u)S` for every `u>0`.
   Here `N/M≤2L` eventually. Also `D_M≤D_N` by the exact nonnegative edge split.

Set `δ=min(a_c,1/2)>0`, `η=δ/4`, and `u=4/δ`. Choose an integer
`L≥max(1,4c,128e²c/δ)`. Then `wM≤c/L`, the low defect loss is at most
`δD_N/4`, and `log N−log M≤log(2L)`. The complete defect coefficient is

`1−δ/4−δ/4−(1−δ)(1+δ/4) = δ/4+δ²/4 ≥ δ/4`.

Every remaining cost is a fixed multiple of `S`; thus `b_c=δ/4` works.
For every prescribed level `T`, finite Ramanujan approximation gives a
finite conductor set `S_(c,T)`, independent of `N`, such that every unit
packet orthogonal to their pole profiles has normalized complete Weil
energy `>T`. A packet of energy `≤T` has defect `≤(C_c+T)/b_c`;
approximation within squared error `1/2` contradicts orthogonality, which
forces error `≥1`.

## Status and scope

Directed prime rows, cutoff localization, Gram upper bound, separated self
energy, and ordered-support Gamma interaction are formalized. The actual spline Gamma reserve is also formalized in
`3-formalized/tilted-spline-gamma-reserve-at-bounded-overlap.md`.
The pole estimate and signed arithmetic source are formalized.
`SpacingScaleHarmonicAnalysis/TheGammaFormLocalizesAtAnOrderedCutoff.lean`
proves the actual Gamma polarization, ordered-support lower bound, and
separated defect estimate. Direct audit passed with standard axioms only;
SSHA umbrella wired.
`RenormalizedArithmeticPotentialTheory/TheArithmeticTailPaysForItsLogarithmicMass.lean`
proves exact packet and mass splitting, ordered supports, monotonicity of the
prefix defect, and `log_mul_tail_mass_le_defect`. Direct audit passed with
standard axioms only; RAPT umbrella wired.

The complete assembly is formalized in
`CriticalArithmeticCorrelationTheory/TheCompleteWeilFormKeepsADefectReserveAtEveryOverlap.lean`:

- `exists_tiltedUnitSpline_gamma_defect_payment`;
- `weilQuad_atomicTest_div_eq_arithmetic_add_gamma`;
- `exists_tiltedUnitSpline_complete_defect_reserve`;
- `exists_finite_ramanujan_complement_with_complete_margin`.

Direct no-olean Lean audit passed. The three main inequalities depend only
on `propext`, `Classical.choice`, and `Quot.sound`; CACT umbrella wired.
Actual bounded-overlap spectral identification remains separate. The corpus
already proves positivity and a uniform conductor floor for the candidate
shell-completed scalar energies.

## Novelty boundary

The corpus's `eventually_transMetzlerMainMatrix_young_coercive` concerns the
reference matrix, assumes `c≤2`, and has defect coefficient
`1−poleShift(c)(1+1/λ)−ε`, without positivity at arbitrary overlap.
The theorem here retains the complete source and a strictly positive defect
coefficient for every fixed `c>0`. The new mechanism combines macroscopic localization with a positive
high-frequency Gamma reserve.
