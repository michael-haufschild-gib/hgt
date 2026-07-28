# Complete noncommutative clock-compass tomography

- **ID:** `clock-compass-noncommutative-tomography`
- **Stage:** 3-formalized
- **Type:** NEW ABSTRACT RECONSTRUCTION THEOREM / NONCOMMUTATIVE PRODUCT ALGEBRA /
  PRINCIPAL-SYMBOL EXACTNESS / HYPERTRANSCENDENTAL PHASE / QUANTUM CLOCK COMPASS
- **Parent:** `../1-in-progress/quantum-clock-compass-chronodromy-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/ClockCompassNoncommutativeTomography.lean`
- **Status:** unconditional Lean proof; physical clock/curvature identification remains in parent

## Exact theorem

Let `R` be a commutative scalar semiring, `A` an arbitrary associative `R`-algebra, and
`curvature : Curv -> A` a finite family. Define finite clock reporters

```text
K_i = sum_a C_ia • curvature_a.
```

Assume a scalar left inverse

```text
sum_i D_ai C_ib = delta_ab.
```

Then:

1. every generator reconstructs exactly:

   ```text
   curvature_a = sum_i D_ai • K_i;
   ```

2. evaluation of the free associative algebra on the curvature generators and evaluation of the
   free associative algebra on the clock reporters have identical ranges in `A`;
3. therefore every ordered curvature word is exactly a clock polynomial, with order retained and
   no commutativity assumption;
4. arbitrary state/readout functionals agreeing on all clock polynomials agree on all curvature
   polynomials;
5. in a ring, every curvature commutator reconstructs as

   ```text
   [curvature_a, curvature_b]
     = sum_i sum_j D_ai D_bj [K_i,K_j].
   ```

6. the reporter family and reported family have identical joint kernels;
7. over a differential-field extension, every reporter is differentially algebraic exactly when
   every reconstructed curvature component is differentially algebraic. Equivalently:

   ```text
   some clock channel is HT  iff  some curvature channel is HT;
   ```

8. for every covector `xi` with a splitter `n`, `xi(n)=1`, the exact kernel of the doubled
   linearized-Riemann principal symbol on symmetric metric symbols is

   ```text
   R_xi(h) = 0  iff  h = xi tensor v + v tensor xi
   ```

   for some covector `v`. Thus linearized curvature removes precisely infinitesimal metric gauge
   and no other principal-symbol polarization.

The range equality is stronger than a degree-by-degree moment identity. It states equality of the
generated associative product algebras.

## Scientific role

The theorem closes the algebraic core of the proposed chronometric observable net. Once a physical
clock protocol derives the scalar reporter relation and left inverse for gauge-invariant smeared
curvature operators, no further assumption is required to pass from classical curvature
tomography to:

- every ordered quantum-curvature correlator;
- the complete noncommutative product law;
- state separation on the generated curvature algebra;
- causal commutator reconstruction.
- invariant HT/DA classification across complete clock/curvature calibration;
- retention of every non-gauge graviton polarization at principal-symbol level.

This matters after the hybrid-classical audit. Entanglement or a Lie commutator alone need not
separate all claimed classical hybrid theories. Complete product-algebra tomography is the
stronger invariant, and this theorem proves that a complete clock compass retains it.

## Exact boundary

Lean does not assert that:

- `curvature` denotes physical spacetime curvature;
- clock frequency ratios satisfy the reporter equation after nonlinear relational dressing;
- the reporter matrix of a physical apparatus has a left inverse;
- the resulting algebra is quantum rather than a hybrid process algebra;
- any HT gravitational reporter exists.

Those are paper-level physical obligations in the parent card. The theorem says that if the
physical relation is derived, noncommutative tomography is exact and loses no ordered product
information.

## Formal surface

The module exports:

- `clockReporter`;
- `curvature_reconstruction`;
- `clockReporter_jointKernel`;
- `curvatureWordEval` and `clockWordEval`;
- `curvatureToClockCode` and `clockToCurvatureCode`;
- `clockWordEval_comp_curvatureToClockCode`;
- `curvatureWordEval_comp_clockToCurvatureCode`;
- `curvatureWordEval_range_eq_clockWordEval_range`;
- `states_agree_on_curvature_words_of_agree_on_clock_words`;
- `mulCommutator`;
- `curvature_commutator_reconstruction`;
- `differentialAlgebraicOver_finset_sum_clock`;
- `differentialAlgebraicOver_clockReporter`;
- `clockReporter_differentialAlgebraic_phase_iff`;
- `exists_hypertranscendental_clockReporter_iff`;
- `doubledLinearizedRiemannSymbol`;
- `doubledLinearizedRiemannSymbol_pureGauge`;
- `pureGaugeMetricSymbol_ext`;
- `doubledLinearizedRiemannSymbol_vanishes_iff_pureGauge`.

## Verification

- Direct foreground check:
  `lake env lean GaloisForLFunctions/HTGeometry/ClockCompassNoncommutativeTomography.lean`
  passed on 2026-07-28.
- Duplicate-scratch `#print axioms` audit returned only `propext`, `Classical.choice`, and
  `Quot.sound` for the first theorem batch. New differential-phase and principal-symbol
  declarations await the final batch axiom audit.
- Final lint and module-build audit remain deferred to the end of the research batch.

## Log

- 2026-07-28 — proved generator reconstruction, equality of generated free-algebra ranges,
  arbitrary-state transfer, and commutator reconstruction without commutativity.
- 2026-07-28 — proved joint-kernel equality, exact HT/DA phase invariance under complete reporter
  calibration, and exactness of the linearized-Riemann principal symbol modulo pure gauge.
