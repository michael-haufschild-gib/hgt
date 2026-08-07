# Cofinal convex recurrence of the Suzuki--Xi zero-trace hierarchy — Lean certificate

- **ID:** `suzuki-zero-trace-cofinal-convex-recurrence-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-zero-trace-cofinal-convex-recurrence.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/CofinalConvexRecurrence.lean`
- `formal/GaloisForLFunctions/HTGeometry/WaveTraceConvexRecurrence.lean`
- `formal/GaloisForLFunctions/HTGeometry/WaveTraceLaplace.lean`
- `formal/GaloisForLFunctions/HTGeometry/WaveTracePoleDivergence.lean`
- `formal/GaloisForLFunctions/HTGeometry/WaveTracePoleTransform.lean`
- `formal/GaloisForLFunctions/HTGeometry/WaveTraceSpectrum.lean`
- `formal/GaloisForLFunctions/RHTower/CCMRectangularTwoEdge.lean`
- `formal/GaloisForLFunctions/RHTower/CentralReciprocalMoments.lean`
- `formal/GaloisForLFunctions/RHTower/LandauIntegralTransfer.lean`
- `formal/GaloisForLFunctions/RHTower/RiemannTower.lean`
- `formal/GaloisForLFunctions/RHTower/WaveTraceLandauRecurrence.lean`
- `formal/GaloisForLFunctions/RHTower/XiCentralHankelDeterminantCriterion.lean`
- `formal/GaloisForLFunctions/RHTower/XiWaveTraceCofinalQuadrature.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.HTGeometry.CofinalConvexRecurrence`:

```text
GaloisForLFunctions.HTGeometry.exists_cofinal_positive_quadrature
GaloisForLFunctions.HTGeometry.zero_mem_interior_convexHull_image_Ioi
```

`GaloisForLFunctions.HTGeometry.WaveTraceConvexRecurrence`:

```text
GaloisForLFunctions.HTGeometry.WaveSpectrum.CofinalWaveSignEscape
GaloisForLFunctions.HTGeometry.WaveSpectrum.apply_tracePath
GaloisForLFunctions.HTGeometry.WaveSpectrum.cofinalHalfSpaceEscape_tracePath
GaloisForLFunctions.HTGeometry.WaveSpectrum.exists_cofinal_positive_quadrature_waveTrace
GaloisForLFunctions.HTGeometry.WaveSpectrum.tracePath
GaloisForLFunctions.HTGeometry.coeff_observablePolynomial
GaloisForLFunctions.HTGeometry.observablePolynomial
GaloisForLFunctions.HTGeometry.observablePolynomial_ne_zero
```

`GaloisForLFunctions.HTGeometry.WaveTraceLaplace`:

```text
GaloisForLFunctions.HTGeometry.WaveSpectrum.hasSum_integral_dampedTerm
GaloisForLFunctions.HTGeometry.WaveSpectrum.integral_dampedTerm
GaloisForLFunctions.HTGeometry.WaveSpectrum.integral_norm_dampedTerm_le
GaloisForLFunctions.HTGeometry.WaveSpectrum.summable_integral_norm_dampedTerm
GaloisForLFunctions.HTGeometry.integrableOn_sin_mul_exp_Ioi
GaloisForLFunctions.HTGeometry.integral_sin_mul_exp_Ioi
GaloisForLFunctions.HTGeometry.sin_mul_exp_eq
GaloisForLFunctions.HTGeometry.sq_add_sq_ne_zero
```

`GaloisForLFunctions.HTGeometry.WaveTracePoleDivergence`:

```text
GaloisForLFunctions.HTGeometry.WaveSpectrum.IsLocallyFiniteSpectrum
GaloisForLFunctions.HTGeometry.WaveSpectrum.countable_poleSet
GaloisForLFunctions.HTGeometry.WaveSpectrum.differentiableOn_poleTransform_compl
GaloisForLFunctions.HTGeometry.WaveSpectrum.exists_ball_denominator_bound
GaloisForLFunctions.HTGeometry.WaveSpectrum.exists_denominator_lower_bound
GaloisForLFunctions.HTGeometry.WaveSpectrum.exists_norm_poleTransform_gt
GaloisForLFunctions.HTGeometry.WaveSpectrum.exists_re_lower_bound
GaloisForLFunctions.HTGeometry.WaveSpectrum.exists_square_separation
GaloisForLFunctions.HTGeometry.WaveSpectrum.isOpen_compl_poleSet
GaloisForLFunctions.HTGeometry.WaveSpectrum.isPreconnected_compl_poleSet
GaloisForLFunctions.HTGeometry.WaveSpectrum.poleNumer_at_pole
GaloisForLFunctions.HTGeometry.WaveSpectrum.poleSet
GaloisForLFunctions.HTGeometry.WaveSpectrum.poleTransform_eq_head_add_tail
GaloisForLFunctions.HTGeometry.WaveSpectrum.squareFiber
GaloisForLFunctions.HTGeometry.WaveSpectrum.squareFiber_finite
GaloisForLFunctions.HTGeometry.WaveSpectrum.traceCoeff_mul_poleNumer_eq_of_mem_squareFiber
```

`GaloisForLFunctions.HTGeometry.WaveTracePoleTransform`:

```text
GaloisForLFunctions.HTGeometry.WaveSpectrum.differentiableOn_poleTransform
GaloisForLFunctions.HTGeometry.WaveSpectrum.norm_poleNumer_le
GaloisForLFunctions.HTGeometry.WaveSpectrum.norm_poleTerm_le
GaloisForLFunctions.HTGeometry.WaveSpectrum.norm_traceCoeff_le
GaloisForLFunctions.HTGeometry.WaveSpectrum.poleTransform_eq_integral
GaloisForLFunctions.HTGeometry.norm_ccos_le_exp_abs_im
```

`GaloisForLFunctions.HTGeometry.WaveTraceSpectrum`:

```text
GaloisForLFunctions.HTGeometry.WaveSpectrum.conj_waveTrace
GaloisForLFunctions.HTGeometry.WaveSpectrum.norm_traceTerm_le
GaloisForLFunctions.HTGeometry.WaveSpectrum.norm_waveTrace_le
GaloisForLFunctions.HTGeometry.WaveSpectrum.ofReal_realWaveTrace
GaloisForLFunctions.HTGeometry.WaveSpectrum.realWaveTrace
GaloisForLFunctions.HTGeometry.WaveSpectrum.realWaveTrace_sum
GaloisForLFunctions.HTGeometry.WaveSpectrum.summable_traceTerm
GaloisForLFunctions.HTGeometry.WaveSpectrum.waveTrace_add
GaloisForLFunctions.HTGeometry.WaveSpectrum.waveTrace_im
GaloisForLFunctions.HTGeometry.WaveSpectrum.waveTrace_smul
```

`GaloisForLFunctions.RHTower.CCMRectangularTwoEdge`:

```text
RHTower.exists_xiDivisorSupport_abs_im_lower_bound
```

`GaloisForLFunctions.RHTower.CentralReciprocalMoments`:

```text
RHTower.xi_divisor_pos_on_support
RHTower.xi_divisor_support_im_ne_zero
RHTower.xi_divisor_support_re_mem_open_unit
RHTower.xi_zero_multiplicity_centered_inv_sq_summable
```

`GaloisForLFunctions.RHTower.LandauIntegralTransfer`:

```text
RHTower.landau_complexMGF_integrable_transfer
```

`GaloisForLFunctions.RHTower.RiemannTower`:

```text
RHTower.xi_one_sub
```

`GaloisForLFunctions.RHTower.WaveTraceLandauRecurrence`:

```text
RHTower.TailConv
RHTower.abs_im_ge_of_mem_poleSet
RHTower.cofinalWaveSignEscape
RHTower.complexMGF_traceMeasure
RHTower.exists_active_of_ne_zero
RHTower.exists_cofinal_positive_quadrature_of_no_imaginary
RHTower.exists_pos_realWaveTrace
RHTower.integrable_exp_traceMeasure_iff
RHTower.tailConv_all
RHTower.tailConv_base
RHTower.tailConv_iterate
RHTower.tailConv_mono
RHTower.tailConv_step
RHTower.traceDensity
RHTower.traceMeasure
```

`GaloisForLFunctions.RHTower.XiCentralHankelDeterminantCriterion`:

```text
RHTower.xiCentralReciprocalSquare_range_infinite
```

`GaloisForLFunctions.RHTower.XiWaveTraceCofinalQuadrature`:

```text
RHTower.exists_cofinal_positive_quadrature_xiWaveTrace
RHTower.exists_neg_and_pos_xiWaveTrace
RHTower.xiWaveSpectrum
RHTower.xiWaveSpectrum_locallyFinite
RHTower.xiWaveSpectrum_re_ne_zero
RHTower.xiWaveSpectrum_squares_infinite
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 79 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- 3 -> 4 publication-ready: standalone theoretical paper, primary-source novelty audit, and

These are research frontier items, not formalization debt.
