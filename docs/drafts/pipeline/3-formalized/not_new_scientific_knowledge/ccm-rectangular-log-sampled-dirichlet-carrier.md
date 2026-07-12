# Log-sampled rectangular shifted-zeta carrier

- **ID:** `ccm-rectangular-log-sampled-dirichlet-carrier`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE]` / unconditional CCM Dirichlet foundation
- **Novelty status:** not promoted separately as new scientific knowledge
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMRectangularDirichletLandau.lean`

## Theorem

Let `XiRightZeroCopy` be the multiplicity copies of Xi zeros with
`Re(rho-1/2)>0`, put `w=rho-1/2`, and define

```text
c_L(w)=A_L(w)^2.
```

Unconditionally:

1. `sum |c_L(w)|<infinity`; if `L>0`, every `c_L(w)` is nonzero.
2. At the logarithmic aperture `a_n=(log n)/2`, the selected growing edge is

   ```text
   c_L(w)n^w.
   ```

3. The actual Xi divisor satisfies the multiplicity-exact reciprocal law

   ```text
   sum_w 1/(|w| sqrt(|w|)) < infinity.
   ```

   This is extracted from the unconditional `O(R log R)` Xi zero-count.
4. On `Re z>=3/4`, uniformly away from the zeta pole,

   ```text
   |zeta(z)| <= C_d sqrt(|z|+2).
   ```

5. Consequently,

   ```text
   sum_w c_L(w) zeta(s-w)
   ```

   converges locally normally and is holomorphic on an explicit positive-radius
   ball centred at the actual real boundary `1+delta_*`.
6. Schwarz conjugation makes the logarithmic samples real.  Their ordinary
   Dirichlet coefficients are `O(n^delta_*)`, and on `Re s>1+delta_*` their
   L-series is exactly twice the shifted-zeta carrier.
7. If those real coefficients are eventually bounded below, adding a constant
   and deleting a finite prefix gives a nonnegative Dirichlet series.  A
   scale-local Landau theorem, with arbitrary Taylor displacement `h>0`, forces
   this series to converge at a real point strictly left of `1+delta_*`.

The earlier safe-half-plane estimate remains available: for every `eps>0` and
`Re s>=3/2+eps`,

   ```text
   |zeta(s-w)| <= 1+1/eps
   ```

   uniformly over the right-half Xi divisor.

## Exact formal surface

- `XiRightZeroCopy`
- `xiRightCenteredZero`
- `xiRectangularRightCoefficient`
- `xiRectangularRightCoefficient_ne_zero`
- `norm_xiRectangularRightCoefficient_le`
- `xiRectangularRightCoefficient_summable`
- `xiRightTransverseSup`
- `xiRightTransverseSup_pos`
- `xiRightTransverseSup_le_half`
- `nonempty_xiRightZeroCopy_of_not_riemannHypothesis`
- `xiSpectralPoint_inv_three_halves_summable`
- `norm_riemannZeta_le_sqrt_norm_add_two`
- `xiRectangularShiftedZetaSeries`
- `norm_riemannZeta_sub_xiRightCenteredZero_le`
- `xiRectangularShiftedZetaSeries_summable`
- `summableLocallyUniformlyOn_xiRectangularShiftedZeta_ball`
- `analyticOnNhd_xiRectangularShiftedZetaSeries_landauBall`
- `exists_analyticOnNhd_xiRectangularShiftedZetaSeries_actualLandauBall`
- `xiRectangularRightDirichletCoefficientReal`
- `norm_xiRectangularRightDirichletComplex_le`
- `LSeries_xiRectangularRightDirichletComplex_eq_shiftedZeta`
- `landau_local_summability_transfer`
- `LSeries_xiRectangularLandauCoefficient_eq_continuation`
- `exists_xiRectangularLandauCoefficient_summable_left_of_boundary`
- `xiRectangularTwoEdgeDominant_logSample_of_right`

## Boundary

The real-boundary continuation and the scale-local Landau transfer are complete.
The remaining theorem is the multiplicity-safe pole-jet contradiction: the
left-boundary convergence must be shown incompatible with at least one genuine
shifted pole `s=1+w`.  No simple-zero hypothesis is available.

## Verification

- exact module build: passed
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration is introduced
