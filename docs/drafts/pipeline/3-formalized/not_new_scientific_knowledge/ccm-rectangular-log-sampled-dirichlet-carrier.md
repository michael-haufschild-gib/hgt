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

3. For every `eps>0` and `Re s>=3/2+eps`,

   ```text
   |zeta(s-w)| <= 1+1/eps
   ```

   uniformly over the right-half Xi divisor.
4. Consequently,

   ```text
   sum_w c_L(w) zeta(s-w)
   ```

   converges absolutely on that safe right half-plane.

## Exact formal surface

- `XiRightZeroCopy`
- `xiRightCenteredZero`
- `xiRectangularRightCoefficient`
- `xiRectangularRightCoefficient_ne_zero`
- `norm_xiRectangularRightCoefficient_le`
- `xiRectangularRightCoefficient_summable`
- `xiRectangularShiftedZetaSeries`
- `norm_riemannZeta_sub_xiRightCenteredZero_le`
- `xiRectangularShiftedZetaSeries_summable`
- `xiRectangularTwoEdgeDominant_logSample_of_right`

## Boundary

The safe-half-plane series is not yet the Landau continuation theorem.  The
remaining analytic statement must prove local normal continuation to the real
abscissa `1+delta_*`, identify every shifted pole with nonzero residue, and
then apply the already formal nonnegative-Dirichlet-series Landau theorem.

## Verification

- exact module build: passed
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration is introduced
