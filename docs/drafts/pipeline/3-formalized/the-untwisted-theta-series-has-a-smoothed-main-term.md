# The untwisted theta series has a Gaussian-smoothed main term

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** O2; contribution 3 of the review-1511 connection programme.
- **Statement:** For `W(y)=exp(−(log y)²/4)/(2√π)` and every `5/8<a<2/3`,
  `Σ_{A squarefree, (A,3)=1} thetaSquareWeight(A) W(N(A)/X)
  = exp(4/9) untwistedThetaResidue · X^(2/3) + O_a(X^a)` for `X≥1`.
  The main coefficient is nonzero.

## Connection

Compact-height Eisenstein forcing, self-adjoint resolvent estimates and cutoff-independent
spectral residues supply a full-strip continuation with controlled growth. The finite-order
Hecke zero-free seed controls cube removal. Gaussian Mellin inversion and the rectangle
residue theorem convert the isolated spectral pole into an actual signed arithmetic asymptotic.

## Paper proof [PROVED HERE]

1. The compact defect is `exp(s log v)(F₂(v)+(2s−1)F₁(v))`, hence has at most linear height growth
   on bounded real strips. The self-adjoint inverse bound divides by
   `|Im(s(2−s))|=2|Re s−1||Im s|`. Thus the correction, its two fixed theta pairings and the seed
   pairings are bounded. Explicit scattering terms have cubic growth, giving
   `|Λ₀(s)|≤C(1+|s|)^3` on closed strips inside `1<Re s<13/3` at large height.
2. The real resolvent residue is `(μ+1)Π_μ`. Equality of corrected seeds in compact cusp regions,
   followed by compact exhaustion, makes the forcing projection independent of the incoming
   cutoff. Transfer from cutoff `[5,6]` removes every real pole except `4/3` at cutoff `[2,3]`.
   Meromorphic normal form fills these removable values and preserves the cubic-pole germ.
3. The cube-removal argument is `z=3s/2−1`. The `7/8` Hecke seed excludes zeros for `Re s>5/4`;
   the regularized reciprocal bound is quadratic in height. The Bessel Mellin Gamma quotient
   is nonzero and has reciprocal at most `C exp(4π|Im w|)` at `s=2w`. Consequently the filled
   squarefree function `L(w)` is holomorphic on `5/8<Re w<13/6` except `2/3`, with residue
   `R=untwistedThetaResidue≠0`, and grows at most
   `C(1+|w|)^6 exp(4π|Im w|)` on closed strips.
4. The arithmetic coefficients have norm at most one. Ideal-zeta convergence proves holomorphy
   on `Re w>1`. The identity theorem extends initial agreement from the upper half-strip to
   all `1<Re w<13/6`. Multiplication by `exp(w²)` gives a uniform bound `C/(1+(Im w)²)`.
5. The quadratic Gaussian integral gives
   `(2π)⁻¹ ∫ x^(−c−it) exp((c+it)²) dt = W(x)`.
   Absolute ideal-zeta convergence permits termwise integration for `c>1`, identifying the
   arithmetic sum with `(2π)⁻¹ ∫ X^(c+it) exp((c+it)²)L(c+it) dt`.
6. Shift from `c=2` to `a`. Gaussian decay removes the horizontal sides. The unique enclosed
   residue is `X^(2/3) exp(4/9)R`. The remaining line is bounded by
   `X^a (2π)⁻¹ ∫ |exp((a+it)²)L(a+it)| dt`, with finite integral independent of `X`.

## Lean

All declarations below are in `SpectralTheoryOfTheCubicCover`, except the first two inputs.

| Input or conclusion | Declaration |
|---|---|
| Resolvent vertical control (MMD) | `kernelEisensteinL2Correction_vertical_bound` |
| Bounded unramified zeta reciprocal (MMD) | `unramifiedIdealZeta_inv_bounded` |
| Pairings and scattering | `thetaSeedPairings_bounded`, `thetaCorrectionPairings_bounded`, `clearedThetaScattering_vertical_bound` |
| Completed square and cube removal | `completedThetaSquares_vertical_bound`, `clearedCubeZeta_inv_vertical_bound` |
| Real spectral poles and filled correction | `correction_spectral_residue_cutoff_independent`, `kernelEisensteinCorrection_removable`, `regularizedEisensteinCorrection_analyticAt` |
| Mellin growth and initial holomorphy | `besselSqMellin_inv_vertical_bound`, `twistedSquarefreeSeries_one_differentiableAt` |
| Full strip and arithmetic agreement | `regularizedUntwistedTheta_differentiableAt`, `regularizedUntwistedTheta_eq_series`, `regularizedUntwistedTheta_simple_pole` |
| Gaussian decay and arithmetic inversion | `continuedUntwistedTheta_gaussian_vertical_bound`, `gaussianSmoothedUntwistedTheta_eq_integral` |
| Nonzero arithmetic main term | `thetaGaussianMainCoefficient_ne_zero`, `gaussianSmoothedUntwistedTheta_main_term` |

Final module: `TheUntwistedThetaSeriesHasASmoothedMainTerm.lean`.
All fourteen modules passed final plain `lake --old env lean` checks and are umbrella-wired.
No axiom checks. Independent OrderSix modules provide the real spectral decomposition and
forcing-projection vanishing for cutoff `[5,6]`; those results are not counted here.

## Scope

This proves the actual untwisted signed squarefree sum, beyond existence of its pole.
The row-root conductor phase, compactly supported or sharp-cutoff asymptotics, and
column-uniform remainders remain open. Auxiliary analytic bounds carry no separate count.
