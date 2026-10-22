# Xi mass-graded trace zero-free distortion universality law

Status: **Stage 3 — formalized in Lean**

## Discovery

Whole-corpus theorem-posting closure joined:

- `XiSpectralFamilyGradedOnLine`: exponential type `lam` of any admissible spectral trace on one
  vertical line is equivalent to a uniform displacement bound `|Im pt| ≤ lam`;
- `AbstractSpectralMass`: mass shift contracts every displacement; and
- `XiMassFaithfulTransfer`: for the Xi divisor, the original displacement is recovered from the
  mass-shifted displacement with explicit uniform squared loss `(9 + a²) / 9`.

No theorem in these modules transfers a nonzero mass-trace exponential type back to an explicit
zero-free chamber for the original Xi divisor.

## Universal law

For every mass `a ≥ 1/2` and exponent `lam ≥ 0`, let `G_a(lam)` mean that the mass-shifted Xi trace
has a vertical-line bound

`‖trace_a(σ + ix)‖ ≤ C exp(lam |x|)`.

Then:

1. if every Xi zero has transverse displacement at most `lam`, then `G_a(lam)`; and
2. if `G_a(lam)`, then every Xi zero satisfies

   `9 · Im(xiSpectralPoint q)² ≤ (9 + a²) · lam²`.

Thus the mass-shifted trace's exponential type is squeezed between original Xi transverse width
and that width with the explicit deformation condition number `sqrt((9+a²)/9)`.  At `lam = 0`,
this collapses to the mass-shifted RH line-bound criterion, but the law controls every nonzero
zero-free chamber.

## Dependency-closed paper proof

1. `abs_csqrtIm_massArg_le` says mass shifting contracts pointwise displacement.
2. `xiMassFamily_pt_eq_mass_pt` identifies the concrete mass carrier with the abstract deformation.
3. `xiPoissonPoint` differs from `xiSpectralPoint` only by a sign selected by half-plane
   orientation, so their imaginary parts have equal absolute value.
4. Hence an original width bound `|Im xiSpectralPoint| ≤ lam` gives the same bound for every point
   of `xiMassFamily`.
5. Apply `SpectralFamily.abs_im_le_iff_exists_line_growth` for the forward trace-growth statement.
6. Conversely, `SpectralFamily.abs_im_le_of_line_growth_all` gives
   `|Im xiMassFamily.pt| ≤ lam`.
7. Squaring and using `lam ≥ 0` gives `Im(xiMassFamily.pt)² ≤ lam²`.
8. Apply `nine_mul_sq_im_xiSpectralPoint_le` and monotonicity of multiplication by `9+a²`.

No RH assumption, computation, or new analytic convergence premise enters.

## Formal targets

- `xiMassTraceLineGrowth`
- `abs_im_xiMassFamily_le_abs_im_xiSpectralPoint`
- `xiMassTraceLineGrowth_of_xiZeroStrip`
- `nine_mul_sq_im_xiSpectralPoint_le_of_xiMassTraceLineGrowth`
- `xiMass_gradedTrace_zeroFreeDistortionUniversality`

## Novelty audit

Post-proof searches covered `Riemann xi + mass-shifted trace + exponential type`, `spectral mass
deformation + displacement + zero-free region`, and `Riemann zeros + vertical trace growth
exponent`.  Results concerned ordinary zero-free regions, bounded-type strip rigidity, Xi Fourier
approximants, or unrelated spectral models.  None stated the mass-deformation exponential-type
sandwich or the explicit `(9+a²)/9` squared distortion.  Representative adjacent sources:

- [The Riemann Xi-function from primitive Markovian cycles II: Strip rigidity and divisor identification](https://arxiv.org/abs/2602.06080)
- [Nonnegative trigonometric polynomials and a zero-free region for the Riemann zeta-function](https://arxiv.org/abs/1410.3926)
- [On the zeros of Riemann Xi function](https://arxiv.org/abs/1706.08868)
- [The Riemann Zeros as Spectrum and the Riemann Hypothesis](https://www.mdpi.com/2073-8994/11/4/494)

No exact collision found in this scoped audit. **[NOVELTY UNVERIFIED]**

## Lean formalization

Formal source:
`formal/GaloisForLFunctions/RHTower/XiMassGradedTraceZeroFreeDistortionUniversalityLaw.lean`.

Verified with:

`lake env lean GaloisForLFunctions/RHTower/XiMassGradedTraceZeroFreeDistortionUniversalityLaw.lean`

Umbrella:
`formal/GaloisForLFunctions/RHTower.lean`.
