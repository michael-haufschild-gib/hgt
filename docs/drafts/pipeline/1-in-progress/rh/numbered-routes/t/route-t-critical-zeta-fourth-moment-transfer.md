# Route T: critical zeta fourth-moment transfer

## Status

- Pipeline stage: in progress
- Route: T, but no commitment to one AFE representation
- Open core: none for the fourth moment itself (closed in Lean, see completion conditions); what remains for Route T is downstream of the density theorem
- Exact target: an unconditional Lean theorem of shape
  `inghamCriticalZetaFourthMoment U V ≤ C · V · (1 + log V)^4` on the required positive-height range

## Corpus and hostile audit

`FourthMoment.lean` and `FourthMomentDiagonal.lean` do not prove a quantitative fourth moment for the
actual zeta function.  Their strongest mean-value statement retains an explicit positive
off-diagonal sum.  `ZetaAFETransfer.lean` is pointwise and the Euler--Maclaurin truncation is too long
on the critical line to preserve the `T log^4 T` scale.

The corpus now contains an exact two-series Gaussian smooth AFE in
`SmoothAFEZetaDualReflection.lean`, together with direct and dual cutoff bounds.  However, its exact
dual weight depends on height.  Replacing that weight by a fixed coefficient sequence without a
quantitative transfer proof would hide the main theorem.

## Heavy conjecturing loop

### F1: the explicit off-diagonal sum is the fourth-moment bottleneck

Status: **FALSIFIED**.

The general affine mean-square theorem prices a finitely supported Dirichlet series by its
`n`-weighted and plain coefficient masses.  For the critical divisor coefficients
`d(n)n^{-1/2}`, these are controlled without an off-diagonal analysis.

Positive survivor, **FORMALIZED** in `Sieve/CriticalDivisorAffineMeanSquare.lean`:

1. `∑_{n≤N} d_r(n)/n ≤ H_N^r` for every positive integer `r`;
2. `∑_{n≤N} d(n)^2/n ≤ (1+log N)^4`;
3. the actual finite critical divisor polynomial satisfies

   `∫_{-T}^{T}|D_N(t)|²dt
      ≤ 5πe N(1+log N)^3 + (5π/2)T(1+log N)^4`.

At conductor length `N ≍ T`, this is already `O(T log^4 T)`.  The old off-diagonal obstruction was
a shadow of using the wrong mean-square normal form.

### F2: pointwise absolute bounds on the exact two-series AFE suffice

Status: **FALSIFIED**.

Absolute summation of either conductor-length Dirichlet series costs `T^{1/4}` pointwise and yields
the wrong fourth-moment power.  Oscillation must remain inside a mean-value theorem.  Any route that
takes absolute values before the height integral is retired.

### F3: current exact Gaussian AFE can be transferred by fixed-coefficient truncation

Status: **OPEN; TWO VIABLE BRANCHES**.

Branch A: construct a completed, reflection-symmetric smooth AFE for `ζ(s)^2`.  On the critical line
the reflected carrier should be a phase times the conjugate of the direct divisor carrier, reducing
both fourth-moment pieces to F1.  Required new work: squared completed functional equation,
double-pole residue bookkeeping, conductor localization, and finite-tail control.

Branch B: retain the current exact zeta AFE.  Express the height-dependent dual weight by its Mellin
integral, keep the shifted Dirichlet polynomial inside the integral, and apply Minkowski plus F1.
Required new work: an `L^2_t(L^1_v)` transfer theorem, truncation of the direct and dual series, and
explicit residue bounds.

Neither branch is declared preferred until its first quantitative closure test.  A branch is kept
only if it preserves the `T log^4 T` scale without an assumed moment or pointwise absolute loss.

### F4: Gabriel exponent has enough room for Route T's `7/10`

Status: **FORMALIZED** in `Sieve/InghamGabrielExponent.lean`.

For right edge `β=1+ε`, the exact critical-edge height exponent is

`3(1+ε-σ)/(2+3ε-σ)
 = 3(1-σ)/(2-σ) + 3ε(2σ-1)/((2+3ε-σ)(2-σ))`.

At `σ=7/10`, the limiting exponent is `9/13`, the margin to `7/10` is `1/130`, and the perturbed
exponent stays below `7/10` exactly when `0≤ε<1/90`.  Hence the `δ/log X` right-edge displacement is
compatible with the fixed short-interval target for all sufficiently large `X`.

## Novelty labels

- External theorem novelty: none claimed; fourth moment and coefficient-three zero density are
  classical.
- Corpus theorem novelty: harmonic generalized-divisor bound and off-diagonal-free critical carrier
  reduction.
- Route-level new knowledge: fourth-moment obstruction has moved from arithmetic off-diagonal
  cancellation to a precise AFE representation/transfer problem; `7/10` has an exact finite
  perturbation budget `ε<1/90`.

## Completion conditions

1. [x] Critical divisor coefficient masses bounded at exact logarithmic powers.
2. [x] Conductor-length divisor carrier mean square formalized.
3. [x] Actual zeta square reduced to three exact Gaussian-AFE summands on a natural conductor:
   `smoothAFEZetaSquare_exact_afe_summands` (`SmoothAFEZetaSquareFourthMomentRouteTBudget.lean`).
4. [x] Actual critical zeta fourth moment at `T log^4 T` scale on dyadic blocks:
   `exists_integral_Icc_norm_riemannZeta_line_pow_four_le_polylog`,
   `exists_inghamCriticalZetaFourthMoment_dyadic_le_polylog`, initial/symmetric forms
   `exists_inghamCriticalZetaFourthMoment_initial_nat_le_polylog`,
   `exists_inghamCriticalZetaFourthMoment_symmetric_nat_le_polylog`.
5. [x] Mollifier second moment and `4/3` error moment at polylog scale:
   `exists_inghamCriticalMollifierSecondMoment_symmetric_nat_le_polylog`,
   `exists_inghamCriticalErrorFourThirdMoment_symmetric_nat_le_polylog`; uniform density with these
   inputs: `exists_eventually_zetaZeroMass_le_uniformGabrielPolylog` (`InghamUniformDetectorDensityPolylog.lean`).
6. [x] Built and wired in the corpus (checked 2026-09-08 by search; this card had not been updated).
