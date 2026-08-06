# Mass–Xi square-root prime-mask boundary residue

## Status

- Lane: `3-formalized`
- Conjecture: `C36`
- Parent: C35 critical `ℓ¹` prime-mask quotient
- Target: `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3 exact open core

## Conjecture and route correction

The first conjecture attacked the cofinal horizontal mask

```text
T(a,τ) = ∑' p, xiMassPrimeSqrtMask(p) * xiMassCenteredPrimeAtom(a,τ,p),
xiMassPrimeSqrtMask(p) = L_{p²}(1/2) / L_p(1/2) = p^(-1/2).
```

Its critical coefficient is `log(p)/p`, so it lies beyond the C35 critical-`ℓ¹` residual
mechanism.  The initial plan was to reassemble a new natural-line Dirichlet series and repeat the
adaptive Cauchy-residue argument.

That plan was superseded by a stronger exact covariance.  For every `a>0`,

```text
g_{a,τ}(x) = g_{a/2,2τ}(x/2),
stripFourier(g_{a,τ})(w) = 2 * stripFourier(g_{a/2,2τ})(2w).
```

Consequently the apparently new horizontal prime mask is exactly the prime-square boundary layer
seen through mass/time dilation:

```text
T(a,τ) = 2 * xiMassPrimeSquareLayer(a/2, 2τ).
```

No second pole extraction is needed.  C32 therefore gives a uniform vertical bound for `T` on
every positive mass/time line.

## Enlarged horizontal quotient

Let `w : Nat.Primes → ℂ`, `c b : ℂ`, and assume

```text
Summable (fun p =>
  ‖(w(p) - b * xiMassPrimeSqrtMask(p)) - c‖
    * xiMassPrimePowerCriticalWeight(p,0)).
```

Lean proves absolute summability of the square-root masked atoms, then proves the actual `tsum`
identity

```text
masked(w) = c * S₁ + b * T + residual(w,c,b).
```

Both `T` and the residual are uniformly bounded on every positive vertical time line.  Hence:

- `c = 0` implies the masked source is unconditionally uniformly bounded;
- `c ≠ 0` implies its fixed-line bound is equivalent to the valuation-one bound;
- therefore `RiemannHypothesis ↔ XiMassPrimeMaskedLineBound w a σ` for every nonzero scalar class.

This strictly enlarges C35: the bounded horizontal ideal contains the dilation image of the
prime-square residue in addition to all critical-`ℓ¹` perturbations.

## Higher principle

The obstruction was misidentified as a special Dirichlet boundary problem.  It is a shadow of a
mass/Fourier dilation action: rescaling the analytic test transports prime-log frequency `log p`
to the prime-power frequency `2 log p`.  The next conjecture is the integer dilation semigroup
`p^{-(r-1)/2}`, whose `r`-th member should transport valuation one to valuation `r`.  If true, all
nonprimitive dilation directions lie in the bounded ideal and only the scalar primitive class
survives.

## Lean implementation

- `XiMassPrimeSqrtDilation.lean`
  - `xiMassAnalyticTest_real_half_dilation`
  - `stripFourier_xiMassAnalyticTest_half_dilation`
  - `xiMassPrimeSqrtMaskLayer_eq_two_mul_primeSquareLayer`
- `XiMassPrimeSqrtBoundaryResidue.lean`
  - `exists_norm_xiMassPrimeSqrtMaskLayer_vertical_bound`
- `XiMassPrimeMaskBoundaryQuotient.lean`
  - `summable_norm_xiMassPrimeSquareCenteredAtom`
  - `summable_xiMassPrimeSqrtMaskedAtom`
  - `xiMassPrimeMaskedLayer_eq_scalar_add_boundary_add_residual`
  - `xiMassPrimeBoundaryMaskedLineBound_of_scalar_eq_zero`
  - `xiMassPrimeBoundaryMaskedLineBound_iff_valuationOne`
  - `riemannHypothesis_iff_xiMassPrimeBoundaryMaskedLineBound`

All proofs are unconditional.  Direct `lake env lean` verification passes.  Targeted module build
and capstone axiom audit are recorded in the log below.

## Novelty audit

Corpus search found C32's valuation-two residue and C35's critical-`ℓ¹` prime masks, but no theorem
identifying a cofinal horizontal prime mask with a rescaled valuation layer.  C36 supplies both the
exact dilation identity and the resulting two-dimensional horizontal quotient classification.

## Log

- 2026-08-05 — opened after C35 isolated the critical `ℓ¹` horizontal ideal.
- 2026-08-05 — original duplicate boundary-residue route superseded by exact half-dilation
  covariance; numerical pre-certification matched pointwise and Fourier identities.
- 2026-08-05 — exact masked `tsum`, summability, uniform bound, quotient equivalence, and RH
  capstone direct-pass in Lean; modules wired into `GaloisForLFunctions.RHTower`.
- 2026-08-06 — targeted build passed `9480/9480`; capstone axiom audit contains only `propext`,
  `Classical.choice`, and `Quot.sound`; forbidden-token scan clean.
