# Mass–Xi integer-dilation prime-mask ideal

## Status

- Lane: `1-in-progress`
- Conjecture: `C37`
- Parent: C36 square-root prime-mask boundary residue
- Target: `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3 exact open core

## Hard conjecture

For every natural valuation `r≥2`, define

```text
xiMassPrimeDilationMask(r,p) = L_{p^r}(1/2) / L_p(1/2)
                              = p^(-(r-1)/2),
D_r(a,τ) = ∑' p, xiMassPrimeDilationMask(r,p)
                  * xiMassCenteredPrimeAtom(a,τ,p).
```

### C37-A — dilation semigroup

Prove for every real `λ>0`

```text
g_{a,τ}(x) = g_{a/λ, λτ}(x/λ),
stripFourier(g_{a,τ})(w) = λ * stripFourier(g_{a/λ,λτ})(λw).
```

Then specialize `λ=r` and prove the actual prime-series identity

```text
D_r(a,τ) = r * ∑' p xiMassCenteredPrimeAtom(a/r,rτ,p^r).
```

### C37-B — uniform boundedness of every nonprimitive orbit

- `r=2`: reuse C32/C36 prime-square boundary residue.
- `r≥3`: prove the fixed valuation layer is a summable slice of C31's joint high-prime-power
  ideal and inherits a vertical-time-independent bound.

Conclude `D_r(a,σ+iu)=O(1)` for every `a,σ>0` and `r≥2`.

### C37-C — horizontal quotient by dilation orbit

Extract the higher universal principle: any finite linear combination of `D_r`, `r≥2`, plus a
critical-`ℓ¹` residual is bounded.  Adding a nonzero scalar primitive class is RH-equivalent;
killing the scalar class is unconditionally bounded.

## Fail criteria

- If general Fourier scaling cannot be expressed without extra integrability assumptions, record
  exact missing theorem and retain strongest natural-number specialization.
- If a fixed `r≥3` layer cannot be extracted from C31, prove a direct critical-weight majorant.
- Do not postulate boundedness or reuse any valuation-one/RH-equivalent estimate.

## Novelty audit

Corpus contains the vertical valuation quotient and the single horizontal half-dilation `r=2`,
but no horizontal dilation-semigroup theorem.  C37 would identify an infinite-dimensional family
of cofinal prime masks that are invisible in the open-core quotient, and explain them uniformly as
pullbacks of nonprimitive Euler valuations.

## Log

- 2026-08-05 — opened from C36's exact half-dilation identity.
- 2026-08-05 — mpmath pre-certification at `r=3,4` gave pointwise error at most
  `2.9e-42` and Fourier error numerically zero at 40 digits.
