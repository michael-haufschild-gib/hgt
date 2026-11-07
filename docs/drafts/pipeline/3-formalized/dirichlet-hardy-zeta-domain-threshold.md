# The square-summable domain of shifted zeta convolution

- **ID:** dirichlet-hardy-zeta-domain-threshold
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Programme:** ArithmeticInnerFunctionTheory
- **Statement:** On square-summable sequences indexed by positive integers, convolution by `n ↦ n^(-ε)` has domain `{0}` exactly when `ε ≤ 1/2`. For `ε > 1/2`, its domain contains every finitely supported sequence and is dense.

## Proof

Write `b(n)=Σ_{d|n} a(d)(n/d)^(-ε)` and suppose `a,b∈ℓ²`. Fix `m≥1`. For every prime `p∤m`, splitting the divisors of `pm` gives

```text
b(pm) = p^(-ε)b(m) + Σ_{d|m}(m/d)^(-ε)a(pd).
```

Each sequence `p ↦ a(pd)` and `p ↦ b(pm)` is square-summable: multiplication by a fixed positive integer is injective. Finite linear combinations preserve square summability. Thus `p ↦ p^(-ε)b(m)` is square-summable outside the finitely many prime divisors of `m`.

If `ε≤1/2`, then `p^(-2ε)≥1/p`; divergence of the prime reciprocal sum forces `b(m)=0`. This holds for every `m`. Induction over `m`, isolating the divisor `d=m`, now gives `a(m)=0`.

If `ε>1/2`, the sequence `n^(-ε)` is square-summable by the ordinary power-series criterion. The convolution of a point mass at `d` is its dilation, supported on multiples of `d`; dilation preserves its square norm. Every finitely supported sequence therefore lies in the domain. Such sequences are dense in `ℓ²`.

## Consequence for the proposed recurrence route

Coefficient phases `a(n) ↦ n^(-it)a(n)` act unitarily on this discrete Hardy space. At shifts where bounded point evaluations could see nontrivial zeta zeros, zeta multiplication has no nonzero domain. Above the domain threshold, point evaluation requires `Re s>1/2`, so the zeta argument satisfies `Re(s+ε)>1`.

The positive survivor is the exact domain threshold and density on its other side. This does not decide AAL or exclude the actual finite exceptional zero layer. Corpus searches found square-summable Dirichlet weights and finite convolution estimates, but no theorem identifying this maximal domain.

## Lean

Module: `ArithmeticInnerFunctionTheory/TheDirichletHardyDomainOfZeta.lean`.

- `shiftedZetaConvolution_prime_mul`: exact divisor splitting.
- `eq_zero_of_shiftedZetaConvolution_mem_two`: trivial arithmetic domain for `ε≤1/2`.
- `shiftedZetaConvolution_mem_two_of_finite_support`: finite sequences belong above `1/2`.
- `closure_shiftedZetaDomain`: complete domain-closure classification, with unused index `0` fixed to zero.
- `shiftedZetaDomain_nontrivial_iff`: nontrivial domain exactly when `ε>1/2`.

Direct `lake --old env lean` check passed without warnings. All eight public theorem dependency closures contain exactly `propext`, `Classical.choice`, and `Quot.sound`.
