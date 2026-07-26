# LAW476 — Xi squared-radial odd Euler `sinh`-response universality

## Status

- Pipeline stage: 3 — formalized
- Conjecture label: `LAW476`
- Discovery mode: theorem-generated reverse-Bessel/odd-source closure
- Mathematical computations used: none
- Novelty status: `[NOVELTY UNVERIFIED]`

## Corpus parents

1. `SquaredXiRadialJetIdentity` proves that squared-radial Xi jets carry the reverse-Bessel
   magnitudes `squaredRadialJetWeight n j`.
2. `ReverseBesselFixedFrequencyBlindness.reverseBesselRatio_tendsto` proves coefficientwise
   convergence of normalized magnitudes to `1/j!`.
3. `ReverseBesselFixedFrequencyBlindness.reverseBessel_fixed_frequency_blind` proves that the
   complete normalized polynomial tends to `exp`, cancelling a fixed Euler damping.
4. `XiSquaredRadialOddResolvedSourceUniversalityLaw.
   squaredXiOddRadialJetPolynomial_eq_neg_resolvedSource` identifies the odd squared-radial sector
   with the negative exact prime–Gamma–polar resolved source sector.

The corpus contains no parity-projected reverse-Bessel limit and no fixed-frequency law for the
odd resolved-source channel.

## Universal law

Let

`Bₙ(x) = Σⱼ b(n,j)xʲ`

be the reverse-Bessel radial polynomial and define its odd projection

`Bₙ⁻(x) = (Bₙ(x) - Bₙ(-x))/2`.

Then for every real `x`,

`Bₙ⁻(x) / b(n,0) → sinh(x)`.

Consequently, at every fixed Euler frequency `m ≥ 2` and radial parameter `w > 0`,

`m^(-1/2-w) Bₙ⁻(w log m) / b(n,0)
  → m^(-1/2-w) sinh(w log m)`.

Unlike the complete channel, whose limit loses Euler damping entirely, the odd
prime–Gamma–polar source retains the antisymmetric two-sided Euler contrast. At every finite
depth it is exactly the source sector appearing with the common negative sign in the squared-Xi
odd radial identity.

## Dependency-closed paper proof

For fixed `j`, normalized reverse-Bessel coefficients converge to `1/j!`. For every real `x`,
their absolute values are dominated by `|x|^j/j!`, whose series is summable. Dominated convergence
therefore extends the existing nonnegative-`x` polynomial limit to all real `x`:

`Bₙ(x)/b(n,0) → exp(x)`.

Apply this at `x` and `-x`, subtract, and divide by two. Continuity of subtraction and scalar
division gives

`Bₙ⁻(x)/b(n,0) → (exp(x)-exp(-x))/2 = sinh(x)`.

Multiplication by the fixed Euler damping `m^(-1/2-w)` gives the stated frequency response at
`x = w log m`.

The odd resolved-source theorem uses exactly the odd indices and the same reverse-Bessel
magnitudes. Its parity sign is `(-1)^(2k+1)=-1`, so the finite odd Xi sector is the negative
resolved source sector while the normalized coefficient response converges to the `sinh` law.

No interchange beyond dominated convergence, numerical evaluation, or asymptotic uniformity in
`m` or `w` is claimed.

## Strength boundary

Convergence is pointwise at fixed `x`, hence fixed `m,w`; it is not uniform over growing Euler
frequencies. The theorem identifies the coefficient response of the odd source sector but does
not assert convergence of the full infinite prime-power sum, which would require a separate
uniform domination theorem.

## Lean target

File:
`formal/GaloisForLFunctions/RHTower/XiSquaredRadialOddEulerSinhResponseUniversalityLaw.lean`

Planned declarations:

- `reverseBesselOddPoly`
- `reverseBesselPoly_div_tendsto_exp_all`
- `reverseBesselOddPoly_div_tendsto_sinh`
- `reverseBesselOdd_fixedEulerFrequency_response`
- `xi_squaredRadialOdd_eulerSinhResponseUniversality`

## Verification log

- Paper proof: dependency-closed
- Lean exact check: passed with
  `lake env lean GaloisForLFunctions/RHTower/XiSquaredRadialOddEulerSinhResponseUniversalityLaw.lean`
- Axiom audit: pending final audit
- Final targeted module build: pending final audit
- Umbrella wiring: complete in `GaloisForLFunctions/RHTower.lean`

## Novelty audit

Primary-source searches were run only after paper proof and direct Lean elaboration. Nearby
literature treats large-degree reverse generalized Bessel asymptotics and logarithmic derivatives
of zeta:

- https://arxiv.org/abs/2506.20934
- https://arxiv.org/abs/2605.27552
- https://arxiv.org/abs/2404.17250
- https://arxiv.org/abs/2311.16371

No located source states the exact law that the odd parity projection of the squared-radial
reverse-Bessel Xi coefficients converges to `sinh`, giving a retained Euler-frequency response
for the exact prime–Gamma–polar odd source sector. Search coverage cannot prove absence from all
literature, so status remains `[NOVELTY UNVERIFIED]`.
