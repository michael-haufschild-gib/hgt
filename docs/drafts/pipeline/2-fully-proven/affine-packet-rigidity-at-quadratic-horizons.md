# Affine packet rigidity at quadratic horizons

- **ID:** critical-rigidity-affine-windows
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Statement:** Actual affine Ramanujan packet differences retain their complete-period energy on every window with relative loss `Q(Q−1)/K`. Joint successor approximation and dyadic dilation control nonconstant packet mass at this horizon.

## Exact transfer

Let `F_a(n)=Σ_(1≤m≤Q) a_m c_m(n)`, `Q≥2`, and
`f(n)=F_a(kn+h)−F_b(ln+j)`. Every primitive root of order at most `Q` remains a root of order at most `Q` after raising to an integer power. Aggregate coefficients whenever these powers coincide. Thus `f` is an exponential sum on the same Farey spectrum, including its constant frequency. Finite Parseval identifies its squared coefficient mass with `E(f)=mean_(n<Q!) f(n)²`.

The corpus's sharp two-sided roots-of-unity large sieve gives, for every phase `A` and length `K`,

`|Σ_(A<n≤A+K) f(n)² − K E(f)| ≤ Q(Q−1) E(f)`.

This is relative to the actual affine difference energy; it does not replace that energy by the separate sizes of the two packets. It is uniform in both multipliers and both shifts.

Delayed-prefix harmonic summation gives

`[log(N+1)−log(Q(Q−1)+1)] E(f) ≤ Σ_(1≤n≤N) f(n)²/n`.

The same statement holds for any finite sum of these nonnegative energies.

## Joint consequence

Put `f(n)=F_a(n+1)−F_b(n)` and `g(n)=F_a(2n)−F_a(n)`. Existing sharp successor phase loss controls all conductors above two. The exact dyadic mean is `a_2`, so Cauchy–Schwarz gives `E(g)≥a_2²`. Therefore

`E(f)+E(g) ≥ (3/4) Σ_(2≤m≤Q) φ(m)a_m²`.

For `K≥Q(Q−1)`, the window sum of `f²+g²` is at least

`(3/4)[K−Q(Q−1)] Σ_(2≤m≤Q) φ(m)a_m²`.

For shorter windows the same displayed bound is nonpositive and follows from nonnegativity. The harmonic version has the analogous logarithmic factor. The common kernel is the constant packet with matching approximant. Pure conductor three, with its exact successor projection, attains the complete-period constant: multiplication by two permutes its primitive roots, so its dyadic difference vanishes.

## Novelty and limits

Sharp successor leakage and the large sieve are existing foundations. The contribution combines them with exact affine spectral transport and the dyadic pole reading, retaining every approximation coefficient on quadratic sampling horizons. This answers a finite-packet rigidity problem. It does not show that a negative complete-Weil state has small values of these observed defects; Gamma, pole, and shell coupling remain a separate source problem.

## Formalization

`CriticalScaleArithmeticRigidity/AffineWindowEnergy.lean` and `FiniteHorizonRigidity.lean`.
