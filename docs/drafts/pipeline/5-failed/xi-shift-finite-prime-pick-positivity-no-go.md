# Finite-prime shifted-Xi Pick positivity fails on every Euler sampling set

- **ID:** `xi-shift-finite-prime-pick-positivity-no-go`
- **Stage:** `5-failed` (finite-stage positivity subroute only)
- **Type:** FALSIFIED / THEOREM (paper and Lean)
- **Scientific status:** Source-specific bridge; not claimed as a fundamental new RH theorem
- **Statement:** For every finite prime set `S` and `0 < omega < 1/2`, the literal finite shifted-Xi Pick kernel is not PSD even on Gaussian-rational Euler-region nodes.

## Exact mechanism and paper proof

Write `s_±(z)=1/2±omega−iz`, `A(s)=s(s−1)Gammaℝ(s)/2`, and

```text
theta_S(z) = [A(s_−(z)) / A(s_+(z))]
             ∏_{p∈S} [(1−p^(−s_+(z))) / (1−p^(−s_−(z)))].
```

At `z₀=i(1/2−omega)`, one has `s_+(z₀)=1` and `s_−(z₀)=1−2omega∈(0,1)`.
The factor `A(1)` vanishes, while `A(1−2omega)` and every finite prime factor
are nonzero. Thus the pole-cleared numerator is nonzero and denominator zero
at `z₀`; above that height the denominator is nonzero.

If the Schur kernel of `theta_S` were PSD on Gaussian-rational Euler nodes,
Nevanlinna--Pick interpolation would produce a bounded holomorphic function on
the upper half-plane agreeing with `theta_S` at those nodes. They accumulate
inside the Euler half-plane, so analytic uniqueness propagates agreement to
the connected region `Im z>1/2−omega`. Approaching `z₀` from above then gives
`|H(z₀)|≤|D(z₀)|=0`, contrary to `H(z₀)≠0`. This proof is unconditional and
does not assume any Xi zero or RH.

## No-go closure

- **Killed:** Any argument requiring all finite-prime shifted-Xi Pick kernels to be PSD, even after restricting to Gaussian-rational Euler nodes.
- **Strongest positive survivor:** The exact uncancelled archimedean pole at `z₀` and the resulting unavoidable finite negative Pick packet. Both are formalized by `finiteThetaPole_uncancelled` and `exists_eulerXiShiftFinitePrimePick_gaussianRational_negativeEnergy` in `RHTower/XiShiftEulerFinitePrimePoleNoGo.lean`.
- **Route meaning:** Finite negative Pick margins are unconditional and therefore cannot diagnose RH failure alone. The all-prime tail comparison in `XiShiftEulerFinitePrimeCertificate.lean` is logically indispensable; it must distinguish a persistent divisor obstruction from a finite-stage pole that analytic completion must account for.
- **Boundary:** This theorem does not establish any all-prime tail estimate, source-derived positivity, or RH.

## Verification and novelty

The generic interpolation/pole lemmas and source-specific module passed direct `lake env lean` and targeted `lake --old build ...:olean` checks on 2026-09-25. No umbrella build was run. Corpus search found the conditional finite-prime certificate from an uncancelled Xi zero, but not this unconditional every-`S` rational-node no-go. The interpolation principle is standard; source-specific novelty beyond the corpus is provisional, and this card does not claim a major scientific jump.
