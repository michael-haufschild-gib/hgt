# Modular-center C5 stationary-locus hostile test

Date: 2026-08-29  
Status: computation complete; diagnostic only; forbidden as input to Lean proofs

## Question

Locate sign changes of the exact velocity `N'(t)` of modular-center source C5 and test `N(t)` at
every located stationary root. A negative value at a velocity root would kill the surviving
stationary-reserve route. Root topology and `N''` signs could instead select a finite analytic
decomposition. Previous bulk C5 scans tested `N`, not its exact stationary locus.

The script evaluates the literal completed-theta source and its first four derivatives. At modular
center it uses `P(t)=Phi(t)^2`, then reconstructs the corpus definitions without numerical
differentiation:

```text
A = P(0)-P(t),  D = -P'(t),  J = -P''(t),  K = -P'''(t),  L = -P''''(t)
N = 24 A² - 9tAD + t²(5AJ-4D²)
V = N' = 39AD + tAJ - 17tD² + t²(5AK-3DJ)
V' = 22D² + 40AJ + t(11AK-39DJ) + t²(2DK+5AL-3J²).
```

All three quantities are normalized by the positive constant `P(0)^2`.

## Outcome

- 79,999 distinct points covered `10^-8 <= t <= 100` with overlapping logarithmic and linear
  meshes at 120 decimal digits.
- Every sampled C5 numerator was strictly positive.
- More importantly, every sampled exact velocity was strictly positive. No velocity sign-change
  bracket and hence no positive stationary root was found.
- Independent 160-digit re-evaluation of endpoints and audit points passed.
- The velocity is super-exponentially tiny in the far cusp, so absence of a sampled sign change is
  not a certified root count. Arbitrary precision was necessary; ordinary floating-point signs
  are unusable there.

## Interpretation

The stationary-locus formulation may be unnecessarily weak. The computation selects the stronger
candidate

```text
[CONJECTURE]  0 < t -> 0 < thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 t.
```

Together with the already formal seam value, that would prove modular-center C5 by direct
monotonicity and make the stationary tax/reserve restriction vacuous. It would also discharge the
entire modular-center rank-four source sign, though not off-center packets, higher packet orders,
or cofinal Weil landing.

Best hostile follow-up is not a denser scan. Derive exact seam and one-atom cusp factorizations,
then search the compact transition for a likelihood-coordinate or total-positivity decomposition
of `V`. A single exact source state or physical `t` with `V<=0` kills direct monotonicity while
leaving the weaker stationary-reserve route alive.

## Reproduction

RunPod used 128 worker processes, Python 3.12.3, mpmath 1.3.0, and NumPy 2.1.2. Runtime was 9.75
seconds. BLAS/OpenMP threads were pinned to one per worker.

```bash
python3 run_experiments.py --output results --workers 128 --dps 120 \
  --log-points 60000 --linear-points 20000
python3 verify_results.py .
```

`results.json`, logs, environment metadata, scripts, and `SHA256SUMS` are included. No result in
this folder may be imported into Lean.
