# Completed-theta C5 fixed-action Jacobian hostile scan

**Date:** 2026-08-29  
**Scope:** diagnostic route selection only; no output is admissible in a Lean proof

## Question

For reflected log action `q(u,t)` and normalized C5 balance `B(u,t)`, test the actual remaining
fixed-action transport candidate

```text
J(u,t) = B_u(u,t) q_t(u,t) - B_t(u,t) q_u(u,t).
```

Since `q_t > 0`, `J >= 0` means B is nondecreasing in centre along each fixed-action level set.
This is the direct parent conjecture left after the earlier two-sign sufficient decomposition was
formally killed.

The script evaluates `q` and its required centre/displacement jets from the literal completed-theta
series through logarithmic order three. It differentiates the stable balance

```text
B = 6 - (9/4)t q_t/r + (5/4)t^2(q_tt-q_t^2)/r - t^2 q_t^2/r^2,
r = exp(q)-1,
```

analytically, rather than finite-differencing level sets.

## Run

- RunPod: 128 workers, Python 3.12.3, mpmath 1.4.1, NumPy 2.5.2
- precision: 160 decimal digits
- deterministic grid: 579 centre values and 1,200 displacement values
- domain: `10^-7 <= u <= 20`, `10^-5 <= t <= 100`
- randomized attack: 200,000 log/linear-mixture points on the same domain
- runtime: 168.46 seconds

Total: **894,800 tested points; every reported Jacobian sign was strictly positive**. No zero or
negative sample remained.

## Precision trap

A preliminary 60-digit run produced apparent negative signs only at huge action, mostly `t=100`,
where `B` has saturated to 6 and `J` is exponentially tiny. Re-evaluation at 50, 80, 120, and
200 digits showed those signs were cancellation artifacts: selected points stabilized positive by
120 digits and remained positive at 200 digits. The production run therefore used 160 digits.

This is not cosmetic. A low-precision sign scan would have falsely retired the route.

## Interpretation

1. The direct fixed-action seam-minimization route survives its first targeted hostile attack.
   Previous broad C5 scans tested only the consequence `C5 >= 0`; this run tested the actual
   transport premise proposed to prove it.
2. Failure of the retired two-sign decomposition is compatible with positive direct Jacobian:
   its two signed terms appear to compensate on the literal theta trajectory.
3. Reflection forces `J(0,t)=0`, so the sharpened proof target is positivity of a desingularized
   transverse Jacobian such as `J(u,t)/u` for `u>0`, with exact seam derivative as boundary value.
4. Useful proof program: exact local seam coefficient, compact bulk certificate in modular or
   atom-likelihood coordinates, then large-action asymptotic positivity. Computation should search
   for exact factorization/shear in those three zones, not merely add more samples.

No sampled sign, location, or precision estimate proves global Jacobian positivity.

## Computation-free formal fallout

`GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5Jacobian` independently formalizes:

- direct two-jet C5 balance equals existing intrinsic velocity balance;
- exact centre and displacement derivatives;
- exact fixed-action Jacobian as determinant of C5/action gradients;
- exact modular-seam vanishing `J(0,t)=0`.

The module contains no numerical result or imported enclosure. Global sign remains open.

## Reproduction

```bash
/root/frontier-venv/bin/python run_experiments.py \
  --workers 128 --dps 160 --u-points 400 --t-points 900 \
  --random-points 200000 --seed 20260829 --output results
```

`verify_results.py` checks parameters, counts, and all reported sign summaries. `SHA256SUMS`
authenticates downloaded artifacts.
