# TG goal loop (2026-10-09) — working log

- **Goal:** route TG → unconditional Lean RH. Conjecture → prove/fail → learn → next.
- **Big picture (fixed inputs):** TG integer = Hardy cubic trace = zero count [L]. Gaussian passage reads
  half-planes, bounded ⇔ RH [L]. CANNOT-461: budget idle for holomorphic source readers. Big-picture §4(c):
  exact trace = index + a-priori sub-unit bound, source identity at √X precision. Walls 1–10.

| # | Conjecture | Verdict | Lean | Learning |
|---|---|---|---|---|
| 1 | Gaussian formation has Re Φₓ'/Φₓ>0 on Re s>0 above T₀(x); reflected Ξₓ RH-true, simple line zeros, TG index 0 | PROVED | GaussianFormationReflectedHermiteBiehler | Gonek mechanism; dominance window X≲log T vs approximation window X≥(log T)^{1/δ}: TG gap quantified |
| 2 | Remove the height threshold: tilt e^{λ(s−½)} with λ ≥ 2+Kₓ+M⁰ₓ makes the reflected source RH-true at all heights | PROVED | HorizontalLogDerivReflectionDominance (generic), GaussianFormationReflectedHermiteBiehler (tilt) | Tilt cost = extra zero density λ/π ∝ prime mass Kₓ; ξ has tilt 0 and infinite mass — RH-truth of models is bought by density excess |
