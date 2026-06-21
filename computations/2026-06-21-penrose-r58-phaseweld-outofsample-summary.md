# R58 — phase-weld out-of-sample validation

**Verdict:** DEAD END / validation-only phase-carrier stress test.

## Setup
- Seed RandomNode: `Modulation equations for blowup parameters such as scale, phase, center, and frequency`.
- STEP 1 cold list + STEP 2 rng `16`: topic `Log-periodic precursors to financial crashes`.
- STEP 3 cold list + STEP 4 rng `19`: NODE `Model validation should use out-of-sample bubble-end forecasts, not only retrospective fits to famous crashes`.
- Standing-order target pick: file rng `3` -> `docs/consolidated/01-landscape-and-weld-geometry.md`; topic rng `14` -> Phase-Weld layer.
- STEP 5 constraint: a fitted signal must survive held-out windows; retrospective one-window tuning is insufficient.
- STEP 8 selected transfer by Levenshtein: `nested-window stability is the phase-weld forecast surrogate` (`64`).
- STEP 9 method rng `13` = find a monotone quantity.
- STEP 11 method rng `21` = dependency chain.

## Computation
Archive script: `computations/2026-06-21-penrose-r58-phaseweld-outofsample.py`.

The NODE validation used a synthetic LPPL fit:
- train-best `tc=106.00`, train RMSE `0.002821`, held-out RMSE `0.009412`;
- held-out-best `tc=105.00`, train RMSE `0.002849`, held-out RMSE `0.003211`;
- train-near-optimal `tc` span within 3% was `[104.50,108.00]`.

The target test calibrated a median phase-weld `Delta` threshold on `[100,170]` and applied it unchanged to `[500,570]` and `[1000,1070]`, comparing true `zeta'/zeta`, finite Euler cutoff, and random-phase controls.

Held-out margin trend:
- `sigma=0.3`: train margin `0.5711`, held-out min `0.5748`, held-out mean `0.6002`;
- `sigma=0.5`: train margin `0.3970`, held-out min `0.0780`, held-out mean `0.2117`;
- `sigma=0.7`: train margin `0.1230`, held-out min `-0.2667`, held-out mean `-0.1165`;
- `sigma=1.2`: train margin `-0.0043`, held-out min `-0.0313`, held-out mean `-0.0185`.

## Dependency chain
1. The observable is the already-corpus phase-weld defect `Delta=max(log|A|,log|P|)-log|A+P|`.
2. The NODE contributes only the train/test validation protocol.
3. The held-out computation usefully bounds the old signal: it is out-of-sample stable in the left strip at `sigma=0.3`, weak at `sigma=0.5`, false at `sigma=0.7`, and collapsed at `sigma=1.2`.
4. Therefore the result is a stress test of the existing phase-carrier story, not a new invariant.

## Reading
For the Phase-Weld layer, one-window retrospective fits are not enough. A legitimate experimental claim must carry held-out window margins and controls. R58 supplies such a validation check, but it does not clear the non-reducing gate.
