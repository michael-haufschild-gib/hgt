# HB arithmetic-occurrence versus radial conditioning: frozen protocol

Status: frozen before computation. Finite empirical selection test; no statistical-independence claim and no theorem.

## Question

Does evaluation at known critical-line zeta zeros select unusually well-conditioned points of the complete 2×2 fundamental radial transfer matrix, compared with nearby nonzero ordinates? This tests a possible source/receiver compatibility mechanism: arithmetic occurrence might avoid radial source mixtures invisible to both readers.

For each `rho=1/2+i gamma`, form all four complete first-subtracted radial moments and the scale-free invariant

`delta = |det A| / ||A||_F^2`.

Use the already validated zero ordinates only as input data. The radial formula is independent of zeta evaluation.

## Prediction audit and frozen gate

One diagonal channel has a high-height survival bound, but it does not determine a 2×2 determinant, smallest singular direction, or zero-conditioned versus nearby contrast. Smooth height drift is a competing explanation. Outcome of the paired scale-free statistic is not known.

Three cohorts are frozen: zero indices 1–64 (discovery repeat), 65–128 (first holdout), and 257–320 (distant holdout). At each zero compare `log delta` with controls at `gamma ± gap/4`, where `gap` is the recorded next-zero spacing. Candidate passes only if both paired mean and paired median are positive in every cohort. One failure retires this selection statistic; no offset or normalization is retuned.

## Experiments, controls, validation

1. Evaluate central, lower and upper ordinates at 60 digits with hypergeometric continuation; 14 worker processes.
2. Record all four entries, determinant, Frobenius norm, `delta`, and singular-value ratio.
3. Validate cohort minima, maxima and largest contrasts at 100/160 digits and with the independent endpoint-binomial series at 190 digits.
4. Retain exact-zero residuals from the input provenance but do not re-evaluate zeta; this experiment concerns receiver conditioning.

Falsifiers: frozen sign gate failure; precision instability; independent entry discrepancy above `1e-80`; or any input cohort mismatch. No finite lower bound is inferred even on success. Nearby controls are deterministic analytic controls, not alternative physical sources.

Full angular coefficient, onset, causal corrections, contacts, independent SS/SV/VV action and spacetime limits remain unknown. Scientific-method mechanics: separate occurrence from receiver; reserve cohorts; attack selection as smooth-height artifact; mix occurrence/control and height cohort; change representation; retain extreme counterexamples as positive salvage.

Each run uses a unique `/tmp/codex-root-hb-zeta-conditioning-*` directory, one 570-second guard, at most 14 workers, one library thread each, and preserves partial output.
