# C5 reflected squared atomic-Laplace no-go (2026-08-28)

Formalized `GaloisForLFunctions.RHTower.ThetaCuspReflectedSquaredAtomicLaplaceNoGo`.

New route kill: no fixed absolutely summable complex atomic Laplace series with a finite noncancelled lowest-frequency shell represents `x ↦ thetaCuspReflectedSourceProduct u (sqrt x)` on `x ≥ 0`; equality already fails on integer squared-scale samples.

Mechanism: if lowest frequency is `N ≥ 0`, normalize sampled series by `exp(N n)`. The complement above the lowest shell vanishes by dominated convergence; the finite lowest shell survives after repeated-frequency coefficients are aggregated. Corpus theorem `not_tendsto_tsum_normalizedExponentialPencil_zero_of_dominantFinset` supplies cancellation-resistant survival. Literal theta theorem `tendsto_exp_mul_thetaCuspReflectedSquaredProduct_atTop_zero` forces the same normalized samples to zero.

Positive survivor/classification: viable C5 measure/action representation must have no finite first active shell, fail fixed ell1 summability, depend on scale, use a continuous carrier with no isolated onset, or be applied before squared displacement. Ordinary fixed signed atomic cancellation is dead.

Validation: direct Lean check clean; targeted module build passed; axiom audit on decay, dominant-pencil obstruction, nat-sample atomic obstruction, and continuous-ray capstone reports only `propext`, `Classical.choice`, `Quot.sound`. Module wired into `RHTower.lean`. Card: `docs/drafts/pipeline/3-formalized/theta-reflected-squared-atomic-laplace-no-go.md`.