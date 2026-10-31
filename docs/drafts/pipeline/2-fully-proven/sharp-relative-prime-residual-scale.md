# Sharp relative prime-residual scale

- **ID:** critical-rigidity-sharp-relative-prime-residual
- **Stage:** 2-fully-proven
- **Type:** THEOREM
- **Lean:** `CriticalScaleArithmeticRigidity/SharpPrimeResidualScale.lean` — pending check

## Statement

Let `w_p=sqrt(p−1)/p` on primes and zero elsewhere. For every sufficiently large integer `P`, put `Q=P²`. For every horizon `N≥P`, the literal prime residual satisfies

`Σ_(n≤N) R_w(N,n)² ≥ (1/384)(log Q)² L_Q(w)`.

Together with the source-relative upper bound, this identifies the quadratic logarithmic conductor cost of the squared residual. The witness has zero constant coefficient; it is not claimed here to lie on every finite-horizon harmonic pole hyperplane.

## Proof

Write `l=log P`, `B=B_Q−B_P`, and `A'=Σ_(P<p≤Q)log p/(p−1)`. The proved Mertens error is bounded by an absolute `E≥0`. For sufficiently large `P`,

`l/2≤B≤B_Q≤3l`, `A'≤B_Q+8≤11l`.

For `N≥P`, put `a=floor(N/P)`. Since `(a+1)P≤N+P≤2(N+1)`, logarithmic integration gives

`H=Σ_(a<n≤N)1/n ≥ log P−log 2 ≥ l/2`.

The source-specific incidence theorem yields

`Σ tail²/n ≥ H B²−2BA'/(a+1) ≥ l³/8−66l²`.

The exact scalar comparison gives `ΣR²≥(1/2)Σtail²/n−C(1+log Q)M`. The excitation gap and coherent energy identity give `2log 2·M≤L=B_Q≤3l`. Since `1+log Q≤3l`, the scalar term is at most `[9C/(2log 2)]l². Thus

`ΣR²≥l³/16−D l²`, where `D=33+9C/(2log 2)`.

For `l≥32D`, this is at least `l³/32`. Finally `(log Q)²L=4l²B_Q≤12l³`, proving the stated constant. Every threshold is absolute and independent of `N`.

## Positive survivor and scope

The upper and lower relative scales match, with a literal positive-incidence extremizer and no distribution hypothesis. This obstructs removing the two conductor logarithms from an absolute residual-norm argument. It does not obstruct direct prime-form positivity or cancellation with the complete Gamma–pole–shell form.
