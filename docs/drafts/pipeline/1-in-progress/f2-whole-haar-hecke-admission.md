# F2 — whole-Haar admission of actual window lifts

- **Stage:** 1-in-progress
- **Conjecture:** For `Re s>0` and a `C²` stage-`A` test `H`, the actual first source Hecke image `T₂,s(windowPeriodLift s H)` has finite Haar square energy on `(0,∞)` iff `H(−log2)=0`. Every test is admitted exactly when `A≤log2`.
- **Purpose:** Attach the paired WTZ period lift to the whole-axis physical carrier. Existing cusp-energy bounds cover only the upper endpoint; compact-support admission requires a stronger germ condition.

## Proposed mechanism

Write `ψ=windowPeriodLift s H`. It is compactly supported in a positive multiplicative interval and fixed by its modular inversion. At sufficiently large `a`, the actual Hecke formula is

`T₂,s ψ(a)=(a+1)^(−2s) ψ(2a/(a+1))`.

Inversion therefore gives the exact lower-end limit `T₂,s ψ(a)→ψ(2)` as `a→0+`. A nonzero limit forces logarithmically divergent Haar square energy. The existing zero-set identity gives `ψ(2)=0 ⇔ H(−log2)=0`.

If this value vanishes, local smoothness at `2` gives `ψ(2a/(a+1))=O(a⁻¹)`. Hence the upper tail is `O(a^(−2 Re s−1))`; inversion makes the lower tail `O(a)`. Both are Haar-square integrable. On compact positive intervals the lift and its Hecke image are continuous.

For `A≤log2`, support and continuity force the first-prime value to vanish, including the endpoint. For `A>log2`, the already constructed smooth first-prime bump has value one and fails admission. Thus whole-Haar admission includes the threshold excluded by universal compact-support admission (`A<log2`).

## Gaps

Check the exact lower-limit normalization and prove the two-endpoint integral classification in Lean. The Cauchy graph theorem alone does not supply this paired-lift admission. No positivity conclusion is claimed.
