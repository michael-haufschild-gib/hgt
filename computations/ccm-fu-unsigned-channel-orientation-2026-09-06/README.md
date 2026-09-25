# Literal unsigned source orientation: numerical guidance

`screen.py` evaluates every ordinary defect prefix A(N) for 1<=N<=100000 and the corresponding undilated half-order response K_1(N+1). It found no negative value in either family. The smallest screened normalized channel is K_1(3)/sqrt(3), approximately .03730049548147723. These floating-point results are exploratory guidance, not a proof of U1/U2 and not inputs to Lean.

| N | A(N) | K_1(N+1) | K_1(N+1)/sqrt(N+1) |
|---|---:|---:|---:|
| 1 | .15443132980306573 | .06396755125974218 | .045231889271661774 |
| 10 | .559430891064362 | .1673781710326118 | .05046641740100967 |
| 100 | 7.813188579448248 | .7755437916608232 | .07716949153389868 |
| 1000 | 85.8457017772561 | 2.7309756080451693 | .08631788340050361 |
| 10000 | 970.625831137248 | 9.36205551383781 | .09361587446166901 |
| 100000 | 8809.383210902693 | 28.353925495155487 | .08966253685984532 |

The independent analytic Lean proof establishes eventual ordinary-prefix positivity and a square-root lower bound for K_1; see [the proof card](../../../3-formalized/ccm-fu-divisor-positive-prefix.md). The stronger all-cutoff U1/U2 theorems are closed by [the analytic orientation certificate](../../../3-formalized/ccm-fu-unsigned-channel-orientation.md), independently of this screen.
