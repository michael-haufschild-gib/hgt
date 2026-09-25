# LI global real-axis scalar-sign route

- **ID:** li-global-real-axis-scalar-sign
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** LI radial generating law and global quotient-shape no-go
- **Statement:** Positivity of the LI radial quotient at every real mass, even together with all-order positive-ray complete monotonicity, does not force nonnegative completed-Abel modes.

## Goal and exact obstruction

The proposed route extends the prime--Gamma radial response from positive to negative real mass and tries to infer LI coefficient orientation from its scalar sign. The existing symmetric packet

`7 × (1/2) + (3/4+i) + (3/4-i)`

falsifies it. Its quotient response `Q(v)=Σ_b b/(v+b)^2` is strictly positive for every real `v ≠ -1/2`, although its completed-Abel endpoint mode `n=3` is strictly negative. The same packet is already strictly completely monotone to every order on the entire positive ray.

Set `t=v+1/2`, `d=(t+1/4)^2+1`. The on-line contribution is `7/(2t²)`. Each off-axis atom has real part at least `-5/(4d)` by its exact norm. Their joint adverse contribution is therefore at most `5/(2d)`, while

`7d-5t² = 2(t+7/8)²+189/32 > 0`.

This proves positivity on the whole real axis away from the on-line pole. The negative mode is the already-closed `liLocalCompletedAbelEndpointMode_three_re_neg`.

## No-go closure

- **Exact killing theorem:** `liLocalQuotient_allRealSign_completeMonotonicity_negativeMode` in `LiEvenCrossGlobalRealAxisSignNoGo.lean`.
- **Strongest positive survivor:** An explicit global spectral masking law: seven positive on-line copies dominate a conjugate off-axis pair at every real mass, not just on a local or positive interval.
- **Route meaning:** Scalar sign survives real-axis continuation while complex singular support differs. A live LI producer must use source-derived complex support, a matrix/indefinite kernel with faithful completion, or another genuinely orientation-sensitive law. This packet is not the literal Xi divisor and proves no off-line Xi zero.
- **Status:** Paper proof dependency-closed; Lean direct check and targeted `lake --old build GaloisForLFunctions.RHTower.LiEvenCrossGlobalRealAxisSignNoGo:olean` passed. Umbrella import wired; no umbrella build run. Literature priority unverified.
