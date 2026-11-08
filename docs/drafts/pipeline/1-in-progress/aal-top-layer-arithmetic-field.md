# Arithmetic field of a finite top layer

- **ID:** aal-top-layer-arithmetic-field
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** The actual prime-convolution source cannot realize the transverse field forced by a finite separated top layer of zeta zeros.

## Exact inputs

At a top zero $p$ of multiplicity $m$, the zero source field is positive, with the reflected zero contributing at least $m/(2\operatorname{Re}p-1)$. The same field is the real part of the simple Laurent coefficient of $(\zeta'/\zeta)^2$, divided by $2m$, plus the logarithmic derivative of the archimedean factor.

On $\operatorname{Re}s>1$, $(\zeta'/\zeta)^2$ has the actual nonnegative Dirichlet coefficients $\Lambda*\Lambda$. Its prime-power part is explicit; its remaining support consists of products of two prime powers with distinct bases. A contradiction must use that arithmetic support together with the functional equation or the finite gap. Geometric source positivity alone also holds for a relocated zero.

## Open step

Derive a source constraint on the simple Laurent coefficient from those actual coefficients that conflicts with the positive transverse field. Nonnegativity on the real axis is insufficient: the pole at $s=1$ dominates there. No sign estimate at a nonreal zero has been established.

Writing $-\zeta'/\zeta=P+H$ separates primes from proper prime powers. Although $H$ is holomorphic on $\Re s>1/2$ and its normalized high jets vanish, the simple Laurent coefficient of $P^2$ differs from that of $(\zeta'/\zeta)^2$ by $2mH(p)$. The same-prime diagonal is holomorphic and can be removed. The exact distinct-prime pair source has double coefficient $m^2$ and simple coefficient $2m(B(p)+H(p))$; its corrected real residue equals the transverse field. These statements are Lean-checked in [prime-pair-source-field](../3-formalized/prime-pair-source-field.md).

## Scope

No AAL proof is claimed. `TheCompleteWeilMatrixIsPositiveAtACriticalMultiple.lean` supplies whole-space positivity for $1\le c\le 2K(\log N)^{1/8}$ with some fixed $K>0$. Direct Lean checking passes; the capstone uses only `propext`, `Classical.choice`, and `Quot.sound`.

At $c^8/\log N\to R$, a window's limiting form retains an exponential aliasing mass. Optimizing over the low-conductor packet removes exactly the polar capacity $S(h)^2/D(R)$, not that mass (`EveryLowPacketCorrectionHasItsPolarCapacity.lean`). Positivity at every critical ratio implies RH (`TheLowPacketPaymentAtEveryRatioIsTheRiemannHypothesis.lean`); only a fixed small interval of ratios is established. Neither the critical band nor the bilateral Eisenstein Gram law supplies the missing sign of the nonreal source residue.
