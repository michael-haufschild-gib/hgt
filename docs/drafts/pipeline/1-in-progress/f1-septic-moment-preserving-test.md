# A moment-preserving septic test of the first-fold comparison

- **ID:** F1-SM
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [Two-moment payment](../5-failed/f1-primitive-variance-joint-payment.md)
- **Statement:** The two-moment comparison `D` has a negative odd C² unit-window direction.

This existence target is now proved by the
[quadratic cutoff](../5-failed/f1-primitive-variance-joint-payment.md).
The septic-specific calculations below remain conjectural and are not needed for that result.

The proposed polynomial test on `[0,1]` is

`g(u)=u(1−u²)(225−470u²+429u⁴)/160`
`     =u−3u³/2+u⁵/2+(P₅(u)−P₇(u))/10`.

Orthogonality preserves both charged moments:
`∫ug=11/105`, `∫P₃g=−17/315`. The endpoint-zero polynomial extends by zero
to an odd Lipschitz function on `[-1,1]`; a C² witness additionally requires
approximation preserving the strict energy sign.

## Exact sign test

Write `g(u)=Σᵢ₌₀³ cᵢu²ⁱ⁺¹`,
`c=(225,−695,899,−429)/160`, and
`g(1−z)=Σᵢ₌₁⁷ hᵢzⁱ`,
`h=(368,−2104,6720,−10520,8110,−3003,429)/160`.
With `s=2−2log2`, the proposed exact evaluations are

`E=Σᵢⱼ cᵢcⱼ/(2i+2j+3)`,
`∫Wg²=Σᵢⱼ [cᵢcⱼ/(2i+2j+3)] Σₖ₌₀ⁱ⁺ʲ⁺¹1/(2k+1)−log2·E`,
`R=Σᵢⱼ hᵢhⱼ i!j! sⁱ⁺ʲ⁺¹/(i+j+1)!`.

The target is `aE+∫Wg²+wR−(5123/1280)(11/105)²−(63/20)(17/315)²<0`.
Even granting `a≤111/200`, the proposed termwise upper certificate with `w≤4902/10000`,
`693147180/10⁹≤log2≤693147181/10⁹` is not negative. It therefore supplies
no negative witness. The actual sign, integral identities, and C² transfer
remain unproved.

## Positive survivor of a negative witness

The audited coercivity `D(G)+(3203/1280)(∫uG)²≥∫G²/1000` makes `D`
strictly positive on the first-moment kernel. A negative witness would therefore
identify exactly one negative direction. This concerns the comparison `D`;
the complete Weil form retains additional positive terms.
