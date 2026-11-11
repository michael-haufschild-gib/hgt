# The absolute-cosine contact law at a height

- **ID:** A102
- **Stage:** 3-formalized
- **Type:** THEOREM

## Exact reduction

For a real packet with nonnegative autocorrelation, maximizing its contact
form over all real systems `|w(n)|≤Λ(n)` chooses
`w_t(n)=Λ(n) sign(cos(t log n))`. The resulting contact form is

`Σ_{2≤n≤N} 2Λ(n) A_f(log n)/sqrt(n) · |cos(t log n)|`.

The existing aligned system chooses `Λ(n) cos(t log n)` and therefore
sees `cos²`, whose mean is `1/2`. Its additive `log 2` is specific to
that choice, rather than an optimality theorem for all dominated systems.

## Improved upper-bound route

The mean of `|cos|` is `2/π`. A bounded periodic primitive gives, uniformly
for `x≥1/2`, `∫_T^{2T}|cos(tx)|dt ≥ 2T/π−O(1)`.
Thus some height in every dyadic window retains `2/π−O(1/T)` of the
prime contact form. The existing even-polar-packet balance then gives
failure at aperture `log log t + log(π/2) + η` for every `η>0`.

This sharpens the upper bound. It does not identify the optimal
uniform additive constant: that also requires controlling exceptional
heights of the weighted absolute-cosine sum.

## Lean status

The modulation identity, cosine-square mean, polar-packet estimates and
upper bound for the archimedean form are already proved.
`SelectiveArithmetic/TheWorstContactsAtAHeightFollowTheCosineSign.lean`
proves the signed maximizer, absolute-cosine mean and
`exists_dominated_height_neg_pi`. Direct Lean check passed; wired into
`SelectiveArithmetic.lean`.
