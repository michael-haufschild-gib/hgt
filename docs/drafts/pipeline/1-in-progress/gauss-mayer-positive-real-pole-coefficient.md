# Positive real spectral parameters and the Mayer pole coefficient

- **Stage:** 1-in-progress
- **Type:** Conjecture
- **Parent:** [exact determinant finite part](../3-formalized/gauss-mayer-raw-determinant-finite-part.md).

## Target

For real `w>0` and `0<λ<(3/2)^w`, conjecture `B(w,λ)≠0`.
This includes every `0<λ≤1`.
In particular, `B(1,1)≠0` would make the actual source determinant at
`λ=1` have a genuine simple pole, contrasting with the certified removable
negative-unit parameter. The exact finite-part theorem is now certified.

## Source mechanism to audit

Let `K=(I−P)R(w)(I−P)`. The actual response
`f_w(z)=1−(1+z)^(−w)` has `f_w(0)=0` and satisfies `Kf_w=−f_w`.
For real `w>0`, its derivative `h_w(x)=w(1+x)^(−w−1)` is positive on `[0,1]`.
For `f(0)=0`, differentiating the actual centered branches suggests

`−(Kf)'(x)=Σ_n [w(n+x)^(−w−1) ∫_0^{1/(n+x)} f'(y)dy
                         +(n+x)^(−w−2) f'(1/(n+x))]`.

Writing `f'=h_w g` and dividing by `h_w(x)` gives a positive averaging
operator `M_w`, with `-(Kf)'/h_w=M_w g`. Its row mass is one by the
actual response identity. The first branch's integral coefficient is
exactly `w(1+x)^(−w−1)/h_w(x)=1`; its integration interval contains
`[0,1/2]` for every `x∈[0,1]`. Hence every row contains the same measure
`h_w(y)dy` on `[0,1/2]`, of mass

`ε_w=1−(3/2)^(−w)>0`.

After removing this common measure, the remaining row mass is
`τ_w=(2/3)^w<1`. For real `g`, the oscillation estimate should be
`osc(M_w g)≤τ_w osc(g)`. Thus a positive eigenvalue `μ` of `K` with
`μ>τ_w` would force both real and imaginary parts of `f'/h_w` constant.
The response identity then rules out that eigenvalue. This avoids a strict
maximum-equality argument and suggests the stronger nonvanishing region
`0<λ<(3/2)^w`. The endpoint remains unclassified.

A direct source formulation may avoid integral construction. If `f(0)=0`
and `Re f'≥0` on `[0,1]`, monotonicity gives

`Re [−(Kf)'(x)/h_w(x)−f(1/2)]≥0`.

Indeed the first branch contributes `f(1/(1+x))−f(1/2)` after
normalization, and every remaining derivative term has nonnegative real
part. Prove this first for actual finite branch sums, then pass through a
bounded interior derivative functional. Applying the inequality to
`f−m f_w` and `M f_w−f`, with `m,M` the extrema of `Re(f'/h_w)`,
gives the proposed oscillation contraction directly. Repeat for `−i f`
to control the imaginary part.

The complementary Fredholm identity would then give the proposed nonvanishing.

## Open obligations

Actual derivative series and interval integral realization; common-measure
minorization and oscillation contraction; injectivity of derivative restriction
on functions vanishing at zero; determinant/eigenvalue transport for the
compressed operator. None may be assumed as an interface.

The corpus search surfaced the actual response and complementary determinant
identity, but no checked theorem discharges this positive-kernel mechanism.
No proof or RH conclusion is claimed. Complex source parameters are outside
this proposed positivity argument.

## Checked source leads

`MayerFredholm.synthesisMap` is public and its checked factorization is
`J ∘ analysisMap = regularized w`. The checked Hilbert evaluation projection
intertwines `analysisMap` with `P`. Thus compressing both factors supplies a
candidate Banach/Hilbert eigenvector bridge for `K`; its exact determinant
identification still needs proof. Existing corpus interval-positivity lemmas
and a separate Markov norm-contraction theorem do not prove this source's
minorization. No generic positivity premise may replace that missing input.
