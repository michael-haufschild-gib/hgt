# Explicit cluster-detector constant

- **ID:** explicit-cluster-detector-constant
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** review-0411 §2.1, A27.

## Target

Replace the existential local-count constant in the cluster detector by a numeral.
`N(t,t+1]≤240 log(|t|+3)` for every real `t`, hence detector aperture
`480000 log(|γ|+3) log(10⁶/δ)` for `|γ|≥102` and depth at least `δ>0`.
At every height the product detector applies when
`a≥exp 6`, `a≥1/δ`, and `24000000 log(|γ|+306) log a≤a`.
A closed choice is `a=max(exp 6,max(1/δ,48000000 log(|γ|+306))²)`.

## Proof

Centre the unit interval at `T=t+1/2`. When `|T|≥4`, the existing xi-copy count is
`40 log(180|T|)`. Since `180|T|≤(|t|+3)^6`, this is at most
`240 log(|t|+3)`. When `|T|<4`, the whole interval lies in the proved zero-free
band `|Im ρ|≤9/2`. Equality of xi and zeta multiplicities transfers the count.
The 200-unit cluster contains at most `96000 log(|γ|+3)` distinct zeros.
The sub-Nyquist size condition is therefore paid by the stated aperture.
Its contrapositive confines high zeros under Hodge positivity to depth
`<10⁶ exp(−a/(480000 log(|γ|+3)))`.

For the product detector, the 202-unit cluster contains at most
`48480 log(|γ|+306)` distinct zeros. Its size condition follows from the
stated numerical bound. The endpoint-source height gap supplies `|γ|≥2`
for every zeta zero. Both constructions give a smooth negative Weil test
supported in `[-(a+1),a+1]`, without separation or simplicity assumptions.
For the closed choice, put `b=max(1/δ,48000000 log(|γ|+306))`. Then
`b≥1`, `b≤√a`, and `log a≤2√a`; these imply all three size conditions.

## Lean status

`SquareRootThreshold/AnExplicitClusterDetectorConstant.lean`:

- `zeta_unit_count_le_240`;
- `not_hodgeIndex_of_explicit_cluster_aperture` and `exists_smooth_explicit_cluster_detector`;
- `not_hodgeIndex_of_explicit_product_aperture` and `exists_smooth_explicit_product_detector`;
- `exists_smooth_detector_at_explicit_product_aperture`;
- `depth_lt_explicit_of_hodgeIndex`.

Direct source check and all seven transitive axiom audits passed: only `propext`,
`Classical.choice`, and `Quot.sound`. Dependency closure is acyclic; umbrella import added.
