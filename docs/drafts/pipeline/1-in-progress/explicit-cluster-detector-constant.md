# Explicit cluster-detector constant

- **ID:** explicit-cluster-detector-constant
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** review-0411 §2.1, A27.

## Target

Replace the existential local-count constant in the cluster detector by a numeral.
Candidate: `N(t,t+1]≤240 log(|t|+3)` for every real `t`, hence detector aperture
`480000 log(|γ|+3) log(10⁶/δ)` for `|γ|≥102` and depth at least `δ>0`.

## Proof

Centre the unit interval at `T=t+1/2`. When `|T|≥4`, the existing xi-copy count is
`40 log(180|T|)`. Since `180|T|≤(|t|+3)^6`, this is at most
`240 log(|t|+3)`. When `|T|<4`, the whole interval lies in the proved zero-free
band `|Im ρ|≤9/2`. Equality of xi and zeta multiplicities transfers the count.
The existing sub-Nyquist detector then gives the explicit aperture and its inverse
height/depth laws, without assumptions on separation or multiplicity.

## Lean status

The missing bridge is the finite xi-copy realization of the zeta window count.
The generic detector's hypotheses must be discharged with the numeral `240`.
