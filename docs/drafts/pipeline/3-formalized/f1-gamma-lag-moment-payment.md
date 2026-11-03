# Gamma payment retaining the two lag moments

- **ID:** F1-GM
- **Stage:** 3-formalized
- **Type:** THEOREM; individually Lean-audited
- **Source:** [Regional reflection payment](../1-in-progress/f1-regional-reflection-payment.md)
- **Statement:** For every real odd C² test supported in `[-1/2,1/2]`, put `E=∫F²`,
  `C(t)=∫F(x)F(x+t)dx`, `D=E−C`, and `Mⱼ=∫₀¹tʲD(t)dt`. Then

`ΓE+J∞≥∫₀¹D(t)/t dt−(γ+logπ+log2)E+E/48−M₁/24−M₂/16`.

## Proof

Oddness gives `∫₀¹C=0`, hence `∫₀¹D=E`. The nonnegative deficit and
`2ω(t)≥1/t+1/2−t/24−t²/16` give the interior jump lower bound
`∫₀¹D/t+E/2−M₁/24−M₂/16`. Outside the support, `C=0`, and the tail contributes
at least `(2log2+π/2−1/2+1/48)E`. Adding
`Γ=−γ−logπ−3log2−π/2` proves the inequality.
All integrals exist: the C² compact source controls the logarithmic singularity;
ordinary moments have continuous integrands on a compact interval.

The existing uniform estimate replaces `M₁` by `3E/4` and `M₂` by `2E/3`.
The retained bound preserves precisely those discarded nonnegative differences.

**Lean:** `WindowTowerOfSpecZ.TheGammaComparisonRetainsItsLagMoments` proves
`unit_odd_gamma_lag_moments_lower`. Individual `lake --old env lean` source check passes;
transitive axioms are `[propext, Classical.choice, Quot.sound]` only.
The moment identities and joint low-moment/prime payment remain open formal obligations.
