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

The exact identity `M₂=E/3+(∫xF)²` cancels the `E/48` term, leaving

`ΓE+J∞≥∫₀¹D/t−(γ+logπ+log2)E−M₁/24−(∫xF)²/16`.

Since `M₁≤3E/4` and `(∫xF)²≤E/12`, the uniform Gamma loss is now
`7/192`, improving `5/96` by `1/64`. The source-dependent bound retains more information.

For `H(x)=∫_{−1}ˣF`, the exact first moment is `M₁=E/2+∫H²`.
Integration by parts gives `∫xF=−∫H` and `sinhPairing F=−∫H cosh(x/2)`.
Thus the Gamma correction and odd pole share one primitive:

`ΓE+J∞−½(sinhPairing F)² ≥ ∫₀¹D/t−(γ+logπ+log2+1/48)E
 −(∫H²)/24−(∫H)²/16−½(∫H cosh(x/2))²`.

**Lean:** in `WindowTowerOfSpecZ.TheGammaComparisonRetainsItsLagMoments`,
`unit_odd_gamma_lag_moments_lower`, `unit_odd_gamma_position_lower`, and
`unit_odd_gamma_jump_second_moment_lower` give the lag and uniform bounds;
`unit_odd_gamma_primitive_lower` and `unit_odd_gamma_pole_primitive_lower` give the primitive bounds.
The position and pole identities are `unit_odd_position_eq_primitive_integral` and
`unit_odd_sinhPairing_eq_primitive_cosh`. Individual `lake --old env lean` source check passes;
transitive axioms are `[propext, Classical.choice, Quot.sound]` only.
Joint payment with the signed prime reflection remains open.
