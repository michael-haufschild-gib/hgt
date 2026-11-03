# Fifth even theta source: origin and tail repair

- **Stage:** 3-formalized
- **Wall:** Σ6; the rank-nine integrated sign remains open.
- **Lean:** `ThetaCuspSections/FifthEvenSourceRepair.lean`, imported by `ThetaCuspSections.lean`.

Write `m_k=(-1)^k D_t^(2k)[Φ(x+t)Φ(x−t)]|₀`, `H₅=[m_(i+j)]`, and
`G=3Φ²+2xΦΦ′`. Let `A=H₄+10¹²G e₃e₃ᵀ`, `b=(m₄,m₅,m₆,m₇)`,
`S=m₈−bᵀA⁻¹b`, and `D=(|S(0)|+Φ(0)²)/Φ(0)²`.

**Theorem.** The fixed matrix `H₅+10¹²G e₃e₃ᵀ+D G e₄e₄ᵀ` is strictly
positive near zero and on a cofinal ray. Replacing its weighted corrections
by derivatives of the center flux preserves every actual mixed moment and
gives the same two positive regions simultaneously for every positive
aperture. A correction confined to the fifth diagonal cannot repair zero.

**Proof.** The fourth native determinant at zero is negative and remains a
principal determinant under a fifth-diagonal correction. The fixed corrected
head `A` is positive. Since `G(0)=3Φ(0)²`, its fifth Schur coordinate becomes
`S(0)+3|S(0)|+3Φ(0)²>0`. Continuity supplies the interval at zero.
Gaussian balancing sends the two corrections to zero at scales `q⁶` and
`q⁸`; the limiting Gamma moment matrix is positive definite.

For `K_a(r)=r²sinh(ar)Φ(r/2)²`, the difference
`K_a′(r)−r sinh(ar)G(r/2)` is nonnegative when `a,r>0`. Both correction
coefficients are positive. Each corrected entry is integrable for
`0≤a<1/2`, and `∫₀∞K_a′=0`, proving entrywise preservation.

Main declarations: `evenFiveRepair_top_only_not_posSemidef`,
`evenFiveRepair_compact_gap`, `centerEvenFiveRepair_integral`, and
`centerEvenFiveRepair_compact_gap`. Canonical Lean check and all eleven
public-declaration axiom audits pass; only `propext`, `Classical.choice`,
and `Quot.sound` occur.

The intervening comparison is refuted by the
[inherited-load boundary](../5-failed/theta-cusp-fifth-even-inherited-load-boundary.md).
The origin and tail statements above remain valid; the integrated rank-nine
sign remains open.
