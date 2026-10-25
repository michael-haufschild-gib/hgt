# Vaughan admission at and above half damping

- **ID:** vaughan-admission-at-and-above-half-damping
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** ../2-fully-proven/vaughan-admission-phase-transition-at-half-damping.md
- **Verification:** Both repository leaves passed producing and final direct Lean checks. All twenty audit targets depend only on `propext`, `Classical.choice`, and `Quot.sound`; umbrella imports are present.

## Exact statements

At every `ε≥1/2`, the actual Bézout interior has a finite uniform pronic norm
bound. At `ε=1/2`, the smooth square-root row instead has exact squared norm
`Σ_(1≤n≤T)1/(n+1)`, which diverges. The fixed Vaughan packet is admitted
exactly when its linear and smooth coefficients vanish. For positive cutoffs,
this says `L_w=0` and `w₂=w₃`; the admitted space has dimension three and its
coefficient quotient has dimension two.

For `ε>1/2`, the divisor-square floor majorant has finite critical Wiener
mass `W=Σ_(d≥1)τ(d)²d^(-ε-1/2)`. Each of the first three centered pieces has
norm at most `B_F=(√2+1)W`. The pole correction has norm at most `1/2`.
The exact five-piece sum therefore gives the common bound
`B_I+3B_F+1/2` for every piece, uniformly in both cutoffs and horizon.
Every centered packet has norm at most this bound times `Σ_i|w_i|`.
Admission is precisely the kernel of the nonzero linear-mean functional,
with dimension four and quotient dimension one, including zero cutoffs.

## Lean declarations

`BezoutValuationIncidence/VaughanAdmissionAtHalfDamping.lean`:

- `exists_pronicNorm_pmBezoutInteriorPrefix_le_of_half_le`
- `sq_pronicNorm_smooth_half`
- `not_exists_pronicNorm_smooth_half_bound`
- `pmPronicVaughanPacketSmoothMean_half_eq_zero_of_admitted`
- `pmPronicVaughanPacketAdmitted_half_iff`
- `pmPronicVaughanPacketAdmitted_half_iff_of_pos_cutoffs`
- `pmPronicVaughanAdmittedSubmodule_half_eq_full_span`
- `finrank_pmPronicVaughanAdmittedSubmodule_half`
- `finrank_pmPronicVaughanAdmittedQuotient_half`

`BezoutValuationIncidence/VaughanAdmissionAboveHalfDamping.lean`:

- `criticalWiener_of_vaughan_floor_majorant`
- `pronicNorm_weightCenteredPrefix_le_vaughan_floor_majorant`
- `pronicNorm_pmPronicVaughanCentredPiece_small_le_of_half_lt`
- `exists_uniform_pronicNorm_pmPronicVaughanCentredPiece_bound_of_half_lt`
- `exists_uniform_pronicNorm_pmPronicVaughanCentredPacket_bound_of_half_lt`
- `pmPronicVaughanPacketAdmitted_iff_of_half_lt`
- `pmPronicVaughanLinearMeanMap`
- `pmPronicVaughanLinearMeanMap_ne_zero`
- `pmPronicVaughanAdmittedSubmodule_eq_ker_of_half_lt`
- `finrank_pmPronicVaughanAdmittedSubmodule_of_half_lt`
- `finrank_pmPronicVaughanAdmittedQuotient_of_half_lt`

## Scope

The parent card's independent joint Gram limits and exact infinite-matrix
ranks remain separate verification obligations. These admission theorems do
not establish receiver admission below half damping or a fixed zero-free strip.
