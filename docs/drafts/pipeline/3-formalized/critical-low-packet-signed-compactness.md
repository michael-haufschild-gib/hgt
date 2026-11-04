# Signed compactness of the growing critical low packet

- **ID:** critical-low-packet-signed-compactness
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [critical-ratio continuation](../1-in-progress/critical-ratio-continuation.md)

## Exact target

Let c_N≥1 and c_N⁸/log N→R>0. Put Q_N=floor((log N)^(13/32)),
E_m=completedConductorEnergy(tiltedUnitSpline,c_N,m),
v_m=normalizedRamanujanHorizonVector(m,N), aφ=(∫φ)²/∫φ²,
and g=2+γ−log(4π)>0, with φ the tilted spline.
For every ε>0, eventually in N, uniformly over real coefficients b,

    |⟨B_N Σ_(m≤Q_N)b_m v_m, Σ_(m≤Q_N)b_m v_m⟩
       − Σ_(m≤Q_N) E_m b_m² − aφ g(c_N/log N)b_1²|
      ≤ ε Σ_(m≤Q_N) E_m b_m².

This removes the small-R restriction on the entire growing low
packet used by the existing whole-space assembly. The intermediate
bands and coupling to the horizon complement remain separate obligations.

## Corpus mechanism

`exists_completeWeil_bilinear_conductor_residual_log_free` bounds the
actual residual pairing by

    C[m²l² c/log N + (ml)⁵ c⁵ log N/N].

`tiltedUnitSpline_completedConductorEnergy_ge_conductor_scale` gives
E_m≥κ m⁷/c⁷ for 1≤m≤c, with κ>0 independent of the conductor.
Consequently the energy-normalized residual, after subtraction of its
positive polar term, has a uniform envelope

    C_R m^(-3/2) l^(-3/2),

eventually in N. For the second residual term use (ml)³≤c⁶ and
c¹⁸ log N/N→0. The polar subtraction is supported only at (1,1).
The envelope is summable over positive conductor pairs.

For the subarray m,l≤c_N, the checked signed fixed-pair limit from
[the Gamma–center calculation](../1-in-progress/critical-gamma-center-signed-limit.md)
makes every entry of this normalized remainder tend to zero. Extending
that subarray by zero outside m,l≤c_N, dominated convergence makes
its total absolute entry sum tend to zero. This controls every
coefficient vector simultaneously. Fixed-pair convergence alone would
not justify that passage; the summable conductor envelope is essential.

Equivalently, square the normalized entries and dominate by
C_R/(m³l³). This avoids fractional powers in the transfer proof and uses
the existing energy-weighted Cauchy–Schwarz argument.

More precisely, write r_ml for the literal vector residual paired with
v_l, and set d_ml=r_ml−ag(c/log N)δ_m1δ_l1. Below overlap,

    |c⁷ r_ml| ≤ C m²l²[c⁸/log N+c¹⁸ log N/N],
    c⁷ E_m ≥ κ m⁷.

Eventually c⁸/log N≤R+1 and c¹⁸ log N/N≤1. Thus
|c⁷d_ml|≤B_R m²l², with B_R=C(R+2)+|ag|(R+1), and
d_ml²/(E_m E_l)≤(B_R/κ)²/(m³l³). For each fixed positive pair,
c⁷d_ml→0 while c⁷E_m→J(m)>0. Extending by zero outside the moving
square m,l≤c_N gives the precise summable array to which dominated
convergence applies. Its sum controls every finite subpacket below c_N.
The array, simultaneous admissibility, envelope, and limit in
`TheSignedCriticalResidualIsCompactBelowOverlap.lean` pass the final
actual-path no-olean audit with `[propext, Classical.choice, Quot.sound]`.

For c_N<m≤Q_N or c_N<l≤Q_N, use
`exists_tiltedUnitSpline_bilinear_conductor_residual_variable_rate` and
the constant energy floor above overlap. The same sums used in
`packetRelBilin_high_sum_le` have a strictly negative logarithmic
exponent: before its small logarithmic losses, the mixed contribution
has scale c⁹Q_N²/(log N)²=O_R((log N)^(-1/16)); the high-high
contribution has scale c²Q_N⁴/(log N)²=O_R((log N)^(-1/8)).
Their decay survives every fixed multiplicative constant in c_N.

A concrete uniform bound uses c_N≤L^(129/1024), eventually for every
fixed R. The variable-rate estimate at k=128 has rate
≤65537 L^(−879/1024); the inverse-energy sums are bounded by
3L^(903/1024)/κ and 65544L^(903/1024)/κ. Since
Q²(1+log L)²≤65536L^(840/1024), the two high-pair sums together are
at most

    (K²/κ²) 65537²·262152 L^(−15/1024).

The polar subtraction vanishes whenever one conductor exceeds c≥1.
`TheSignedCriticalResidualAboveOverlapDecays.lean` verifies this estimate
and its all-R limit; its final no-olean audit passes with
`[propext, Classical.choice, Quot.sound]`.

The residual is defined relative to E_m⟨v_m,v_l⟩, whereas the target
uses the diagonal E_m[m=l]. The public polarized Gram discrepancy
`CompletedArithmeticForms.abs_inner_sum_normalizedRamanujanHorizonVector_sub_le`
and the energy bounds used in
`spectralFloorWeilMatrix_subspace_inner_ge_of_bilinear_budget` give a
relative Gram error O(c⁴(1+log Q_N)²/log N). This tends to zero at every
fixed R. Its unrestricted critical specialization is formalized in
`eventually_energy_weighted_gram_low_packet_le`.

The coefficient transfer is finite Cauchy–Schwarz. Set
t_m=sqrt(E_m)b_m and u_ml=d_ml/sqrt(E_m E_l). Then

    |Σ b_m b_l d_ml|² ≤ (Σ E_m b_m²)² Σ d_ml²/(E_m E_l).

The whole packet square is bounded by the below-overlap square plus the
two high-pair sums above. For the Gram term use E_m≤C(1+log Q) and
E_m≥κ/c⁷; polarized Gram discrepancy gives relative factor
9(C/κ+1)(1+log Q)²c⁴/L. On c≤L^(129/1024), this is eventually
≤L^(−1/4). Finally, the literal complete form decomposes as
the energy-weighted Gram form, the signed residual pairing, and
ag(c/L)b₁². These bounds yield the displayed ε approximation and,
since ag≥0, an eventual lower bound (1/2)ΣE_m b_m² at every fixed R.
The complete transfer in `TheCriticalLowPacketRetainsItsSignedPolarPart.lean`
passes its actual-path no-olean check with
`[propext, Classical.choice, Quot.sound]` for all five audited endpoints.

## Attack and open core

- The complete signed fixed-pair limit passes its actual-path no-olean audit.
- Simultaneous horizon and row-radius admissibility, the high-pair
  estimates, the weighted Gram estimate and the coefficient transfer
  are formalized without a small-R premise. Both array modules and the
  complete transfer pass their final actual-path no-olean checks.
- The summable envelope handles only pairs below overlap; the separate
  variable-rate estimate handles the rest of the low packet. Neither
  pays the dual seventh-power collar norm. No whole-space conclusion follows.

The separate complement reserve loses C_S c times weighted collar mass
against a reserve of order (log N)/c⁷. Its prefix-pole/window payment also
retains a c¹⁶/(log N)² loss. These are respectively R and R² at critical
scale (`exists_critical_multiple_far_reserve`). The summable conductor
argument does not alter either loss. Source drafts for coherent charge
receivers provide a further stress test: vanishing input energy can
coexist with nonzero mixed complete-form pairing on a polynomially growing
conductor cutoff. That scale lies outside the present polylogarithmic
packet; it prevents inferring complement control merely from small input
energy.

Verdict: `BRIDGE` within the local corpus. The advance is uniformity
on a specified growing arithmetic packet at every
positive critical ratio. No new general dominated-convergence principle
or external novelty claim is proposed.
