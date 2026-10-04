# Literal reciprocal sine response: growth and vanishing boundary

- **ID:** LI-CLOCK-SINE-GROWTH-BOUNDARY
- **Stage:** 2-fully-proven; literal sine identity formalized, growth consequences paper-only
- **Type:** THEOREM (paper); unconditional positive survivor and conditional classification
- **Parent:** [actual-current route](../1-in-progress/li-actual-current-small-mass-sinc-scaling.md)
- **Prior work:** [complete-source Volterra positive mass](../3-formalized/li-actual-clock-volterra-positive-mass.md)

## Source identity and strongest survivors

With `S(w)=liEvenCrossActualCurrentClockSeries w`, `F(t)=tS(t²/16)`, `α_q=xiSpectralPoint q`, `r_q=α_q⁻¹`,

`F(t)=Σ_(q:XiZeroCopy) r_q sin(t r_q)`.

Every analytic multiplicity copy contributes once. No square-root branch is used. Source symmetries make the complex sum real; `t=4√w` for `w≥0`.

Unconditionally, `∀B,T₀ ∃t>T₀, F(t)>B`, and `liminf_(w→∞)|S(w)|=0`. These strengthen divergent positive-part mass and rule out a nonzero uniform absolute tail margin. They give no pointwise source sign or RH producer.

## Complete-source interchange

Literal source moment APIs identify `(M_j:ℂ)=Σ_q r_q^(2j+2)`. Compact absolute double-sum domination is

`Σ_qΣ_j |r_q|^(2j+2)T^(2j+1)/(2j+1)! ≤ A T Σ_j(T²/150)^j/(2j+1)!`,

where `A=Σ_q|r_q|²<∞`. Thus the entire sine Taylor series interchanges with every multiplicity copy, matching the already formalized F series. Required APIs: `XiEndpointCentralMomentBoundaryValue.ofReal_normalizedPrimeArchMoment_eq_xiCentralReciprocalMoment`, `XiRelativeResolventTrace.tsum_xiZeroCopyReciprocalSquare_pow`, `XiCanonicalProduct.xiSpectralPoint_inv_sq_summable`, and the exact second-moment radius.

## RH branch

Real reciprocal frequencies give `S(w)=Σ_q r_q² sinc(4√w r_q)→0` by summable domination. Positive ordinates have exact multiplicity response `F(t)=2Σ_(γ>0)m_γ sin(t/γ)/γ`.

In fact `(1/T)∫₀ᵀF(t)dt=(1/2)log T+O(1)`. For `N(y)=xiZeroCount y`, exact ordinate gap excludes zeros below 10, and integration yields `(2/T)∫_[10,∞)(1−cos(T/y))dN(y)`. Put `Q(y)=y/(2π)log(y/(2πe))+7/8` and `E=N−Q`; existing RVM theorem gives `|E(y)|≤C log(y+2)` after enlarging C on the initial compact interval. Integration by parts leaves error bounded uniformly by `4|E(10)|/T+2∫₁₀∞|E(y)|/y²dy`. Upper boundary vanishes. In the smooth Q term substitute `x=T/y`; integrable `(1−cos x)log x/x²` and tail bound `∫_U∞(1−cos x)/x²≤2/U` give coefficient `(1/π)∫₀∞(1−cos x)/x²dx=1/2`. Hence F is cofinally unbounded above under RH.

Multiplicity identification is `RiemannVonMangoldt.xiZeroCount_eq_pos_sum`; smooth normalization is in `XiPrimeMarkedPhysicalEndpointRVMRelocation`; remainder is in `XiZeroCountRVMRemainder`. The Stieltjes/mean transfer is paper-only.

## Non-RH branch

Square summability implies reciprocal frequencies tend to zero cofinally. Therefore the positive maximum `b=max_q|Im r_q|` is attained by a finite packet, with a strict remainder gap `b₂<b`. Reflection/conjugation preserve analytic multiplicity; the real-coordinate source gap excludes zero real frequencies.

Top quartets with frequencies `a_ℓ+ib`, `a_ℓ>0`, and weights `m_ℓ>0` give

`F(t)=e^(bt)P(t)+o(e^(bt))`, `P(t)=2Σ_ℓm_ℓ[a_ℓ sin(a_ℓt)−b cos(a_ℓt)]`.

Remainder is bounded by `L e^(−bt)+A t e^(b₂t)`. Distinct positive frequencies give zero mean and positive mean square for P, forcing fixed cofinal positive and negative amplitudes. Thus S has limsup `+∞`, liminf `−∞`, and cofinal zeros, **conditional on failure of RH**. Continuity of S is already formalized. Combining branches gives the unconditional survivors above.

## Novelty and limits

Reciprocal sine growth uses classical mechanisms; RH-equivalent decay/boundedness is a terminal divisor classification, not an independently proved source constraint. Prior actual Euler-jet oscillation concerns a different germ and supplies no negative literal S witness. No RH proof/falsification or world-novelty claim.

## Plan

1. Formalize branch-free literal sine identity and complete-source absolute interchange — complete in [sine-source card](../3-formalized/li-actual-clock-reciprocal-sine-source.md); all 12 public axioms foundational, final exact check passed.
2. Formalize real-frequency decay under RH — complete in `LiEvenCrossActualClockSineDecay.lean`; all four public axioms foundational, named build and final exact check passed. RH remains an explicit premise.
3. Finite attained top-frequency packet and strict tail gap are formalized in `LiEvenCrossActualClockTopFrequency.lean`, from `¬RiemannHypothesis`, with all multiplicity-copy ties included. Named build, final exact check and all nine public axiom audits passed. Oscillatory amplitudes and exact RVM mean transfer remain paper-only.
4. Promote only exact unconditional capstones after named builds, direct checks and axiom audits.

## Log

- 2026-09-30 — Independent literal-source audit closed multiplicity normalization, both branches and exact mean-law remainder. Root checked existing source series and original packet scope. New consequences remain paper-only; card recorded before hard Lean work.
- 2026-09-30 — Branch-free full complex sine identity and absolute double-series interchange formalized, named build and final direct checks passed. RH decay and finite top-frequency isolation assigned to disjoint leaves; growth/mean transfer remain paper-only.
- 2026-09-30 — Literal RH-conditional decay is Lean-closed by complete squared-weight DCT. Structural [unbounded-support alternative](../3-formalized/li-clock-unbounded-support-response-growth.md) is independently paper-audited twice for the unconditional cofinal-unbounded survivor, avoiding the RH/RVM case split; stronger all-R kernel growth and unconditional cofinal response height are now Lean-closed in three leaves, with all 12 public axiom audits foundational. Signed non-RH packet asymptotics and RH RVM mean remain paper-only.
