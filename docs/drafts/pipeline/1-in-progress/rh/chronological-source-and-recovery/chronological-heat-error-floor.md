# Chronological heat error floor — frozen attack

Original bounded-array convergence target [R] remains unchanged and open.
This attack tests whether the rapid finite numerical decay can persist.

**Frozen [C].** For r(t)=e^(−t)+Σ_(k≤N)a_k h(kt), h(t)=1/t−1/(e^t−1),
|a_k|≤C, and A=1+CN, every critical-line zeta zero ρ should give

G ≤ 4A/K + 2||r||₂ sqrt(log K),  K>1,  G=|Γ(ρ)|>0.

Choosing K=1+8A/G then gives
||r||₂ ≥ G/(4 sqrt(log(1+8A/G))). For fixed coefficient budget this is
a logarithmic error floor, excluding any persistent positive power of N decay.
It permits convergence to zero and does not prove or disprove [R].

**Proposed proof to audit.** The actual Mellin integral of r at ρ equals Γ(ρ),
because the Mellin transform of each h dilation vanishes. Bounds |r(t)|≤A and
|r(t)|≤A/t control the integrals below K^(−2) and above K² by 2A/K each.
Cauchy–Schwarz bounds the middle by 2||r||₂ sqrt(log K).

**Status:** [C], its unconditional existential specialization, and the cost
corollary are formalized. Both leaf builds and all 15 public axiom audits pass;
only standard axioms occur. Formal lint passes. `HardyDyadicWindowTheorem` supplies a
critical-line zero unconditionally, with only standard axioms. `FusionMellin`
supplies the actual Bose transform. No numerical zero ordinate enters the proof.
No new experiment is needed for this attack.

**Proved cost corollary:** if ||r||₂≤η and η>0, then
G(exp((G/(4η))²)−1)≤8(1+CN). This follows by squaring the positive lower
bound, exponentiating, and rearranging. Thus geometrically decreasing error
as a function of repair depth requires a doubly exponential arithmetic cutoff
at fixed positive C. This is a constraint on possible constructions, not [R].

**Positive survivor obtained:** an explicit error floor and exponential cutoff
cost for every bounded coefficient vector. These exclude persistent power-rate
decay in N while permitting the original convergence target. The next hard task
is still to construct a bounded array with full L² decay. No novelty claim;
the Mellin zero mechanism belongs to classical Nyman–Beurling lower bounds.
[Paper proof and full certificate](../../../3-formalized/chronological-heat-error-floor.md).
