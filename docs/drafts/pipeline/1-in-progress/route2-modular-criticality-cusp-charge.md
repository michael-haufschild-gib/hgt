# ξ is critical inside the positive exactly-modular source class (cusp-charge law)

- **ID:** route2-modular-criticality-cusp-charge
- **Stage:** 1-in-progress
- **Type:** CONJECTURE → THEOREM (paper in progress), no-go for route 2 steps 5–6
- **Source:** route-proposals/route2.md claim (i), steps 5–6; 3F/route2-prime-two-cusp-rigidity.
- **Statement (frozen):** For every ε>0 there is t∈(0,ε) such that the source k+t·k₁
  (k₁ = source of θ₃h, h = θ₂⁴θ₄⁴/θ₃⁸) is positive, even, two-periodic in τ with the exact θ
  inversion law, has positive renewal increment, and its transform Ξ+tΞ₁ has a zero with
  0<Im z<½.

## Why it matters for route 2

Route 2 steps 5–6 ask whether a deformation/coupling argument can reach ξ. The seam card showed
criticality in the non-modular renewal-coupling family. This statement puts ξ on the boundary of
the off-line set inside the exactly modular, positive, renewal-positive class: no continuity or
positivity argument inside that class can confine zeros.

## Paper proof plan

1. **RH false:** Hurwitz near an off-line zero of Ξ gives off-line zeros of Ξ+tΞ₁ for all small t.
2. **Cusp-charge law (core).** With w=¼−iu/2 and η=√(7π/(2u)):
   Ξ₁(u) = −(u²+¼)/4 · e^{−i(π/2−η)w} ∫₀^∞ r^{w−1}F(re^{iη}) dr, F=θ₃h (ray rotation).
   Near r=1: F(1+s) = −2^{−7}(−is)^{−1/2}e^{7πi/(4s)}(1+O(e^{−π Im(−1/s)})).
   With s=r−1+iη the exponent Φ = 7πi/(4s) − (iu/2)(r−1) has a real saddle at r=1,
   Φ(1)=7π/(4η), Φ''=−7π/(2η³), Im Φ = O((r−1)³/η⁴). Main term
   ≍ e^{−πu/4+√(7πu/2)} u^{α}, real, fixed sign.
3. **Far field (circle method on the ray).** SL₂(ℤ) reduction τ ↦ γτ ∈ 𝒟 and the S,T laws of
   θ₂,θ₃,θ₄ give |F(τ)| ≤ C|cτ+d|^{−1/2} e^{(7π/4) Im τ/|cτ+d|²} when c,d are both odd, and
   ≤ C|cτ+d|^{−1/2} otherwise. On the ray arg τ=η away from r=1 the exponent is
   ≤ (7π/4)/(pqη) ≤ (7π/12)/η (pq≥3), strictly below the main term.
4. **Contact.** Ξ(u)=O(e^{−πu/4}u^A) (corpus strip decay) ⇒ R=Ξ/Ξ₁→0 on the real tail. Hardy:
   Ξ changes sign infinitely often, so R has components of one sign with extrema m_j→0.
   At a minimizer u*, R−m_j ≥ 0 on ℝ near u*, vanishes at u*; open mapping gives z near u* with
   R(z)−m_j = −δ, z∉ℝ. So Ξ+tΞ₁ vanishes at z for t=|m_j|+δ.
5. **Positivity.** k₁/k → 8 at ±∞ (leading atom 16e^{−πy} vs 2e^{−πy}), k>0 continuous ⇒
   k+tk₁>0 for |t|<1/sup|k₁/k|; same for the renewal increment.

## Log
- 2026-09-26 — frozen; plan written; saddle computed on paper.
