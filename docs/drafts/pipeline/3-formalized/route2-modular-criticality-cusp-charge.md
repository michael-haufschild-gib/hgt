# ξ is critical inside the positive exactly-modular source class (cusp-charge law)

- **ID:** route2-modular-criticality-cusp-charge
- **Stage:** 3-formalized
- **Type:** THEOREM [L] (all clauses), no-go for route 2 steps 5–6
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

## Lemma chain (as proved; parameter `a = sin(η/2) = t²`, `b = √(1−a²)`, `u = 7π/(8a²)` exact saddle)

- L0 [L] `norm_thetaForm_farey` (ThetaModularFareyBound).
- L1 [L] `modXi_eq_tailTransform` (ThetaGroupCuspChargeTail): `Ξ_F(w) = −(w²+¼)∫e^{−iwx}T(x)dx`.
- L2 [L] `integral_tail_shift` (ThetaCuspChargeContourShift): shift to `Im = −β`, `β = π/4 − arcsin a`.
- L3a [L] `thetaGroupBasis_one_window`, `norm_chargeErr_le` (ThetaCuspChargeWindowLaw):
  `θ₃h(1−1/v) = −(−iv)^{1/2}2⁻⁷e^{−7πiv/4}(1+ε(v))`, `|ε| ≤ 1/8` for `Im v ≥ 4`.
- L3b [L] (ThetaCuspChargeSaddleGeometry) exact closed forms, `σ = 2 sinh s`:
  `R₀ − ReΨ = 7πbσ²/(8a(σ²+4a²))`, `ImΨ + 7π/8 = (7π/8)(a²(σκ−4s) − sσ²)/(a²(σ²+4a²))`,
  `P(0) = (2a)^{−1/2}e^{−iθ/2}`, `|A| ≤ 1`, `|A−1| ≤ 10|s|/t²`, `|φ| ≤ 10|s|³/t⁸`.
- L3c [L] `chLine_eq`, `half_le_re_chLine_core` (ThetaCuspChargeSaddleWindow): exact factorization
  `g = g₀e^{ReΨ−R₀}·A·e^{iφ}(1+ε)` (unit phase at `s=0` is exactly 1); `Re g ≥ g₀e^{ReΨ−R₀}/2` on `|s| ≤ 144t³`.
- L4 [L] `norm_chLine_far` (ThetaCuspChargeFarField): `|s| ≥ 2a` ⇒ `|g| ≤ B_far e^{−|s|}`,
  `B_far = max(3⁸2⁷κ⁻³e^{R₀/3}/2, M/(2πκ))`; odd cusps give `|cτ+d|² ≥ 12ρa⁴`.
- L5 [L] `re_chLineInt_ge`, `exists_re_chLineInt_pos`, `norm_XiC_ofReal_le_strip`,
  `cuspCharge_dominance_chU`, `cuspCharge_law`, `XiC_le_eps_thetaGroupXi_one`.
- L6 [L] `thetaGroup_charge_critical` (ThetaCuspChargeCriticality): three Hardy zeros give a real
  minimizer of `Ξ/Ξ₁` with value `≤ 0`; open mapping gives the nonreal zero.
- L7 [L] `exists_charge_source_domination`, `thetaGroup_modular_criticality`
  (ThetaCuspChargeModularCriticality).
- Renewal clause [L] `thetaGroup_modular_criticality_full` (ThetaCuspChargeRenewalIncrement): `ν_F(2x)/2 = −e^{x/2}pF'(p)`
  (canonical: `ν_θ₃ = 2πΣn²e^{(5/4)t−πn²e^t}`), reflection law `ν(−x)+ν(x) = e^{x/2}F(p)/2`, `|ν₁| ≤ Cν₀`.

## Lean certificate

`RHTower.thetaGroup_modular_criticality_full`: all clauses (source real > 0, renewal increment real > 0, off-line strip zero).
`RHTower.thetaGroup_modular_criticality {ε} (hε : 0 < ε) : ∃ s, 0 < s ∧ s < ε ∧
(∀ x, (modSource (thetaGroupDeformation s 0) x).im = 0 ∧ 0 < (modSource (thetaGroupDeformation s 0) x).re) ∧
∃ z, 0 < z.im ∧ z.im < 1/2 ∧ modXi (thetaGroupDeformation s 0) z = 0`.
`RHTower.cuspCharge_law : ∃ U > 0, ∀ u ≥ U, (Ξ₁ u).re < 0 ∧ ‖Ξ u‖ ≤ 2¹⁶·3·10⁶·10!·(7π/(8u))^{1/4}‖Ξ₁ u‖`.
Axioms: `propext, Classical.choice, Quot.sound`. Lint gate passed. 12 modules wired into `RHTower.lean`.

## Log
- 2026-09-26 — frozen; plan written; saddle computed on paper.
- 2026-09-26 — L0 in Lean (`ThetaModularFareyBound`: SL₂(ℤ) modulus law, parity classification, 𝒟 bounds).
- 2026-09-26 — L1–L7 in Lean. Exact saddle `u = 7π/(8 sin²(η/2))` (not `7π/(2η²)`): Ψ'(0)=0 and Ψ''(0) real exactly.
  Sharp `Ξ` decay needed its own shifted-line bound (corpus rate `δ < π/4` is too weak); done via explicit
  constant in the corpus strip bound + `thetaGaussianPowerSum ≤ 3k!2^k/γ^{k+1}`.
- 2026-09-26 — renewal clause in Lean; card complete. Successor: 3F/route2-charge-line-hardy-rigidity (all of θ₃·ℝ[h]).
