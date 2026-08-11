# Attempts 4–5 on the Hodge mass wall: seam unification + coherence budget (2026-08-11)

Card: `hodge-sign-wall-constructed-pairing` (stage 1). Modules (all wired, built, axiom-clean
`[propext, Classical.choice, Quot.sound]`, 17 theorems audited):
- `RHTower/GaussHodgeSeamEnergyBridge.lean`
- `RHTower/GaussHodgeCoherenceBudget.lean`
- hyperbolic comparison layer appended to `HTGeometry/HyperbolicBounds.lean`

## Attempt 4 (seam-energy pivot)
The Gauss-lane Hodge mass current H(q,p) and the Burnol FE–Schwarz seam reflection energy are
ONE invariant: seam density ‖seam(p,ρ)‖²/p = (log p)²p^{−2}(p^t+p^{−t}−2), t = 2Re−1; two-sided
domination vs hodgeMassShape with constants log p/2 (all rates) and 2√p/log p (|t|≤1); every
divisor copy proved in the open strip (`xiZeroCopy_re_mem_open_unit`). Chains: RH ⟺ prime-2
seam charge ≡ 0 on divisor ⟺ prime-2 burnolPrimeCharacter unimodular on divisor ⟺ full seam
energy ≡ 0 ⟺ divisor annihilates the moment-curve convexity defect M(1+2σ)+M(3−2σ)−2M(2)
(prime side COMPLETELY evaluated by the pre-existing seam layer). Info-gap impossibility:
`no_function_of_fePair_computes_hermitian` — the FE-pair channel is constant 1 (divisor-blind);
no function of it computes ‖char‖. The ∑g² vs ∑|g|² gap is now a theorem.

## Attempt 5 (classification + budget)
`hermitianSample_eq_conjugatePair_product`: char(ρ)·char(conj ρ) = p^{2Reρ−1} via
`xiZeroCopyConjEquiv` (point law rfl) — the missing transform IS the conjugate-pair diagonal of
a squared explicit formula (pair-correlation classification as a theorem).
`norm_sq_charSum_le_defectMass_add`: ‖Σ_F v·char‖² ≤ Σ‖v‖²·(defect mass + 2|F|) — the mass is
an exact coherence certificate; collapses to 2|F| under RH (square-root cancellation per
frequency).

## Successor gate (exact next open core)
Limit-exchange statement: vertical time-averaging extracts the conjugate-pair diagonal for
finite families (completed-time torus layer: TorusCharacterMean etc.) but yields the
multiplicity-SQUARED diagonal (gap closes on zero-simplicity, see
cauchy-core-density-is-zero-simplicity) and requires interchanging T→∞ with the divisor
closure (fenced by copoisson-mellin-truncate-first). External anchors: Suzuki screw function
arXiv:2206.03682; Connes–Consani Sonin positivity arXiv:2006.13771, arXiv:2310.18423.

Frontier map §3 and anchors updated; card carries attempts 1–5 with exact failure points.
Note: concurrent sessions fixed proof-level details in both new modules (imports,
pow_le_pow_left₀, field_simp endings) — statements unchanged. MEMORY.md index reorganized into
thematic hubs this session (253 → 11 lines, content preserved in hub files).
