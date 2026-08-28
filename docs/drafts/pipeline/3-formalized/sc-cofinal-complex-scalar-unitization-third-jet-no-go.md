# SC cofinal complex-scalar unitization third-jet no-go

- **ID:** SC-CCSUTJ-1
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `rh-current-frontier-map.md` route SC; map is read-only
- **Statement:** No arbitrary complex scalar sequence can make the complete coefficient-faithful holomorphic SC reservoir converge compact-open to normalized centered Xi.

## Hard frontier target

For `c : ℕ → ℂ`, set

`Vₘᶜ(z) = det(I + cₘ Rₘ diag(B_{p_i}(z)))`, `i : Fin (m+3)`.

Real-scale sign coherence is unavailable: phases `cₘ^k` can cancel distinct odd exterior degrees at fixed nonzero `z`. The proposed invariant is instead the central jet filtration, which prevents cross-degree cancellation.

## Conjecture loop

### C1 — exact isolated central jets

`(Vₘᶜ)''(0) = -2 cₘ² e₂(q)` and `(Vₘᶜ)'''(0) = 12 cₘ³ e₃(q)`, where `q_i = 2 F_{p_i} log p_i > 0`.

Reason: Bocksteins are odd and vanish at zero. At derivative order `r`, only exterior degree at most `r` survives; the reservoir singleton coefficient is zero. Degree two is even and has zero third jet, so the cubic layer is isolated exactly.

### C2 — diffuse elementary-symmetric lower law

Let `Sₘ = Σ_{i<m+3} q_i`. Prove `Sₘ → ∞`, `q_i ≤ 2`, and eventually

`12 e₃(q) ≥ Sₘ³`.

Newton–Girard gives `6e₃ = S³ - 3S P₂ + 2P₃`; boundedness gives `P₂ ≤ 2S`, while eventually `S ≥ 12`. Euler divergence supplies `Sₘ → ∞` because `q_i` dominates a positive constant times the enumerated reciprocal-prime sequence.

### C3 — complex-scale exclusion

Compact-open convergence to even normalized Xi forces the third central jets to zero. C1–C2 then force `|cₘ| Sₘ → 0`. The fermionic bound `2e₂ ≤ Sₘ²` forces the quadratic central jets to zero, contradicting the strictly negative normalized-Xi second central jet.

## Hostile falsification

1. Allow arbitrary complex phases and oscillations; no subsequence phase selection may enter the theorem.
2. Check degree-two third-jet contamination from individual Bockstein third derivatives; it vanishes because a product of two odd entire functions is even.
3. Check whether `e₃` can be sparse despite divergent mass; Newton–Girard plus the global `q_i ≤ 2` bound blocks concentration once `Sₘ ≥ 12`.
4. Do not claim matrix-valued or singular shifts: they remain the positive survivor after this class.

## Novelty audit

- **Internal corpus:** search found the new real-scalar theorem and generic rank-one reservoir infrastructure, but no complex cofinal scalar theorem, exact SC third central jet, or RH-facing `e₃/e₂` compact-open dichotomy.
- **External primary literature through 2026-08-28:** rank-one perturbation work treats spectra, eigenvalue placement, Jordan/Kronecker structure, and complex perturbation parameters; targeted search found no prime Gamma-Bockstein central-jet filtration or normalized-Xi obstruction.
- **Status:** `[PROVED HERE] [FORMALIZED IN LEAN] [INTERNALLY NOVEL] [EXTERNALLY UNVERIFIED BEYOND TARGETED PRIMARY-SOURCE SEARCH]`.

## Closed proof

1. `six_mul_sum_powersetCard_three_eq_powerSums` transports the corpus Newton--Girard identity to arbitrary real finite packets.
2. `preDivisorHolomorphicPrimeNeutralJet_le_two` proves the uniform atom cap `q_i ≤ 2`.
3. `not_summable_preDivisorHolomorphicPrimeNeutralJet_nthPrimePoint` and `tendsto_neutralJet_packetSum_atTop` prove `S_m → ∞` from the corpus reciprocal-prime divergence theorem.
4. `sum_pow_three_le_twelve_mul_sum_powersetCard_three` proves `S³ ≤ 12e₃` once `S ≥ 12`.
5. Exact product-jet filtration gives
   `V_m''(0) = -2c_m²e₂(q)` and `V_m'''(0) = 12c_m³e₃(q)`.
6. Third-jet convergence to even normalized Xi forces `‖c_m‖S_m → 0`; the fermionic degree-two bound then forces `V_m''(0) → 0`, contradicting normalized Xi curvature.

## Sharp boundary / survivor

The complete coefficient-faithful holomorphic SC reservoir admits no compact-open normalized-Xi landing under any scalar spectral shift, real or complex. Any surviving SC unitization must leave this mechanism class by introducing genuinely non-scalar cross-prime coupling, a singular limit, or a nondeterminantal landing. This architecture boundary is exact; phase oscillation and arbitrary scalar decay are no longer survivors.

## Lean status

- Module: `GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicCofinalComplexScalarUnitizationNoGo`
- Final theorem: `RHTower.not_tendstoLocallyUniformly_normalizedXiC_of_cofinalComplexScalarUnitization`
- `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalHolomorphicCofinalComplexScalarUnitizationNoGo.lean`: pass.
- `lake build GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicCofinalComplexScalarUnitizationNoGo`: pass (`13292/13292`).
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella: wired into `GaloisForLFunctions.RHTower` without building the umbrella.
- Global lint: new module reachable and contains no forbidden declaration; repository lint remains red only because unrelated concurrently-added modules are unreachable from their umbrellas.

## Log

- 2026-08-28 — created from strongest positive survivor of SC-CSUD-1; corpus and primary-literature audits complete; frontier map untouched.
- 2026-08-28 — C1 closed: exact second and third central jets formalized for arbitrary complex phases.
- 2026-08-28 — C2 closed: actual prime neutral-jet packet mass diverges and satisfies eventual cubic `e₃` coercivity.
- 2026-08-28 — C3 closed: complex scale collapses in neutral-jet mass, forcing quadratic-curvature contradiction.
- 2026-08-28 — promoted to stage 3; leaf source check, leaf build, umbrella wiring, and axiom audit pass.
