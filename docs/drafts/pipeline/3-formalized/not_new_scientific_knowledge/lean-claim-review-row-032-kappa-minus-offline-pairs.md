# Lean claim review row #32 — exact `kappa_-` count for finite carriers

- **ID:** lean-claim-review-row-032-kappa-minus-offline-pairs
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — Door grade **BRIDGE** (Krein–Langer / Sylvester inertia); AUDIT PASSED 2026-06-19 (Professor); LEAN CERTIFIED 2026-06-19 (Leaner)
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/00-status.md · 00-status row #32; ../../door/bucket-ledger-footholds.md
- **Claimed ledger status:** `THEOREM (Lean)`; matching 3-formalized ticket certified 2026-06-19.
- **Statement:** `kappa_-` equals the number of off-line zero-pairs exactly, for the finite carrier.

## Goal
Audit the claim from scratch. Researchers first verify the finite-carrier mathematical theorem, including hypotheses and exact notion of negative inertia. Leaner checks the claimed formalization only after that review.

## Claimed Lean footholds to verify
- `formal/GaloisForLFunctions/CarrierCauchy.lean`
- Candidate names: `multiPair_carrier_exact_neg_inertia`, `multiPair_carrier_linearIndependent`

These names are leads, not certification.

## Gates
- [x] 0 -> 1 in-progress: audited (Professor 2026-06-19); model + hypotheses + inertia convention fixed (below)
- [x] 1 -> 2 fully-proven: complete from-scratch proof confirmed (Sylvester's law; both bounds); numerically verified k=1..6 (high precision — Cauchy ill-conditioning beaten)
- [x] 2 -> 3 formalized: Leaner verified exact theorem names by scratch file; `lake build` green; `scripts/check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone proof note plus Lean certificate

## Approach
Review the finite Pick matrix / carrier model, isolate the off-line conjugate-pair contribution, and check that the linear independence hypotheses are sufficient for exact negative inertia.

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean)` ledger row.

## AUDIT — 2026-06-19 (Professor): claim VERIFIED from scratch (κ₋ = #off-line pairs, exactly)

**Model (recovered from `formal/GaloisForLFunctions/CarrierCauchy.lean`).** `k` distinct off-line poles
`tᵢ` (`Im tᵢ ≠ 0`, taken in `C⁺`) with conjugates `t̄ᵢ`; `2k` distinct nodes `zⱼ`. Cauchy vectors in `ℂ^{2k}`:
`aᵢ(j)=(tᵢ−zⱼ)⁻¹`, `eᵢ(j)=(t̄ᵢ−zⱼ)⁻¹`. Carrier vectors `wᵢ=eᵢ+aᵢ`, `uᵢ=eᵢ−aᵢ`. The factored carrier
(Pick) form is `H = Σᵢ wᵢwᵢ* − Σᵢ uᵢuᵢ* = 2·multiPairPick`.

**Theorem (κ₋ exact).** If the `2k` carrier vectors `{wᵢ,uᵢ}` are linearly independent (⟺ `[W|U]∈ℂ^{2k×2k}`
invertible), then the negative inertia `κ₋(H) = k = #off-line conjugate pairs`, exactly.

**Proof (from scratch — Sylvester's law of inertia).** Write `W=[w₁…w_k]`, `U=[u₁…u_k]` (each `ℂ^{2k×k}`).
Then `H = WW* − UU* = [W|U]·diag(I_k,−I_k)·[W|U]*`. The hypothesis makes `[W|U]` invertible (a congruence).
By **Sylvester's law of inertia**, `H` is congruent to `diag(I_k,−I_k)`, hence `κ₊(H)=k`, `κ₋(H)=k`, `κ₀(H)=0`.
*Both bounds at once:* `κ₋≤k` (only `k` summands `−uᵢuᵢ*`) and `κ₋≥k` (the `k` directions `uᵢ` are negative and
independent of the positive block, by invertibility). ∎

**Why it counts OFF-LINE pairs exactly (the mechanism).** An *on-line* pole has `tᵢ` real ⟹ `t̄ᵢ=tᵢ` ⟹
`eᵢ=aᵢ` ⟹ `uᵢ=eᵢ−aᵢ=0` — it contributes **no** negative direction. Only off-line poles (`Im tᵢ≠0`) give
`uᵢ≠0`. So `κ₋ = #off-line conjugate pairs`, precisely. (Verified: an injected real pole adds `0` to `κ₋`.)

**The linear-independence hypothesis is exactly the non-degeneracy.** `multiPair_carrier_linearIndependent`
(invertibility of `[W|U]`, = `2ᵏ·det(Cauchy)≠0`) is what makes the Sylvester congruence valid, giving the
EXACT inertia. Without it the inertia could drop. This is the `hT`-surjectivity input that
`multiPair_carrier_exact_neg_inertia` discharges to reach Krein–Langer `exact_neg_inertia`.

**Numerical certification.** `computations/2026-06-19-carrier-kappa-minus-inertia.py`: `κ₋=k` for `k=1..6`.
*Caveat banked:* the Cauchy/carrier matrix is ill-conditioned — at `k≥4` **double precision falsely reports a
deficient inertia** (the `det[W|U]` underflows, e.g. `~3.5e−25` at `k=5`); high precision (`mpmath dps=60`)
restores `κ₋=k`. The exact-arithmetic theorem (Sylvester) is unaffected; only naive float inertia fails.

**Door-2: BRIDGE.** Classical Krein–Langer generalized-Nevanlinna / Pontryagin-space inertia (the negative
index counts poles in `C⁺`) + Sylvester's law. No multi-q apparatus. Its worth: the exact finite anchor
`κ₋ = #off-line pairs` underpinning the carrier/G5 reading (RH ⟺ `κ₋=0`, `carrier-herglotz-rh`).

**Verdict.** Claim **SOUND**; Lean footholds `multiPair_carrier_exact_neg_inertia` /
`multiPair_carrier_linearIndependent` exist and match the audited theorem. → `2-fully-proven`; the 2→3 Lean
certification (lake build + axiom audit) remains Leaner's gate.

## Leaner certification — 2026-06-19

Verified exact Lean names by scratch file with `import GaloisForLFunctions`:
- `GaloisForLFunctions.multiPair_carrier_linearIndependent`
- `GaloisForLFunctions.multiPair_carrier_exact_neg_inertia`
- parent theorem `GaloisForLFunctions.exact_neg_inertia`

The formal theorem `multiPair_carrier_exact_neg_inertia` states the factored finite carrier form
`Σ_i w_i w_i* - Σ_i u_i u_i*` has negative inertia exactly `k`, as an upper bound for every negative-definite
subspace plus existence of a `k`-dimensional negative-definite subspace, under the ticket's distinct off-line
pole, node-injectivity, and node-avoidance hypotheses. `#print axioms` for the two named footholds reports only
`[propext, Classical.choice, Quot.sound]`.

Verification commands:
- `cd formal && lake env lean /tmp/kappa_row032_check.lean`
- `cd formal && lake build GaloisForLFunctions`
- `bash scripts/check_axioms.sh`
