# Lean claim review row #73 — superzeta as additive resolvent trace

- **ID:** lean-claim-review-row-073-superzeta-additive-resolvent-trace
- **Stage:** 3-formalized
- **Type:** claim-review (AUDIT PASSED 2026-06-19, Professor) — Door grade **BRIDGE** (power-series/resolvent algebra)
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/00-status.md · 00-status row #73; ../../door/bucket-ledger-footholds.md
- **Claimed ledger status:** `THEOREM (Lean)`; no matching ticket is present in `../3-formalized/` as of 2026-06-19.
- **Statement:** the superzeta is the additive resolvent trace, using a sum rather than a product.

## Goal
Audit the claim from scratch. Researchers first verify the finite formal statement, its relation to the named superzeta object, and the exact Sigma-versus-product content. Leaner checks formalization after that review.

## Claimed Lean footholds to verify
- `formal/GaloisForLFunctions/SuperzetaResolvent.lean`
- Candidate names: `superzeta_eq_sum_resolvent`, `superzeta_coeff_eq_powerSum`

These names are leads, not certification.

## Gates
- [x] 0 -> 1: audited (Professor); exact finite power-series/resolvent statements fixed (below)
- [x] 1 -> 2: all three identities confirmed sound (elementary, verified symbolically); finite-vs-analytic scope gap identified and correctly excluded by the file header
- [x] 2 -> 3 formalized: Leaner verifies exact theorem names by scratch file, `lake build` green, `scripts/check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone proof note plus Lean certificate

## Approach
Check the geometric-series identity, sum over a finite spectrum, and compare coefficients with power sums. Keep the analytic/infinite superzeta interpretation out of scope unless researchers explicitly prove it.

## Log
- 2026-06-19 — created in 0-backlog as a claim-review ticket for an un-ticketed `THEOREM (Lean)` ledger row.

## AUDIT — 2026-06-19 (Professor): claim VERIFIED (superzeta = additive resolvent trace; coeff = power sum)

Three foothold theorems (`SuperzetaResolvent.lean`), all **elementary true** power-series identities in `ℂ⟦X⟧`:
1. **`geom_eq_inv`:** `Σ_m r^m X^m = (1−rX)⁻¹` — the per-zero geometric series is the resolvent of the local
   `1×1` operator `[r]`. (Standard formal-power-series geometric identity.)
2. **`superzeta_eq_sum_resolvent`:** `Σ_i Σ_m r_i^m X^m = Σ_i (1−r_iX)⁻¹` — the secular/superzeta generating
   function is the **sum** of resolvents (an additive *trace*), **not** a product. (Sum of (1) over `i`.)
3. **`superzeta_coeff_eq_powerSum`:** the `k`-th coefficient is `Σ_i r_i^k` = the power sum `P_k` = the finite
   superzeta value `𝒵(k)`. With `r_i = ρ_i⁻¹`, this is `𝒵(k)=Σ_ρ ρ^{−k}`.

**Verification.** Symbolically confirmed (`r={½,⅓,⅕}=ρ⁻¹` for `ρ∈{2,3,5}`): coeff of `X^k` in `Σ_i(1−r_iX)⁻¹`
equals `Σ_i r_i^k = Σ_ρ ρ^{−k} = 𝒵(k)` for `k=0..5` (exact rationals match). The geometric-series→power-sum
extraction is `1/(1−r_iX)=Σ_k r_i^k X^k`, summed over `i`.

**Door-2: BRIDGE.** Classical power-series / resolvent-trace algebra (geometric series + Newton power-sum
coefficient extraction). No multi-q apparatus.

**Scope (correctly limited by the file header — verified honest).** The file formalizes ONLY the finite
power-series witness. It does **NOT** claim the Voros analytic continuation, the values-are-periods salvage, or
the off-line location of the superzeta's own zeros — all correctly left out of scope. No overclaim.

**Structural placement (sound and meaningful).** The contrast — additive `Σ` (spectral, resolvent trace) vs
the `L`-function's multiplicative `∏` (prime, Euler product) — is exactly the `[𝔾_a,𝔾_m]` seam: the superzeta
sits on the **spectral/additive side**, carries no Euler product and no second difference-Galois `G_L`. This is
a legitimate, ledger-grade finite witness for that placement.

**Cross-lane note.** These finite superzeta values `𝒵(k)=Σ_ρ ρ^{−k}` are exactly the **Keiper `σ_k` secondary
sums** = the prime-explicit cumulants for Wheeler's `finite-free-convolution-flow` Jacobi chain (chat 409): the
FE-symmetric variant `Σ_ρ(ρ(1−ρ))^{−k}=Σ(¼+γ²)^{−k}` is the natural input, and Li-positivity `λ_n≥0⟺RH` is
the `σ_k`-polynomial repackaging. This card formalizes the resolvent/power-sum identity underneath that machinery.

**Verdict.** Claim **SOUND**; footholds `superzeta_eq_sum_resolvent`/`superzeta_coeff_eq_powerSum`/`geom_eq_inv`
exist and match. → `2-fully-proven`; 2→3 Lean certification (lake build + axiom audit) remains Leaner's gate.

## Lean certification - 2026-06-19 (Leaner)

Certified against the current toolchain by `/tmp/superzeta_row073_check.lean`:

```lean
import GaloisForLFunctions
#check GaloisForLFunctions.geom_eq_inv
#check GaloisForLFunctions.superzeta_eq_sum_resolvent
#check GaloisForLFunctions.superzeta_coeff_eq_powerSum
#print axioms GaloisForLFunctions.geom_eq_inv
#print axioms GaloisForLFunctions.superzeta_eq_sum_resolvent
#print axioms GaloisForLFunctions.superzeta_coeff_eq_powerSum
```

Lean statements certified:
- `geom_eq_inv`: the per-zero geometric series equals `(1 - rX)^{-1}` in `C[[X]]`.
- `superzeta_eq_sum_resolvent`: the finite superzeta generating series is the sum of resolvents, i.e. an additive trace.
- `superzeta_coeff_eq_powerSum`: the `k`-th coefficient is the finite power sum `sum_i r_i^k`.

Verification run:
- `cd formal && lake env lean /tmp/superzeta_row073_check.lean`
- `cd formal && lake build GaloisForLFunctions`
- `bash scripts/check_axioms.sh` (PASS: 335 audited theorem outputs; only `[propext, Classical.choice, Quot.sound]`; no `sorry`)
