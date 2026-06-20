# Weil positivity as an operator: RH ⟺ H_W = −Δ_prime + V_arch ≥ 0 (G5)

- **ID:** weil-positivity-operator
- **Stage:** 0-backlog
- **Type:** OPEN CORE → CONJECTURE (candidate G5)
- **Source:** ../../door/G5-unitarity-gatekeeper.md (Face 7, #88 §8; HP #90), ../../door/bucket-the-seam-archimedean-obstruction.md · 00-status rows #38, #39
- **Statement:** **`RH ⟺ H_W := −Δ_prime + V_arch ≥ 0`** — the Weil-positivity Schrödinger operator on
  `ℓ²` of the smooth numbers, with kinetic `−Δ_prime = Σ_p J_p` (commuting per-prime long-range Jacobi
  operators, **separable**, closed-form symbol, **indefinite**) and potential `V_arch` = the archimedean
  Toeplitz kernel (a **logarithmic confining potential**, certified to 1e-15). RH ⟺ the log archimedean
  potential is **dominated** by the separable indefinite prime kinetic (= the team's `Z_n ≻ A_n` in
  operator form). Related face: the Hilbert–Pólya operator `= gen(G_L)`, RH ⟺ `[D, P_{prime-coinv}] = 0`
  (#39).

## Goal
The **most actionable G5 face**: the operator is **built and certified**, the multiplicative side is
**fully diagonalized**, and only the **domination** `V_arch ≼ −Δ_prime` is open. Complements the carrier
form (`carrier-herglotz-rh.md`, `m_ξ` Herglotz / `κ₋=0`): same gatekeeper, the operator/spectral
language instead of the analytic-germ language. The sole obstruction is the **archimedean Γ-term** (the
seam) — exactly what the multiplicative wing cannot supply.

## Door passport
- **Door-1:** `gen(G_L) = {D} ∪ {σ_p}` (the Berry–Keating archimedean generator + the prime dilations) —
  essentially the native object.
- **Door-4:** lives where the separable prime kinetic meets the single archimedean place — the native
  zone (and exactly where every parent's positivity method goes apex-blind, the seam).
- **Insufficiency note:** positivity alone passes the fakes (Davenport–Heilbronn); **conjoin with the
  Euler cut** (`realization-problem.md`) so `H_W ≥ 0` is not satisfiable by a non-genuine spectrum.

## Gates
- [ ] 0 → 1  in-progress: `H_W` pinned (kinetic symbol, `V_arch` kernel); the domination inequality stated;
  Door passport + fake-rejection condition written
- [ ] 1 → 2  fully-proven: `V_arch ≼ −Δ_prime` proved (= RH) — the apex; expect a long campaign
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
Bound the archimedean confining potential by the indefinite separable prime kinetic. Use the per-prime
Jacobi symbols (closed form) for `−Δ_prime` and the certified Toeplitz kernel for `V_arch`. Cross-check
against the CMV/`|γ_k|<1` face (#78 §12, numeric across ζ, Dirichlet β, Ramanujan Δ, elliptic 11a) and
the Hodge-index `(1,∞)` signature (#89 §7). The HP framing (#90): `D = −i(x∂_x+½)` essentially
self-adjoint, Weyl law = smooth Riemann–von Mangoldt count; the **fluctuations = the prime perturbation
= the wall**.

## Cross-references
- `carrier-herglotz-rh.md` — the same G5 gatekeeper in carrier (`m_ξ` Herglotz) form.
- `compute-omega-h2-gl.md` — `ω=0 ⟺ D trace-class ⟺ HP ⟺ RH` (the operator-level unification).
- `realization-problem.md` — the Euler cut that must be conjoined to reject fakes.
- `hp-not-too-algebraic.md` — why this operator is hard (the two faces fight: B18).
- `../../door/bucket-the-seam-archimedean-obstruction.md` — the archimedean Γ-term is the sole obstruction.

## Log
- 2026-06-19 — created in 0-backlog. The operator/positivity face of G5 (H_W ≥ 0, the most actionable),
  distinct from the carrier-Herglotz face already carded.

## R14 finding (2026-06-20, novelty loop) — RH is a BKT transition; the no-margin is BKT marginality `[wild leap; explains the no-margin]`

**Exact substrate:** `ζ'/ζ(s)=Σ_ρ 1/(s−ρ)` IS the 2D Coulomb field of unit charges at the zeros; Hadamard
`ξ=ξ(0)∏_ρ(1−s/ρ)` is their log-gas partition function. The zeros are a **2D logarithmic Coulomb gas**.

**Leap:** the canonical physics of a 2D log-gas is the **Berezinskii–Kosterlitz–Thouless** transition.
Dictionary: zeros = vortices; FE `ρ↔1−ρ̄` = mirror-charge pairing; **RH = the confined phase** (every charge
pinned to `Re s=½` by its FE-mirror); **off-line zero = unbound vortex pair** (deconfined); `κ₋` (#32) = vortex
density; **the no-margin = BKT marginality.**

**Why the margin is exactly zero (the payoff):** the no-margin is a competition of two *logarithmic* terms —
`V_arch` is a PROVEN log-confining potential and the prime kinetic's PROVEN heart is the **loglog divergence of
`Σ_p p^{−2σ}` at `σ=½`** (Mertens). `log` vs `loglog` is the BKT marginal balance; a **RG-marginal** operator
has, by construction, **zero margin**. So `inf spec H_W=0` is not a coincidence on 8 faces — the deciding
operator is RG-marginal. **This is the structural CAUSE of the no-margin the project never had.**

**Cross-round coherence:** off-line zero = unbound vortex = **R13's nonzero AB flux quantum** (vortices = flux
defects) ⟹ `κ₋` = AB flux count = vortex density (one object). R10's "margin `=π²/(8d)→0` only as `d→∞`" = BKT
**finite-size scaling** (sharp transition only in the thermodynamic limit). Three unrelated draws (R10/R13/R14)
assemble into one topological-defect/marginal-criticality picture.

Speculative: BKT `η=¼` at `T_BKT` vs the arithmetic `½(1−½)=¼` — deep or rhyme, open. Full derivation +
self-judgment (prior ~12, significance ~42, proof ~35) in `logs/2026-06-20-novelty-generation-loop.md` Round 14.

**Forward lead:** construct the Kosterlitz RG flow for the FE-mirror prime-vortex gas; if its separatrix is
`Re s=½` and Rodgers–Tao (`Λ_dBN≥0`) is the approach from the deconfined side, the BKT picture upgrades from
analogy to mechanism and `κ₋` becomes a literal order parameter.
