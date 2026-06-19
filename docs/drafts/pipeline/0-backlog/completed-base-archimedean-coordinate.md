# The completed base R⁺ — adjoin the archimedean coordinate to the Bohr ring (the definitional foundation)

- **ID:** completed-base-archimedean-coordinate
- **Stage:** 0-backlog
- **Type:** CONJECTURE / CONSTRUCTION (foundational definitional brick — the first thing the reorientation needs)
- **Priority:** FOUNDATIONAL
- **Source:** the Hölder-recentering (`../../00-charter-wall-and-door.md` §2, `../../00-foundations-native-objects-and-gatekeepers.md` N1⁺);
  the base under `../../door/bucket-archimedean-generator.md` and `completed-connection-category.md`;
  the operator from #88 §7 / #90 §1; 00-status rows #24, #59
- **Statement (to shape).** The current base is `R = ℂ[x_p^{±1} : p]` (Bohr–Dirichlet, finite primes only,
  `x_p = p^{-s}`). To carry the archimedean generator `∂_s` and the `Γ`-factor **as native data** (charter
  §2, N1⁺), construct the **completed base `R⁺`**: `R` together with (i) the archimedean coordinate / the
  `s`-direction on which `∂_s = −Σ_p(log p)θ_p` acts as a genuine generator, (ii) a symbol for the
  archimedean factor `Γ` carrying its **polynomial-multiplier** recurrence, and (iii) the **product-formula
  relation** `∏_v |x|_v = 1` tying the archimedean coordinate to the finite ones. Then `(R⁺, {σ_p}, ∂_s)`
  is the infinite-base **difference–differential** ring on which `𝓜⁺` lives.

  **This is the brick under everything else:** `completed-connection-category`, `archimedean-corank-collapse`,
  and the `Γ`-module all *assume* such a base. Building it precisely is step 0 of the reorientation.

## Why it is not automatic (the design choices to settle)
`s` is **not independent** of the `x_p` (`x_p = p^{-s}`), so the archimedean direction is the **diagonal**
transverse to the `𝕋^∞` torus, and `∂_s` is the diagonal derivation. Three candidate constructions, to be
compared and one chosen:
1. **Differential completion:** `R⁺ = (R, ∂_s)` as a `∂`-ring, `∂_s` the diagonal derivation
   `−Σ(log p)θ_p`. Minimal; but `Γ` is not yet an element — only its generator is.
2. **`Γ`-symbol extension:** adjoin a transcendental symbol `g` for `π^{-s/2}Γ(s/2)` with its **difference**
   relation (the polynomial-multiplier recurrence `Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)`, #90 §64) — a difference-ring
   extension `R[g; σ_∞]` with a *non-constant* multiplier, the archimedean analogue of the `σ_p`.
3. **Adelic / product-formula completion:** adjoin `x_∞` with the constraint `∏_v|x|_v = 1`
   (`log|x_∞| = −Σ_p v_p(x)log p`), making the archimedean coordinate the dependent one — the cleanest home
   for "`∂_s` = the product-formula relation" (the corank-collapse bet, #128).

*Conjecture:* the right `R⁺` is the **synthesis** — the `∂_s`-differential structure (1) **and** the
`Γ`-symbol with its polynomial-multiplier recurrence (2), with the product formula (3) as the relation that
ties the archimedean lane to the primes. Settling which, and proving `(R⁺,{σ_p},∂_s)` is a well-defined
difference–differential ring with `[∂_s,σ_p]=0`, is the deliverable.

## Concrete first steps (this is meant to be worked, not just framed)
1. **Pin `∂_s` on `R`:** verify `∂_s = −Σ_p(log p)θ_p`, `∂_s x_p = −(log p)x_p`, `[∂_s,σ_p]=0`,
   `∂_s e_m = −(m·ℓ)e_m` (elementary; Lean/numerically certifiable — the reorientation's first ledger floor).
2. **Adjoin the `Γ`-symbol** with `σ_∞ g = (s/2π)g`-type recurrence; check it commutes with `σ_p` and is
   compatible with `∂_s` (the polynomial multiplier is where Source A's wildness enters).
3. **Impose the product formula** and check consistency (does it over-determine the ring? is `∂_s` then the
   product-formula relation, as the corank bet needs?).
4. **`F_q` shadow** (Door-5): over `F_q(C)` the archimedean coordinate is absent / a Frobenius place; `R⁺`
   must degenerate to the bare prime ring (no `Γ`-symbol).

## Door passport
- **Door-1/4:** `R⁺` is the native interior's base (charter §2, redrawn); the archimedean coordinate is the
  Source-A lane. Definitional, so BRIDGE-prerequisite; the native theorems are what it enables.
- **Door-5:** the `F_q` degeneration (no archimedean coordinate) is the required recovery.

## Gates
- [ ] 0 → 1  in-progress: the three constructions compared, one chosen; `R⁺` defined; `[∂_s,σ_p]=0` and the
  `Γ`-symbol recurrence stated; product-formula consistency posed; Door passport
- [ ] 1 → 2  fully-proven: `(R⁺,{σ_p},∂_s)` proven a well-defined difference–differential ring; the
  elementary operator facts proven; `F_q` degeneration checked
- [ ] 2 → 3  formalized: Lean floor — `∂_s = −Σ(log p)θ_p`, `[∂_s,σ_p]=0`, `∂_s e_m = −(m·ℓ)e_m` (reuse
  `linearIndependent_log_primes`); the `Γ`-symbol recurrence as a difference-ring fragment
- [ ] 3 → 4  publication-ready: "the completed difference–differential base of the multi-q theory"

## Cross-references
- `completed-connection-category.md` — builds the **category/Galois** on this base (dependency: this card
  first). `gamma-module-construction.md` — the `Γ`-symbol becomes the module `M_∞`.
- `archimedean-corank-collapse.md` (#128) — needs the product-formula relation defined here.
- `../../door/bucket-archimedean-generator.md`, `two-sources-of-hypertranscendence.md` — the framing.

## Log
- 2026-06-19 — created in 0-backlog as the **definitional foundation** of the reorientation: the completed
  base `R⁺` adjoining the archimedean coordinate / `Γ`-symbol / product formula to the Bohr ring. The brick
  under `completed-connection-category`. First step = compare the three constructions, pin `∂_s` and
  `[∂_s,σ_p]=0` (the first Lean floor).
</content>
