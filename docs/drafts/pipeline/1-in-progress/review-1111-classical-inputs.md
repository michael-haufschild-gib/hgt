# Classical inputs from review-1111

- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAM
- **Source:** `docs/reports/review-1111/obstacles-summary.md`, §2.1, Classical inputs to formalize.
- **Acceptance:** Unconditional proofs on the actual objects, direct Lean checks, umbrella imports.

| Task | Required conclusion | Status |
|---|---|---|
| A115 | Newton polygon of the Carlitz–Goss zeta function from the greedy optimum | **Formalized** for every `q = p^s` and every `z ∈ ℤ_p`: `gossZetaNeg_eq_prod` (`z ∈ ℕ`), `gossZeta_riemannHypothesis` (`z ∉ ℕ`). See `../3-formalized/carlitz-goss-rh-from-greedy-compositions.md`. |
| A26 | Modular Weyl asymptotic `N(Λ) ∼ Λ/12` | open |
| A59 | Primes in short intervals in every reduced residue class | In progress (`ShortIntervalPrimesInProgressions/`). Route: Hoheisel for fixed `q`. Lean, compiled: zeros of primitive `Λ(s,χ)` in `0<Re<1`; explicit formula; short-window bound `‖ψ(x+h,χ)−ψ(x,χ)‖ ≤ windows + 2hΣ_ρ zeroShortWeight(x, 8x²/(hh'), ρ) + C log x + C/h'` (`CharacterSumsInShortWindows`); local count (`LocalZeroCount`); Littlewood growth `|L(σ+it,χ)| ≤ (3+4888q)log³|t|` for `σ ≥ 1−(log log|t|)²/log|t|` (`CharacterPhaseBlocks`, `LittlewoodGrowth`); Littlewood region `β ≤ 1 − log log|γ|/(10⁷ log|γ|)` (`LittlewoodZeroFreeRegion`); density `N(σ,T) ≤ D(1+log T)^{11}T^{12(1−σ)}` (`ZeroDetectionForACharacter`, `ZeroDensityForACharacter`). Remaining: vanishing of `Σ_ρ zeroShortWeight(x, c x^{2u}, ρ)` for `u < u₁/4`, `u₁ = 1/(14·10⁷+12)` (split `β ≤ 3/4` / `|γ| > x^{u₁}` by `Σ(|ρ||1−ρ|)^{−3/4} < ∞`, near zeros by slabs + density + region); window step with Huxley; imprimitive → primitive; orthogonality; primes. |
| A120 | Selberg zeta function of a surface with a small eigenvalue: Euler product and functional equation, zero off the line | open |
| A41 | Count law for every curve over `𝔽_q`, first case plane quartics | open |
| A33 | Fourier coefficients of the cubic residue at all heights | open |
| A18 | Twisted second moments past the square root | open (below `1/2` formalized: `../3-formalized/twisted-second-moments-below-square-root.md`) |
| A21 | Logarithmic two-point Chowla | open |
