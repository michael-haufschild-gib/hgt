# Kraft-sparse spike combs of Riemann's kernel are Weil-positive

- **ID:** C606 (HCF ledger row 608)
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) for the positive half; sharpness is CONJECTURE
- **Source:** HCF exact-layer loop, rows 605–607 (MUST-1302 single edge; row 607 pole-free direction)
- **Statement:** There is `L₀` such that for every finite set of levels `L_i ≥ L₀`, pairwise at least
  `4/Y(L₀)` apart, with `Σ_i (L_i+1)² e^{−L_i} ≤ 1`, the Weil form of ζ is positive definite on
  `span{P_{L_i}}`. Here `P_L = Φ·(χ_{L+2η,η} − χ_{L,η})`, `η = 1/Y(L)`, `Y(L) = 2πe^{2L}`, is the
  thin spike of Riemann's kernel at level `L`.

## Goal
MUST-1302 showed that one near-null direction (Φ cut at one level) is Weil-positive without RH. This
card asks how many near-null directions are positive at once, and what limits them.

Answer (conjectured, proved below for the positive half): spikes interact through primes in two ways.
- **Same side.** The lag `|L_i − L_j|` falls near some `log n`. These couplings are summable over `n`
  because of the factor `√(Y_min/Y_max) = e^{−|L_i−L_j|}`, as long as the levels are `1/Y`-separated.
- **Opposite sides.** The lag `L_i + L_j` sees about `e^{|L_i−L_j|}` integers near
  `X = e^{L_i+L_j}`. After normalization each pair costs `≍ (L_i+L_j) e^{−(L_i+L_j)/2}`. This is a
  rank-one form `v_i v_j` with `v_i = (L_i+1)e^{−L_i/2}`.

So the trivial (counting) prime bound gives positivity exactly under the Kraft condition
`Σ_i (L_i+1)² e^{−L_i} ≲ 1`. Equivalently, about `e^{L}/L²` spikes are allowed near level `L`: the
square-root-of-X wall (`X = e^{2L}`), written as a sparsity law. For a single spike of width `w` at
level `L` the condition reads `w·e^{L} ≲ 1/L`, which is the thin-shell law.

**Sharpness heuristic ([OPEN CORE], next cycle).** An off-line zero `ρ = β + iγ` gives a negative
comb once about `e^{(3−2β)L}` spikes cohere within `1/γ`. So the unconditional exponent 1 (Kraft
`Σe^{−L}`) cannot be improved without a zero-free strip.

**Conjectured exponent dictionary.** Comb positivity at density `e^{θL}` holds iff
`θ < 3 − 2Θ`, where `Θ = sup Re ρ`. RH ⟺ every exponent `< 2`.

Not a producer for smooth tests. Smooth tests at level `L` need density `e^{2L}`, i.e. spacing
`1/Y`, which is where the comb becomes dense. That is RH.

## Gates
- [x] 0 → 1  in-progress: well-posed, unconditional, attack via explicit formula with
  pairwise lag majorants
- [x] 1 → 2  fully-proven: paper proof below
- [x] 2 → 3  formalized: `RHTower.eventually_re_W_spikeComb_pos`, standard axioms
- [ ] 3 → 4  n/a (no stage 4 per user directive)

## Approach (paper proof)
Notation:
- `Φ` = `riemannKernelReal`, `E(L) = e^{9L/2}e^{−πe^{2L}}`, `Y = 2πe^{2L}`, `c = Y − 9/2`, `η = 1/Y`.
- `C₀` = `riemannEnvelopeConst`, `κ₀ = 400e^{−6}/C₀²`.
- `A_i = C₀E(L_i)`, `N_i² = ∫P_i²`, `Q = Σ a_i² N_i²`.

Piece facts (all levels `≥ 1`, `Y ≥ 12`):
1. `0 ≤ P_L ≤ Φ`; `P_L(u) ≠ 0 ⇒ L < |u| < L + 3η`; `P_L` is even, `C^∞`, compactly supported.
2. Majorant: `P_L(u) ≤ A e^{−c(|u|−L)} 1_{|u|>L}` (envelope bound plus `E(L+y) ≤ E(L)e^{−(Y−9/2)y}`).
3. Layer: `P_L = Φ` on `L+η ≤ |u| ≤ L+2η`, so `N² ≥ 400e^{−6}E²/Y = κ₀A²/Y`.
4. `∫P ≤ 2A/c ≤ 4A/Y ≤ 4N/√(κ₀Y)`.
5. Pieces at levels `≥ 4η(L₀)` apart have disjoint supports, so `∫F² = Q` and `∫|F| ≤ Σ|a_i|∫P_i`.

Pair lag bound, for `x ≥ 0`, `d = L_i − L_j`, `D = L_i + L_j`, `c_m = min(c_i, c_j)`,
`c_M = max(c_i, c_j)`:
`A_ij(x) = ∫P_i(u)P_j(u−x)du ≤ A_iA_j [ (e^{−c_m|x−d|} + e^{−c_m|x+d|})/(c_i+c_j) + (2/c_M) e^{−(c_m/2)(x−D)} 1_{x≥D} ]`.
Proof by sign cases of `u` and `u − x`:
- `(+,+)`: write `u = m + t`, `m = max(L_i, L_j + x)`. The exponent is at least
  `c_m|x − d| + (c_i + c_j)t`; integrate over `t ≥ 0`.
- `(−,−)`: the same after `u ↦ −u`, with `d ↦ −d`.
- `(+,−)`: here `L_i ≤ u ≤ x − L_j`. The exponent `c_i t + c_j(s − t)` (with `s = x − D`) is at least
  `(c_m/2)s + (c_M/2)·(the variable carrying c_M)`; integrate over a half-line: `2/c_M`.
- `(−,+)`: empty.

Normalization: `A_iA_j ≤ N_iN_j √(Y_iY_j)/κ₀`, `√(Y_iY_j)/(c_i+c_j) ≤ 2e^{−|d|}`,
`√(Y_iY_j)/c_M ≤ 2e^{−|d|}`.

Same-side sum:
- Use `e^{−|d|} ≤ n^{−1}e^{|log n − |d||}`. Then
  `(4/κ₀)Σ_n Λ(n) n^{−3/2}(e^{−(c₀−1)|log n − d|} + e^{−(c₀−1)|log n + d|})`.
- Row sums over `j`: `Σ_j e^{−κ|z − L_j|} ≤ 2e^{κs/2}/(κs)`, comparing with disjoint intervals of
  length `s` around the separated levels. With `s = 4/Y(L₀)` and `κ = c₀ − 1`, this is `≤ G` (absolute).
- AM–GM then gives at most `(8G/κ₀) σ₃ Q`, where `σ₃ = Σ Λ(n)n^{−3/2}`.

Opposite-side sum:
- For `n ≥ e^D ≥ e²`, `log n/√n ≤ De^{−D/2}`.
- `Σ_{n ≥ e^D}(n/e^D)^{−c_m/2}` ≤ `1 + 2e^D/(c_m − 2)`, or in the corpus form
  `e^{c_mD/2}Σ_{n≥n₀} logPowDecay((c_m+1)/2, n)`.
- Normalized, this is `≤ K₂(D+2)e^{−D/2}`, and `(D+2)e^{−D/2} ≤ 2(L_i+1)e^{−L_i/2}(L_j+1)e^{−L_j/2}`.
- Cauchy–Schwarz then gives at most `4K₂ K Q`, with `K = Σ(L_i+1)²e^{−L_i} ≤ 1`.

Archimedean term:
- `(ℓ−10)Q − (ℓM/π)(∫|F|)²` with `(∫|F|)² ≤ (16/κ₀)(Σ 1/Y_i)Q ≤ (16/κ₀)(e^{−L₀}/2π)Q`.
- Take `M = π²κ₀e^{L₀}/16`. The archimedean term is then `≥ (ℓ/2 − 10)Q`, with
  `ℓ = log(1 + M/4) → ∞`.

Pole term: `2(∫F e^{u/2})² ≥ 0`, since `F` is even and real.

Conclusion: `Re W(F,F) ≥ (ℓ/2 − 10 − 2[(8G/κ₀)σ₃ + 4K₂])·Q > 0` for `L₀` large and `a ≠ 0`.

## No-go closure (mandatory when falsified)
n/a (positive half proved on paper).

## Log
- 2026-10-12 — created. Phase 4 verdict: SURVIVES PRELIMINARY ATTACK.
  - Corpus search: no multi-level truncation positivity (`isPosDefOn_span_of_gram` is generic
    infrastructure).
  - The ground-state jump form is owned (`RiemannKernelGroundStateZeroIdentity`, theta jump
    energies), but it does not give this law.
  - Row 607's claim that pole-freeness creates wall 1 is corrected. Annuli `U = Φ(χ_{L+s} − χ_L)` have
    super-exponentially small pole value and are arch-dominated positive. The width-½ smoothing,
    not pole-freeness, causes the wall.
- 2026-10-12 — Lean done: `RHTower/RiemannKernelSpikeLag` (pieces, pairwise lag law), `RiemannKernelSpikePrimeSums` (separated sums, amplitude–scale, per-pair prime bound), `RiemannKernelSpikeCombWeilPositive` (assembly). Standard axioms; wired after `RiemannKernelTruncationWeilPositive`. Constants differ slightly from the paper: Kraft `Σ(L+1)²e^{−L} ≤ 1`, separation `4/Y(L₀)`, `G ≤ 8`. Next: sharpness half, via a negative comb from an off-line zero.
