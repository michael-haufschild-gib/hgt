# The forward monodromy group is transitive on the zeros

- **ID:** gtz-forward-monodromy-transitive
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-1311 §2.19 question 1 (B193), second part; programme card
  `gtz-galois-theory-of-zeros-programme.md`, open core item 6.
- **Statement:** for every forward time `b` off the branch times and all zeros `z, z'` of `H_b`
  there is `σ ∈ G₊(b)` with `σz = z'`.

## Goal

The zero cover of the heat family over the forward half-plane is irreducible: its simple part is
path connected. With the sign flips and the exchanges this is the step from "`G₊` contains an
exchange" to the structure of the whole group. Unconditional.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Objects

Saddle `a = σ + iη`, `δ = π/4 − η`; `P`, `τ(a)`, `f`, `B₀`, `S₀`, `Q` as on the card
`galois-zero-collision-away-from-the-centre-at-a-forward-time.md`. Scaled variable `ζ = az`.

- Wide region `Ω⁺`: `σ ≥ 50`, `η ≥ 0`, `δ ≥ 1/(4σ)`. It contains the real saddles `a = σ`, whose
  times `τ(σ) = πe^{2σ}/σ` are real, and the saddle region.
- Strip `j ∈ ℤ` (closed box): `πj + 1/8 ≤ Re ζ ≤ π(j+1) − 1/8`, `|Im ζ| ≤ 1`. Negation maps strip
  `j` to strip `−j−1`.
- `S`-side: saddles of `Ω⁺` with `|B₀| ≤ (97/100)|2S₀|`.
- Simple join: `(τ, z) ∼ (τ', z')` if a continuous path of forward times from `τ` to `τ'` has a
  continuous lift of zeros from `z` to `z'` all of whose points are simple zeros. The path may
  pass through branch times.

## Theorems

1. (Simple joins are monodromies.) If `b` is a forward time off the branch times and
   `(b, z) ∼ (b, z')`, then `σz = z'` for some `σ ∈ G₊(b)`.
2. (Model on the wide region.) For every `R` there is `C` with: for `a ∈ Ω⁺`, `Re a ≥ R`,
   `|ζ| ≤ R`: `|H_{τ(a)}(ζ/a) − B₀ − 2S₀ cos ζ| ≤ Cσ⁵e^{−σ}(|B₀| + |S₀|)`. With `G` the difference
   as a function of `ζ`: `|G'(ζ)| ≤ Cσ⁵e^{−σ}(|B₀| + |S₀|)` for `|ζ| ≤ R − 1`.
3. (One zero per strip.) For `a ∈ Ω⁺` with `σ ≥ σ₀(R)`, `|B₀| ≤ 3|S₀|`, and a strip `j` inside
   `|ζ| ≤ R − 1`: `H_{τ(a)}(ζ/a)` is injective on the strip and its derivative does not vanish
   there. On the `S`-side all zeros with `|ζ| ≤ R − 1` lie in the interior of strips.
4. (Signed loops.) For `ε ∈ {1, −1}` and every `σ₀` there is a closed loop `a(s)` in the saddle
   region with `Re a(s) ≥ σ₀` and `|2S₀ cos ξ₀(s) − εB₀| ≤ |B₀|/4096`, `ξ₀(s) = e^{iπs}/4`.
5. (Exchanges of strips.) Let `ε`, `a(s)` be as in 4, `θ ∈ πℤ` with `cos θ = −ε`, `|θ| ≤ R − 2`.
   A zero of `H_{τ(a(0))}` in the strip of `θ + 1/4` is joined simply, along the loop, to the
   zero in the strip of `θ − 1/4`.
6. (Real saddles.) For `σ ≥ σ₀(R)` each strip of the window at `τ(σ)` holds exactly one zero,
   and it is real. Along real times `≥ 1/8` lifts keep their sign and their order. A zero of a
   strip at `τ(σ)` is joined simply to the zero of the same strip at every saddle of the wide
   region on the `S`-side with `Re a ≥ σ₀(R)`.
7. (Transitivity.) Statement above.

## Proof

1. Let `Γ` be the loop and `w` the lift. Claim `𝒢(s)`: for every `ε > 0`, for all times `τ'`
   near `Γ(s)` off the branch times there is a forward path from `b` to `τ'` that transports
   `z` to a zero within `ε` of `w(s)`. `𝒢(0)`: chart of the simple zero `z` over a disc `D` of
   times at `b`; two times of `D` off the branch times are joined by an arc inside `D` that
   avoids the branch times (arcs with different heights are disjoint, a box of forward times
   has finitely many branch times), and the lift of the arc is the chart. Propagation: at
   `s₀` take the chart `(W, Z, ρ)` of `(Γ(s₀), w(s₀))`, `W` a disc. For `s` near `s₀`:
   `Γ(s) ∈ W`, `|w(s) − w(s₀)| < ρ`, so `w(s) = Z(Γ(s))`. If `𝒢(s₁)` holds for one such `s₁`,
   pick `τ₁ ∈ W` off the branch times near `Γ(s₁)` with a forward path from `b` transporting
   `z` to a zero within `ρ` of `w(s₀)`, hence to `Z(τ₁)`; continue inside `W` by an arc to
   `τ'`; its lift is `Z`. So `𝒢` holds near `s₀`. The set of `s` with `𝒢` is open, closed and
   contains `0`. At `s = 1`, `τ' = b`: the transported zero is within every `ε` of `z'`, and
   the zeros of `H_b` are isolated.
2. Corner path at the height `η = Im a` (card of the collision, theorems 1–4). The window
   enters only through `|e^{izx}| ≤ e^{R}` on the left part of the line and `e^{|Im ζ|} ≤ e^R`.
   On `Ω⁺`: `cos 2η = sin 2δ ≥ 1/(4σ)`, so `πe^{2σ} ≤ 4σp`, `p ≥ 18`,
   `Re τ ≥ pσ/|a|² ≥ πe^{2σ}/(8σ²)`, `8 Re τ ≤ p`, `K_η ≤ 324Bσ³`, `|B₀| ≥ |Φ(0)|e^{−σ}`,
   `|S₀| ≥ e^{7σ/2 + Re f}`. For `η ≥ 1/2` the proof of the saddle region applies. For
   `η < 1/2`: `Re f ≥ 0`, the two segments are `≤ eK_η` each, `|B₀| ≤ 2|Φ(0)|`,
   `e^{−η² Re τ} ≤ 1 ≤ e^{Re f}`; all are `≤ Cσ⁴e^{−3σ}|S₀|`. Derivative: Cauchy's estimate on
   circles of radius `1`.
3. On strip `j`: `Re((−1)^j sin ζ) = sin(Re ζ − πj) cosh(Im ζ) ≥ sin(1/8) ≥ 1/9`. The derivative
   of `F(ζ) = H_{τ(a)}(ζ/a)` is `−2S₀ sin ζ + G'`, `|G'| ≤ ε(|B₀|+|S₀|) ≤ 4ε|S₀|`, so
   `Re(−(−1)^j F'/(2S₀)) ≥ 1/9 − 2ε > 0` on the convex strip: `F` is injective with nonzero
   derivative. The hypothesis holds on the `S`-side and on the signed loops (`|B₀| ≤ 2|S₀|·17/16`).
   Outside the strips on the `S`-side: `|cos ζ|² = cos²(Re ζ) + sinh²(Im ζ)`, so
   `|cos ζ| ≥ cos(1/8) ≥ 127/128` if `|Re ζ − πk| ≤ 1/8` and `|cos ζ| ≥ sinh 1 > 1` if
   `|Im ζ| ≥ 1`; then `|B₀ + 2S₀ cos ζ| ≥ |2S₀|(127/128 − 97/100) > ε(|B₀| + |S₀|)`.
4. `u = 2S₀/B₀` is continuous on a path of saddles and `u² = Q`. On the segment
   `t ↦ a₁ + th`: `u(a₁+th)² = (u(a₁)e^{D₁th})² X(th)`, `|X − 1| ≤ 70K`; a continuous square
   root of a function near `1` that is `1` at `t = 0` stays near `1`:
   `|u(a₁+h) − u(a₁)e^{D₁h}| ≤ 70K|u(a₁)e^{D₁h}|`. Take
   `h(s) = (Log(ε/u(a₁)) − Log cos ξ₀(s))/D₁`: `u(a₁)e^{D₁h(s)} = ε/cos ξ₀(s)`. Sizes as for
   the unsigned loop (`|Log(ε/u(a₁))| ≤ ½|log|Q(a₁)|| + π`).
5. On the loop `|S₀| ≤ |B₀|` and `|2S₀ cos θ cos ξ₀ + B₀| ≤ |B₀|/4096`. As on the collision
   card: no zero with `1/16 ≤ |ζ − θ − ξ₀(s)| ≤ 1/8`, a zero with `|ζ − θ − ξ₀(0)| < 1/16`
   exists, and a lift that starts in the disc of radius `1/16` around `θ + ξ₀(0)` stays in the
   moving disc and ends in the disc around `θ − ξ₀(0) = θ − 1/4`. In the moving disc
   `|sin(ζ − θ)| ≥ 3/32`, so the derivative `−2S₀ cos θ sin(ζ − θ) + G'` does not vanish: the
   lift is simple. The base `a(0)` is on the `S`-side (`cos(1/4) < 97/100·(1 − 1/4096)`), the
   two discs lie in the strips of `θ ± 1/4`, and each strip has one zero (3).
6. At a real saddle `|B₀| ≤ |Φ(0)|` and `|S₀| ≥ e^{7σ/2}`, so `4|B₀| ≤ |S₀|` far out: `S`-side.
   Existence in each strip: minimum modulus on the disc of radius `1/2` around `θ + π/2`, where
   the model is `B₀ − 2S₀ cos θ sin w`, `|sin w| ≥ 9/20` on the circle; uniqueness by 3. The
   zeros at times `t ≥ 1/8` are real and simple (`riemannHeat_zeros_real_simple_of_eighth_le`),
   `H_t(0) > 0`; the real part of a lift and the difference of two lifts are continuous and
   never `0` (two lifts that meet agree), so sign and order are kept. Path to the `S`-side:
   the real saddles from `σ` to `Re a` (`4|B₀| ≤ |S₀|`), then the vertical segment to `a`. With
   `|Q| = (64π⁴/Φ(0)²)e^{9σ + 2 Re f}/|2a − 1|`, `Re f = πe^{2σ}(cos 2η(σ − 1) − η sin 2η)`
   decreases and `|2a − 1|` increases in `η`, so `|Q| ≥ |Q(a)|` on the segment, and the `S`-side
   is `1 ≤ (97/100)²|Q|`. Along both segments the zero stays in its strip (3).
7. Base time `b = 1/8`. For zeros `x, x'` of `H_b` let `N` be the number of zeros of `H_b` with
   `|z| ≤ max(|x|, |x'|)`, `R = π(N + 2) + 2`, and `σ ≥ σ₀(R)` with both signed loops beyond it.
   Adjacent strips `θ`, `θ − π` of the window, `θ = πk`, are joined at `τ(σ)`: along the path of
   6 to the base of the signed loop with `cos θ = −ε`, the exchange (5), and back; the zeros at
   the base are identified by uniqueness in the strips (3). By induction all strips
   `−N − 1 ≤ k ≤ N` are joined. Along `[b, τ(σ)]` let `x` go to `y`. If `σ|y| ≥ π(N + 1)`, say
   `y > 0` (else `−x`), the zeros of the strips `0, …, N` lie in `(0, y)` and pull back to
   `N + 1` distinct zeros of `H_b` in `(0, |x|)`: impossible. So `y` lies in the window, and in a
   strip `−N − 1 ≤ k ≤ N` (3). Hence `(b, x)` and `(b, x')` are joined simply, and by 1 they are
   in one orbit of `G₊(b)`. Other base times: a forward path from `b` to `1/8` carries the
   joins.

## Formalization

Headline: `exists_mem_forwardMonodromy_apply_eq (b) (hb₀ : 0 < b.re) (hb : b ∉ branchTimes) (p q)
: ∃ g ∈ forwardMonodromy b hb₀ hb, g p = q` in `TheForwardMonodromyGroupIsTransitiveOnTheZeros`;
axioms `propext`, `Classical.choice`, `Quot.sound`.

Modules in `GaloisTheoryOfZeros/`:

| Module | Content |
|---|---|
| `AZeroFollowedThroughSimpleZerosIsMovedByTheForwardMonodromy` | theorem 1: `SimplyJoined` (symm, trans), `simplyJoined_iff_exists_mem_forwardMonodromy` |
| `AZeroAloneInAMovingRegionIsFollowedThroughSimpleZeros` | tracking tool for 3, 5: `exists_simplyJoined_of_alone` |
| `TheLineThroughTheSaddleIsAGaussianAtTheSaddleValue`, `TheHeatFamilyAtASaddleTimeIsAConstantPlusACosine` | theorem 2: `WideRegion`, `exists_forall_norm_complexHeat_sub_wide_model_le` |
| `ForEachSignALoopOfSaddlesTurnsTheRatioOfTheTwoTerms` | theorem 4: `IsSignedLoop`, `exists_isSignedLoop` |
| `AZeroOfAStripStaysInItsStripWhereTheCosineTermDominates` | theorem 3: derivative of the model, `StripFacts`, `exists_stripFacts`, `exists_simplyJoined_of_stripFacts` |
| `ASignedLoopOfSaddlesExchangesTheZerosOfTwoAdjacentStrips` | theorem 5: `exists_exchange` |
| `TransportAlongRealTimesKeepsTheOrderOfTheZeros` | theorem 6, real times: `re_pos_iff_of_lift`, `re_lt_iff_of_lifts`, `SimplyJoined.neg`, `SimplyJoined.refl` |
| `AtARealSaddleEachStripOfTheWindowHoldsOneZero` | theorem 6, saddles: `exists_real_dominance`, `exists_zero_mem_cosStrip`, `norm_saddleRatioSq_le_of_im_le`, `exists_simplyJoined_to_cosineSide` |
| `TheForwardMonodromyGroupIsTransitiveOnTheZeros` | theorem 7: `exists_realSaddleWindow`, `RealSaddleWindow.simplyJoined_strips`, `RealSaddleWindow.lt_of_lift`, `simplyJoined_eighth`, `exists_mem_forwardMonodromy_apply_eq` |

## Log
- 2026-11-13 — created; paper proof written.
- 2026-11-13 — theorem 1, the tracking tool and the model on the wide region formalized.
- 2026-11-14 — theorems 3–7 formalized; transitivity of `G₊` at every forward base time.
