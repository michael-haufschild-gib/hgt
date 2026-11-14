# The sign of the zeros is not trivial on the forward monodromy group

- **ID:** gtz-sign-of-the-zeros
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** programme card `gtz-galois-theory-of-zeros-programme.md`, open core items 4
  ("simplicity of the zeros of `c`") and 5 ("the two characters"); review-1311 §2.19 question 1.
- **Statement:**
  (A) for every `T` the centre value `c(τ) = H_τ(0)` has a simple zero `τ₀` with `Re τ₀ > T`;
  `H_{τ₀}` has a zero of order exactly two at the centre;
  (B) at a forward time `τ₀` with a zero of order exactly two at the centre, the turn around `τ₀`
  is, for all small radii, an involution of the fibre that exchanges one zero `w` with `−w` and
  carries no other zero to its negative;
  (C) a group of signed permutations with finite supports that contains the signed 3-cycles and
  the double flips, and an involution as in (B), contains the flip of one pair, or the flip of
  one pair times the exchange of two other pairs;
  (D) for every forward time `b` off the branch times: either `G₊(b)` contains the flip of every
  single pair, or it contains, for all zeros `p, a, a'` in three distinct pairs, the element
  `(p −p)(a a')(−a −a')`.

## Goal

`W⁰ ≤ G₊ ≤ W` and `W/W⁰ = (ℤ/2)²` with the characters `χ₁` (sign of the permutation of the zeros)
and `χ₂` (sign of the permutation of the pairs). (D) says `χ₁` is not trivial on `G₊`:
`G₊ ⊇ ker χ₂` in the first case, `G₊ ⊇ ker χ₁χ₂` in the second, so `[W : G₊] ≤ 2`. Which case
holds is the parity of the number of exchanges, i.e. `χ₂`; it stays open.

## Gates
- [x] 0 → 1
- [x] 1 → 2  paper proof below
- [x] 2 → 3  Lean (`formal/GaloisForLFunctions/GaloisTheoryOfZeros/`; axioms `propext, Classical.choice, Quot.sound`)

## (A) A simple zero of the centre value

Notation of the saddle model: `τ(a) = πe^{2a}/a`, `H_{τ(a)}(ζ/a) = B₀(a) + 2S₀(a) cos ζ + E`,
`|E| ≤ ε(|B₀| + |S₀|)` on the saddle region for `Re a ≥ σ(ε)`, `|ζ| ≤ 8`; `(2S₀)² = Q B₀²`;
`Q(a₁ + h) = Q(a₁) e^{2D₁h} X(h)`, `D₁ = P₁(2a₁ − 1)`, `|X − 1| ≤ 70K` for the shifts of size
`O(e^{−2σ})`.

Family. Base point `a₁` far out with `Re f(a₁) = 0`. For `|v| ≤ 1`, `t ∈ [0, 1]`:
`a(v, t) = a₁ + (−Log Q(a₁) + v)/(2D₁) + t·πi/D₁`. Then `a(v, t)` is in the saddle region and
`|Q(a(v, t)) e^{−v} e^{−2πit} − 1| ≤ 1/4096`.

Sign. `A = 2S₀(a(v, t)) e^{−v/2} e^{−iπt}` has `|A² − B₀²| ≤ |B₀|²/4096`, so along every path
`A = ηB₀` up to `|B₀|/4096` with one sign `η`. The paths `v ↦ rv` (fixed `t`) and `t ∈ [0, 1]`
(at `v = 0`) join all points, and `e^{−iπ} = −1`: for `t = 0` or for `t = 1` we have
`2S₀ e^{−v/2} = −B₀` up to `|B₀|/4096` on the whole disc `|v| ≤ 1`. Fix that `t`.

Ratio. `Φ(v) = c(τ(a(v)))/B₀(a(v))` is holomorphic on a neighbourhood of `|v| ≤ 1` (the family
is affine in `v`; `τ` and `B₀` are holomorphic on the saddle region; `B₀ ≠ 0`). With
`δ = 2S₀e^{−v/2} + B₀`, `|δ| ≤ |B₀|/4096`: `2S₀ = e^{v/2}(δ − B₀)`, `|S₀| ≤ 2|B₀|`, and with the
model at `ζ = 0` (`ε = 1/16384`)

`Φ(v) − (1 − e^{v/2}) = (E + e^{v/2}δ)/B₀`, of norm `≤ 3/16384 + 2/4096 ≤ 1/1024`.

Zero. On `|v| = 1/2`: `|1 − e^{v/2}| ≥ 1/4 − 1/16`, so `|Φ(v) − Φ(0)| ≥ 3/16 − 2/1024 ≥ 1/8`,
and `|Φ(0)| ≤ 1/1024 < 1/16`. The quantitative open mapping theorem on the disc `|v| ≤ 1/2`
(a holomorphic function with `|f − f(0)| ≥ ε` on the circle takes every value within `ε/2` of
`f(0)`) gives `v*`, `|v*| ≤ 1/2`, with `Φ(v*) = 0`; so `c(τ₀) = 0`, `τ₀ = τ(a(v*))`,
`Re τ₀ ≥ Re a(v*) > T`.

Simple. `g = Φ − (1 − e^{v/2})` has `|g| ≤ 1/1024` on the circle of radius `1/2` around `v*`
(inside `|v| ≤ 1`), so `|g'(v*)| ≤ 1/512` (Cauchy). If `c'(τ₀) = 0`, the numerator of `Φ` has a
zero of order two at `v*`, so `Φ'(v*) = 0` and `g'(v*) = e^{v*/2}/2`, of norm
`≥ e^{−1/4}/2 ≥ 3/8`. Contradiction. So `c'(τ₀) ≠ 0`, and by
`c^{(n)}(τ) = (−1)ⁿ H_τ^{(2n)}(0)` the zero of `H_{τ₀}` at the centre has order exactly two. ∎

## (B) The turn at a central collision of order two

Let `Re τ₀ > 0`, order two at the centre. For small `r` the turn `T_r` of radius `r²` acts on
the fibre over `τ₀ + r²`. There is `R` such that the zeros with `|z| ≥ R` return. Around every
zero `ζ` of `H_{τ₀}` with `|ζ| ≤ R` choose a disc `D_ζ` of radius `≤ |ζ|/2` (if `ζ ≠ 0`) in
which, for small `r`:

- `ζ` simple: the zeros in `D_ζ` return;
- `ζ` a collision of order `m ≥ 2`: the zeros in `D_ζ` are the sheets `Z_ρ(r)`, `T_r` carries
  `Z_ρ` to `Z_{−ρ}` and back, and all sheets lie in `D_ζ` (they tend to `ζ`);
- `ζ = 0`: the zeros in `D_0` are `±w`, `w = Z_{√2}(r) ≠ 0`, and `T_r w = −w`, `T_r(−w) = w`.

Outside the discs the closed disc of radius `R` has no zero of `H_τ` for `τ` near `τ₀`
(compactness; finitely many zeros of `H_{τ₀}` there). So every zero `z ≠ ±w` has an image `z'`
with `T_r z' = z`, and `z' ≠ −z`: either `z' = z ≠ 0`, or `z, z' ∈ D_ζ`, `ζ ≠ 0`, while
`−z ∈ D_{−ζ}` and the two discs are disjoint. ∎

## (C) Reduction of an involution with one flipped pair

`G` a group of permutations of `Ω` that commute with the involution `x ↦ −x`, have finite
supports, and contains every signed 3-cycle `(p q r)(−p −q −r)`. Let `σ ∈ G`, `σ² = 1`,
`σp = −p`, `σq ≠ −q` for `q ≠ ±p`.

Induction on the number of points moved by `σ`. If `σ` moves `a ≠ ±p`, put `b = σa`; `b ≠ ±a`,
`b ≠ ±p`, `σb = a`. If `σ` moves a further `c ∉ {±p, ±a, ±b}`, put `d = σc`. The element
`u = (a b c)(b c d)` with its mirror lies in `G`, exchanges `a ↔ b`, `c ↔ d` and fixes the
points off the four pairs. `σu` fixes the four pairs, agrees with `σ` elsewhere, is an
involution with the same properties, and moves fewer points. At the end `σ` moves only `±p`
(a single flip), or only `±p, ±a, ±b` (a flip times one exchange). ∎

## (D) Assembly

(A) gives `τ₀`; (B) the turn; the turn is an element of `G₊` at every base time `b`, with the
same properties (transport along a path commutes with `z ↦ −z`); (C) with the signed 3-cycles
of `G₊(b)`; multiple transitivity of `G₊(b)` on the signed pairs moves the flipped pair and the
exchanged pairs to any prescribed ones by conjugation. ∎

## Lean

| Step | Module | Declaration |
|---|---|---|
| A | `TheCentreValueHasASimpleZeroAtAForwardTime` | `exists_centreValue_simple_zero`, `exists_isCollision_center_two` |
| B | `TheTurnAroundACollisionOfOnePairAtTheCentreFlipsExactlyOnePair` | `eventually_forall_zero_of_local`, `IsCollision.eventually_turn_exchange`, `eventually_turn_involution_one_flip`, `exists_mem_forwardMonodromy_involution_one_flip` |
| C | `AnInvolutionWithOneFlippedPairGivesTheFlipOfOnePairUpToOneExchange` | `HasFlip`, `HasFlipExchange`, `IsWindowedSignedGroup.exists_double_exchange`, `.hasFlip_or_hasFlipExchange_of_moved`, `.exists_apply_three`, `.forall_hasFlip_or_forall_hasFlipExchange` |
| D | `TheForwardMonodromyGroupContainsTheFlipOfEveryPairUpToOneExchange` | `forall_flip_or_forall_flip_exchange_mem_forwardMonodromy`, `exists_mem_forwardMonodromy_flip_up_to_exchange` |

Lean form of (C): the hypothesis on `σ` is used as "`σ` fixes every pair, other than that of
`p`, that it maps to itself"; the pairs need no fixed-point-free involution.

## Open

`χ₂` on `G₊`: the parity of the number of exchanges of a turn. At the centre time `τ₀` of (A)
the model has double zeros near every `ζ = 2πk` to leading order; whether they are exact
collisions at the time `τ₀` is below the error `O(σ⁵e^{−σ})` of the model.
