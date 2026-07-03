# Notes toward Problem 16 (from the proposer, 2026-07-03)

Two findings that sharpen what remains of Problem 16; free to use.

## 1. The question is bypassed whenever the curve family avoids a disk containing K₂

If a closed curve γ (indeed a whole domain Ext carrying the relevant cycles) lies in
`{|z| > s}` with `K₂ ⊂ D(0, s)` — for quadratic Julia sets `K₂ ⊂ D(0, √(2|c₂|))` by the crude
escape bound — then the winding number `n(γ, ·)` is constant on the connected set `D(0, s)`,
hence constant on `K₂`, and the winding mass `∫ n(γ, w) dμ₂(w) = n · μ₂(K₂) = n ∈ ℤ` is an
integer for EVERY such cycle. Integrality is then automatic and Question A is moot for such
configurations. Question A is only load-bearing when the curves must pass BETWEEN pieces of
`K₂` (the comparable-scale interleaved case).

## 2. Question A's "mass 1" clause holds for all comparable scales, elementarily

Claim: for `w ∈ K₂`, writing `t = |c₂|/|c₁|` and `h₁ = G₁(0)`,

  `G₁(w) ≤ h₁ + max(1, ½·log(1+2t)) + o(1)`  (as `|c₁| → ∞`, uniform).

Proof sketch (no maximum principle): `|w| ≤ √(2|c₂|)` (crude escape). Iterate the functional
equation `G₁(w) = G₁(f₁ⁿ(w))/2ⁿ` to the first `n` with `|f₁ⁿ(w)| ≥ |c₁|`.
- If `n = 1`: `|f₁(w)| ≤ 2|c₂| + |c₁| = (1+2t)|c₁|`, and at norms `≥ |c₁|` the pointwise
  far-field bound `|G₁ − log|·|| ≤ 2|c₁|/|·|²` applies, giving
  `G₁(w) ≤ ½(log((1+2t)|c₁|) + ε) = h₁ + ½log(1+2t) + O(1/|c₁|)` (using `2h₁ = log|c₁| ± ⅛`).
- If `n ≥ 2`: the previous iterate had norm `< |c₁|`, so `|f₁ⁿ(w)| ≤ |c₁|² + |c₁|`, giving
  `G₁(w) ≤ (1/2ⁿ)(log(|c₁|²+|c₁|) + ε) ≤ ¼(2log|c₁| + 1 + ε) ≤ h₁ + 1` for `|c₁| ≥ 100`.
- If no such `n` exists the orbit is bounded, `w ∈ K₁`, `G₁(w) = 0`.

Consequence: for `t ≤ 4` (in particular all comparable pairs) and `h₁ ≥ 2.9`, the level
`ℓ = h₁ + 1.2` lies in the window `(h₁ + ⅛, 3h₁/2)` and satisfies `K₂ ⊂ {G₁ < ℓ}` strictly:
the level curve `{G₁ = ℓ}` avoids `K₂` and encloses mass exactly `1`. So Question A's outer
requirement is TRUE for comparable scales; what remains of Problem 16 is only the behaviour of
cycles that must separate pieces of `K₂` — i.e. deep curves in the interleaved region — where
finding 1 does not apply and partial masses `m/2^k` genuinely appear.

## What this leaves open (the sharpened Problem 16)

For comparable `|c₁| ≍ |c₂|`, the deep curves of any dyadic descent toward a piece of `K₁`
must thread between pieces of `K₂` when `K₁` and `K₂` interleave at scale `√|c₁|`. The open
question is now exactly: can the descent target (a small piece `P ⊂ K₁`, which may be chosen
with a moat avoiding `K₂` — this is proved) be reached by a nested sequence of closed curves
each of INTEGER winding mass against `μ₂`, within the Green–geometry constraints of the
`c₁`-tower? Equivalently: does interleaving obstruct integer-mass nesting, or can the curves
always "snap to" the dyadic piece structure of `K₂`?
