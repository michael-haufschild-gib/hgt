# Open Problem 4: Hole-free accessible tip for a NONEXCEPTIONAL pair of connected filled Julia sets

> **STATUS (2026-07-02): ANSWERED — see [04-answer.md](04-answer.md); proof audited and
> correct.** The Statement holds for the explicit nonexceptional both-connected class
> `−3/4 < c₂ < c₁ < 0` (real main cardioid), with the tip `z₀ = i·t₁`, `t₁ = √(β₁+c₁)`,
> exactly the file's recommended candidate. New ingredient beyond the file's elementary
> bricks: for hyperbolic `c` the Julia set is a Jordan curve (quasicircle), so Schoenflies
> gives a local exterior collar `U ∖ K₁` connected at `z₀`; the collar plus the imaginary
> ray `{iy : y ≥ t₁+ε}` (disjoint from both filled sets) puts all of `B(z₀,r) ∖ (K₁ ∪ K₂)`
> in the unbounded component `W`, so no hole meets the ball. (Note: the monotonicity of
> `t(c)` claimed below holds on `(−2, 0]`, which contains this class; it fails on
> `(0, 1/4]`.) The q62 programme now has **no open mathematical input**; what remains is
> formalization, chiefly the collar (Jordan/Schoenflies) and the smooth-piece rigidity
> endgame.

**Field:** plane topology / complex dynamics / potential theory.
## Setting

For `c ∈ ℂ` let `K_c = { z : the orbit of z under f_c(z) = z² + c stays bounded }` be the
filled Julia set, `J_c = ∂K_c`. Each `K_c` is compact and full (`ℂ ∖ K_c` connected). Recall
`c ∈ M` (the Mandelbrot set) iff `0 ∈ K_c` iff `K_c` is connected.

Fix `c₁ ≠ c₂` with **both** `c_i ∈ M ∖ {0, −2}` — both filled sets connected, both
parameters nonexceptional (`φ₀(z) = z` and `φ₋₂` are algebraic; every other Böttcher
coordinate is transcendental — that part is already machine-checked and may be assumed).

Write `X = K₁ ∪ K₂`, `W` = the unbounded component of `ℂ ∖ X`, **holes** = the bounded
components of `ℂ ∖ X`.

Note `0 ∈ K₁ ∩ K₂` always (both connected), so the intersection is **never empty**: there is
no disjoint-case escape hatch here, unlike Problem 3.

## Statement (the problem)

> **Prove:** there exist a point `z₀ ∈ ∂W ∩ J₁` with `z₀ ∉ K₂` (indices may be swapped) and
> a radius `r > 0` such that
>
> `B(z₀, r) ∩ K₂ = ∅`  and  `B(z₀, r) ∩ H = ∅` for **every** hole `H`,
>
> for some explicitly described **nonempty class of pairs with both `c_i ∈ M ∖ {0, −2}`**.
> If it fails for all such pairs, characterize the failure.

## The recommended concrete class, with the tip already explicit

Take both `c_i` real, `c_i ∈ (−2, 1/4] ∖ {0}`, `c₁ ≠ c₂`. Then (elementary, may be assumed;
formalization is our job):

- `β_i = (1 + √(1 − 4c_i))/2` is the repelling (parabolic at `1/4`) fixed point,
  `K_i ∩ ℝ = [−β_i, β_i]`, and `K_i ∩ iℝ = i·[−t_i, t_i]` with `t_i = √(β_i + c_i)`
  (a point `it` maps to the real point `−t² + c_i` in one step).
- `c ↦ β(c) + c` is strictly increasing on `(−2, 1/4]`, so `t₁ ≠ t₂`; swap indices so
  `t₁ > t₂`.
- `z₀ = i·t₁` lies in `J₁` (points `i·t₁(1+ε)` escape for every `ε > 0`) and
  `dist(z₀, K₂) > 0`.

So for real pairs the candidate tip is **explicit**, and the *only* missing content is the
hole condition at `z₀`: that basin points near `z₀` reach `∞` inside `ℂ ∖ (K₁ ∪ K₂)`.

## Attack routes

1. **Janiszewski (the route that solved Problem 3).** If `K₁ ∩ K₂` is connected, then — both
   sets being nonseparating continua — Janiszewski's theorem makes `K₁ ∪ K₂` nonseparating:
   **no holes at all**, and the explicit tip finishes. So it suffices to prove:
   > for some nonempty class of real pairs as above, `K_{c₁} ∩ K_{c₂}` is connected.
   Both sets are symmetric about `ℝ` and intersect `ℝ` in the nested intervals
   `[−β_i, β_i]`. Is the intersection connected for all real pairs? For pairs with `c_i`
   close together? A counterexample here would also be valuable (it would force route 2/3).
2. **Extremal length / channel modulus** (Problem 3's original route 2): at a
   hole-accumulation point `z₀ ∉ K₂`, infinitely many disjoint hole-channels of diameter
   `≥ dist(z₀, K₂) − o(1)` cross every small circle `∂B(z₀, ρ)`; sum the moduli of the
   disjoint family against the annulus bound.
3. **Harmonic measure / prime ends** (Problem 3's route 1): hole-accumulation points as a
   harmonic-measure-null or nowhere-dense subset of `∂W ∖ K₂` — the downstream argument can
   discard a countable or nowhere-dense bad set.

## Why exceptional partners do not count (context)

For `c₂ ∈ {0, −2}` the coordinate `φ_{c₂}` is algebraic over `ℂ(z)`, so the pair
independence statement is vacuous (a nonzero relation always exists), and the surviving
single-coordinate content — transcendence of `φ_{c₁}` over `ℂ(z)` — is already an
unconditional machine-checked theorem via the disk-model natural boundary, needing no tip.
The tip's unique load-bearing consumer is the **both-connected nonexceptional** pair case:
a relation between `φ_{c₁}` and `φ_{c₂}` propagates (identity theorem) from the far field
through `W` only; at a hole-free tip every `J₁`-point nearby is a limit of relation-carrying
points, and the root-limit + Baire pigeonhole + boundary-rigidity chain (formalized / in
verified preparation) closes the theorem.

## Acceptance criterion

A rigorous paper proof of the Statement for an explicitly described nonempty class of pairs
with **both `c_i ∈ M ∖ {0, −2}`** (e.g. both real in `(−2, 1/4] ∖ {0}`) — or a
counterexample pair together with a characterization of when the hole-free tip exists.
Classes containing an exceptional parameter (`0` or `−2`) do not qualify.
