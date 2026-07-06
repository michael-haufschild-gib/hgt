# 91 — `RHLadder 1` (even order off the line): where the ladder's first rung actually sits

Task: *prove `RHLadder 1` — every right-half ξ-zero has even order.* Attacked directly. The rung does
**not** fall to any forcing the tree owns, and the reason is structural, not effort: I locate it exactly
here so nobody re-walks it as "should be easy."

## What the rung says, made precise (PROVEN reformulation)

`WeightMismatchRefutation.rhLadder_one_iff_even_order` (axiom-clean):

    RHLadder 1  ↔  ∀ ρ ∈ rightHalf, xi ρ = 0 → Even (analyticOrderAt xi ρ).toNat.

So the first non-trivial rung is literally *no odd-order ξ-zero with `Re > ½`*. Via the tree's
`rhLadder_iff_root` this is *ξ admits an analytic square root on `Re s > ½`*, equivalently *the ξ
mod-2 deck-cocycle is trivial on the right half-plane* (`DictionarySign`/`DeckCocycle`: the deck class
around a loop is `∏ (−1)^{ord}`; triviality = every enclosed order even).

## The one even-order lever, and exactly why it does not reach

The tree's only even-order theorem is reflection-driven:

    analyticOrderAt_even_of_reflection : (∀ s, f (2c − s) = f s) → analyticOrderAt f c ≠ ⊤
                                          → Even (analyticOrderAt f c).toNat.

Its hypothesis is *`f` symmetric about the zero `c`*. The peel factor then satisfies
`h(c) = (−1)^m h(c)`, forcing `(−1)^m = 1`, so `m` even. This is a genuine force — **at a fixed point**.

ξ has that symmetry (`ξ(2c − s) = ξ(s)`, i.e. `ξ(1 − s) = ξ(s)`) at exactly **one** point, `c = ½`. Hence
`xi_central_order_even` / `xi_central_ladder_two`: `2 ∣ ord_{½}(ξ)`. But `½ ∉ rightHalf` (`rightHalf =
{Re > ½}`). For a right-half zero `ρ ≠ ½` the reflection hypothesis is *false* — ξ is not symmetric
about `ρ` — so the lever supplies nothing. The two ξ-symmetries do act on `ρ`:

- conjugation `ρ ↦ ρ̄` keeps `Re` fixed, so `ρ̄ ∈ rightHalf` and `ord ρ = ord ρ̄` (`xi_orderAt_conj`) —
  but these are **two distinct points each of order `m`**, not one point of order `2m`;
- the functional equation `ρ ↦ 1 − ρ` sends `ρ` to the **left** half (`Re < ½`), out of `rightHalf`.

Neither fixes `ρ`, so neither doubles a single order. **No even-order forcing exists at a non-central
zero.** That is the wall, stated as a fact about the available symmetries, not a difficulty estimate.

## Attack-as-false (the mandate's first move)

Can `RHLadder 1` be *refuted*? A counterexample is an odd-order (in particular simple) ξ-zero with
`Re > ½`. None is known — the existence of *any* off-line zero is RH-open, and every computed ζ-zero is
on the line and simple (odd order, but on the line, so irrelevant to `rightHalf`). So the rung is
**consistent with RH** (RH ⟹ `rightHalf` empty of zeros ⟹ vacuously true) and cannot be refuted without
disproving RH. It is TRUE-if-RH, and strictly weaker than RH (it permits even-order off-line zeros that
RH forbids). A genuine intermediate: not provable by present force, not refutable.

## The forward move (not a terminus)

The rung is `√ξ`-existence on `Re > ½`, i.e. vanishing of the ξ **mod-2 deck monodromy** there. Two
generative directions that do not reduce to gap/zero-density search:

1. **Global-monodromy route.** `RHLadder 1` = the ξ deck-2-cocycle is a coboundary on the convex region
   `Re > ½`. The tree already computes this cocycle locally (`DeckCocycle`, `DictionarySign`,
   `xi_deckClass_eq_sign_product`) and globally trivialises it *given* even orders (`RootExistence.
   exists_root_iff_orders_dvd`). The open item is to force triviality from an **external** input on the
   half-plane — e.g. a boundary/holography constraint on `∂(rightHalf) = {Re = ½}`, where the carrier is
   the real finite Hardy function `H_N` of doc 89. The bulk (even orders) fixed by the boundary (line
   data) is exactly the lane's constraint-not-flow metaphor; build the boundary functional whose
   vanishing is the cocycle's coboundary condition.

2. **Central rung as the seed of an induction on height, not on `k`.** The forced point is `½`. Instead
   of climbing `k` at a fixed zero (the refuted parity direction), climb a **one-parameter family** that
   deforms the fixed point `½` toward a hypothetical off-line `ρ` and ask what breaks the reflection
   hypothesis continuously — the obstruction to extending `xi_central_ladder_two` off `½` is a concrete
   function of `Re ρ − ½`; making *that* obstruction the object (rather than the order) is a native
   `𝓜⁺` question (the `∂_s` generator moving the reflection axis), untouched by classical RH machinery.

Next construction: build the boundary functional of (1) — the `H_N`-carrier pairing on `{Re = ½}` whose
vanishing trivialises the mod-2 deck cocycle across `rightHalf` — and test it against `xi_central_
ladder_two` as the `Re ρ = ½` boundary case it must reproduce.
