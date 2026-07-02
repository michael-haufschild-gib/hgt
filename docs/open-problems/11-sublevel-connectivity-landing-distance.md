# Open Problem 11: Connected sublevel sets of the landing-distance function at the β fixed point

**Field:** complex dynamics (one variable) / one-dimensional topology of self-similar
functions.
**Self-contained:** everything needed is defined below; classical results from the
literature may be used freely with citation. **The request:** prove the Problem (any
explicitly described subrange of the parameter is a complete partial solution), or
refute it.

This is a ONE-DIMENSIONAL problem: it concerns a single continuous function on the
circle.

## Setting

For REAL `c ∈ [−2, 1/4)` let `f_c(z) = z² + c`,

- `K_c = { z ∈ ℂ : the f_c-orbit of z stays bounded }` — compact, full, connected for
  these `c`; `J_c = ∂K_c`;
- `β = (1 + √(1−4c))/2` — the larger (repelling) fixed point, real, `β ∈ J_c`, with
  real multiplier `λ := f_c'(β) = 2β ∈ (1, 4]`;
- `Ψ_c : {|ζ| > 1} → ℂ ∖ K_c` — the inverse Böttcher coordinate: the conformal
  isomorphism with `Ψ_c(ζ)/ζ → 1` at `∞`, conjugating `ζ ↦ ζ²` to `f_c`:
  `Ψ_c(ζ²) = f_c(Ψ_c(ζ))`.

**Facts usable without proof (with citation):**

1. **Local connectivity on the whole real slice.** `J_c` is locally connected for
   every real `c ∈ [−2, 1/4]` — including non-hyperbolic parameters (Levin–van
   Strien, *Local connectivity of the Julia set of real polynomials*). Consequently
   (Carathéodory) `Ψ_c` extends continuously to `{|ζ| = 1}`, defining the continuous
   surjective **landing map**
   `γ_c : ℝ/ℤ → J_c`, `γ_c(t) = Ψ_c(e^{2πit})`, with `γ_c(2t) = f_c(γ_c(t))`.
2. **Only the angle `0` lands at `β`.** The external ray of angle `0` lands at `β`
   and no other ray lands there (Douady–Hubbard; Milnor), i.e. `γ_c⁻¹(β) = {0}`.
3. `K_c ∩ ℝ = [−β, β]`; `K_c ⊆ closedBall(0,2)`; `K_c` is invariant under complex
   conjugation, and `γ_c(−t) = conj(γ_c(t))`.

## The object

Define the **landing-distance function**

> `φ = φ_c : ℝ/ℤ → [0, ∞)`, `φ(t) = |γ_c(t) − β|`.

Its basic properties (immediate from the facts above; one-line proofs):

- `φ` is continuous, and `φ(t) = 0` ⟺ `t = 0`;
- `φ(−t) = φ(t)` (conjugation symmetry);
- **exact self-similarity**: from `Ψ(ζ²) = f_c(Ψ(ζ))` and
  `f_c(z) − β = (z − β)(z + β)`,

  > `φ(2t) = φ(t) · |γ_c(t) + β|`, and `|γ_c(t) + β| → 2β = λ` as `t → 0`.

  So near `t = 0` the profile of `φ` reproduces itself under angle-doubling with
  multiplicative factor `≈ λ`: the graph of `log φ` against `log t` is asymptotically
  periodic.

## The Problem

> **Prove: for every real `c ∈ [−2, 1/4)` (or every `c` in an explicitly described
> subrange) and every `ε > 0` there exists `0 < ρ < ε` such that the sublevel set**
>
> `{ t ∈ ℝ/ℤ : φ_c(t) < ρ }`
>
> **is connected (a single open arc, necessarily containing `t = 0`).**

Equivalently: there exist arbitrarily small levels `ρ` at which no "side well" of
`φ_c` away from `t = 0` dips below `ρ` while being separated from the central arc by a
barrier `≥ ρ`.

### What is known about the level structure

- The sublevel `{φ < ρ}` always contains an open arc around `0`; disconnection means
  some angle bounded away from that arc has `φ(t) < ρ` — a **near-miss**: an external
  ray of angle far from `0` landing at distance `< ρ` from `β`.
- The strong form ("all small `ρ`") is FALSE in general: numerically at `c = −0.9`
  the sublevels are disconnected for `ρ` in bands recurring once per multiplicative
  period `λ ≈ 3.1448` down to at least `ρ ≈ 0.003` (stable rasterized bounded-orbit
  computations of the equivalent planar statement; see below for the equivalence).
  The same computations show wide CLEAN bands of `ρ` in every period — the Problem
  asserts exactly that clean levels never die out.
- By the self-similarity, the pattern of side wells near level `0` is asymptotically
  one fundamental pattern repeated with factor `λ`; a proof that ONE clean level
  exists per fundamental scale-window, robustly under the `o(1)` distortion of the
  factor `|γ_c(t) + β|`, would settle the Problem. (Caution: the self-similarity is
  asymptotic, not exact, so a one-window check must come with distortion control.)

### Suggested routes (take or ignore freely)

1. **Well-versus-barrier geometry.** For a side well `w` (a local-minimum region of
   `φ` away from `0`), let `d(w)` be its bottom value and `b(w)` the smaller of the
   two barrier heights separating it from the central arc's basin. The bad levels
   contributed by `w` form the interval `(d(w), b(w))`. The Problem asserts the union
   of these intervals does not cover a neighborhood of `0`. A bound
   `b(w) ≤ C·d(w)` (bounded multiplicative well aspect), plus summable/sparse well
   distribution per period, would suffice. Well bottoms are near-miss distances of
   dyadic-adjacent rays; Koebe distortion along the pullbacks that create a well
   controls both `d(w)` and `b(w)` by the same conformal factor — this is the most
   concrete attack.
2. **Symbolic dynamics.** Under angle-doubling, a well is created at `t` when the
   itinerary of `t` begins with a long block of `0`s after some prefix (the orbit
   shadows `β`); `d(w)` and `b(w)` are then comparable to `λ^{−(length)}` times
   prefix-dependent factors. The Problem becomes a statement about the value-ranges
   of finitely many prefix classes per scale window.
3. **Hyperbolic subranges first.** For hyperbolic real `c` the landing map is Hölder
   and the distortion is uniformly bounded; the parabolic-adjacent and Feigenbaum
   parameters are harder and can be excluded from a first partial solution. The
   endpoint `c = 1/4` (where `λ = 1` and the self-similarity degenerates) is excluded
   from the Problem as stated.

## Why this suffices (the planar consequence — proved, may be assumed)

The following reduction is already established and may be used as a black box; it is
why only the 1D statement above is open. For all but countably many `ρ` (excluding
the local-minimum values of `φ_c`), if `{φ_c < ρ}` is connected then
`B(β,ρ) ∖ K_c` is connected in the plane. Hence the Problem implies: for every
`ε > 0` there is `ρ < ε` with `B(β,ρ) ∖ K_c` connected — "cofinal one-sidedness" of
`β`. For two real parameters `c₁ < c₂` (both nonexceptional) this produces at
`β₁ = β(c₁)` — which lies off `K_{c₂}` and is visible from infinity along the real
ray — arbitrarily small balls meeting no bounded complementary component of
`K_{c₁} ∪ K_{c₂}`: the final geometric input in a proof that the Böttcher coordinates
of `f_{c₁}` and `f_{c₂}` are algebraically independent over `ℂ(z)` for all such real
pairs.

## Deliverable

A rigorous, self-contained proof (modulo cited literature) of the Problem for all
real `c ∈ [−2, 1/4)` or an explicitly described subrange; or a refutation exhibiting
a real `c` where every sufficiently small level is disconnected.
