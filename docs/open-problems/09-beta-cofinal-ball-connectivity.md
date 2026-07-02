# Open Problem 9: Cofinal connectivity of punctured balls at the β fixed point of a real quadratic Julia set

**Field:** complex dynamics (one variable) / plane topology.
**Self-contained:** everything needed is defined below and every nonclassical input is
proved inline; classical results from the literature may be used freely with citation.
**The request:** prove the Problem as stated (any parameter subrange is a valuable
partial solution) with a complete rigorous proof, or refute it.

## Setting

For REAL `c ∈ [−2, 1/4]` let `f_c(z) = z² + c` on `ℂ`,

- `K_c = { z : the f_c-orbit of z is bounded }` (compact, full, connected for these `c`),
- `J_c = ∂K_c`,
- `β = β(c) = (1 + √(1−4c))/2` — the larger fixed point of `f_c`, real, `β ∈ J_c`,
  with real multiplier `f_c'(β) = 2β ∈ [1, 4]` (repelling for `c < 1/4`, parabolic at
  `c = 1/4`).

Elementary facts, usable freely (one-line proofs indicated):

- **Real slice:** `K_c ∩ ℝ = [−β, β]`. (`x > β ⟹ x < f_c(x)` and any bounded
  increasing orbit would converge to a real fixed point `> β`, impossible; `x < −β`
  maps beyond `β` in one step; `|x| ≤ β ⟹ |f_c(x)| ≤ β` on the real slice.)
- **Symmetry:** `K_c` is invariant under complex conjugation (real coefficients) and
  under `z ↦ −z` (since `f_c(−z) = f_c(z)`).
- **Full invariance:** `f_c^{-1}(K_c) = K_c = f_c(K_c)`.
- **Single access at β:** the external ray of angle `0` lands at `β` and no other ray
  lands there; at a repelling landing point the number of local accesses to `ℂ ∖ K_c`
  equals the number of landing rays, so `β` has exactly one access (Douady–Hubbard;
  Milnor, *Dynamics in One Complex Variable*). CAUTION: as shown below, this does NOT
  settle the Problem — access counting and ball-connectivity are different notions.

## The Problem

> **Prove: for every real `c ∈ [−2, 1/4]` (equivalently: for every `c` in some
> explicitly described subrange — any subrange is a complete partial solution),**
>
> for every `ε > 0` there exists `ρ` with `0 < ρ < ε` such that
> `B(β, ρ) ∖ K_c` **is connected.**

Call this **cofinal one-sidedness** of `β`: good radii exist at every scale, though not
necessarily on a full interval of scales.

### Trivial and known cases

- `c = 0`: `K_0` is the closed unit disk, `β = 1`; `B(1,ρ) ∖ K_0` is a lune —
  connected for ALL `ρ`. Trivial.
- `c = −2`: `K_{−2} = [−2,2]`, `β = 2`; `B(2,ρ) ∖ [−2,2]` is a slit ball — connected
  for ALL `ρ`. Trivial.
- All other real `c` have fractal `J_c`; nothing is known rigorously.

### The strong form is FALSE — do not aim at it

One might hope for the stronger statement "`B(β,ρ) ∖ K_c` is connected for ALL small
`ρ`". Numerical evidence refutes it at `c = −0.9` (period-2 hyperbolic window,
`β ≈ 1.5724`, `λ := 2β ≈ 3.1448`): rasterized bounded-orbit tests (grids `401²`–`1601²`,
`800`–`8000` iterations, escape radius `9`, 4-connected component counts of the
complement inside the disk) find `B(β,ρ) ∖ K_c` DISCONNECTED at

> `ρ ≈ 0.0962, 0.0306, 0.00973, 0.00309` — consecutive ratios exactly `λ`,

i.e. once per scaling period, by conjugation-mirror pairs of complementary pockets of
stable relative area `≈ 2–4 · 10⁻⁴`, located at the ball rim and cut off inside the
ball by limbs of `K_c` (they rejoin the exterior only outside the ball). Component
counts are identical from `800` to `3200` iterations and stable under grid refinement;
pocket positions scale self-similarly toward `β`. Interpretation: the multiplier at `β`
is REAL, so the germ of `K_c` at `β` is asymptotically log-periodic in scale; whatever
pinching occurs at one scale recurs at every scale. The same data show wide CLEAN
`ρ`-bands in every period — which is exactly the cofinal statement. At
`c ∈ {0.2, 0.24, −0.5, −1.0}` every sampled phase over five periods was clean.

## Structural anchors (proved inline)

- **The real gate.** `(β, β + ρ) ⊆ B(β,ρ) ∖ K_c` (real slice), for `ρ < 2β`. Call the
  component of `B(β,ρ) ∖ K_c` containing it the **main component**.
- **Every component reaches the rim.** If `V` is a connected component of
  `B(β,ρ) ∖ K_c` with `∂V ∩ ∂B(β,ρ) = ∅`, then `∂V ⊆ K_c`, so `V` is a bounded open
  set with boundary in the full compact `K_c`, hence `V ⊆ K_c` — contradiction. So
  every component touches the rim, and **disconnection happens iff a "limb" of `K_c`
  chords the ball** (crosses it separating rim arcs).
- **Extra components avoid the axis and come in mirror pairs.** A component meeting
  `ℝ` meets `B(β,ρ) ∩ ℝ ∖ K_c = (β, β+ρ)` (for `ρ < 2β`), hence IS the main
  component; so any other component lies in an open half-ball, and conjugation
  symmetry pairs it with its mirror image.

So the Problem is: **find arbitrarily small radii at which no limb of `K_c` chords
`B(β,ρ)` off the real axis.**

## The known obstruction to the naive attack

The dynamics relates scales: `f_c` is univalent near `β` with real multiplier `λ`, so
inverse iteration maps the picture at scale `ρ` to the picture at scale `≈ ρ/λ`. But:

1. connectivity of `B(β,ρ) ∖ K_c` is NOT monotone in `ρ` (a limb entering deeper than
   the new rim can chord the smaller ball while the larger was clean), and
2. inverse branches distort round balls into non-round domains, and connectivity of
   `D ∖ K_c` for a distorted `D` says nothing about a round ball inside `D`.

So a clean radius does not obviously propagate to a clean radius one period down. Any
solution must break this, e.g. by controlling a full annulus of shapes, by quantifying
the distortion (Koebe) against the width of clean bands, or by a non-dynamical
argument.

## Suggested routes (take or ignore freely)

1. **Linearize and select a phase.** In the Koenigs coordinate at `β` (real `λ`), the
   germ of `K_c` becomes asymptotically invariant under `w ↦ λw`. The Problem becomes:
   a `λ`-invariant full germ, symmetric about `ℝ`, meeting `ℝ` exactly along
   `(−δ, 0]`, admits arbitrarily small clean round radii. Beware: this cannot be
   purely local — global inputs are available (`K_c ⊆ closedBall(0,2)`, the real
   slice, connectivity of `K_c`) and may be needed.
2. **Hyperbolic geometry of the basin.** For hyperbolic real `c` the basin of `∞` is a
   John (even uniform) domain (Carleson–Jones–Yoccoz for semi-hyperbolic maps, with
   citation): fjords have bounded aspect. A John constant bounds how deeply a limb can
   chord a ball relative to the mouth it leaves open — quantify to produce clean radii
   in each period.
3. **Inner disk anchor for `c ∈ (0, 1/4]`.** `|z| ≤ β ⟹ |z² + c| ≤ β² + c = β`, so
   `closedBall(0, β) ⊆ K_c`: the ball at `β` meets `K_c` in the round inner disk plus
   limbs confined to the annulus `β < |z| < (1+√(1+4c))/2`; control those limbs.
4. **Quasicircle range `−3/4 < c < 1/4`.** `J_c` is a quasicircle (hyperbolic Jordan
   case, with citation); bounded turning (Ahlfors' three-point property) bounds the
   diameter of the subarc between two nearby limb points — combine with the rim-pocket
   characterization above.

## What a solution yields

For real `c₁ < c₂` in `[−2, 1/4]`, both nonexceptional: `β₁ > β₂`, so `β₁ ∉ K₂`
(real slice), and the ray `(β₁, ∞)` lies in the complement of `K₁ ∪ K₂` — so `β₁` is
on the outer boundary of the union, visible from infinity. Cofinal one-sidedness at
`β₁` is then the ONLY missing clause to produce, at `β₁`, arbitrarily small balls
meeting no bounded complementary component of `K₁ ∪ K₂` — the final geometric input in
a proof that the Böttcher coordinates of `f_{c₁}` and `f_{c₂}` are algebraically
independent over `ℂ(z)` for all such real pairs. A refutation at some real `c` would
redirect that program and be equally decisive for this class.

## Deliverable

A rigorous, self-contained proof (modulo cited literature) for all real
`c ∈ [−2, 1/4]` or any explicitly described subrange, written so that each step can be
checked independently; or a refutation exhibiting a real `c` and a scale `ε` below
which every radius is disconnected.
