# Open Problem 8: A cofinally one-sided Julia point on the outer boundary of a union of two quadratic filled Julia sets

**Field:** complex dynamics / plane topology / potential theory.
**Self-contained:** everything needed is defined below and every nonclassical input is
proved inline; classical results from the literature may be used freely with citation.
**The request:** prove the Problem as stated (or one of the listed weakenings) with a
complete rigorous proof, or refute it with a characterization of the failing pairs.

## Setting

For a parameter `c ∈ ℂ` let

- `f_c(z) = z² + c`,
- `K_c = { z ∈ ℂ : the orbit z, f_c(z), f_c(f_c(z)), … stays bounded }` — the **filled
  Julia set**, a compact set with connected complement (a *full* compact set),
- `J_c = ∂K_c` — the **Julia set**,
- `G_c` — the Green's function of `ℂ ∖ K_c` with pole at `∞`: continuous on `ℂ`,
  vanishing exactly on `K_c`, harmonic outside, `G_c(z) = log|z| + o(1)` at `∞`, and
  `G_c(f_c(z)) = 2 G_c(z)`. Each `K_c` has logarithmic capacity `1`.

`K_c` is connected exactly when `c` lies in the Mandelbrot set `M`. The parameters
`c = 0` (closed unit disk) and `c = −2` (segment `[−2,2]`) are **exceptional** and
excluded. Fix

> `c₁ ≠ c₂`, both in `M ∖ {0, −2}`,

write `K_i = K_{c_i}`, `J_i = J_{c_i}`, and

- `X = K₁ ∪ K₂` (note `0 ∈ K₁ ∩ K₂`, so `X` is connected),
- `W` = the unbounded connected component of `ℂ ∖ X`,
- `Y = ℂ ∖ W` — the filled hull of `X`; `Y` is compact and full, `∂Y = ∂W`.

## The local condition, and why it is stated cofinally

For `p ∈ J_c` and `ρ > 0` consider the **punctured ball** `B(p,ρ) ∖ K_c`.

- `p` is **strictly one-sided** if there is `ρ₀ > 0` such that `B(p,ρ) ∖ K_c` is
  connected for EVERY `0 < ρ ≤ ρ₀`.
- `p` is **cofinally one-sided** if for every `ε > 0` there is SOME `0 < ρ < ε` with
  `B(p,ρ) ∖ K_c` connected.

The cofinal form is the correct one here, for two reasons.

1. **It is all the application needs.** The downstream argument requires, at a point
   `p ∉ K₂`, a single radius `ρ` below the clearance `dist(p, K₂)` with
   `B(p,ρ) ∖ K₁` connected; arbitrarily small good radii therefore suffice. (Note
   connectivity of `B(p,ρ) ∖ K` is NOT monotone in `ρ` — shrinking the ball can
   disconnect the complement — so the two forms genuinely differ.)
2. **The strict form fails at natural witness points.** Numerical evidence at
   `c = −0.9` (real, period-2 hyperbolic window; `β = (1+√4.6)/2 ≈ 1.5724` the
   landing point of the external ray of angle `0`, a single access): rasterized
   escape-time tests (grids up to `1601²`, up to `8000` iterations, escape radius `9`)
   show `B(β,ρ) ∖ K_c` DISCONNECTED for `ρ ≈ 0.0962, 0.0306, 0.00973, 0.00309` —
   consecutive ratios exactly `λ = 2β ≈ 3.1448`, i.e. one per scaling period of the
   (real-multiplier) linearization — by mirror-symmetric pairs of complementary pockets
   at the ball rim, of stable relative area `≈ 2–4 · 10⁻⁴`, cut off inside the ball by
   limbs of `K_c` and rejoining the exterior only outside the ball. Counts are
   unchanged from 800 to 3200 iterations and stable under grid refinement, and the
   pocket positions scale self-similarly toward `β`. So a point can have a single
   access yet fail strict one-sidedness at log-periodically recurring scales — while
   remaining cofinally one-sided (clean bands of `ρ` recur every period).

## The Problem

> **Prove: for every pair `c₁ ≠ c₂ ∈ M ∖ {0, −2}` there exists — possibly after
> exchanging the indices — a point `x ∈ J₁` with**
>
> 1. `x ∉ K₂`,
> 2. `x ∈ ∂W` (visible from infinity), **and**
> 3. `x` cofinally one-sided for `K₁`.
>
> **If this fails for some pairs, characterize the exceptional pairs.**

### Why such a point matters

At such an `x`, any radius `ρ < dist(x, K₂)` with `B(x,ρ) ∖ K₁` connected gives a ball
meeting no bounded complementary component of `X` (the connected punctured ball meets
`W`, hence lies in `W`). This "hole-free ball at an exposed Julia point" is the last
geometric input in a proof that the Böttcher coordinates `φ_{c₁}` and `φ_{c₂}` (the
conformal maps conjugating `f_{c_i}` to `z ↦ z²` near `∞`, normalized `φ(z)/z → 1`) are
algebraically independent over the rational function field `ℂ(z)` for every pair of
distinct nonexceptional connected parameters.

## Known facts (proved inline or citable)

**KF1 (exposure).** After possibly exchanging indices, `E := ∂W ∖ K₂` is a nonempty
subset of `J₁`.
*Proof.* If `∂W ⊆ K₂` then, since `Y` is the filled hull of `X` and `K₂` is full,
`Y ⊆ K₂`, so `K₁ ⊆ K₂`. If also `∂W ⊆ K₁` then symmetrically `K₂ ⊆ K₁`, hence
`K₁ = K₂`; equality of the filled sets forces equality of Green's functions, and
`G(z²+c₁) = 2G(z) = G(z²+c₂)` for all `z` with surjectivity of `z ↦ z²` makes `G`
invariant under translation by `c₂ − c₁`, impossible for `G(z) = log|z| + o(1)` unless
`c₁ = c₂`. So after a swap `∂W ∖ K₂ ≠ ∅`; and any `x ∈ ∂W ∖ K₂` lies in `X ∖ K₂ ⊆ K₁`
with every neighborhood meeting `W ⊆ ℂ ∖ K₁`, so `x ∈ J₁`. ∎

**KF2 (the exposed set has positive equilibrium measure).** Let `μ₁` be the
equilibrium measure of `K₁` (= harmonic measure of `ℂ̂ ∖ K₁` at `∞`), and `ν` the
equilibrium measure of `Y` (= harmonic measure of `W` at `∞`), `R = cap(Y)`. Then
`μ₁(E) ≥ ν(E) > 0`.
*Proof.* For a full compact `A` with continuous potential write
`p_A(z) = ∫ log|z−w| dν_A(w)`; then `G_A = p_A − log cap(A)` on `ℂ`. For `K₂ ⊆ Y`,
Fubini symmetry of the mutual energy `∫ p_{K₂} dν_Y = ∫ p_Y dν_{K₂}` gives
`∫ G_{K₂} dν_Y = ∫ G_Y dν_{K₂} + log R − log cap(K₂) = 0 + log R − 0 = log R`,
using `G_Y = 0` on `Y ⊇ K₂ ⊇ supp ν_{K₂}` and `cap(K_c) = 1`. If `R = 1`, the same
identity with `K₁` gives `∫ G_{K₁} dν_Y = ∫ G_{K₂} dν_Y = 0`; since `G_i ≥ 0` are
continuous and vanish exactly on `K_i`, `supp ν_Y ⊆ K₁ ∩ K₂`; but `supp ν_Y = ∂W`
(outer boundary), so `∂Y ⊆ K₁` forces `Y ⊆ K₁` (fullness), hence `K₂ ⊆ K₁` and
symmetrically `K₁ = K₂`, contradicting KF1's endgame. So `R > 1` and
`∫ G_{K₂} dν_Y = log R > 0`, which forces `ν_Y({G_{K₂} > 0}) > 0`, i.e.
`ν(∂W ∖ K₂) > 0`. Finally `W ⊆ ℂ̂ ∖ K₁` share the boundary portion `E ⊆ ∂W ∩ J₁`, and
harmonic measure increases under domain enlargement (subordination), so
`μ₁(E) ≥ ν(E) > 0`. ∎

**KF3 (single-access points, density).** The external ray of angle `0` lands at the
β-fixed point (no local connectivity needed), no other ray lands there, and at a
repelling or parabolic landing point the number of local accesses to `ℂ ∖ K_c` equals
the number of rays landing there (Douady–Hubbard; Milnor, *Dynamics in One Complex
Variable*; Eremenko–Levin for landing at repelling points). Pullbacks along orbits
avoiding the critical point preserve access counts, and backward orbits are dense in
`J_c`; the resulting dense single-access set is countable. CAUTION: a single access
does NOT imply strict one-sidedness (see the `c = −0.9` evidence above), and says
nothing directly about the cofinal form either; access counting and ball-connectivity
must not be conflated.

**KF4 (μ_c basics).** `μ_c` is a non-atomic Borel probability measure with support
`J_c`, invariant and ergodic under `f_c`, of entropy `log 2` (Brolin).

## What is known NOT to work

- **(N1) Measure + a.e. strict one-sidedness.** The needed a.e. statement is FALSE:
  at the basilica `c = −1`, the strictly one-sided points form a `μ_{−1}`-null set.
  *Sketch.* The two rays of angles `1/3, 2/3` land at the repelling fixed point
  `α = (1−√5)/2`, giving two accesses, hence a radius `R₀` with `B(α,R₀) ∖ K`
  disconnected by two marked exterior points near `α`. The ball avoids the postcritical
  set `{0,−1}`, so along any orbit segment `f^n(p) ∈ B(α,η)` the inverse branch is
  univalent on `B(f^n(p),R₀)`; Koebe ¼ + distortion transport the two marked points
  into `B(p, s_n)` with `B(p,s_n) ∖ K` disconnected, and hyperbolicity gives
  `s_n ≤ C λ^{−n} → 0`. By ergodicity (Birkhoff), a.e. orbit visits `B(α,η)`
  infinitely often, so a.e. `p` has disconnected punctured balls at arbitrarily small
  scales. ∎ — Note this kills only the STRICT form a.e.; whether a.e. points are
  *cofinally* one-sided is open (see W2).
- **(N2) Measure + density.** The dense single-access set of KF3 is countable and
  `μ_c` non-atomic, so a positive-measure set need not meet it; `E` can a priori avoid
  every β-preimage.
- **(N3) Density + topology.** `E` need not be relatively open in `J₁`, so density of
  good points in `J₁` does not put one inside `E`.
- **(N4) Pure local analysis at a marked point.** The number of accesses is a
  prime-end/global datum; the `c = −0.9` evidence shows local ball behavior at a
  single-access point can still be bad on recurring scale bands. Any solution must
  control ball geometry, not count accesses.

## Acceptable weakenings (any one is a complete solution)

- **(W1) Subclass of pairs.** The statement for all pairs in an explicitly described
  subclass — e.g. both parameters in the main cardioid (where `J_c` is a Jordan
  quasicircle with no cut points). The subclass of pairs of REAL parameters reduces to
  the single-parameter Problem 9 of this series (for real `c₁ < c₂ ≤ 1/4` the witness
  can be taken to be the β-fixed point of `c₁`: it lies off `K₂` since
  `K₂ ∩ ℝ = [−β₂, β₂]` with `β₂ < β₁`, and the real ray `(β₁, ∞)` exhibits it on
  `∂W`; only the cofinal ball-connectivity at `β₁` is missing) — so W1 solutions
  should target complex subclasses.
- **(W2) Full measure of cofinal points.** Prove for every `c ∈ M ∖ {0,−2}` (or a
  subclass) that the COFINALLY one-sided points of `J_c` have full `μ_c` measure; then
  KF2 and a pigeonhole finish the Problem on that class. Unlike the strict form (N1),
  this is open even at the basilica: the pullback argument produces infinitely many
  bad scales a.e. but says nothing against infinitely many good scales coexisting.
- **(W3) Refutation** of the full statement, with a characterization of failing pairs
  — noting which weakening survives.

## Deliverable

A rigorous, self-contained proof (modulo cited literature) of the Problem or of one of
(W1)–(W3), written so that each step can be checked independently.
