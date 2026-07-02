# Open Problem 5: Hole-free accessible boundary points for every pair of connected quadratic filled Julia sets

**Field:** plane topology / complex dynamics / potential theory.
**Self-contained:** everything needed is defined below; classical results from the literature
may be used freely with citation. **The request:** solve the Problem as stated and provide a
complete rigorous proof (paper mathematics; effective constants are welcome but not required).

## Setting

For a parameter `c ∈ ℂ` let

- `f_c(z) = z² + c`,
- `K_c = { z ∈ ℂ : the orbit z, f_c(z), f_c(f_c(z)), … stays bounded }` — the **filled Julia
  set**, a compact set with connected complement,
- `J_c = ∂K_c` — the **Julia set**.

Recall that `K_c` is connected exactly when `c` lies in the Mandelbrot set `M` (equivalently,
`0 ∈ K_c`), and that for every `c ∈ M` one has `0 ∈ K_c`. The two parameters `c = 0`
(where `J_c` is the unit circle) and `c = −2` (where `K_c = [−2, 2]`) are called
**exceptional** and are excluded throughout.

Fix two parameters

> `c₁ ≠ c₂`, both in `M ∖ {0, −2}`,

so both filled Julia sets are connected, and note `0 ∈ K_{c₁} ∩ K_{c₂}` — the two sets
**always overlap**. Write

- `X = K_{c₁} ∪ K_{c₂}`,
- `W` = the unbounded connected component of `ℂ ∖ X`,
- **holes** = the bounded connected components of `ℂ ∖ X`.

Holes are the interesting objects here: each hole has boundary points in both `K_{c₁}` and
`K_{c₂}` (a bounded complementary component bounded by one of the sets alone cannot exist,
since each `K_{c_i}` has connected complement), so holes arise from a comb-like interlocking
of the two sets.

## The Problem

> **Prove: for every pair `c₁ ≠ c₂ ∈ M ∖ {0, −2}` there exist — possibly after exchanging
> the indices `1` and `2` — a point `z₀` and a radius `r > 0` with:**
>
> 1. `z₀ ∈ J_{c₁}`, `z₀ ∉ K_{c₂}`, and `z₀` lies on the boundary of the unbounded
>    component `W`;
> 2. `B(z₀, r) ∩ K_{c₂} = ∅`;
> 3. `B(z₀, r) ∩ H = ∅` for **every** hole `H` of `X`.
>
> **If this fails for some pairs, characterize exactly the exceptional pairs.**

In words: some boundary point of one Julia set, escaping the other filled set and visible
from infinity, has a neighborhood in which *every* point outside the two filled sets can be
joined to `∞` without crossing them.

### Acceptable weakenings (any one of these is a complete solution)

The application consuming this statement can discard a small bad set, so each of the
following also fully solves the Problem:

- **(W1) Nowhere-dense version.** Show that the set of points of `∂W ∩ J_{c₁} ∖ K_{c₂}`
  at which holes accumulate is **nowhere dense** in `∂W ∩ J_{c₁} ∖ K_{c₂}` (or has zero
  harmonic measure as seen from `∞`, together with the statement that
  `∂W ∩ J_{c₁} ∖ K_{c₂}` itself is nonempty after a suitable choice of indices — this
  nonemptiness is elementary and may be assumed).
- **(W2) Topological criterion.** Show that `K_{c₁} ∩ K_{c₂}` is **connected** for every
  pair as above. (By Janiszewski's theorem, the union of two nonseparating continua with
  connected intersection is nonseparating, so there would be **no holes at all** and any
  accessible point of `J_{c₁} ∖ K_{c₂}` works.) A characterization of the pairs with
  connected intersection, combined with a direct treatment of the disconnected-intersection
  pairs, is equally welcome.
- **(W3) Characterization.** A counterexample pair together with a complete
  characterization of when the hole-free point exists.

### What does NOT suffice

- Proofs for a restricted subclass of pairs. (The case of both parameters real with
  `−3/4 < c₂ < c₁ < 0` is already settled: there `K_{c₂} ∩ i·ℝ ⊊ K_{c₁} ∩ i·ℝ` are nested
  segments, the point `z₀ = i·√(β₁ + c₁)` with `β₁ = (1+√(1−4c₁))/2` is an explicit choice,
  and the Julia set of a hyperbolic parameter is a Jordan curve, so a Schoenflies collar
  plus the escape ray along the imaginary axis puts a whole ball outside all holes. The open
  content is the **general** pair, where neither set need be locally connected, no explicit
  symmetry is available, and hole-accumulation could a priori happen everywhere.)
- Replacing either parameter by `0` or `−2`.

## Known facts that may be used without proof

1. Each `K_c` is compact, full (connected complement), of logarithmic capacity `1`, with
   Green's function `G_c` continuous on `ℂ`, vanishing exactly on `K_c`, harmonic outside,
   and `G_c(z) = log|z| + o(1)` at infinity.
2. Each `J_c` is perfect. Distinct parameters have distinct filled Julia sets
   (`K_{c₁} = K_{c₂} ⟹ c₁ = c₂`).
3. `J_{c₁} ⊄ K_{c₂}` after a suitable choice of indices, and `∂W ∖ K_{c₂}` is then a
   nonempty subset of `J_{c₁}`.
4. Every hole `H` satisfies `∂H ∩ K_{c₁} ≠ ∅` and `∂H ∩ K_{c₂} ≠ ∅`. Consequently, if
   infinitely many distinct holes accumulate at a point `z₀ ∉ K_{c₂}`, their diameters are
   bounded below by `dist(z₀, K_{c₂}) − o(1) > 0`: near `z₀` they form infinitely many
   disjoint channels of definite diameter, all crossing every small circle `∂B(z₀, ρ)` on
   their way to `K_{c₂}`.
5. Anything from the standard literature on polynomial dynamics, plane topology, and
   potential theory (Douady–Hubbard theory, external rays and their landing behaviour,
   prime ends, extremal length, harmonic measure, Janiszewski-type separation theorems, …),
   with citation.

## Suggested attack routes (take or ignore freely)

1. **Extremal length at an accumulation point.** Fact 4 gives, at a hole-accumulation point
   `z₀`, infinitely many disjoint channels of diameter `≥ δ₀` crossing every circle
   `∂B(z₀, ρ)` for `ρ < δ₀`. Disjoint families of crossings of the annulus
   `B(z₀, δ₀) ∖ B(z₀, ρ)` carry conformal modulus; summing against the annulus bound as
   `ρ → 0` looks contradictory — but the channels may share the annulus in a way that needs
   a genuinely quantitative argument. If this works it likely proves much more than (W1).
2. **Prime ends / harmonic measure.** `W ∪ {∞}` is a simply connected domain on the sphere.
   Uniformize by the Riemann map from the disk; accessible prime ends are dense; the
   question is whether hole-accumulation can happen at a set of full harmonic measure of
   the `J_{c₁} ∖ K_{c₂}` part of the boundary. F. & M. Riesz-type theorems are relevant.
3. **External rays.** Rays of `K_{c₁}` landing on `J_{c₁} ∖ K_{c₂}` approach `∂W` from `W`;
   the interplay between the two ray foliations near a common boundary arc may rule out
   hole-accumulation at every landing point of a ray avoiding `K_{c₂}` — landing points are
   dense enough for (W1) if one shows a positive-measure set of rays lands off `K_{c₂}`.
4. **The intersection criterion (W2).** Nothing known to us excludes
   `K_{c₁} ∩ K_{c₂}` disconnected; but no example is known to us either. Even resolving
   this side question in either direction would be valuable.

## Deliverable

A rigorous, self-contained proof (modulo cited literature) of the Problem or of one of the
weakenings (W1)–(W3), written so that each step can be checked and, eventually, formalized.
