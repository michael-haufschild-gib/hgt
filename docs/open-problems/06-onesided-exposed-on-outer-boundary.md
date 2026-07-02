# Open Problem 6: A one-sided boundary point visible from infinity, for a pair of quadratic filled Julia sets

**Field:** plane topology / complex dynamics.
**Self-contained:** everything needed is defined below; classical results from the
literature may be used freely with citation. **The request:** solve the Problem as stated
and provide a complete rigorous proof.

## Setting

For a parameter `c ∈ ℂ` let

- `f_c(z) = z² + c`,
- `K_c = { z ∈ ℂ : the orbit z, f_c(z), f_c(f_c(z)), … stays bounded }` — the **filled
  Julia set**, a compact set with connected complement (a *full* compact set),
- `J_c = ∂K_c` — the **Julia set**.

`K_c` is connected exactly when `c` lies in the Mandelbrot set `M`. The parameters `c = 0`
(where `K_c` is the closed unit disk) and `c = −2` (where `K_c = [−2,2]`) are called
**exceptional** and are excluded throughout.

Fix two parameters

> `c₁ ≠ c₂`, both in `M ∖ {0, −2}`,

so both filled Julia sets are connected, and note `0 ∈ K_{c₁} ∩ K_{c₂}`, so the union
overlaps. Write

- `X = K_{c₁} ∪ K_{c₂}`,
- `W` = the unbounded connected component of `ℂ ∖ X`,
- **holes** = the bounded connected components of `ℂ ∖ X`. Each hole has boundary points
  in both `K_{c₁}` and `K_{c₂}` (a bounded complementary component bounded by one of the
  sets alone cannot exist, since each `K_{c_i}` is full), so holes arise from a comb-like
  interlocking of the two sets.

**One-sided points.** Call `p ∈ J_c` **one-sided** if there is `ρ₀ > 0` such that for
every `0 < ρ ≤ ρ₀` the set `B(p, ρ) ∖ K_c` is connected — a single local access to the
exterior. For example, the β-fixed point of `f_c` (the landing point of the external ray
of angle `0`) is one-sided for every `c ∈ M ∖ {0, −2}`, and so is every iterated
`f_c`-preimage of it along orbits avoiding the critical point `0`; these preimages are
dense in `J_c` (see Known Facts 3 below).

## The Problem

> **Prove: for every pair `c₁ ≠ c₂ ∈ M ∖ {0, −2}` there exists — possibly after
> exchanging the indices `1` and `2` — a ONE-SIDED point `x ∈ J_{c₁}` with**
>
> 1. `x ∉ K_{c₂}`, **and**
> 2. `x ∈ ∂W` — the point is on the boundary of the unbounded component, i.e. visible
>    from infinity.
>
> **If this fails for some pairs, characterize exactly the exceptional pairs.**

### Why condition 2 is the entire content

Dropping condition 2, the statement is TRUE and elementary; the following two
observations may be used without proof (short proofs are included so the document stands
alone):

- **(A) A one-sided visible point has a hole-free neighborhood.** Suppose `x` is
  one-sided, `x ∉ K_{c₂}`, and `x ∈ ∂W`. Choose `r` below both `ρ₀` and
  `dist(x, K_{c₂})`. Then `B(x,r) ∩ K_{c₂} = ∅`, so
  `B(x,r) ∖ X = B(x,r) ∖ K_{c₁}`, which is connected by one-sidedness. Since `x ∈ ∂W`,
  this connected set meets the component `W`, hence lies in `W`; so no hole meets
  `B(x,r)`. (This is why the Problem matters: such an `x` is a boundary point of one
  Julia set, at positive distance from the other filled set, with a ball meeting no hole
  — the configuration our application consumes.)
- **(B) A one-sided point off the other set always exists (without condition 2).**
  Suppose, for contradiction, that every one-sided point of `J_{c₁}` lies in `K_{c₂}` and
  every one-sided point of `J_{c₂}` lies in `K_{c₁}`. One-sided points are dense in each
  Julia set (Known Fact 3) and the filled sets are closed, so `J_{c₁} ⊆ K_{c₂}` and
  `J_{c₂} ⊆ K_{c₁}`. Fullness upgrades boundary inclusion to full inclusion: every
  bounded component `U` of `ℂ ∖ J_{c₁}` has `∂U ⊆ J_{c₁} ⊆ K_{c₂}`, and the unbounded
  component of `ℂ ∖ K_{c₂}` is connected, misses `∂U`, and has points outside `U`, hence
  misses `U`; so `U ⊆ K_{c₂}`, giving `K_{c₁} ⊆ K_{c₂}`, and symmetrically
  `K_{c₂} ⊆ K_{c₁}`. So `K_{c₁} = K_{c₂}`, hence the Green's functions coincide; from
  `G(z² + c₁) = 2G(z) = G(z² + c₂)` for all `z` and surjectivity of `z ↦ z²`, the Green's
  function is invariant under translation by `c₂ − c₁`, which contradicts
  `G(z) = log|z| + o(1)` at infinity unless `c₁ = c₂`. Contradiction.

So the open content is exactly: **can the one-sided point off `K_{c₂}` be chosen on
`∂W`?**

### The obstruction to be excluded

A one-sided `x ∈ J_{c₁} ∖ K_{c₂}` has a small connected exterior piece
`U₀ = B(x,r) ∖ K_{c₁} = B(x,r) ∖ X` (for `r` as in (A)). Being connected, `U₀` lies in a
SINGLE component of `ℂ ∖ X` — either `W` (then `x ∈ ∂W` and we are done) or one hole. The
scenario to rule out (or characterize) is the **capped exterior**: every one-sided point
of `J_{c₁} ∖ K_{c₂}` (and symmetrically of `J_{c₂} ∖ K_{c₁}`) has its local exterior
inside a hole. For general full continua this genuinely happens: shape one set like a
bowl with `x` on the inner wall (one-sided into the cavity) and let the other set be a
lid closing the cavity at a distance — both full, connected, overlapping elsewhere; the
cavity is a hole and captures the only access of `x`. Nothing in general topology
prevents this, so the quadratic dynamics must be used in an essential way.

### Acceptable weakenings (any one is a complete solution)

- **(W1)** Show that not every one-sided point of `J_{c₁} ∖ K_{c₂}` has capped exterior
  (after a suitable choice of indices) — by (A), a single uncapped point suffices.
- **(W2)** Show that `∂W ∖ K_{c₂}` — after a swap this is a nonempty subset of `J_{c₁}`
  (Known Fact 4) — contains at least one one-sided point. Caution: one-sided points are
  dense in `J_{c₁}`, but `∂W ∖ K_{c₂}` need not be relatively open in `J_{c₁}`, so
  density alone does not conclude.
- **(W3)** A counterexample pair together with a complete characterization of the pairs
  for which the one-sided visible point exists.

### What does NOT suffice

- Producing a one-sided point off `K_{c₂}` without condition 2 — that is (B) above.
- Assuming local connectivity of `J_{c₁}` or `J_{c₂}` (the general case must handle
  non-locally-connected Julia sets).
- Replacing either parameter by `0` or `−2`.

## Known facts that may be used without proof

1. Each `K_c` (`c ∈ M`) is compact, full, connected, contained in the closed ball of
   radius `2`, of logarithmic capacity `1`, with Green's function `G_c` continuous on
   `ℂ`, vanishing exactly on `K_c`, harmonic outside, and `G_c(z) = log|z| + o(1)` at
   infinity; `G_c(f_c(z)) = 2·G_c(z)`.
2. Each `J_c` is perfect. Distinct parameters have distinct filled Julia sets.
3. External rays (`c ∈ M`): the ray of angle `0` lands at the β-fixed point — no local
   connectivity is needed; β is the landing point of no other ray; at a repelling or
   parabolic landing point the number of local accesses to `ℂ ∖ K_c` equals the number
   of rays landing there, so β is one-sided for `c ≠ 0, −2`; pullbacks along orbits
   avoiding the critical point preserve the number of accesses; backward orbits of
   boundary points are dense in `J_c`. Hence one-sided points are dense in `J_c` for
   `c ∈ M ∖ {0, −2}`, and each such point is the landing point of a single external ray
   of dyadic angle.
4. Every hole `H` of `X` satisfies `∂H ∩ K_{c₁} ≠ ∅` and `∂H ∩ K_{c₂} ≠ ∅`; after a
   suitable choice of indices, `∂W ∖ K_{c₂}` is a nonempty subset of `J_{c₁}`.
5. Anything from the standard literature on polynomial dynamics, plane topology, and
   potential theory (Douady–Hubbard theory, Milnor's book, prime ends, harmonic measure,
   extremal length, Janiszewski-type separation theorems, …), with citation.

## Suggested attack routes (take or ignore freely)

1. **Follow the ray.** A one-sided `x ∈ J_{c₁} ∖ K_{c₂}` is the landing point of a
   single external ray `R_{c₁}(θ)` of `K_{c₁}`, whose tail near `x` lies in the local
   exterior `U₀`. If the WHOLE ray is disjoint from `K_{c₂}`, it connects `U₀` to `∞`
   inside `ℂ ∖ X`, so `U₀ ⊆ W` and `x ∈ ∂W`, done. Since `K_{c₂}` lives in the ball of
   radius `2` while rays foliate a full neighborhood of `∞`, the question becomes: does
   some (equivalently, a dense or positive-measure set of) dyadic ray of `K_{c₁}` avoid
   `K_{c₂}` entirely AND land off `K_{c₂}`?
2. **Harmonic measure.** `∂W` carries the harmonic measure of `W` at `∞`. If the
   `J_{c₁} ∖ K_{c₂}` part of `∂W` has positive harmonic measure, combine with the fact
   that one-sided landing points carry the full equilibrium measure of `J_{c₁}` to
   produce a one-sided point on `∂W` measure-theoretically.
3. **Cap accounting.** A capped one-sided point's hole `H` has `∂H` meeting the
   connected set `K_{c₂}`, which misses the ball `B(x,r)`. Study whether one connected
   `K_{c₂}` can simultaneously cap a dense family of one-sided exteriors of `J_{c₁}`
   while the unbounded component still reaches the nonempty set `∂W ∖ K_{c₂}` — a
   separation constraint on the comb geometry.
4. **Level curves.** For small `s > 0` the level curve `{G_{c₁} = s}` is a real-analytic
   Jordan curve around `K_{c₁}` crossing every external ray; its portions inside `W`
   versus inside holes quantify which accesses are capped, and shrink as `s → 0`.

## Deliverable

A rigorous, self-contained proof (modulo cited literature) of the Problem or of one of
the weakenings (W1)–(W3), written so that each step can be checked and, eventually,
formalized.
