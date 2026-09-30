# Floquet rigidity of the Weil cone on two geometric progressions

- **ID:** weil-two-geometric-floquet-rigidity
- **Stage:** 3-formalized (paper proof and Lean, 2026-09-30)
- **Type:** THEOREM [P + Lean] + REDUCTION [P]
- **Source:** `1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md`, entry L166
- **Lean:** `RHTower.eq_vonMangoldt_of_weilPositiveFull_of_two_geometric`,
  `RHTower.eq_vonMangoldt_of_weilPositiveFull_of_four_twentyOne`
  (modules `RHTower/RiemannKernelFloquetBlockTests`, `RHTower/WeilFullConeTwoGeometricRigidity`;
  axioms `propext`, `Classical.choice`, `Quot.sound`)

## Statement

**Theorem.** Let `b ≥ 4` and `c ≥ 2` be integers such that the fractional part of `log c / log b`
lies in `(1/6, 1/4)`. If `lam` is full-cone Weil-positive for ζ's archimedean datum and
`lam(n) = Λ(n)` for every `n ≥ 2` outside `{b^(q+1) : q ≥ 0} ∪ {c b^q : q ≥ 0}`, then `lam = Λ`.

No size condition is imposed on the deviation beyond the universal box `|lam(n)| ≤ √n(log n + C₀)`,
which every Weil-positive system satisfies.

**Instance.** `{4^(q+1)} ∪ {21·4^q}`. Its consecutive ratios alternate between `21/16 = 1.3125` and
`64/21`. The ratio `21/16` is below `4/3`, the threshold of the lacunary theorem (L165, paper) and
below `3/2` (L165, Lean). Other admissible pairs: `(b, c) = (4, 22)`, `(4, 81…90)`, `(5, 7)`,
`(5, 33…37)`, and so on.

## Proof

Write `v(n) = (Λ(n) − lam(n))/√n` and `X(ξ) = Ξ(2πξ)`. The only input from the positivity of `lam` is
the near-null pairing inequality (L160, L165): for every Schwartz `g` with `𝓕g = h/X`, where `h` is
smooth, real and supported in `|ξ| < 1633/1000`,
`Re Σ_n v(n)[T(log n) + T(−log n)] ≥ 0`, with `T(y) = ∫ h(ξ)² e^{2πiξy} dξ`.
The zero-free window `X ≠ 0` on `|ξ| ≤ 1633/1000` (`|t| ≤ 10.26`) comes from the fourth reciprocal
trace (L165).

1. **Floquet decomposition.** Put `ℓ = log b`, `P = 1/ℓ`, `α = log c`. The support lies on the
   lattice `ℓℤ` and its translate `α + ℓℤ`. Let `ψ` be a smooth bump supported in `[−δ, P + δ]` with
   `Σ_n ψ(ξ + nP)² = 1` (a sine–cosine partition over the ramp; `δ = P/8`). For a block
   `h_k(η)² = ψ(η − kP)² w(η − kP)`, with `w` periodic on the overlap `[−δ, δ]`, unfolding over
   three periods gives, for integer `q` and real `β`,
   `∫ h_k² e^{2πiη(β + qℓ)} dη = ∫₀^P w(ξ) e^{2πiξ(β+qℓ)} e^{2πikPβ} Ψ_β(ξ) dξ`,
   where `Ψ_β(ξ) = ψ(ξ−P)² e^{−2πiPβ} + ψ(ξ)² + ψ(ξ+P)² e^{2πiPβ}`. The key fact is
   `e^{2πi mP qℓ} = 1`, because `Pℓ = 1`.
2. **Three blocks and barycentric weights.** Take blocks `k = −2, 0, 1`, with vertices
   `z_k = e^{2πikPα}`, and put `θ = 2πPα`. The triangle `(z_{−2}, z_0, z_1)` contains `0` in its
   interior iff its three edge cross products `sin θ`, `−sin 3θ` and `sin 2θ` are all positive.
   Writing `Pα = m + f`, this holds exactly when `f ∈ (1/6, 1/4)`. For a target `(u, x)`
   (a real mass and a complex moment), the barycentric weights `w_k` satisfy `Σ w_k = u` and
   `Σ w_k z_k = x`, and they are positive whenever `u · min cross > 2|x|`. Summing the three blocks:
   - on the base lattice: `T(qℓ) = ∫₀^P u(ξ) e^{2πiξqℓ} dξ`;
   - on the shifted lattice: `T(α + qℓ) = ∫₀^P x(ξ) Ψ_α(ξ) e^{2πiξ(α+qℓ)} dξ`.
3. **Isolating a shifted point** `n₀ = c b^{q₀}`. Take `u = 1` and
   `x(t) = s e^{−2πit(α+q₀ℓ)} conj Ψ_α(t) / max(|Ψ_α(t)|², 1/4)`.
   - On `[−2δ, P + 2δ]` we have `|Ψ_α|² ≥ 1/2`, since `Re e^{2πiPα} > 0` and `Ψ_α` is a convex
     combination of two neighbouring unit vectors. Hence `x Ψ_α = s e^{−2πit(α+q₀ℓ)}` on a period.
   - `|x| ≤ 2|s|` everywhere, and `x` is `P`-periodic on the overlap, because
     `Ψ_α(t + P) = e^{−2πiPα} Ψ_α(t)` there.
   - Therefore `T(qℓ) = P·[q = 0]` and `T(α + qℓ) = sP·[q = q₀]`. On `S` the transform vanishes except
     at `n₀`, and the pairing equals `2sP·v(n₀) ≥ 0`. Both signs of `s` are allowed, so `v(n₀) = 0`.
4. **Isolating a base point** `n₀ = b^{q₁}` with `q₁ ≥ 1`. Take `u(t) = 1 + 2s cos(2πtq₁ℓ)` with
   `|s| = 1/4`, and `x = 0`. Then `T(qℓ) = P([q = 0] + s[q = −q₁] + s[q = q₁])` and
   `T(α + qℓ) = 0`, so again `v(n₀) = 0`.
5. **Admissibility.** All blocks lie in `|η| ≤ 2P + δ < 1633/1000`, since `b ≥ 4` gives
   `log b > 1.302`. The pairing lemma needs `Σ_S |v(n)|(1+log n)^{−3} < ∞`, which follows from the
   box bound because `S` has `O(log N)` elements up to `N`. ∎

## What is new

- **Exact lattice annihilation for two-coset supports.** L164 sketched exact annihilators for a single
  geometric progression by periodization. For several cosets it claimed a "fiberwise construction"
  without a condition. The Floquet fiber analysis shows the construction works iff, on every fiber,
  the orbit points `(e^{2πi(ξ + k/ℓ)α_i})_i` over the admissible `k` surround the origin. The window
  version of this condition is the fractional-part condition above.
- **The resolution law for periodic supports is a cone law, not a gap law.** A radical test
  band-limited to the zero-free window `|t| < γ` resolves two cosets at logarithmic gap `h` as soon as
  the window points' phases span an arc greater than `π`. That requires about `h > π/(2γ)`, half of
  the gap `π/γ` that L165's resolution law gives for arbitrary lacunary sets. The present Lean
  instance has gap `log(21/16) = 0.272 < log(4/3)`.

## Reduction (paper): beyond the window, the wall is arithmetic progressions of zeros

- **Setting.** Tests need not stay in the window. The fiber construction needs only finitely many
  fiber points `ξ + k/ℓ` that avoid real zeros of `Ξ(2π·)` and whose phases surround `0`.
- **Where it fails.** For all but countably many fibers no fiber point is a zero. A fiber `ξ*` is
  obstructed only if the zeros cover every fiber point in an open half-space of the orbit. That is a
  positive-density subset of an arithmetic progression `2πξ* + (2π/log b)ℤ` in the ordinates.
- **What happens at such a fiber.** One-sided (Hardy-space) boundary behaviour of the deviation
  series forces all singular parts there to vanish. The exception is a first-order singularity
  whose phase pattern is carried exactly by the blocked (zero) points: an evaporation-type defect.
- **Consequence.** Full rigidity on every finite union of geometric progressions with a common ratio
  `b`, at every gap, follows if the ordinates of ζ contain no subset of positive upper density in an
  arithmetic progression of difference `2π/log b`.
  - This hypothesis is implied by the linear independence hypothesis: three zero ordinates in one such
    progression satisfy a rational linear relation.
  - It is not known unconditionally. Putnam (1954) and van Frankenhuijsen (2005) exclude full
    progressions, not positive-density subsets.
- **Reading.** For periodic supports, the Nyquist wall of L165 is exactly the arithmetic-progression
  structure of the zero ordinates. The same comb `γ₀ + 2πk/log 2` appears as the counterexample
  shape in CANNOT-464.

## Gates
- [x] 0 → 1: mechanism identified (Floquet fibers plus barycentric cones)
- [x] 1 → 2: paper proof above
- [x] 2 → 3: Lean, `lake build` green, wired into `RHTower`, standard axioms
- [ ] 3 → 4: not planned (no manuscripts; see memory "No stage 4")

## Log
- 2026-09-30: L166. Theorem, instance, Lean modules (about 800 + 630 lines); reduction to
  arithmetic progressions of zeros recorded.
