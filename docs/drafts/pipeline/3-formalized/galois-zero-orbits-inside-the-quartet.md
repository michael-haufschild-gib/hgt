# Orbits inside the quartet: ordinate, width and quartet criteria

- **ID:** gtz-orbits-inside-the-quartet
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** programme card `gtz-galois-theory-of-zeros-programme.md`, problem 2 (review-1411 §2.19).
- **Statement:** `E = ℚ(p^ρ)`, `B` the prime trace field, `G = Gal(E/B)`, `Δ` the integer span
  of the zeros. For a zero `ρ = β + iγ` and a prime `p`: weight value `p^{2β}`, width value
  `v = p^{2β−1} + p^{1−2β}`, ordinate value `u = 2cos(2γ log p)`, all in `E ∩ ℝ`.
  (A) `x ∈ E` lies in `B` iff `G` fixes it; `δ ∈ Δ` is fixed by `G` iff `2^δ, 3^δ ∈ B`;
  (B) `u ∈ B` iff `σρ̄ = conj(σρ)` for every `σ ∈ G`; independent of `p`; conjugation is central
  in `G` iff `u ∈ B` at every zero; `p^{2β} ∈ B ⇒ u ∈ B` at every prime;
  (C) `v ∈ B` iff for every `σ`: `σρ̄ = conj(σρ)` and `Re σρ ∈ {β, 1 − β}`; then `σρ` lies in
  the quartet `{ρ, ρ̄, 1 − ρ, 1 − ρ̄}`; `p^{2β} ∈ B ⇒ v ∈ B ⇒ u ∈ B`; if `v ∈ B` and
  `p^{2β} ∉ B`, some `σ` has `σρ = 1 − ρ`, `σρ̄ = 1 − ρ̄`, and `β ≠ ½`;
  (D) `u + v ∈ B` and `uv ∈ B` iff every `σ` sends `ρ` into the quartet;
  (E) if every `σ` sends `ρ` into the quartet: `u ∈ B ⇔ v ∈ B`; for `β ≠ ½`, some `σ` has
  `σρ̄ = 1 − conj(σρ)` iff `u ∉ B`, and such a `σ` exchanges `u` and `v`.

## Goal

Problem 2 of the programme: classify finite orbits by memberships of prime values in `B`.
Inside a quartet the three orbit types are: `{ρ, ρ̄}` (`p^{2β} ∈ B`); the quartet acted on
through `{1, c, r, cr}` (`v ∈ B`, `p^{2β} ∉ B`); the quartet with a partial flip (`v ∉ B`,
`u + v, uv ∈ B`). None of the memberships forces `β = ½`: each holds at every zero with
rational real part, and the pair criterion asks `p^{2β} ∈ B`, not `p^{2β} = p`.

## Gates
- [x] 0 → 1
- [x] 1 → 2  paper proof below
- [x] 2 → 3  Lean (axioms `propext, Classical.choice, Quot.sound`)

## Proof

(A) `E/B` is Galois (infinite Galois theory: fixed field of `G` is `B`). Two primes separate
exponents: `(2^z, 3^z)` determines `z`.

Symmetric values. If `σ(y + y') = x + x'` with `yy' = 1 = xx'`, then
`(σy − x)(σy − x') = σy² − σy(σy + σy') + xx' = 0`, so `σy ∈ {x, x'}`.

(B) `x = p^{ρ−ρ̄}` has modulus one. `σ` fixes `u` iff `σx ∈ {x, x⁻¹}`; then `|p^{σρ−σρ̄}| = 1`,
so `Re σρ = Re σρ̄`. `σρ, σρ̄` are distinct zeros (injectivity) with ordinates `±γ`
(the absolute ordinate is kept), so `σρ̄ = conj(σρ)`. Conversely `σ(ρ − ρ̄) = 2i Im σρ = ±(ρ − ρ̄)`.
Centrality: `cσρ = σcρ` for all `ρ` is the condition, and the action is faithful.
`p^{2β} ∈ B` gives `Re σρ = Re σρ̄ = β` (weight criterion applied to `σ` and `σc`).

(C) `x = p^{2β−1}` is real; `c` fixes it. Let `K` be the stabilizer of `x`; it contains `c`, and
for `τ ∈ K`, `|p^{τ(ρ+ρ̄−1)}| = |x|` gives `Re τ(ρ + ρ̄) = 2β`. Doubling in `K` (the displacement
`Re τρ − β` doubles under `τcτ⁻¹ ∈ K` and is bounded) gives `Re τρ = β`, so `τρ ∈ {ρ, ρ̄}`.
For any `σ` fixing `v`, `σx ∈ {x, x⁻¹}` and both are real, so `k = σ⁻¹cσ` fixes `x`: `k ∈ K`.
Then `conj(σρ) = σkρ ∈ {σρ, σρ̄}`; `σρ` is not real, so `σρ̄ = conj(σρ)`, and
`2 Re σρ − 1 = ±(2β − 1)`. Conversely the two conditions give `σ(ρ + ρ̄ − 1) = ±(2β − 1)`.
Local reflection: `p^{2β} ∉ B` gives `σ` with `Re σρ ≠ β`; in the quartet `σρ ∈ {1 − ρ, 1 − ρ̄}`;
compose with `c` if needed. `β = ½` would put `p^{2β} = p ∈ B`.

(D) If `σ` fixes `u + v` and `uv`, `(σu − u)(σu − v) = 0`. `σu = u`: `σ` fixes `u` and `v`, so
`Re σρ = Re σρ̄` and `Re σρ + Re σρ̄ − 1 = ±(2β − 1)`. `σu = v`: `σx ∈ {y, y⁻¹}`
(`y = p^{ρ−ρ̄}`) has modulus one, so `Re σρ + Re σρ̄ = 1`, and `σy ∈ {x, x⁻¹}` gives
`Re σρ − Re σρ̄ = ±(2β − 1)`. Either way `Re σρ ∈ {β, 1 − β}`, and with `|Im σρ| = |γ|` the
image is in the quartet. Conversely, for `β = ½` all three values lie in `B`. For `β ≠ ½`:
`σρ̄` lies in the quartet of `σρ` and differs from `σρ` and from `1 − σρ = σ(1 − ρ)`
(`ρ̄ ≠ 1 − ρ`), so `σρ̄ ∈ {conj σρ, 1 − conj σρ}`. In the first case `σ` sends both exponents
`ρ − ρ̄` and `ρ + ρ̄ − 1` to `±` themselves; in the second `σ(ρ + ρ̄ − 1) = 2i Im σρ = ±(ρ − ρ̄)`
and `σ(ρ − ρ̄) = 2 Re σρ − 1 = ±(ρ + ρ̄ − 1)`, so `σ` exchanges `u` and `v`. Both fix `u + v`, `uv`.

(E) Every `σ` fixes `u, v` or exchanges them; so `u` is fixed by all `σ` iff `v` is.
A partial flip with `u ∈ B` would give `conj σρ = 1 − conj σρ`, `Re σρ = ½`, `β = ½`.
If `u ∉ B` some `σ` has `σρ̄ ≠ conj σρ`, and (D) leaves the partial flip. ∎

## Lean

| Step | Module | Declaration |
|---|---|---|
| A | `ConjugationIsCentralAtAZeroIffItsOrdinateValueLiesInThePrimeTraceField` | `coe_mem_primeTraceField_iff_fixed`, `primeTraceExponentHom_fixed_iff`, `primeTraceExponentValue_pair_map` |
| B | same | `primeOrdinateValue_mem_iff_conj`, `primeOrdinateValue_mem_iff_mem`, `primeTraceConjugation_central_iff`, `primeOrdinateValue_mem_of_weight_mem`, `primeOrdinateValue_mem_of_critical`, `primeTraceExponentHom_ordinate_of_conj` |
| C | `TheGroupActsOnAZeroThroughTheTwoInvolutionsIffItsWidthValueLiesInThePrimeTraceField` | `eq_or_eq_of_add_eq`, `primeTraceZeroMap_re_of_fixed_centred`, `primeWidthValue_mem_iff`, `primeWidthValue_mem_iff_mem`, `primeTraceZeroMap_mem_quartet`, `primeWidthValue_mem_of_weight_mem`, `primeOrdinateValue_mem_of_width_mem`, `exists_primeTraceZeroMap_eq_reflect` |
| D | `TheOrbitOfAZeroLiesInItsQuartetIffItsWidthAndOrdinateValuesSolveAQuadraticOverThePrimeTraceField` | `primeTraceZeroMap_re_of_sum_prod_fixed`, `primeTraceZeroMap_conj_or_flip`, `primeTraceExponentHom_of_flip`, `sum_prod_mem_iff_mem_quartet` |
| E | same | `primeOrdinateValue_map_of_flip`, `primeOrdinateValue_mem_iff_width_mem`, `exists_partialFlip_iff` |

Subgroup doubling: `primeTraceZeroMap_re_of_weight_re_of_mem` in
`TheOrbitOfAZeroIsItsConjugatePairIffItsWeightLiesInThePrimeTraceField`.

## Open

Orbits that leave the quartet (other zeros of the same absolute ordinate); stabilizers; any
membership of a prime value of a zero with irrational real part.
