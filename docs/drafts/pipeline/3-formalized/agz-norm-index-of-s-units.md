# The norm index of the `S`-units

- **ID:** agz-norm-index-of-s-units
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-1211/obstacles-summary.md §2.14 question 4 (A154); gates G5c,
  G5d1 of `agz-artin-reciprocity-law`
- **Statement:** Let `L/K` be a cyclic extension of number fields with group `G = ⟨σ⟩`. Every
  finite set of primes of `K` lies in a finite set `S_K` such that, for the set `S` of primes of
  `L` above `S_K` and the `S`-units `L_S`,
  `H¹(G, L_S) = 0` and `[L : K] · [L_S^G : N L_S] = Π_ω |G_ω|`,
  the product over the orbits `ω` of `G` on the infinite places of `L` and on `S` of the orders
  of the stabilizers.

## Goal
The `S`-unit term of the second inequality.

## Gates
- [x] N1 Herbrand quotient of `L_S`: valuations onto a subgroup of finite index of `ℤ^S`
- [x] N2 Hilbert 90 for a finite cyclic group acting faithfully on a field
- [x] N3 `H¹(G, L_S) = 0` if the invariant divisors prime to `S` descend
- [x] N4 descent outside a large set of primes; existence of such sets
- [x] N5 permutation modules: `H¹(G, ℤ^X) = 0`, `|Ĥ⁰(G, ℤ^X)| = Π_ω |G_ω|`

## Approach
`f = σ − 1`, `g = Σ_τ τ`, `h_f(A) = [ker f : im g]`, `h_g(A) = [ker g : im f]`; `v_w` the
exponent at a prime `w`.

**N1.** `S` a `G`-stable finite set of primes of `L`, `φ : L_S → ℤ^S`, `x ↦ (v_w(x))_w`,
equivariant for `(τ y)(w) = y(τ⁻¹ w)`. `ker φ = E_L`. For `w ∈ S` and the class number `h`,
`w^h = (a)`, so `h δ_w ∈ im φ`: the image has finite index. The Herbrand quotient is
multiplicative and insensitive to finite index (`agz-herbrand-quotient-of-units` H1–H3), so with
the unit theorem (H7):
`n · h_f(L_S) · h_g(ℤ^X) · h_g(ℤ^S) = h_f(ℤ^X) · h_f(ℤ^S) · h_g(L_S)`, `X` the infinite places. ∎

**N2.** `G = ⟨σ⟩` of order `n` acting faithfully on a field `L`, `Π_τ τx = 1`. Put
`p_i = x · σx ⋯ σ^{i−1}x` and `R(c) = Σ_{i<n} p_i σ^i(c)`. Then `p_{i+1} = x σ(p_i)`, `p_n = 1`,
so `x σ(R(c)) = R(c)`. The `σ^i`, `i < n`, are distinct characters `L^× → L^×`, hence linearly
independent: `R(c) ≠ 0` for some `c`, and `x = σy/y` for `y = R(c)⁻¹`. ∎

**N3.** Suppose: every `y ∈ L^×` with `v_{τw}(y) = v_w(y)` for all `w ∉ S`, `τ ∈ G` is `c z`
with `c` fixed by `G` and `z ∈ L_S`. Let `x ∈ L_S`, `N x = 1`. By N2, `x = σy/y`; for `w ∉ S`,
`0 = v_w(x) = v_{σ⁻¹w}(y) − v_w(y)`, so the exponents of `y` outside `S` are constant on orbits.
With `y = c z`: `x = σz/z`. ∎

**N4.** Class representatives: let `J_C` be integral ideals representing the classes `C` of a
number field and `S ⊇ T₀` contain the primes dividing them. For `v ∉ S` and the class `C`
inverse to that of `v`, `v J_C = (c)`: `v_v(c) = 1` and `v_{v'}(c) = 0` for `v' ∉ S ∪ {v}`.

The primes of `K` ramified in `L` are finite in number (the ramified primes of `L` divide the
different). Let `S_K` contain them and satisfy the property above, `S` the primes of `L` above
`S_K`. `G` is transitive on the primes above `v`, and `v_w(c) = e(w|v) v_v(c) = v_v(c)` for
`c ∈ K^×`, `w ∉ S` above `v`. If the exponents of `y` outside `S` are constant on orbits, let
`a_v` be the exponent above `v ∉ S_K` (zero for almost all `v`) and `c = Π_v c_v^{a_v}`: then
`v_w(y/c) = 0` for `w ∉ S`. Enlarging `S_K` by the primes below a set with the property for `L`
gives the property for `L` and `S` as well. ∎

**N5.** `(N y)(r) = Σ_τ y(τ⁻¹ r) = |G_r| · Σ_{x ∈ G r} y(x)`, since `#{τ : τ⁻¹ r = b} = |G_r|`
for `b ∈ G r`. Let `r(x)` be the chosen point of the orbit of `x`.
- If `N y = 0` the orbit sums vanish, so `Σ_x y(x) δ_{r(x)} = 0` and
  `y = Σ_x y(x)(δ_x − δ_{r(x)})`. With `x = τ r(x)`: `δ_x − δ_{r(x)} = (τ − 1) δ_{r(x)}`, in
  the image of `σ − 1` (the `τ` with `(τ − 1) a ∈ im(σ − 1)` for all `a` form a subgroup
  containing `σ`). So `h_g(ℤ^X) = 1`.
- Invariant functions are functions on the orbits; `y ↦ (y(r_ω) mod |G_{r_ω}|)_ω` maps them
  onto `Π_ω ℤ/|G_{r_ω}|` with kernel the norms. So `h_f(ℤ^X) = Π_ω |G_ω|`.

With N1, N3: `n · h_f(L_S) = Π_{ω ⊂ X} |G_ω| · Π_{ω ⊂ S} |G_ω|`. ∎

## Lean
`formal/GaloisForLFunctions/RHTower/Artin/`:
- `TheHerbrandQuotientOfTheSUnits.lean`: `primeMulAction`, `fieldUnitsRep`, `ordAt`, `sUnits`,
  `divMap`, `sUnits_inf_ker_divMap`, `index_map_divMap_ne_zero`,
  `card_mul_herbrandSubIndex_sUnits` (N1).
- `SUnitsOfNormOneAreQuotientsOfConjugates.lean`: `exists_smul_div_eq_of_prod_smul_eq_one`,
  `mem_range_actionDiff_of_actionNorm_eq_zero` (N2), `InvariantDivisorsDescend`,
  `herbrandSubIndex_actionNorm_sUnits_eq_one` (N3).
- `InvariantDivisorsDescendOutsideALargeSetOfPrimes.lean`: `PrincipalOutside`,
  `exists_finset_principal_outside`, `primesAbove`, `ordAt_baseIncl`,
  `invariantDivisorsDescend_primesAbove`, `finite_not_isUnramifiedPrime`,
  `exists_finset_unramified_principalOutside` (N4).
- `TheHerbrandIndicesOfAPermutationModule.lean`: `actionNorm_permRep_apply`,
  `herbrandIndex_actionNorm_permRep`, `herbrandIndex_actionDiff_permRep` (N5),
  `card_mul_herbrandSubIndex_sUnits_eq`, `herbrandSubIndex_actionDiff_sUnits_ne_zero`.

## Log
- 2026-11-13 — N1–N5 proved and formalized
