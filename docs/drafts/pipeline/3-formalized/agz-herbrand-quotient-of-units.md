# The Herbrand quotient of the unit group

- **ID:** agz-herbrand-quotient-of-units
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-1211/obstacles-summary.md §2.14 question 4 (A154); gates G5a,
  G5b of `agz-artin-reciprocity-law`
- **Statement:** Let a finite cyclic group `G = ⟨σ⟩` act on a number field `L`, `E` the units of
  `L`, `X` the infinite places of `L`, `f = σ − 1`, `g = Σ_τ τ`, `h_f = [ker f : im g]`,
  `h_g = [ker g : im f]`. Then `h_f(E)`, `h_g(E)` are finite and
  `|G| · h_f(E) · h_g(ℤ^X) = h_f(ℤ^X) · h_g(E)`, and
  `|G| · [E^G : N E] ≤ Π_ω |G_ω| · |H¹(G, E)|`, the product over the orbits `ω` of `G` on `X`.

  For `K = L^G`: `[L : K] · [E_K : N E_L] ≤ 2^ρ · |H¹(G, E_L)|`, `ρ` the number of real places of
  `K` that become complex in `L`.

## Goal
The unit term of the second inequality `[I^𝔪 : P_𝔪 N(I_L^𝔪)] ≥ [L : K]` for cyclic `L/K`.

## Gates
- [x] H1 Herbrand indices of a stable subgroup and of the quotient
- [x] H2 finite groups, subgroups of finite index
- [x] H3 a stable subgroup `C` and a compatible map `φ`: `C ∩ ker φ`, `φ C`, `C`
- [x] H4 finitely generated modules have finite indices; the trivial module `ℤ`
- [x] H5 permutation modules: `[(ℤ^X)^G : N ℤ^X] ≤ Π_ω |G_ω|`
- [x] H6 units `η_w` permuted by `G`, independent on exponents of sum zero, of finite index
- [x] H7 the Herbrand quotient of `E`

## Approach
`f, g` endomorphisms of an abelian group `A`, `f g = g f = 0`, `h_f(A) = [ker f : im g]`; indices
are `0` if infinite.

**H1.** For a subgroup `B` stable under `f, g`: `ker f ∩ B ⊃ gA ∩ B ⊃ gB`,
`f⁻¹B ⊃ ker f + B ⊃ gA + B`. With `[M : N] = [M + B : N + B][M ∩ B : N ∩ B]` for `N ⊂ M`,
`h_f(A) = [ker f + B : gA + B][ker f ∩ B : gA ∩ B]`, and `f` maps `f⁻¹B/(ker f + B)`
isomorphically to `(fA ∩ B)/fB`. So
`h_f(B) h_f(A/B) = h_f(A) · [fA ∩ B : fB][gA ∩ B : gB]`, where `h_f(B) = [ker f ∩ B : gB]`,
`h_f(A/B) = [f⁻¹B : gA + B]`. The last two factors are symmetric in `f, g`:
`h_f(B) h_f(A/B) h_g(A) = h_g(B) h_g(A/B) h_f(A)`. ∎

**H2.** `A` finite: `|ker f||im f| = |A| = |ker g||im g|`, so `h_f = h_g ≠ 0`. For `B` of finite
index apply this to `A/B` and H1: `h_f(B) h_g(A) = h_g(B) h_f(A)`, and `h_f(B) ≠ 0 ⇔ h_f(A) ≠ 0`. ∎

**H3.** For `φ : A → W` compatible with `(f, g)`, `(f', g')` and `C ⊂ A` stable, H1 in the group
`C` with `B = ker φ|_C`, whose quotient is `φ C`:
`h_f(C ∩ ker φ) h_{f'}(φ C) h_g(C) = h_g(C ∩ ker φ) h_{g'}(φ C) h_f(C)`. ∎

**H4.** `G = ⟨σ⟩` finite. For `a ∈ ker f`, `g a = |G| a`; for `a ∈ ker g`,
`|G| a = Σ_τ (a − τ a)` and `a − τ a ∈ im f` (the `τ` with this property for all `a` form a
subgroup containing `σ`). So `ker f/im g`, `ker g/im f` are killed by `|G|`, and finite if `A` is
finitely generated. For `ℤ` with trivial action `f = 0`, `g = |G|`: `h_f = |G|`, `h_g = 1`. ∎

**H5.** `(τ y)(x) = y(τ⁻¹ x)` on `ℤ^X`. Choose `r_ω ∈ ω` in each orbit. If `y` is invariant
and `y(r_ω) = |G_{r_ω}| d_ω` for all `ω`, then `y = g z` for `z = Σ_ω d_ω δ_{r_ω}`, because
`#{τ : τ⁻¹ x = r_ω} = |G_{r_ω}|` for `x ∈ ω`. The invariant `y` modulo these are counted by
`(y(r_ω) mod |G_{r_ω}|)_ω`. ∎

**H6.** Let `u_w` be a unit with `|u_w|_{w'} < 1` for `w' ≠ w` and
`η_w = Π_τ τ(u_{τ⁻¹ w})`. Then `ν η_w = η_{ν w}` and `|η_w|_{w'} = Π_τ |u_{τ⁻¹ w}|_{τ⁻¹ w'} < 1`
for `w' ≠ w`. `M_{w' w} = n_{w'} log |η_w|_{w'}` is negative off the diagonal with zero column
sums. If `M c = 0`, `Σ c = 0`, `c ≠ 0`, let `P = {c > 0}`; `P` and its complement are not
empty. Summing the rows in `P`: `Σ_w c_w S_w = 0`, `S_w = Σ_{w' ∈ P} M_{w' w}`; for `w ∈ P`,
`S_w = −Σ_{w' ∉ P} M_{w' w} > 0`; for `w ∉ P`, `S_w < 0`, `c_w ≤ 0`. Contradiction. So
`φ : y ↦ Π_w η_w^{y_w}` is injective on `B = {Σ y = 0}`; `B` and `E` have rank `|X| − 1`, so
`φ B` has finite index. ∎

**H7.** H3 for the sum `ℤ^X → ℤ` (`C = ℤ^X`) and H4:
`h_f(B) |G| h_g(ℤ^X) = h_g(B) h_f(ℤ^X)`. H3 for `φ` and `C = B`:
`h_f(φB) h_g(B) = h_g(φB) h_f(B)`. H2: `h_f(φB) h_g(E) = h_g(φB) h_f(E)`. All indices are
finite (H4, H2). Eliminating `B`, `φB`: `|G| h_f(E) h_g(ℤ^X) = h_f(ℤ^X) h_g(E)`. With H5 and
`h_g(ℤ^X) ≥ 1` the inequality follows. ∎

## Lean
`formal/GaloisForLFunctions/RHTower/Artin/`:
- `TheHerbrandQuotientIsMultiplicative.lean`: `herbrandIndex`, `herbrandSubIndex`,
  `herbrandQuotIndex`, `relIndex_eq_sup_mul_inf`, `herbrandSubIndex_mul_herbrandQuotIndex` (H1),
  `herbrandIndex_comm_of_finite`, `herbrandSubIndex_mul_of_index_ne_zero`,
  `herbrandSubIndex_ne_zero_iff_of_index_ne_zero` (H2), `herbrandSubIndex_inf_ker_mul`,
  `herbrandSubIndex_ne_zero_of_inf_ker` (H3).
- `HerbrandIndicesOfFinitelyGeneratedAndPermutationModules.lean`: `actionDiff`, `actionNorm`,
  `herbrandIndex_actionDiff_ne_zero`, `herbrandIndex_actionNorm_ne_zero`,
  `herbrandIndex_int_trivial` (H4), `permRep`, `herbrandIndex_permRep_le` (H5).
- `UnitsPermutedByTheGaloisGroupHaveFiniteIndex.lean`: `infinitePlaceMulAction`, `unitsRep`,
  `artinUnit`, `unitsMap_artinUnit`, `logAt_artinUnit_neg`, `eq_zero_of_offDiag_neg`,
  `artinUnitHom`, `eq_zero_of_artinUnitHom_eq_zero`, `index_map_artinUnitHom_ne_zero` (H6).
- `TheHerbrandQuotientOfTheUnitGroup.lean`: `card_mul_herbrandIndex_units`,
  `card_mul_herbrandIndex_units_le` (H7).

## Log
- 2026-11-13 — H1–H7 proved and formalized
