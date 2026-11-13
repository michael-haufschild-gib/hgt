# The zero configuration of an Artin character: index law and orders

- **ID:** agz-artin-configuration-orders
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-1311/obstacles-summary.md §2.14 (question 5); open items of
  `3-formalized/agz-ray-class-characters-at-their-conductors.md`
- **Statement:** (A) A linear character `χ ≠ 1` of a Galois group of number fields has a
  primitive ray class character `ψ' ≠ 1`, and every analytic continuation of its Euler product to
  `Re s > 1/2` has, right of the critical line, exactly the zeros of the configuration of `ψ'`;
  the index law holds on the Artin `L`-function itself. (B) For every representation `ρ` of the
  group there are integers `n_q` and tempered configurations `Z_q` (Brauer pairs `q`) such that
  for every representation `L(s, ρ) = A/B` by functions analytic on `Re s > 0`:
  `ord_{s₀} A − ord_{s₀} B = Σ_q n_q m_{Z_q}(s₀)` for `Re s₀ > 0`, `s₀ ≠ 1`, and the form
  `Σ_q n_q W_{Z_q}` has `m` negative squares on some `m` tests iff `L(s, ρ)` has at least `m`
  zeros or poles `≠ 1` right of the line or poles on it.

## Goal

The index law on the `L`-function of the Artin character, not on an auxiliary Hecke function,
and the virtual configuration of a general Artin character with the orders of its zeros.

Not a statement on the position of the zeros. Holomorphy of `L(s, ρ)` (Artin's conjecture) is
not claimed: (B) counts the poles.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `eq_one_of_forall_artinSymbol_eq_one`, `exists_zeroConfig_linearCharacter`, `analyticOrderNatAt_heckePoleCleared`, `exists_le_negIndex_combination_iff`, `exists_virtualConfig_artin`

## Proof

`L/K` Galois with group `G`; `(χ, v)` the Artin symbol of a linear character: `χ(Frob_v)` if `χ`
is trivial on the inertia groups above `v`, else `0`.

### A. Linear characters

**A1. The symbols determine the character.** If `(χ, v) = 1` for all `v` with `N v > B`, then
`χ = 1`. For abelian `G`: the ramified primes are finitely many; raise `B` above their norms.
For `N v > B`: `χ(Frob_v) = (χ, v) = 1`. The subgroup `ker χ` contains the Frobenius elements of
all primes of norm `> B`, so it is `G` (`eq_top_of_forall_frobeniusElement_mem`). General `G`:
`χ = χ' ∘ π`, `π : G → G/ker χ = Gal(F/K)`, `F` the fixed field of `ker χ`, `G/ker χ` cyclic;
`(χ, v) = (χ', v)_{F/K}` (inflation). So `χ' = 1` and `χ = 1`.

**A2. `ψ' ≠ 1`.** Let `ψ` modulo `𝔪` have `(χ, v) = ψ(v)` for `v ∤ 𝔪`. If `ψ = 1` then
`(χ, v) = 1` for `v ∤ 𝔪`, and the primes dividing `𝔪` have bounded norm: `χ = 1` by A1. The
primitive character `ψ'` of `ψ` is trivial iff `ψ` is.

**A3. Continuations.** Let `χ ≠ 1`, `c`, `ψ'` modulo `𝔫` as in the reciprocity law with a
primitive character, and for `Re s > 0`

  `F(s) = L(s, ψ') Π_{v | c} (1 − ψ'(v) N v^{−s}) (1 − (χ, v) N v^{−s})^{−1}`.

`L(s, ψ')` is entire (`ψ' ≠ 1`); a factor `1 − a N v^{−s}`, `|a| ≤ 1`, is entire without zeros
in `Re s > 0`, and `|(χ, v)| ≤ 1`, `|ψ'(v)| ≤ 1`. So `F` is analytic on `Re s > 0`, equal to the
Euler product of `χ` on `Re s > 1`, with `F(s) = 0 ⇔ L(s, ψ') = 0`. Let `Λ` be analytic on
`Re s > 1/2`, equal to the Euler product on `Re s > 1`. The half plane is connected: `Λ = F`
there. For `Re s > 1/2`: `Λ(s) = 0 ⇔ L(s, ψ') = 0 ⇔ Ξ_{ψ'}(s) = 0`. So

  `{Re s > 1/2, Λ(s) = 0} = rightZeros(Z_{ψ'})`,

and by the index law of `ψ'`: Weil's form of `Z_{ψ'}` has `m` negative squares on some `m`
tests iff `Λ` has at least `m` distinct zeros right of the line. ∎

### B. General characters

**B1. Orders of a ray class `L`-function.** Let `ψ` be a ray class character modulo `𝔪`, `ψ'`
modulo `𝔫` primitive, `Ξ = Ξ_{ψ'}` the entire completion (poles cleared by `s(s − 1)` if
`ψ' = 1`), `Z_ψ` its configuration, and

  `E_ψ(s) = (s − 1) L(s, ψ)`,

entire: `L(s, ψ) = R(s) + κ/(s − 1)` with `R` entire. Claim: for `Re s₀ > 0`,

  `ord_{s₀} E_ψ = m_{Z_ψ}(s₀) + [s₀ = 1][ψ ≠ 1]`.

Proof. With `c(s) = N^{s/2}` the conductor factor and `γ(s)` the Gamma factor of `ψ'`, both
without zeros in `Re s > 0`, `1/γ` entire: for `ψ' ≠ 1`, `Ξ = c γ L(·, ψ')` on `ℂ`, so
`(s − 1) c(s) L(s, ψ') = (s − 1) Ξ(s)/γ(s)`. For `ψ' = 1`: `Ξ(s) = s (s − 1) c(s) γ(s) L(s, ψ')`
on `Re s > 1`, so `s c(s) E_{ψ'}(s) = Ξ(s)/γ(s)` there, and on `ℂ` (both sides entire). And
`L(s, ψ) = L(s, ψ') M(s)` on `ℂ ∖ {1}` with `M` the product of the Euler factors of `ψ'` at
the primes of `𝔪`, entire without zeros in `Re s > 0`: `E_ψ = E_{ψ'} M` on `ℂ`. Orders add; the
factors `s`, `c`, `1/γ`, `M` have order `0` at `s₀`; `s − 1` has order `[s₀ = 1]`. So for
`ψ ≠ 1`: `ord E_ψ = ord Ξ + [s₀ = 1]`; for `ψ = 1`: `ord E_ψ = ord Ξ`. And
`ord_{s₀} Ξ = m_{Z_ψ}(s₀)` by definition of the configuration. Also `Ξ(1) ≠ 0`: for `ψ' ≠ 1`,
`L(1, ψ') ≠ 0`; for `ψ' = 1`, `E_{ψ'}(1) = κ ≠ 0`, the residue. So `1 ∉ Z_ψ`.

**B2. Integer combinations of configurations.** Let `Z_q` be tempered configurations and
`n_q ∈ ℤ`, `q` in a finite set. Repeat `Z_q` `n_q` times in a family `Z⁺` if `n_q > 0` and
`−n_q` times in `Z⁻` if `n_q < 0`. Then `Σ_k W_{Z⁺_k} − Σ_k W_{Z⁻_k} = Σ_q n_q W_{Z_q}` and the
net multiplicity is `Σ_q n_q m_{Z_q}`. By the index law of a quotient of products
(`exists_le_negIndex_quotient_iff`): `Σ_q n_q W_{Z_q}` has `m` negative squares on some `m`
tests iff there are at least `m` points `s₀` with `Re s₀ > 1/2`, `Σ_q n_q m_{Z_q}(s₀) ≠ 0`, or
`Re s₀ = 1/2`, `Σ_q n_q m_{Z_q}(s₀) < 0`.

**B3. The Artin character.** Brauer and reciprocity: there are `n_q ∈ ℤ` for finitely many pairs
`q = (E, χ_q)`, and for each pair `c_q` and a ray class character `ψ_q` modulo `(c_q) ∞` of the
fixed field of `E`, with, for `Re s > 1`,

  `L(s, ρ) = Π_q Λ_q(s)^{n_q}`,  `Λ_q(s) = L(s, ψ_q) D_q(s)`,
  `D_q(s) = Π_{v | c_q} (1 − (χ_q, v) N v^{−s})^{−1}`.

`D_q` is analytic without zeros on `Re s > 0`. Put `G_q = E_{ψ_q} D_q`, analytic on `Re s > 0`,
`G_q(s) = (s − 1) Λ_q(s)` on `Re s > 1`, and `P⁺ = Π_{n_q > 0} G_q^{n_q}`,
`P⁻ = Π_{n_q < 0} G_q^{−n_q}`, `a = Σ_{n_q > 0} n_q`, `b = Σ_{n_q < 0} (−n_q)`. On `Re s > 1`:

  `L(s, ρ) (s − 1)^a P⁻(s) = (s − 1)^b P⁺(s)`.

Let `A`, `B` be analytic on `Re s > 0`, `B` not identically zero, `A = B · L(·, ρ)` on
`Re s > 1`. Then `A (s − 1)^a P⁻ = B (s − 1)^b P⁺` on `Re s > 1`, hence on `Re s > 0`
(connected). No factor vanishes identically, so at every `s₀`, `Re s₀ > 0`, orders are finite
and add:

  `ord A + a [s₀ = 1] + Σ_{n_q < 0} (−n_q) ord G_q = ord B + b [s₀ = 1] + Σ_{n_q > 0} n_q ord G_q`.

By B1, `ord_{s₀} G_q = m_{Z_q}(s₀) + [s₀ = 1][ψ_q ≠ 1]`, `Z_q = Z_{ψ_q}`. So

  `ord_{s₀} A − ord_{s₀} B = Σ_q n_q m_{Z_q}(s₀)` for `s₀ ≠ 1`,
  `ord_1 A − ord_1 B = −Σ_{q : ψ_q = 1} n_q`.

With B2 and `1 ∉ Z_q`: the form `Σ_q n_q W_{Z_q}` has `m` negative squares on some `m` tests iff
there are at least `m` points `s₀` with `Re s₀ > 1/2`, `s₀ ≠ 1`, `ord A ≠ ord B`, or
`Re s₀ = 1/2`, `ord A < ord B`. ∎

## Lean

| Step | Declaration | Module |
|---|---|---|
| A1 | `eq_one_of_forall_artinSymbol_eq_one_of_comm`, `eq_one_of_forall_artinSymbol_eq_one` | `RHTower/Artin/ALinearCharacterWithTrivialArtinSymbolsAtAlmostAllPrimesIsTrivial.lean` |
| A2 | `heckeCharacter_ne_one_of_artinSymbol`, `exists_primitive_heckeCharacter_ne_one_artinSymbol` | same |
| A3 | `eulerFactorQuotient`, `rightZeros_heckeZeros_eq_of_eq_mul_eulerFactorQuotient`, `exists_heckeZeros_linearCharacter`, `exists_zeroConfig_linearCharacter` | `AbsoluteGeometryOfSpecZ/TheIndexLawOfALinearArtinCharacterHoldsOnItsOwnLFunction.lean` |
| B1 | `heckePoleCleared`, `completionFactor_mul_heckePoleCleared`, `heckeXi_one_mul_gamma_inv`, `heckeXi_one_ne_zero`, `heckePoleCleared_eq_primitiveHecke_mul`, `one_notMem_rayClassZeros`, `analyticOrderNatAt_heckePoleCleared` | `AbsoluteGeometryOfSpecZ/TheOrdersOfARayClassLFunctionAreTheMultiplicitiesOfItsConfiguration.lean` |
| B2 | `netMult`, `combinationDefect`, `virtualDefect_repeated`, `exists_le_negIndex_combination_iff` | `AbsoluteGeometryOfSpecZ/TheIndexOfAnIntegerCombinationOfConfigurationsCountsItsNetMultiplicities.lean` |
| B3 | `analyticOrderNatAt_sub_eq_sum_of_eq_mul_prod_zpow`, `analyticOrderNatAt_sub_eq_sum_sub_of_cleared`, `brauerHeckeCleared`, `analyticOrderNatAt_sub_artin_of_brauerHecke`, `exists_virtualConfig_artin` | `AbsoluteGeometryOfSpecZ/TheOrdersOfAnArtinLFunctionAreTheNetMultiplicitiesOfItsVirtualConfiguration.lean` |

In Lean the order at `1` is `−p` with `p = Σ_{q : ψ_q = 1} n_q`.

## What stays open

- The conductor–ramification theorem (card `agz-conductor-ramification`): with it the finite
  products in A3 and B3 are `1`.
- `Σ_{q : ψ_q = 1} n_q` is the multiplicity of the trivial character in `ρ` (not proved here).

## Log
- 2026-11-13 — created in 1-in-progress with the paper proof
- 2026-11-14 — formalized; moved to 3-formalized
