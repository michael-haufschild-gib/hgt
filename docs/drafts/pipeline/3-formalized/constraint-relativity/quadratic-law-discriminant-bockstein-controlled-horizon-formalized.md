# Quadratic law-discriminant, Bockstein, and controlled horizon — formalized

- **ID:** `quadratic-law-discriminant-bockstein-controlled-horizon-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `quadratic-law-discriminant-bockstein-controlled-horizon.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.QuadraticLawHorizon` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/QuadraticLawHorizon.lean` |
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.MonogenicKaehler` | new reusable infrastructure |
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.RankOneFraming` | fibre classification, reused |

All wired into `GaloisForLFunctions.HTGeometry`.

## New infrastructure

`MonogenicKaehler` proves, for any commutative ring `R` and any `f : R[X]`,

`Ω[R[X]/(f) ⁄ R] ≅ R[X]/(f) ⧸ (f'(α))`  (`kaehlerEquivMonogenic`),

by constructing the canonical derivation `g(α) ↦ g'(α) mod f'(α)` and checking the universal
property, and derives `Module.annihilator (Ω[S⁄R]) = (f'(α))` (`annihilator_kaehler`).  A corpus
search (`formal_tools.py research`, plus a grep over every module mentioning
`KaehlerDifferential`) found no existing computation of the relative differentials of a monogenic
algebra, and mathlib has only the polynomial case `KaehlerDifferential.polynomialEquiv` and the
abstract conormal sequence.  Four further cards in this folder need the same normal form.

## Realization

| Card | Lean |
|---|---|
| `B = ℂ[h]` | `LawBase`, `lawParam = X` |
| `A = B[η]/(η(η−h))` | `LawAlgebra = AdjoinRoot lawPoly`, `lawEta` |
| `J(a + bη) = (a, a + bh)`, card `(2)` | `lawObserver` |
| `r(x, y) = y − x mod h`, card `(3)` | `collisionReporter` |
| fibre `A_c = ℂ[η]/(η(η−c))` | `quadAlgebra c 0` |
| `D_c(u,v) = (v − u)/c`, card `(9)` | `hiddenDecoder c` |

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Theorem 1 — exact global descent, card `(4)`:

1. `exists_lawCoords`, `lawCoords_unique` — `A` is free on `1, η` over `B`.
2. `lawObserver_injective` — `J` is injective.
3. `range_lawObserver` — `im J = ker r`.
4. `collisionReporter_surjective` — `r` is surjective.

Theorem 2 — non-Morita law collision, card `(5)`–`(6)`:

5. `fibre_discr` — the fibre discriminant is `c²`.
6. `fibre_split` — `c ≠ 0` gives `ℂ × ℂ`.
7. `fibre_dual` — the collision fibre is the dual numbers.
8. `fibre_not_algEquiv` — the two are not isomorphic, so the horizon is genuine.

Theorem 3 — the erased direction is the derived class, card `(7)`–`(8)`:

9. `collisionObserver`, `collisionObserver_root`, `collisionObserver_kills_nilpotent` — the
   specialized observer is `a + bε ↦ (a, a)` and kills the nilpotent generator.
10. `ker_collisionObserver` — `ker J₀ = ℂ ε` exactly.
11. `tor_one_eq_top` — the parameter acts by zero on `B/(h)`, so the first Koszul homology of the
    free resolution `0 → B →^h B → 0` tensored with the residue field is all of `k`:
    `Tor₁^B(k,k) ≅ k`.

Theorem 4 — sharp discriminant conditioning, card `(9)`–`(11)`:

12. `hiddenDecoder_recovers` — off the collision the decoder returns the hidden coefficient.
13. `hiddenDecoder_normSq` — the coefficient vector `(−1/c, 1/c)` has squared norm `2/‖c‖²`.
13b. `decoderVector`, `hiddenDecoderCLM`, `hiddenDecoderCLM_apply`, `hiddenDecoderCLM_eq`,
    `norm_hiddenDecoderCLM` — **card `(10)`**: the decoder as a continuous functional on *Euclidean*
    `ℂ²` — which is where the card takes the norm; mathlib's default product norm is the supremum
    one — and its **operator norm** `‖D_c‖ = √2/|c|`, obtained from the Riesz vector through
    `innerSL_apply_norm`.  Item 13 alone gives the coefficient vector's norm, not the operator
    norm.
14. `conditioning_law` — `√|Disc| · (√2/|c|) = √2`; `conditioning_law_opNorm` states the same with
    the genuine operator norm `‖D_c‖`, which is card `(11)` boxed.

Theorem 5 — universal decoder blow-up, card `(12)`:

15. `decoder_norm_tendsto_atTop` — for any family of left inverses of a family of maps whose value
    on a fixed unit vector tends to zero, the operator norms tend to infinity.

Theorem 6 — relative cotangent equals the nonreduced discriminant shadow, card `(13)`–`(14)`:

16. `derivative_lawPoly`, `rootDifferent_lawPoly` — the different element is `2η − h`.
17. `lawKaehlerEquiv` — `Ω[A⁄B]` is cyclic on `dη` with the single relation `(2η − h) dη = 0`.
18. `annihilator_lawKaehler` — the annihilator is the different ideal `(2η − h)`.
19. `lawDifferent_sq` — `(2η − h)² = h²`, the exact reason the base annihilator is `(h²)`.
20. `lawCotangentMap_surjective`, `ker_lawCotangentMap`, `lawKaehlerBaseEquiv` — as a `B`-module,
    `Ω[A⁄B] ≅ B/(h²)`.

21. `four_shadow_table` — **card `(15)`, the four-shadow table**, as one proposition: the oriented
    family defect is the different `2η − h`; its square is `h²`, which presents the cotangent
    module over the base; the topological support wall is the collision kernel; and the hidden
    decoder conditioning obeys `√|Disc| · ‖D_h‖ = √2` with the genuine operator norm.  Asserting
    the four together is the card's claim that they are shadows of *one* object, which items 16,
    20, 3, 10 and 14 give only separately.  The arithmetic substitution `(16)`–`(18)` is explicitly a
representation, not a theorem, on the paper card.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/MonogenicKaehler.lean      # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/QuadraticLawHorizon.lean   # clean
lake build GaloisForLFunctions.HTGeometry                                                    # green
```
