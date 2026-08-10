# congruence-order-trace-kahler-exterior-square-nonmetricity-law — Lean progress

Card: `docs/drafts/pipeline/2-fully-proven/constraint-relativity/congruence-order-trace-kahler-exterior-square-nonmetricity-law.md`
Module: `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/CongruenceOrderExteriorSquare.lean`
(green, wired into `HTGeometry.lean`, ~1557 lines — SPLIT the next phase into a new file).

## DONE

- card (3): `observerDefectEquiv` — `O/A ≅ k^m`.
- card (15): `congruencePresentation` (`A ≅ R[x]/(xᵢ²−axᵢ, xᵢxⱼ)`), `congruenceCoordEquiv`
  (`R × R^m ≃ₗ A`, the free basis `1, x₁,…,x_m`).
- structural half of (5): `kaehlerModelEquiv` — `Ω[A⁄R] ≃ₗ[A] (A^m ⧸ kaehlerRelations)`.
- **card (5) COMPLETE**: `kaehlerCongruenceEquiv (ha : a ≠ 0) :
  Ω[(MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)⁄R] ≃ₗ[R] cotangentModel a m`
  where `cotangentModel a m = (Fin m → R ⧸ span{a²}) × (pairIndex m → R ⧸ span{a})`,
  `pairIndex m = {p : Fin m × Fin m // p.1 < p.2}`.
  Hypotheses: `[CommRing R] [IsDomain R] [Invertible (2 : R)] (ha : a ≠ 0)` — no premises.

### How card (5) was proved (reusable pattern)
1. `coordSplit` on coordinates: `(c,d) ↦ (cᵢ + ½a·dᵢᵢ  mod a², dᵢⱼ − dⱼᵢ  mod a)`.
2. `kaehlerSplitRaw = coordSplit ∘ congruenceCoordPi` and four evaluation lemmas
   `kaehlerSplitRaw_single_one / _single_self / _single_lt / _single_gt`.
3. The A-span of the relations is the R-span of the ENLARGED set
   `kaehlerRelationSetR = kaehlerRelationSet ∪ {a • Pi.single i xₖ}`:
   `kaehlerRelations_restrictScalars`. Proof route: build an A-submodule `kaehlerRelationsA`
   whose carrier is the R-span (needs `smul_mem_relR`, which decomposes `c ∈ A` via
   `congruenceCoordEquiv_eq` into `algebraMap c₀ + ∑ algebraMap cₖ * xₖ`).
4. Inverse `modelInv` built from `diagLift i` / `pairLift p` (`Submodule.liftQ` of
   `toSpanSingleton`), using `sq_smul_cotBasis` (`a²·eᵢ = 0`) and `smul_a_cotPair` (`a·zᵢₖ = 0`).
5. `span_cotGens` (the classes `eᵢ`, `xₖeᵢ` span over R) + `LinearMap.ext_on`.

## Lean traps hit here (do not rediscover)
- `Module R (MvPolynomial ι R ⧸ I)`: the R-smul instance found is NOT `Algebra.toSMul`, so
  `rw [Algebra.smul_def]` FAILS on `r • x`. Always phrase A-side products with `algebraMap`
  and cross over with `IsScalarTower.algebraMap_smul A r`.
- `rw [← Pi.single_smul]` on the quotient type causes whnf TIMEOUTS. Instead prove
  `smul_single : c • Pi.single i x = Pi.single i (c * x)` once by `funext`+`by_cases`.
- `Pi.single p t` inside a `show`/`have` needs `(ι := …) (M := fun _ => …)` — the implicit
  names are `ι`/`M`, not `I`/`f`.
- `(x, y).1` does not reduce for `rw`; use `show` to change the goal instead.
- `rcases` on `kaehlerRelationSet` membership unfolds `sqRelation`/`crossRelation`; re-fold
  with `show congruenceX a m l • sqRelation a m i ∈ _`.
- Unused section variables (`[IsDomain R]`, `[Invertible 2]`) are lint ERRORS; and declaring
  an instance BOTH as a section variable and explicitly gives "overlapping instances".

## REMAINING for the card
- (4) `L = A♯/A ≅ (R/a²)^m`. PLAN (fully worked out on paper, no Smith machinery needed):
  work with `scaledDual = {z : Fin N → R | a ∣ ∑ z i}` (`= a·A♯`) and `a·A`; the map
  `Φ z = (i ↦ (z i − N⁻¹ ∑ⱼ z ⱼ) mod a²)` is R-linear, kills `a·1` and `a²eᵢ`, is surjective
  (lift `c` to `z = (c, −∑c)`), and has kernel exactly `a·A` because `N − m = 1` forces
  `z_N ≡ N⁻¹ s` too. Only `IsUnit (N : R)` is needed (NOT `Invertible 2`).
  Faithful version: `A♯ ⊆ Fin N → FractionRing R`, card (9) `A♯ = a⁻¹·scaledDual`, then
  multiplication by `a` gives `A♯/A ≅ scaledDual/(a·A)`.
- (6) `Ω/aΩ ≅ C ⊕ Λ²C`; use `Fintype.card_finset_len` and `exteriorPower.finrank_eq`
  (both verified present), with `pairIndex m ≃ {s : Finset (Fin m) // s.card = 2}`.
- (7) pair sector has rank `binom (N−1) 2`.
- (26b)–(26g) tangent-head soldering obstruction (`Hom_A(Ω,L) ≅ Mat_{m×m}(k)`, head map zero).
- (26k) `𝔇_D = a²O`, (26l) `𝔇_K = Fitt₀ Ω = a^m O`.
- (27)/(28) lengths `2m` vs `2m + binom m 2`, discrepancy `binom (N−1) 2`.
