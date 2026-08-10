# congruence-order-trace-kahler-exterior-square-nonmetricity-law — Lean progress

Card: `docs/drafts/pipeline/2-fully-proven/constraint-relativity/congruence-order-trace-kahler-exterior-square-nonmetricity-law.md`

Three modules, all green, wired into `GaloisForLFunctions/HTGeometry.lean`;
`lake build GaloisForLFunctions.HTGeometry` is GREEN.
1. `ConstraintRelativity/CongruenceOrderExteriorSquare.lean` (1557 lines — do NOT grow it)
2. `ConstraintRelativity/CongruenceOrderTraceDual.lean`
3. `ConstraintRelativity/CongruenceOrderHorizon.lean`

## DONE (card items) — all unconditional, no hypotheses beyond the card's own setting

- (3) `observerDefectEquiv` — `O/A ≅ k^m`.
- (15) `congruencePresentation`, `congruenceCoordEquiv` (free basis `1, x₁,…,x_m`).
- (16-Lean) `kaehlerModelEquiv` — `Ω[A⁄R] ≃ₗ[A] (A^m ⧸ kaehlerRelations)`.
- **(5)** `kaehlerCongruenceEquiv (ha : a ≠ 0) : Ω[…⁄R] ≃ₗ[R] cotangentModel a m`,
  `cotangentModel a m = (Fin m → R ⧸ span{a²}) × (pairIndex m → R ⧸ span{a})`,
  `pairIndex m = {p : Fin m × Fin m // p.1 < p.2}`.
  Setting `[CommRing R] [IsDomain R] [Invertible (2 : R)] (ha : a ≠ 0)`.
- **(9)** `mem_traceDual_iff`, `traceDual_eq_map` — `A♯ = a⁻¹·{z : a ∣ ∑ zᵢ}`.
- **(4)** `traceDefectEquiv` (and integral form `scaledTraceDefectEquiv`):
  `A♯/A ≅ (R/a²)^m`.  Key map `traceCoord a m z i = mk (z i.castSucc − N⁻¹·∑ⱼ zⱼ)`;
  `N − m = 1` forces the last coordinate into the same class, so no Smith machinery is needed.
  Setting adds `[Invertible ((m : R) + 1)]` and a fraction field `K`.
- **(6)** `horizonExteriorSquareEquiv (ha : a ≠ 0) :
  Ω ⧸ (span{a} • ⊤) ≃ₗ[R ⧸ span{a}] (Fin m → k) × ⋀[k]^2 (Fin m → k)`,
  plus `kaehlerFibreEquiv` (R-linear, into `(Fin m → k) × (pairIndex m → k)`).
- **(7)** `card_pairIndex : Fintype.card (pairIndex m) = m.choose 2`.
- **(27)** `length_cotangentModel` = `2m + choose m 2`, `length_traceDefectModel` = `2m`.
- **(28)** `length_cotangentModel_eq_length_traceDefect_add`.

## REMAINING

- **(26b)–(26g)** tangent-head soldering obstruction: `xⱼ` acting on `L`, `𝔪_A L = aL`,
  `im φ ⊆ aL` for every A-linear `φ : Ω → L`, `Hom_A(Ω,L) ≅ Mat_{m×m}(k)`, head map ≡ 0.
  Also needs `N − 2` a unit (`Invertible ((m : R) − 1)`).
- **(26k)** `𝔇_D = a²O` (needs `N ≥ 3`: a third coordinate of `d·bᵢ` is 0, which forces
  `a ∣ dᵢ/a`).  **(26l)** `𝔇_K = Fitt₀^A Ω = a^m O` (the card's (26m)–(26o) minor computation).

## Reusable assets created
`aMul a M` (= `span{a} • ⊤`, `aMul_eq_smul_top`), `aMul_prod`, `aMul_pi`, `map_aMul`,
`prodFibreEquiv`, `piFibreEquiv`, `sqFibreEquiv` (`(R/a²)/a ≅ R/a`), `linFibreEquiv`,
`quotientScalarsEquiv` (an R-linear equiv of `R⧸I`-modules with `IsScalarTower` is `R⧸I`-linear),
`pairIndexEquivPowersetCard`, `exteriorSquareModel` (`(pairIndex m → k) ≃ₗ[k] ⋀[k]^2 k^m`).

## Lean traps (do not rediscover)
- `Module R (MvPolynomial ι R ⧸ I)` picks the quotient-module instance, NOT `Algebra.toSMul`;
  `rw [Algebra.smul_def]` fails on `r • x`. Phrase A-side products with `algebraMap`, cross over
  with `IsScalarTower.algebraMap_smul A r`.
- `rw [← Pi.single_smul]` on the quotient type causes whnf TIMEOUTS; prove
  `smul_single : c • Pi.single i x = Pi.single i (c * x)` once by `funext`+`by_cases`.
- `Pi.single p t` inside `show`/`have` needs `(ι := …) (M := fun _ => …)`.
- `(x, y).1` does not reduce for `rw`; use `show`.  `abbrev`s (e.g. `cotangentModel`) cannot be
  `rw`-unfolded; use `show`.
- `LinearMap.proj i` / `LinearMap.id` inside a `have`/`def` often need an explicit type ascription
  or instance search gets stuck on metavariables.
- `x ∈ aMul a M` does not display as `∃ u, a • u = x`; `rw [mem_aMul]` first.
- `Module R (⋀[k]^2 M)` does NOT synthesize for `k = R ⧸ I`; state the exterior-square half over
  `k` and upgrade the R-linear half with `quotientScalarsEquiv`
  (mathlib HAS `Module (R⧸I) (M ⧸ I • ⊤)` and `IsScalarTower R (R⧸I) (M ⧸ I • ⊤)`).
- Unused section variables are lint ERRORS; an instance declared both as a section variable and
  explicitly gives "overlapping instances".
- UMBRELLA COLLISION hit here: `sumForm_apply` already existed in
  `ConstraintRelativity/PortCapacity.lean`; renamed to `congruenceSumForm`. Per-file
  `lake env lean` cannot see this — run `lake build GaloisForLFunctions.HTGeometry`.
- The lint gate reports one PRE-EXISTING error from another session:
  `owned module unreachable from umbrella GaloisForLFunctions.RHTower.DeningerWordHeight`.
  Not ours — do not touch.
