# Card: phase-holomorphic-autonomous-ade-frequency-rank — Lean build (started 2026-08-06)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/phase-holomorphic-autonomous-ade-frequency-rank.md`
`[FORMALIZATION IN PROGRESS]`; five-layer plan + ledger at card EOF. Target `rank_ℚ Γ(f) = s ≤ n`.

## Why this card (not the other two on the loop list)
- `euler-activation-squarefree-valuation-disintegration`: all PROVED theorems already formalized;
  remaining gates are `[BOLD CONJECTURE]`/RH-bearing.
- `commutative-d-group-source-boundary-universality`: needs algebraic `D`-groups + differential
  transcendence degree; mathlib has neither.

## LAYERS 1–4 DONE (all axiom-clean), layer 5 in progress
All modules in `formal/GaloisForLFunctions/HTGeometry/`, all wired into `HTGeometry.lean`.

**L1** `CharacterLatticeFrequencyRank.lean` — eq (26). `rank_span_int_eq_rank_span_rat`
(`IsLocalization.rank_eq ℚ ℤ⁰` + `LinearIndependent.iff_fractionRing`),
`injective_ratCharacterDetuning`, `rank_span_characterFrequencySet`.

**L2a** `PolyannulusTorusUniqueness.lean` — `logAnnulus`, `eqOn_zero_logAnnulus`,
`polyannulus`, `unitTorus`, `mixedAnnulus`, `eqOn_zero_polyannulus_of_eqOn_zero_unitTorus`,
`eqOn_polyannulus_of_eqOn_unitTorus`.

**L2b** `TorusOrbitPolyannulusUniqueness.lean` — `torusOrbitPoint`, `circleCoords`,
`unitTorus_subset_closure_range_torusOrbitPoint`, `isOpen_polyannulus`,
`eqOn_zero_polyannulus_of_eqOn_zero_orbit` = eq (10).

**L3** `TorusDerivationJets.lean` — eqs (7)–(8). `phasePoint`, `phaseStrip`, `coordDeriv`,
`torusDerivation`, `analyticOnNhd_torusDerivation(_iterate)`, `fderiv_apply_eq_sum`,
`deriv_phaseFunction`, `iteratedDeriv_phaseFunction(_ofReal)`.

**L3'** `PhaseJetRelationTransfer.lean` — eqs (9)–(10). `analyticOnNhd_mvPolynomialEval`,
`analyticOnNhd_polynomialEval₂`, `phaseJet`, `phaseJetEval`, `RealAutonomousAnnihilator`,
`realAutonomousAnnihilator_iff_phaseJetEval_eq_zero`.

**L4a** `ActivePhaseLattice.lean` — eqs (4), (17), (20), (21). `eq_of_mFourierCoeff_eq`,
`fourier_neg_point`/`fourier_add_point`/`mFourier_add_point`/`mFourier_neg_point`/`mFourier_apply_zero`
(mathlib has these only in the INDEX variable, not the point), `torusRestriction`, `activeCoeff`,
`activeSupport`, `activeLattice`, `eqOn_polyannulus_of_activeCoeff_eq`, `torusScale`,
`mFourierCoeff_translate`, `activeCoeff_comp_torusScale`, `eqOn_comp_torusScale_iff`.

**L4b** `AllJetLevelSet.lean` — eqs (19), (22). `eqOn_of_iteratedDeriv_eq`
(`natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero` + `analyticOrderAt_eq_top`),
`convex_phaseStrip`, `analyticOnNhd_phaseFunction`, `torusScaleL`,
`torusDerivation_comp_torusScale`, `torusDerivation_congr`, `phaseJet_congr`,
`phaseJet_comp_torusScale`, `iteratedDeriv_phaseFunction_comp_torusScale_zero`,
`eqOn_polyannulus_of_phaseJet_eq`, `phaseJet_eq_iff_mFourier_eq_one`.

**L5 (partial)** `AlgebraicIndependenceFromDifferentials.lean` —
`mvPolynomial_eq_zero_of_eqOn_zero_isOpen` (polynomial vanishing on a nonempty open subset of ℂ^r
is zero; uses `AnalyticOnNhd.eval_mvPolynomial` + the SEVERAL-VARIABLE identity theorem
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`, which IS general in mathlib,
+ `MvPolynomial.funext`), `mvPolynomial_eq_zero_of_hasStrictFDerivAt_equiv/_injective`
(via `HasStrictFDerivAt.map_nhds_eq_of_equiv`), `mvPolynomial_eq_zero_of_family_hasStrictFDerivAt`.

## KEY DISCOVERY — the Laurent gap is avoidable
Mathlib has NO Laurent expansion (1 or several variables). Not needed: define the active lattice by
the TORUS FOURIER coefficients (`Mathlib.Analysis.Fourier.AddCircleMulti`: `UnitAddTorus.mFourier`,
`mFourierCoeff`, `mFourierBasis`), then push identities from the torus to the polyannulus with L2.

**Instance trap**: `AddCircleMulti` declares `MeasureSpace UnitAddCircle` as a LOCAL instance which
differs from the global `AddCircle.measureSpace 1`. To use its theorems, put at file top:
`attribute [local instance] instMeasureSpaceUnitAddCircle` plus local `IsProbabilityMeasure` and
`Measure.IsAddHaarMeasure` instances for `(volume : Measure UnitAddCircle)`.

## REMAINING (layer 5)
- differential-rank argument: if the max span dimension `d` of the jet differentials is `< r`, the
  implicit function theorem gives a nonconstant curve in the all-jet level set, contradicting the
  finiteness of that level set (= (22) when the active lattice has full rank). So `d = r`.
- reduce the general case to a full-rank active lattice (factor `F` through `z ↦ (z^{m_1},…,z^{m_s})`).
- separant half `trdeg ≤ n`: mathlib HAS `Algebra.trdeg` (`RingTheory/AlgebraicIndependent/Basic`);
  corpus already uses it in `HTGeometry/LinearVersusAlgebraicCollapse.lean`. Ambient algebra should
  be functions on `↥(polyannulus ρ)`, not on all of ℂ^d.
- `bohrCoefficient f (m·ω) = activeCoeff F m` via Weyl equidistribution, for the `rank_ℚ Γ(f) = s` half.

## Traps hit
- `convex_halfSpace_re_gt` takes an EXPLICIT `(r : ℝ)`; module `Mathlib.Analysis.Complex.Convex`.
- `Real.two_le_pi` instead of `Real.pi_gt_three` when imports are narrow.
- `Module.rank` universes: state frequency-rank results with `d : Type` (universe 0).
- `Circle` is a non-reducible `def`; use `fourier 1` and `Complex.norm_mul_exp_arg_mul_I`.
- `simpa ... using h` breaks `AnalyticOnNhd`/`Pi.add` defeq — prove the FUNCTION equality with
  `funext` + `rw`, then `rw [hfun]; exact ...`; for `⇑clm ∘ f` vs a lambda use `intro z hz; exact h z hz`.
- `Function.iterate_succ_apply'` is NOT defeq — `show ... = f^[k+1] x` then `rw`, never `show f (f^[k] x)`.
- narrow mathlib imports: `Mathlib.Analysis.Analytic.Polynomial` does not bring ℂ's instances; add
  `Mathlib.Analysis.Complex.Basic`, `Mathlib.Analysis.Normed.Module.FiniteDimension`,
  `Mathlib.Algebra.MvPolynomial.Funext`.
