# Premise discharge by connecting corpus results (250 target)

- **ID:** premise-discharge-250-20261023
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Statement:** Conditional corpus theorems whose premise (named `Prop` interface or explicit
  hypothesis) is proved elsewhere in the corpus get hypothesis-free forms.

## Counting rule

One discharge = one new hypothesis-free Lean theorem obtained by supplying corpus proofs for every
non-typing premise of an existing conditional theorem, where no hypothesis-free form existed.
Not counted: trivial premises (`(0:ℝ) < 1/2`), theorems that keep any non-typing premise,
restatements of an already-welded conclusion. Each module is compiled with
`lake --old env lean <file>` and wired into its umbrella.

**Discharges: 264 compiled / 250.** Every module is compiled with `lake --old env lean` and checked with `#print axioms` (only `propext`, `Classical.choice`, `Quot.sound`).

## Candidate finder (scratch, not in repo)

Declaration census of `formal/GaloisForLFunctions` (binders, conclusion, namespace, `open`s,
section variables); closed premises = hypotheses mentioning no bound variable; closure of
proved closed propositions through premise-free theorems, top-level `↔` and `∧`. Traps found:
outer-paren stripping on `(A) ↔ (B)`, namespace collisions (resolve through namespace chain and
`open`s), instance binders `[FiniteDimensional …]` as premises, `autoImplicit` true in many files
(unknown lowercase identifiers are bound variables). Text identity is exhausted after ~45 welds;
further discharges need statement bridging (unfolding, `↔`, weakening) found by corpus search.

## Ledger

| # | module | premise discharged (provider) | theorems |
|---|--------|-------------------------------|----------|
| 1–16 | `RHTower/RiemannGaussian/GaussianPremiseDischarges` | `ZetaZeroGaussianOrdinateSummable`, `RiemannXiQuadraticGrowth`, `QuarterLineDigammaGaussDifferenceFormula`, `GaussianDigammaScrewTransform`, `GaussianArithmeticExplicitFormulaIdentified`, `ZetaGaussianZeroDivisorSeparation` | 16 |
| 17–23 | `HTGeometry/PaperFourierLLogL/GoodBoundUnconditional` | `GridBound → UnitTreeBound → AffineTreeBound → RealGoodBound`, `GoodBound` | 7 |
| 24–33 | `RHTower/Zeta23InputDischarges` | `GammaFacts`, μ-increment constant, `PaperInputs ζ` | 10 |
| 34 | `Bottcher/Brolin/RieszDiracUnconditional` | `FundamentalSolutionProp` | 1 |
| 35 | `HTGeometry/PaperStableCoordinate/AllFibersNonrectifiable` | `¬ IsCoordinate f` | 1 |
| 36 | `RHTower/BakerHomogeneousIndependence` | `BakerTheorem` | 1 |
| 37–44 | `RHTower/GuthMaynardCorollariesUnconditional` | `GuthMaynardLargeValuesBound` | 8 |
| 45–52 | `RHTower/XiZeroCopyPremiseDischarges` | `Infinite/Nonempty XiZeroCopy`, `TwistedArcMinimumPrinciple`, `xiEndpointCompletedCurvature < 1` | 8 |
| 53–54 | `RHTower/ModularLambdaCellEnergyBoundUnconditional` | `Fintype (SL₂ℤ ⧸ Γ(2))`, finite `[Γ(2):Γ_N]` | 2 |
| 55–57 | `RHTower/CHMDZeroMeasurePositivityUnconditional` | `Nonempty zetaZeroConfig.carrier` | 3 |
| 58–77 | `RHTower/ThetaCuspSteinCertificates` | Stein ratio bounds, strict first minor, `BW_{j,0,1} = wⱼ`, `BW_{j,1,1} = w_{j+1}` → `↔` certificates | 20 |
| 78 | `RHTower/SuzukiCutoffSimpleCriticalUniqueness` | positive simple-critical density | 1 |
| 79–134 | `RHTower/RiemannGaussian/GaussianXiGrowthConstantDischarges` | ξ growth laws as `∃ A` | 56 |
| 135–140 | `RHTower/RiemannGaussian/ThetaTailConstantDischarges` | `exists_riemannThetaTail_exp_bound` | 6 |
| 141–245 | `*/UniformConstantDischarges*` (23 modules) | proved `∃`-bounds (ζ/χ strip bounds, Stirling μ, Γ decay, kernel bounds, smooth-transition derivative bounds, …) | 105 |
| 246–247 | `RHTower/CCM/UniformConstantDischarges` (Barta far defect) | smooth-transition first and second derivative bounds | 2 |
| 248–251 | `RHTower/InstantiationPremiseDischarges` | AFE inner cutoff radius, `xiMassVerticalBound_nonneg`, `xiSpectralPoint_re_ne_zero` | 4 |
| 252–253 | `RHTower/Deninger/CharZeroUnitRankDischarges` | `C^× ≠ μ(C)` in characteristic zero (`deningerExists_notMem_torsion_charZero`) | 2 (incl. `dim_ℚ = #C`) |
| 254–256 | `RHTower/ThetaCusp/WitnessPremiseDischarges` | first-fiber rise, positive compensation zero | 3 |
| 257–259 | `RHTower/ZetaStripBoundPremiseDischarges` | `ζ` strip polynomial bound, `χ` decay, critical-line second moment, pole-cleared growth | 3 |
| 260–261 | `RHTower/AbelLineConstantDischarges` | `Γ`, `Γζ` decay and `1/ζ` on `Re s ≥ 3/2` | 2 |
| 262–264 | `RHTower/UniformConstantDischargesE` | explicit pole bound `A = 1`, smooth-transition derivative bound | 3 |

Heartbeat budgets: the three direct dependencies that raised `maxHeartbeats`
(`Sieve/ZetaWideDLVP`, `ThetaGibbsSteinSourceMinor`, `XiStrictSchwarzSixthSpectralCeiling`) compile
at the default budget with the option removed. 446 further modules deeper in the import closure
still set a raised budget.

Uniform-constant discharges: a consumer `(C : ℝ) (hC : P C) … ⊢ Q C` with `∃ C, P C` proved becomes
`∃ C, ∀ …, Q C`, or the constant is eliminated when `Q` does not mention it. Drafted by a generator
from the census (consumer binders + provider `∃`-shape), filtered to constant-like witnesses whose
provider is a bound and whose retained hypotheses only constrain data; each module is compiled.

Excluded after audit: the order-24 sixth-trace chain (its moment bounds use `native_decide`);
headline welds the authors already made (Theorem D headline, GM 30/13, Weyl/Riesz support,
q62 Weyl discharge, PNT-power windows, ξ-growth Jensen counts, `ThetaWronskian23` consumers,
exponential-tower exact order, all-cofinal Cesàro no-go); weakenings of existing strict facts
(first minor, `2 × 2` determinant); consumers that keep an analytic hypothesis (Möbius/k-free Abel
edges, Littlewood windows, vertical mean-square window); typing side-conditions used only to build
a term (domain memberships).

## Log
- 2026-10-23 — created; candidate finder built; batches through #36 green; concurrent `lake build`s by other agents delete oleans transiently, so compiles of pending modules wait for them.
