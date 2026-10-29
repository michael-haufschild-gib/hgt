# Arithmetic Krein–Langer theory (AKL): from local data to a global index

- **ID:** akl-programme
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2910/obstacles-summary.md §2.8
- **Statement:** the local-to-global part of Krein–Langer theory on `Γ = ℚ_{>0}`: locality, ceilings, producers, completion and parity; HKT is the foundation and is not restated.

## Goal
Build `formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/` with umbrella and README; prove the
pillars that are theorems; prove no-gos with positive survivors for those that are not.

Scope decision (2026-10-29): §2.8 restates HKT's agenda almost item for item; AKL owns only the
four pillars §2.8 lists as missing (ceiling, producer, completion, parity at √-precision) plus
locality, and must not duplicate HKT modules.

## Gates
- [x] 0 → 1  scope fixed, README first draft
- [ ] modules below proved and wired into the umbrella

## Module plan
1. `CyclicSubgroupsDecideTheKreinLangerClass` — cyclic Hasse principle on every group (Neumann's
   lemma + Dedekind on torsion classes); separation without torsion aliasing; ℤ² KL kernel
   `2i sinh(v₁ log 2)(1−(−1)^{v₂})` of index 2 vanishing on both axes; non-KL kernel
   `δ₀ − ½Σ_{e₁,e₂,e₁+e₂}(δ_w+δ_{−w})` positive on every cyclic subgroup, not on ℤ².
2. `TowerFaithfulSpectra…` — abstract tower Hasse principle; logarithmic spectra tower-faithful.
3. `TheEulerFactorIsAPoissonKernel` — `r^{|n|}` PD; local constituent `log p δ₀ − L_p`; twins PD;
   finite place sets have infinite index.
4. `𝔽_q` local-to-global — trace kernel = pole − closed points; `κ ≤ g`; golden.
5. Twist completion over `𝔽_q` — upper counts for `D` and `β ↦ −β` force unitarity.
6. Index continuity along non-coalescent convergence.

## Leads checked (exist; do not redo)
- One-sided real-node principle: ACS `UpperLefschetzBoundsAreBlindOnlyToRealZeros`,
  `OneSidedLefschetzBoundsAt{One,Two}Prime(s)AreTheStrip`.
- Subtracted-wave Landau: `RHTower/FiniteOffLineLandau`.
- Arithmetic tower locality: HKT `negIndex_eq_zero_of_posDef_on_infinitely_many_towers`.
- Neumann's lemma: Mathlib `Subgroup.leftCoset_cover_filter_FiniteIndex`.
- Real zeros: `RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo`.

## Proved (axiom audit clean, wired into the umbrella)
- `CyclicSubgroupsDecideTheKreinLangerClass`, `TowerFaithfulSpectraAreDecidedByAlmostEveryTower`,
  `LocalConstituentsMeetOnlyAtTheIdentity`, `TheTwistTowerCompletesTheUpperCount`,
  `TheIndexIsContinuousOffTheDiscriminant`, `TheParityFormOfTheGlobalLaw`,
  `TheIndexIsTheNumberOfExceptionalWaves`, `CompressionsAreReceivers`,
  `FineTowersDecideEveryOrbitKernel`, `LocalityIsTwinBlind`, `TheCollisionMassIsTheWaveNumber`,
  `AttainedDepthIsSeenByAlmostEveryPrime`, `IntegralityProducesLinearCounts` (Bézout ledger,
  binomial multiplicity cap, divisibility is parity-blind), `StepanovsOrderOverTheFiniteField`,
  `TheParityTwinIsGeometricOnlyInTheBohrClosure`, `PointwiseClosedStatementsAreTwinBlind`, `TheFunctionFieldCeilingIsExact` (exact ceiling and the
  lower half of the second rung over `𝔽_q[T]`), `FineTowersHaveUnboundedNyquistWindows`, `ChebyshevsProducerPassesTheIntegerChebyshevCap`, `ThePolarDivisorCountsTheIndex`.

## Open (RH/LH-deep, recorded in README §9)
Producer over ℤ; Lindelöf bridge from the kernel; a geometric parity twin beyond vertical shifts;
selective transfer past Robin–Euler; the upper half of the second rung over `𝔽_q[T]` (spectral gap
of `P_N` on the pole hyperplane); two-sided coalescent pair theory; prime-tower locality when the depth supremum
is unattained (attained depth and fine towers are settled; the collision law is read from one
minimal count).

## Log
- 2026-10-29 — created; README draft written; twenty-one modules in the umbrella (one by another agent); README tools table covers every §2.8 tool.
