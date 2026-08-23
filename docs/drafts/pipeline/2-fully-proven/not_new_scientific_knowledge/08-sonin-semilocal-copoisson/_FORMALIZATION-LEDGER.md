# 08-sonin-semilocal-copoisson — stage-2 → stage-3 formalization ledger

Goal: formalize unconditionally in Lean every proven theorem of every card in this folder, add the
missing infrastructure, then move each card to
`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/08-sonin-semilocal-copoisson/`.

Rules in force: no added hypotheses standing for analytic inputs, no axioms, no `sorry`;
never full builds / umbrella builds (`lake env lean <file>` to check, `lake build <module>` only for
the oleans an `#print axioms` scratch needs); search the corpus before building anything.

## Card triage (17 cards) — 7 promoted, 10 remain

| # | card | state | notes |
|---|---|---|---|
| 1 | archimedean-prolate-jacobi-limit-circle-transition | TODO | needs discrete limit-circle theory; card's λ=0 exponents are wrong (see below) |
| 2 | boolean-sonin-full-history-mate-fracture-law | **PROMOTED 2026-08-22** | `HTGeometry/BooleanSoninFullHistory.lean` |
| 3 | connes-semilocal-finite-part-orbital-source-class | **PROMOTED 2026-08-22** | `HTGeometry/QuantizedDifferentialCocycle.lean` + `RHTower/ConnesSemilocalOrbitalSourceClass.lean`; `(1)`–`(3)` stay literature (Connes) and are *not* assumed by any Lean statement |
| 4 | finite-euler-connection-cauchy-phase-chambers | **PROMOTED 2026-08-22** | `RHTower/FiniteEulerConnectionCauchyPhaseChambers.lean`; the card's "Kronecker hitting theorem missing" note was stale |
| 5 | prime-tail-copoisson-essential-boundary-bockstein | TODO | |
| 6 | rectangular-semilocal-observer-tail-separation | **PROMOTED 2026-08-22** | `RHTower/RectangularSemilocalObserverTailSeparation.lean` |
| 7 | route-b-semilocal-sonin-interim-verdict | TODO | |
| 8 | semilocal-dual-pair-euler-connection-source-law | **PROMOTED 2026-08-22** | `RHTower/SemilocalDualPairEulerConnection.lean`; the card's "needs an unbounded operator interface" note was wrong — the content is a commutator identity on the differentiable core |
| 9 | semilocal-euler-kernel-chart-differentiability | TODO | |
| 10 | semilocal-jacobi-linear-growth-prolate-domain-gate | **PROMOTED 2026-08-22** | `HTGeometry/MonicOrthoExtremalComparison.lean` + `RHTower/SemilocalJacobiLinearGrowthProlateDomainGate.lean` |
| 11 | sonin-burnol-conductor-cutoff-bounded-graph-law | TODO | |
| 12 | sonin-place-transition-cutoff-dichotomy | **PROMOTED 2026-08-22** | `RHTower/SoninRawSupportCutoffCornerNoncompact.lean` closes part B |
| 13 | sonin-prime-seam-exterior-factorization | PARTIAL | `HTGeometry/BilinearExteriorPairFactorization.lean` + `RHTower/SoninPrimeSeamExteriorFactorization.lean` give `(3)`, `(8a)`, `(8g)`; blocked only on card 15's tensor estimate `(4)`–`(5)` |
| 14 | sonin-small-cutoff-ground-row-survival | TODO | |
| 15 | sonin-two-particle-prime-coherence | TODO | |
| 16 | squarefree-cutoff-jump-root-avoidance-inertia | TODO | |
| 17 | transported-prolate-relative-resolvent-corner | TODO | |

## Corpus assets found (do not rebuild)

- `HTGeometry/MomentInnerProduct.lean` — `momentInner`, `PositiveMomentForm`.
- `HTGeometry/OrthogonalMomentPolynomials.lean` — `monicOrtho`, degree/monicity/orthogonality.
- `HTGeometry/AdaptiveOrthogonalSourceJacobiEnergy.lean` — `monicOrthoNormSq`, `monicOrthoAlpha`,
  `monicOrthoBeta` (`monicOrthoBeta s (n+1) = H_{n+1}/H_n`).
- `HTGeometry/FavardJacobiMomentRealization.lean` — `monicOrthoNormSq_favardMoment`.
- `RHTower/SoninSemilocalGammaMeasureCharacteristic.lean` — `semilocalArchimedeanGammaMeasure`,
  `semilocalArchimedeanGammaDensity`.
- `RHTower/SoninSemilocalJacobiRecurrence.lean` — `semilocalArchimedeanJacobiCoefficient n =
  √((n+1/2)(n+1))` = the card's `a_n(∅) = √((2n+1)(2n+2))/2`.
- `RHTower/SoninSemilocalJacobiOrthonormal.lean` — orthonormality of the archimedean family.
- `RHTower/SoninSemilocalFinitePrimeMeasure.lean` — `semilocalFinitePrimeEulerDensity`
  (finite family `p : Fin n → ℕ`), positivity, integrability, Poisson expansion.
- `RHTower/JacobiDeficiencyRankTwoAmbiguity.lean` — `IsJacobiSolution`, `jacobiSolutions`,
  `jacobiDeficiency`, `rank_jacobiDeficiency_le_one`, `jacobi_deficiency_indices`,
  `exists_isSelfAdjoint_extension_of_deficiency_one`.
- `RHTower/SemilocalProlateCriticalPotential.lean` — the four-point critical-potential identities.

## Mathematical corrections found while auditing the cards

- **card 1** (`archimedean-prolate-jacobi-limit-circle-transition`), section "Lean route":
  the `λ = 0` frozen-coefficient discriminant analysis is invalid.  At a **double** characteristic
  root the frozen roots do not approximate the true solution ratios to order `1/n`
  (test case `u_{n+1} − 2u_n + u_{n−1} = 0`: frozen roots `{1,1}`, true exponents `{0,1}`).
  The exact discrete Wronskian `ρ_n(u_{n+1}v_n − u_n v_{n+1}) = const` forces
  `s_1 + s_2 = −1`, not the card's `−2`.  Correct indicial equation at `λ = 0`:
  `s² + s + (3/4 − z)/4 = 0`, i.e. `s = (−1 ± √(1/4 + z))/2`; at `z = 0` the exponents are
  `−1/4, −3/4`.  The card's conclusion (limit point at `λ = 0`) survives, because the dominant
  exponent `−1/4 > −1/2`.

## Per-card formalization plan (2026-08-22)

### 10 · semilocal-jacobi-linear-growth-prolate-domain-gate — IN PROGRESS
New modules:
- `HTGeometry/MonicOrthoExtremalComparison.lean` (DONE, checks clean):
  `momentInner_self_eq_monicOrthoNormSq_add`, `monicOrthoNormSq_le_momentInner_of_monic`,
  `eq_monicOrtho_of_monic_of_orthogonal`, `mem_span_of_degree_lt`,
  `monicOrtho_eq_of_orthogonal_family`, `monicOrthoNormSq_of_orthogonal_family`,
  `monicOrthoNormSq_le_of_momentInner_le`, `monicOrthoBeta_le_of_momentInner_le`.
- `RHTower/SemilocalJacobiLinearGrowthProlateDomainGate.lean` (in progress): archimedean moment
  form, `monicOrthoBeta_ccmMetaplecticGammaMoment n = (n+1/2)(n+1)`, the Euler-density two-sided
  bound, the semilocal cyclic moment sequence, the `K_P` comparison, the Jacobi-coefficient
  two-sided bound, quadratic growth of `b^±`, and summability of their reciprocals.

### 2 · boolean-sonin-full-history-mate-fracture-law
New module `HTGeometry/BooleanSoninFullHistory.lean` (written, unchecked):
`ReciprocalContractionSection`, `wordMap`, `historyEnergy`, `historyEnergy_le` (5),
`historyEnergy_y` (6), `norm_y_lower` (7), `mateDefect`, `mateCoeff`, `mateCoeff_true`/`_false`
(14), `mate_difference` (15), `mate_fracture` (16), `norm_eq_one_of_mates_small` (17), and the
`dilationCharacter` specialization (22b)–(22e).
Still to add: the (28)–(31) quotient-class algebra.

### Remaining triage notes
- **1** needs a genuine discrete limit-circle theorem (see the correction above); plan: discrete
  variation-of-constants `z`-independence + a sharp Liouville–Green estimate at one real `z`.
- **3** formalizable core: the Leibniz cocycle `ω(UV) = V⁻¹ω(U)V + ω(V)` and the unbounded-response
  quotient nonvanishing; the semilocal trace formula itself is literature.
- **4** needs Kronecker density on the finite prime torus from the existing character
  nonresonance (`HTGeometry/KroneckerFlow.lean`).
- **5** needs PNT with classical error term + Mellin; heavy but the corpus owns much of the PNT lane.
- **6** formalizable: von Mangoldt support stabilization, the `L¹`→operator contraction/trace
  duality bridge, and the section-3 triangular-array separation counterexample.
- **8**/**9** are one-variable complex analysis plus Hardy-space multiplier algebra.
- **12** needs the `L²(ℝ_+^*, d*u)` shell noncompactness of `(1−P_λ)D_p P_λ`.
- **13**/**15** rest on the corpus's Sonin Calkin layer; the prime-coherence step is elementary.
- **16** is finite linear algebra (Haynsworth inertia additivity, CRT root avoidance).
- **17** needs Connes–Moscovici prolate spectral theory (uniqueness of the cutoff-commuting
  self-adjoint extension) — the deepest literature dependency in the folder.

## Card 1: the analytic core, worked out on paper (2026-08-22)

The card's `λ > 0` "transfer-matrix ellipticity" plan and its `λ = 0` frozen-discriminant plan are
both unusable: at a **double** characteristic root the frozen roots do not approximate the true
solution ratios to order `1/n`.  The correct reduction is:

1. **Symmetrization.**  With `γ_{n+1} = γ_{n-1} ρ_{n-1}/ρ_n` (so `γ_n ≍ 1/n`), `u_n = γ_n v_n`
   turns `ρ_{n-1}u_{n-1} + (q_n − z)u_n + ρ_n u_{n+1} = 0` into the unimodular form
   `v_{n+1} − 2v_n + v_{n−1} + p_n v_n = 0`, with

   `p_n = 4πλ²/n + O(n⁻²)`   (even and odd blocks alike; `z` only enters at order `n⁻²`).

2. **λ > 0.**  This is the discrete Bessel/Laguerre oscillatory regime.  Sharp answer:
   `|v_n| ≍ n^{1/4}`, so `|u_n| ≍ n^{−3/4}` and `∑|u_n|² < ∞`: limit circle.
   (The card's `|u_n| ≍ C/n` is wrong — it omits the Liouville–Green amplitude factor
   `p^{−1/4}` — but the conclusion is unaffected.)

3. **λ = 0.**  `p_n = κ/n² + O(n⁻³)` and the indicial equation is `s² + s + (3/4 − z)/4 = 0`,
   i.e. `s = (−1 ± √(1/4 + z))/2`; at `z = 0` the exponents are `−1/4, −3/4`.  The dominant
   solution is not `ℓ²`, so the block is limit point.  (Sum of exponents is `−1`, forced by the
   exact discrete Wronskian `ρ_n(u_{n+1}v_n − u_n v_{n+1}) = const`; the card's `−2` is wrong.)

### The Lean-friendly proof of step 2 (discrete Liouville–Green, elementary)

With `d_n = v_{n+1} − v_n`, `M_n = v_n v_{n+1}`, the *exact* identities are

- `E_n := d_n² + p_n M_n`,   `E_n − E_{n−1} = (p_n − p_{n−1}) M_{n−1}`;
- `Δ⁺(v_n d_{n−1}) = d_n² − p_n v_n²`   (the discrete `(v v')' = v'² − p v²`);
- `d_{n−1}² = E_{n−1} − p_{n−1} M_{n−1}`, hence
  `M_{n−1} = [E_{n−1} + (p_{n−1}M_{n−1} − d_{n−1}²)]/(2 p_{n−1})`.

Put `F_n = E_n / √(p_n)`.  The first bracket cancels the `1/√p` drift to relative order
`(Δp/p)² = O(n⁻²)`; the second bracket is the oscillating part, equal to a discrete derivative up
to `p_n v_n d_n = O(n⁻¹)`.  Abel summation of that derivative against
`Δp_n / p_n^{3/2} = O(n^{−1/2})`, whose own difference is `O(n^{−3/2})`, gives

`F_N ≤ F_{N₀} + ε(N₀)·sup F + C ∑_{n>N₀} n^{−3/2} sup F`,

so `F` is bounded by discrete Gronwall for `N₀` large.  Then
`v_n² ≤ E_n / p_n ≲ p_n^{−1/2} ≍ n^{1/2}` — exactly the sharp `n^{1/4}` amplitude.

This is the continuum computation `(E/√p)' = p^{−3/2} p' (p v² − v'²)/2 = −p^{−3/2}p'(vv')'/2`
transcribed to the lattice; no Bessel asymptotics, no Levinson/Harris–Lutz machinery, and no
literature input are needed.  Planned module: `HTGeometry/DiscreteLiouvilleGreen.lean`.


## Corpus findings that change the remaining plan (2026-08-22)

- **Card 15's prime-coherence theorem is already Lean-closed**:
  `RHTower.primePairDifferenceEnergyBounded_iff_constant` (`XiPrimeSeamPairEnergy.lean`), together
  with the variance/Plücker identities in `XiPrimeSeamPairVariance.lean`.  What is left of card 15
  is only the **tensor-square** Calkin lower bound `(1)`/`(2)`.
- Mathlib **does** carry the Hilbert tensor product inner product (`TensorProduct.inner_tmul`,
  and a `NormedAddCommGroup` instance on `H ⊗[ℂ] H`), but **not** an `InnerProductSpace` instance
  on `UniformSpace.Completion (H ⊗[ℂ] H)`.  Planned workaround, faithful and completion-free:
  state the estimate against every operator in the **norm closure of the finite-rank operators**
  on `H ⊗[ℂ] H` (which is exactly the compacts of the completion), prove it for finite rank via
  weak nullity, and extend by a `3ε` argument.
- **Card 13** is nearly closed by corpus work: `SoninPrimeGramCompression.lean` has
  `norm_finiteMatrixBilinear_le_norm_finitePrimeEvenDilationGram_sub_compact` and
  `sqrt_half_finiteWeightedDifferenceEnergy_le_norm_primeGram_sub_compact`, i.e. `(8b)`–`(8e)`.
  Its own remaining content is the algebraic exterior factorization `(3)`, which needs only
  `TensorProduct.map` on the algebraic tensor product.
- **Card 16** needs matrix inertia theory that the corpus does *not* have: Sylvester's law of
  inertia and Haynsworth additivity (only `rankOneRepair_inertia_*` exists).  That is the single
  blocking build for it.
- **Card 12** part A is already Lean (`RHTower/CutoffCochain.lean`); part B needs the shell
  noncompactness of `(1−P_λ)D_p P_λ` on `L²(ℝ_+^*, d*u)`.  The corpus has the additive-model
  analogue `RHTower.evenCentralSoninDilationCorner_not_isCompactOperator`.

## Card 15 / card 13 `(4)`–`(5)`: what the Hilbert tensor square needs (2026-08-22)

Mathlib **does** provide, in `Mathlib/Analysis/InnerProductSpace/TensorProduct.lean` and
`Mathlib/Analysis/InnerProductSpace/Completion.lean`:

- `TensorProduct.instInner`, `TensorProduct.inner_tmul`, `TensorProduct.norm_tmul`,
  `TensorProduct.instNormedAddCommGroup`, `TensorProduct.instInnerProductSpace`
  (so `H ⊗[ℂ] H` is a *pre*-Hilbert space);
- `UniformSpace.Completion.innerProductSpace` — the completion of a **seminormed** inner product
  space is an inner product space (note: it is found only with `SeminormedAddCommGroup` in scope and
  with `Mathlib.Analysis.InnerProductSpace.Completion` imported);
- `ContinuousLinearMap.completion` (`Mathlib/Topology/Algebra/LinearMapCompletion.lean`) to lift a
  bounded operator to the completion.

**CORRECTION (same day): there is no mathlib gap.**  The same file already provides
`TensorProduct.mapL (f : E →L[𝕜] F) (g : G →L[𝕜] H) : (E ⊗[𝕜] G) →L[𝕜] (F ⊗[𝕜] H)` with
`TensorProduct.norm_mapL_le : ‖mapL f g‖ ≤ ‖f‖ * ‖g‖`, plus `rTensor`/`lTensor`,
`Orthonormal.tmul`, `adjoint_mapL`, and the associativity/commutativity isometries.  (My first
audit only read the first 314 of 748 lines.)

Why the estimate cannot simply be stated on the incomplete `H ⊗[ℂ] H`: the corpus's
`IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null` needs weak nullity against
**every** continuous functional, and on an incomplete inner-product space that does not follow from
weak nullity against the inner products of the space itself.  Working in the completion restores
Riesz and closes the gap.

Planned module: `RHTower/SoninTwoParticlePrimeCoherence.lean` — the shell amplification plus the
estimate, carried out in `UniformSpace.Completion (evenSubspace ⊗[ℂ] evenSubspace)` so that Riesz
is available and `IsCompactOperator` means what the card means.  The bridge that makes this work is
now built: `HTGeometry/HilbertCompletionWeakNull.lean` proves
`HTGeometry.completion_weakly_tendsto_zero` — a bounded sequence that is weakly null against the
dense pre-Hilbert space is weakly null against **every** continuous functional on the completion,
which is exactly the hypothesis shape the compact-operator criteria need.

## State after the 2026-08-22 session — 6 promoted, 11 remain

Promoted: **2** (boolean-sonin-full-history), **3** (connes-semilocal-finite-part),
**4** (finite-euler-connection-cauchy-phase-chambers), **6** (rectangular-semilocal-observer),
**8** (semilocal-dual-pair-euler-connection), **10** (semilocal-jacobi-linear-growth).

New modules built this session (all wired, all `#print axioms`-clean, `formal lint passed`):

| module | what it owns |
|---|---|
| `HTGeometry/MonicOrthoExtremalComparison.lean` | monic-norm extremality, uniqueness, span-by-degree, identification with any orthogonal family, and the `K`/`K²` comparison of monic norms and Jacobi `β`'s |
| `HTGeometry/BooleanSoninFullHistory.lean` | reciprocal contraction sections, the full binary-history energy law, the adjoint-mate fracture, the `Λ`-perturbed curvature class, and off-unitary models |
| `HTGeometry/QuantizedDifferentialCocycle.lean` | `δ(xy)=δ(x)y+xδ(y)`, the Leibniz cocycle `ω(UV)=V⁻¹ω(U)V+ω(V)`, and cyclic-trace additivity over an ordered factorization |
| `HTGeometry/BilinearExteriorPairFactorization.lean` | `∑∑(aᵢ−aⱼ)•B(Cᵢ)(Dⱼ) = B(∑aᵢCᵢ)(∑Dⱼ) − B(∑Cᵢ)(∑aⱼDⱼ)`, with tensor and algebra specializations |
| `RHTower/SemilocalJacobiLinearGrowthProlateDomainGate.lean` | the whole of card 10 |
| `RHTower/FiniteEulerConnectionCauchyPhaseChambers.lean` | the whole of card 4 |
| `RHTower/ConnesSemilocalOrbitalSourceClass.lean` | card 3's response-quotient nonvanishing |
| `RHTower/RectangularSemilocalObserverTailSeparation.lean` | the whole of card 6 |
| `RHTower/SoninPrimeSeamExteriorFactorization.lean` | card 13's `(3)`, `(8a)`, `(8g)` |
| `RHTower/SemilocalDualPairEulerConnection.lean` | the whole of card 8's scalar/differential layer |

### Exact remaining blocker per card

| card | blocker |
|---|---|
| 1 archimedean-prolate-jacobi-limit-circle | the discrete Liouville–Green theorem sketched above, then the deficiency-index transfer |
| 5 prime-tail-copoisson-essential-boundary | PNT with classical error term + Mellin/`E₁`; the heaviest analytic card |
| 7 route-b-semilocal-sonin-interim-verdict | a synthesis card: it becomes formalized once its cited bullets are (several already are) |
| 9 (CLOSED 2026-08-22) semilocal-euler-kernel-chart | Hardy spaces `H^±` of a half-plane — absent from mathlib and from the corpus (only Cauchy-kernel Grams exist); plus the Hilbert-space closed-range projection formula `(8)` and its derivative `(9)`–`(11)` |
| 11 sonin-burnol-conductor-cutoff | the Coifman–Rochberg–Weiss/Nehari BMO commutator theorem; the algebraic layer is already Lean (`SoninBurnolConductorReflection`, `…Concrete`) |
| 12 sonin-place-transition-cutoff-dichotomy | part A is Lean (`CutoffCochain`); part B is the shell noncompactness of `(1−P_λ)D_p P_λ`. **Elementary route found**: in the log coordinate the corner carries the normalized indicators of the disjoint intervals `(c − a/2ⁿ, c − a/2ⁿ⁺¹]` to an orthonormal family, so it maps an orthonormal (hence weakly null) sequence to a norm-one sequence |
| 13 (CLOSED 2026-08-22) sonin-prime-seam-exterior-factorization | only card 15's tensor estimate |
| 14 sonin-small-cutoff-ground-row-survival | the semilocal cyclic spaces `H_P`, the number operators, and strong convergence of the Sonin projections |
| 15 (CLOSED 2026-08-22) sonin-two-particle-prime-coherence | the tensor-square Calkin estimate; mathlib supplies everything needed (`TensorProduct.mapL`, `norm_mapL_le`, `UniformSpace.Completion.innerProductSpace`, `ContinuousLinearMap.completion`) — what remains is lifting the corpus shell data to the tensor square |
| 16 squarefree-cutoff-jump-root-avoidance | **STALE**: Sylvester's law of inertia *is* in the corpus — `HTGeometry/HermitianInertia.lean` has `hermPosIndex/hermNegIndex/hermNullIndex`, congruence invariance, the diagonal case and the spectral characterisation. What is missing is Haynsworth additivity (block-diagonal additivity + the Schur congruence) and iterated-tensor inertia |
| 17 transported-prolate-relative-resolvent-corner | Connes–Moscovici prolate spectral theory (uniqueness of the cutoff-commuting self-adjoint extension) and Ramis–Richard-Jung–Thomann order-`1/2` determinants |

## 2026-08-22 (continued): cards 15 and 13 closed

**Card 15 `sonin-two-particle-prime-coherence` → stage 3.**
`RHTower/TensorSquareCalkinLower.lean` (abstract `ShellDatum` + `tensor_calkin_lower`),
`HTGeometry/HilbertCompletionWeakNull.lean` (weak nullity transported to the completion) and
`RHTower/SoninTwoParticlePrimeCoherence.lean` (`soninShellDatum`, `sonin_tensor_calkin_lower`,
`sonin_euler_tensor_calkin_lower`, `soninPrimePairSection`,
`sqrt_primePairDifferenceEnergy_le_norm_soninPrimePairSection_sub_compact`,
`sonin_prime_pair_calkin_bounded_imp_constant`).  Shell parameters are chosen inside the proofs by
`exists_finiteScale_gramSeparatingInteriorShell`, so every statement is unconditional.

Typeclass notes for anyone touching `evenSubspace ⊗[ℂ] evenSubspace`: the module needs
`set_option maxHeartbeats 2000000`, `synthInstance.maxSize 2000`,
`synthInstance.maxHeartbeats 4000000`, plus the three explicit instances
`evenSoninTensorUniformContinuousConstSMul` (a genuine `SMul` diamond between
`TensorProduct.instSMul` and `DistribMulAction.toDistribSMul.toSMul`),
`evenSoninTensorCompletionNormedAddCommGroup` and `evenSoninTensorCompletionNormedSpace`.  The last
two come from the `@[reducible] noncomputable def` helpers in `TensorSquareCalkinLower.lean`;
plain `theorem`s there fail with "type of theorem is not a proposition" and an unmarked `def`
fails with "definition of class type must be marked reducible".

**Card 13 `sonin-prime-seam-exterior-factorization` → stage 3.**
`HTGeometry/HilbertExteriorPairFactorization.lean` (`mapLBilinear`,
`sum_sub_smul_bilinear_finset`, `sum_sub_smul_mapL`) and
`RHTower/SoninPrimeSeamExteriorCalkin.lean` (`evenSoninWeightedSection`,
`evenSoninUniversalSection`, `soninPrimePairSection_eq_exterior`,
`sqrt_primePairDifferenceEnergy_le_norm_exterior_sub_compact`,
`sonin_exterior_calkin_bounded_imp_constant`, `xiSeamExteriorCalkinDistance`,
`re_eq_half_of_xiSeamExteriorCalkinDistance_submass`,
`riemannHypothesis_of_xiSeamExteriorCalkinSubmass`).

Remaining cards: 1, 5, 7, 9, 11, 14, 16, 17.

## Card 9 `semilocal-euler-kernel-chart-differentiability`: build plan (2026-08-22)

The card's Lean content and where it goes.

| Item | Content | Module | State |
|---|---|---|---|
| `(8)` | closed-range projection formula `P = M Q A⁻¹ Q M*`, `A = Q M* M Q + (1−Q)` | `HTGeometry/BoundedBelowRangeProjection.lean` | DONE (`isUnit_rangeProjectionGram`, `rangeProjection_mul_self`, `rangeProjection_isIdempotentElem`, `rangeProjection_isSelfAdjoint`, `range_rangeProjection`, `starProjection_eq_rangeProjection`) |
| analyticity | `t ↦ P_t` operator-norm real analytic | `HTGeometry/RangeProjectionAnalytic.lean` | TODO — `analyticAt_inverse` (mathlib) composed with the polynomial `A_t`; needs the ℝ-linear continuous `adjoint` |
| `(9)`,`(11)` | `P'_0 = (1−Q) X Q + Q X* (1−Q)` at `M_0 = 1` | `HTGeometry/RangeProjectionDeriv.lean` | TODO — product rule + `hasFDerivAt_ring_inverse` |
| `(4)` | `S(u_t) = D_t S(u_∞)`, bounded isomorphism | `HTGeometry/InvariantMultiplierChart.lean` | TODO — purely algebraic: `S(u) = {f ∈ Hp : u f ∈ Hm}`, `D` invertible with `D(Hp) = Hp`, `N` invertible with `N(Hm) = Hm`, `u_t = u N D⁻¹` |
| `(5)` | `|t_p| < √p ⟹ D_t, D_t⁻¹ ∈ H^∞` | same | TODO — Neumann series: `‖cT‖ < 1`, `T` leaves the closed subspace invariant ⟹ `1 − cT` invertible and both it and its inverse preserve the subspace |
| `(10)`,`(12)`--`(15)` | metric tangent is the positive Euler Sonin corner | `RHTower/SemilocalEulerKernelChart.lean` | TODO — in the corpus physical model `M_t = 1 − t p^{−1/2} U_p*` is affine in `t`, so `M_t* M_t` is a quadratic polynomial and `∂_t|_0 = −p^{−1/2}(U_p + U_p^{−1})`; cross-boundary is `centralPositiveEulerCorner_eq_smul` |
| `(16)` | finite Euler combination is Calkin-faithful | `finitePositiveEulerCorners_calkinIndependent` | already in the corpus |
| `(17)`,`(18)` | `ρ_{p,t} B_{p,t} = −p^{z−1/2}`, singular limit of the local Hankel kernel | `RHTower/LocalEulerHankelSingularLimit.lean` | TODO — elementary `sinh` algebra |
| `(19)`,`(23)`,`(24)` | connection source law | `RHTower/SemilocalDualPairEulerConnection` | already done (card 8) |
| cofinite reader rigidity, compact mixed derivatives | | `cofinite-euler-connection-reader-rigidity` (stage 3) | already done |

Unchecked gates `(21)`, finite two-prime compact curvature and prime-seam coherence are open
research problems, not formalization gaps.

## 2026-08-22: card 9 closed

`semilocal-euler-kernel-chart-differentiability` → stage 3.  New modules:

- `HTGeometry/BoundedBelowRangeProjection.lean` — self-adjoint + bounded below ⟹ invertible; the
  Gram operator `A = Q M* M Q + (1−Q)`; the closed-range projection formula `P = M Q A⁻¹ Q M*` and
  its identification with `starProjection` of `M(range Q)`.
- `HTGeometry/RangeProjectionDeriv.lean` — `adjointRealCLM` (the adjoint as a continuous
  **real**-linear map; it is conjugate-linear over ℂ), `hasDerivAt_adjoint`, and
  `P'_0 = (1−Q) X Q + Q X* (1−Q)` at `M_0 = 1`.
- `HTGeometry/RangeProjectionAnalytic.lean` — real analyticity of `t ↦ P_t` through
  `analyticAt_inverse`.
- `HTGeometry/InvariantMultiplierChart.lean` — `multiplierKernel`, the exact chart
  `S(u N D⁻¹) = D S(u)`, and the Neumann lemma `map_one_sub_eq_of_norm_lt_one`.
- `RHTower/HalfLineMultiplierChart.lean` — the Paley--Wiener half-line model
  (`logHalflineLower/Upper`, translation invariance from
  `logHalflineCutoff_mul_logTranslationCLM`), the Euler numerator/denominator multipliers and the
  instantiated chart.
- `RHTower/SemilocalEulerKernelChart.lean` — `M_t = 1 − (t/√p) U_p*` in the actual Sonin model, the
  metric `M_t* M_t`, its tangent, the identification of the cross-boundary with
  `positiveEulerDilationOperator`, analyticity, the projection derivative and the second
  fundamental form.
- `RHTower/LocalEulerHankelSingularLimit.lean` — the division-free identity
  `(1 − e^{L(z+c−1)})·sinh(L(z−c)/2) = −e^{L(z−1/2)}(1 − e^{L(c−z)})·sinh(L(z+c−1)/2)` and the
  degenerate limit `B → −p^{z−1/2}`.

Remaining cards: 1, 5, 7, 11, 14, 16, 17.

## Card 16 `squarefree-cutoff-jump-root-avoidance-inertia`: build plan (2026-08-22)

The corpus already owns Sylvester's law (`HTGeometry/HermitianInertia.lean`:
`hermPosIndex/hermNegIndex/hermNullIndex`, `posIndex_conjugate`, `posIndex_diagonal`,
`posIndex_eq_card_pos_eigenvalues`, `posIndex_add_negIndex_add_nullIndex`).

**DONE** `HTGeometry/HaynsworthInertia.lean`: `fromBlocks_diagonal`, `isUnit_fromBlocks_zero`,
`exists_congr_diagonal`, `posIndex/negIndex/nullIndex_fromBlocks_zero`, `fromBlocks_schur_congr`,
`isHermitian_schurComplement`, `haynsworth_posIndex/negIndex/nullIndex`.

Identification of the card's local matrices (verified against `(CJ8)` by hand):
local space `α p` of size `p`, `e` the delta at `0`, `u` the all-one vector,

- `A_p = e eᴴ`  (the `(SG7)` anchor `p⁻² a aᵀ` with `a = p e`),
- `w = p⁻¹ u − e`, `T_p = e eᴴ − w wᴴ`  (so `T_p = U_p J₀ U_pᴴ` with `U_p = [e, w]`),
- `Δ_p = 2p⁻¹ e eᴴ − p⁻² 1`  (the normalised diagonal `p⁻² diag(D_p)` of `(SG4)`);
  `Δ_p` has inertia `(1, p−1, 0)`, `Δ_p|Z_p = −p⁻²`, and `U_pᴴ Δ_p⁻¹ U_p` is exactly the card's
  `G_p = (2p−1)⁻¹ [[p², −p(p−1)], [−p(p−1), −p(p−1)]]`.

Remaining layers:

1. `HTGeometry/TensorFamilyInertia.lean` — `tensorFamily M x y = ∏ i, M i (x i) (y i)` for
   rectangular families, `tensorFamily_mul` (via `Finset.prod_univ_sum`), `_conjTranspose`,
   `_diagonal`, `_one`, `isUnit_tensorFamily`, Hermitian-ness, and
   `hermPosIndex (tensorFamily M) = card {x | 0 < ∏ i, μ i (x i)}`.
2. Isometric rectangular congruence: `Cᴴ C = 1 ⟹ In (C X Cᴴ) = In X` on the pos/neg indices
   (the ambient nullity is the trichotomy complement).  This replaces all the `Q − q` bookkeeping:
   with `C_p = 1` for `p ∈ U` and `C_p = ` the `p × 1` column `e` for `p ∉ U`,
   `E_U − R_U = C (D_E − D_R) Cᴴ`.
3. Block-swap congruence `fromBlocks 0 1 1 0`, so Haynsworth can be applied at either corner.
4. `In(−J)` (J is diagonal with `±1` entries), `In(−D_E)` (tensor inertia of the local `(1,p−1,0)`),
   and the balanced nonsingular `In(−(J−G)) = (2^{r−1}, 2^{r−1}, 0)`.
   Balance: `L_p` with `L_pᵀ J₀ L_p = −J₀`, `L_pᵀ G_p L_p = −G_p`, acting on one factor.
   Nonsingularity: `J − G = J(1 − JG)`, `JG = tensorFamily (J₀G_p)`; each `M_p = J₀G_p` is a real
   `2×2` with `tr = p`, `det = p²(p−1)/(2p−1) > 1` and negative discriminant, so with
   `N_p = M_p − (p/2)1`, `ω_p² = det − p²/4 > 0` and `P_p = 1 + N_pᵀN_p/ω_p²` one gets
   `M_pᵀ P_p M_p = det(M_p) · P_p` with `P_p` positive definite; then `P = tensorFamily P_p` is
   positive definite and `(tensorFamily M)ᵀ P (tensorFamily M) = (∏ det) P` with `∏ det > 1`,
   so `1` is not an eigenvalue and `1 − JG` is invertible.
5. Assembly of `(CJ1)`--`(CJ6)`, `(CJ16)`, `(CJ17)`.

### Card 16 infrastructure landed (2026-08-22)

All four general inertia modules build clean and are wired into `HTGeometry.lean`:

- `HTGeometry/HaynsworthInertia.lean` — block-diagonal additivity of pos/neg/null, the Schur
  congruence `Sᴴ diag(A, C − Bᴴ A⁻¹ B) S = [[A,B],[Bᴴ,C]]` with `S = [[1, A⁻¹B],[0,1]]`, and
  `haynsworth_posIndex/negIndex/nullIndex`.
- `HTGeometry/IsometricCongruenceInertia.lean` — `hermQuad_rect_conjugate`,
  `mulVecLin_injective_of_isometry`, `posIndex/negIndex_isometric_congr` for `Cᴴ C = 1`.
- `HTGeometry/TensorFamilyInertia.lean` — `tensorFamily`, `_mul`, `_conjTranspose`, `_one`,
  `_diagonal`, `isUnit_tensorFamily`, `isHermitian_tensorFamily`,
  `posIndex/negIndex_tensorFamily` (counting products of local eigenvalues).
- `HTGeometry/InertiaScalingSwap.lean` — `posIndex/negIndex_smul_pos`, `equivMatrix` and
  `posIndex/negIndex_submatrix_equiv` (reindexing by a bijection, proved through the isometric
  congruence), `posIndex/negIndex_swapBlocks`, `isPosDefOn_top_of_posIndex_eq_card`.

Local-block plan (dimension `k+2`, scale `P = k+2`, so `κ = k`):
`localAnchorBlock`, `localOccupancyBlock` are **diagonal** (`e eᴴ = diagonal (1,0,…)`), so their
inertia is a direct count; `localFrame = [e, w]`, `w = P⁻¹ u − e`, `binaryJ = diag(1,−1)` and
`localDensityBlock = frame * J * frameᴴ`.  The balance matrix may be taken **unscaled**,
`L = [[−1, 2m],[−2m, 1]]` with `m = P − 1`, giving `Lᴴ J L = −(4m²−1) J` and
`Lᴴ G L = −(4m²−1) G`; `posIndex_smul_pos` absorbs the positive factor, so no square root is
needed.  Nonsingularity of `1 − JG` uses only `N² = −ω² 1` for `N = M − (P/2)1`:
then `P₀ = 1 + NᵀN/ω²` is positive definite, `NᵀP₀ + P₀N = 0`, and `MᵀP₀M = det(M)·P₀`.

### Card 16 progress: local blocks (2026-08-22)

`formal/GaloisForLFunctions/RHTower/SquarefreeCutoffLocalBlocks.lean` builds clean and now holds
`localScale` (= `k+2`), `localAnchorBlock`, `localOccupancyBlock` (both diagonal), `localColumn`
(with `Cᴴ C = 1` and `C Cᴴ = A`), `localFrame`, `binaryJ`, `localDensityBlock = U J Uᴴ`,
`frameRowZero/frameRowOther`, `frameGram_eq` (the general frame Gram against a diagonal weight),
`localOccupancyInvDiag`, `inv_localOccupancyBlock`, `isUnit_localOccupancyBlock` and the explicit

`localGram_eq : localGram k = (2P−1)⁻¹ • !![P², −P(P−1); −P(P−1), −P(P−1)]`.

Traps met: `field_simp` will not clear `(−1 + P*2)⁻¹` even with the matching `≠ 0` hypothesis in
context — finish with `ring_nf` then `all_goals linear_combination (P − 1) * hDinv` where
`hDinv : (−1 + P*2) * (−1 + P*2)⁻¹ = 1`.  `isUnit_of_mul_eq_one` does not apply to matrices
(noncommutative): build the unit directly and get the left inverse from `mul_eq_one_comm`.

Still to write for card 16: `M = J₀ G` with `tr M = P`, `det M = P²(P−1)/(2P−1)`;
`N = M − (P/2)1` with `N² = −ω² 1`, `ω² = P²(2P−3)/(4(2P−1)) > 0`; the metric `P₀ = 1 + ω⁻² NᴴN`
with `NᴴP₀ + P₀N = 0` and `MᴴP₀M = det(M)·P₀`; the unscaled balance `L = !![−1, 2(P−1); −2(P−1), 1]`
with `Lᴴ J₀ L = −(4(P−1)²−1) J₀` and `Lᴴ G L = −(4(P−1)²−1) G`; then the global assembly.

### Card 16: local blocks module COMPLETE (2026-08-22)

`formal/GaloisForLFunctions/RHTower/SquarefreeCutoffLocalBlocks.lean` builds and is wired.
Contents: `localScale`/`realScale`, `localAnchorBlock`, `localOccupancyBlock`, `localColumn`
(+`Cᴴ C = 1`, `C Cᴴ = A`), `localFrame`, `binaryJ` (+`binaryJ_eq : binaryJ = !![1,0;0,-1]`,
`binaryJ_mul_self`, `isUnit_binaryJ`, `isHermitian_binaryJ`), `localDensityBlock = U J Uᴴ`,
`frameGram_eq`, `localOccupancyInvDiag`, `inv_localOccupancyBlock`, `isUnit_localOccupancyBlock`,
`localGram_eq` / `localGramRaw` / `localGram_eq_smul`, `localPencilRaw`(`= J₀ G̃`),
`localRotationRaw` (`= !![P/2, −P(P−1); P(P−1), −P/2]`), `localOmegaSqRaw` (>0),
`localRotationRaw_sq` (`Ñ² = −ω̃²`), `localMetric` (`= ω̃²·1 + ÑᴴÑ`, positive definite,
`posIndex = 2`, explicit form `!![2b², −P²(P−1); −P²(P−1), 2b²]`), `localMetricScalar`
(`= P²(2P−1)(P−1)`), `localPencilRaw_metric` (`M̃ᴴ P₀ M̃ = d̃ • P₀`),
`two_realScale_sub_one_lt_metricScalar`, and `localBalance` / `localBalanceFactor` with
`localBalance_binaryJ` and `localBalance_gramRaw`.

Also added to `HTGeometry/IsometricCongruenceInertia.lean`: `hermQuad_add`, `hermQuad_one`,
`hermQuad_one_pos`, `hermQuad_conjTranspose_mul_self_nonneg`, `isPosDefOn_top_smul_one_add_gram`.

**Remaining: the global assembly** `RHTower/SquarefreeCutoffJumpInertia.lean`, over a nonempty
`Fintype ι` with local dimensions `m i + 2`:

1. `Δ := tensorFamily (localOccupancyBlock ∘ m)`, `T := tensorFamily (localDensityBlock ∘ m)`,
   `V := tensorFamily (localFrame ∘ m)`, `J := tensorFamily (fun _ => binaryJ)`; `T = V J Vᴴ`.
2. Haynsworth at the `−Δ` corner of `fromBlocks (−Δ) V Vᴴ (−J)` and, after `posIndex_swapBlocks`,
   at the `−J` corner, using `(−J)⁻¹ = −J`; gives
   `In(−J) + In(T − Δ) = In(−Δ) + In(−(J − G))`, `G = Vᴴ Δ⁻¹ V = tensorFamily (localGram ∘ m)`.
3. `In(−J)`: `J` is diagonal with `±1` entries, so `(2^{r−1}, 2^{r−1}, 0)`.
4. Balance: `L := tensorFamily (fun i => if i = i₀ then localBalance (m i) else 1)` gives
   `Lᴴ (J − G) L = (−f) • (J − G)` with `f = localBalanceFactor (m i₀) > 0`, so
   `pos(J − G) = neg(J − G)` by `posIndex_smul_pos`.
5. Nonsingularity: `J − G = J (1 − JG)`, `JG = c⁻¹ • M̃` with `M̃ = tensorFamily (localPencilRaw ∘ m)`
   and `c = ∏ (2P_i − 1)`.  If `(1 − JG) x = 0` then `M̃ x = c x`, and with
   `P₀ = tensorFamily (localMetric ∘ m)` positive definite and `M̃ᴴ P₀ M̃ = d • P₀`,
   `d = ∏ localMetricScalar (m i)`, one gets `(d − c²) hermQuad P₀ x = 0`; `d/c = ∏ P²(P−1) > c`
   by `two_realScale_sub_one_lt_metricScalar`, so `x = 0`; then
   `Matrix.exists_mulVec_eq_zero_iff` gives `det ≠ 0`.
6. `In(Δ)` by `posIndex_tensorFamily` plus the sign-count identity
   `∑_x ∏_i s_i(x_i) = ∏_i ∑_a s_i(a)` (`Finset.prod_univ_sum`), giving
   `pos − neg = ∏(1 − (m_i+1)) = ∏(−m_i) = (−1)^r κ` and `pos + neg = q`.
7. Padding: for any unit vector `v : ρ → ℂ`, `C ((x,s), y) = 1 x y * v s` has `Cᴴ C = 1`, so
   `posIndex_isometric_congr` transfers the inertia and adds `card − q` to the null index.
   This is exactly `(CJ2)`'s `Q − q`.

## 2026-08-23: card 16 closed

`squarefree-cutoff-jump-root-avoidance-inertia` → stage 3.  New modules (all wired, all clean under
`#print axioms`):

- `HTGeometry/HaynsworthInertia.lean` — block-diagonal additivity + **Haynsworth inertia
  additivity** (a genuine mathlib gap).
- `HTGeometry/IsometricCongruenceInertia.lean` — rectangular isometric congruence and the
  `hermQuad` positivity toolkit.
- `HTGeometry/InertiaScalingSwap.lean` — positive rescaling, reindexing by a bijection, block
  swap, `isPosDefOn_top_of_posIndex_eq_card`, `nullIndex_eq_zero_of_isUnit`, `nullIndex_neg`.
- `HTGeometry/TensorFamilyInertia.lean` — `tensorFamily`/`tensorVec` algebra, tensor inertia,
  trace, and the signed-count identity.
- `RHTower/SquarefreeCutoffLocalBlocks.lean` — the three local blocks, the exact local Gram,
  the balance matrix, the pencil/rotation/metric, the local traces and the local root avoidance.
- `RHTower/SquarefreeCutoffJumpInertia.lean` — the global assembly: `(CJ1)`–`(CJ5)`, `(CJ16)`.

Traps recorded: `field_simp` in this toolchain will **not** clear an inverse whose denominator is a
polynomial in an atom even with the matching `≠ 0` hypothesis present; finish with
`ring_nf` + `linear_combination c * (d * d⁻¹ = 1)`.  A rectangular matrix product whose factor has
an **under-determined implicit type argument** silently picks `CStarMatrix`'s default `HMul`
instance and every later `rw` fails; pin the argument (`crossingJ (ι := ι)`) — type ascriptions and
`attribute [-instance]` do not help.

Remaining cards: 1, 5, 7, 11, 14, 17.

### Card 14 survey (2026-08-23)

`sonin-small-cutoff-ground-row-survival` needs, beyond what exists:

- the **scalar** side is already in the corpus: `semilocalFinitePrimeActualEvenJacobiMoment`,
  `semilocalFinitePrimeEvenJacobiMoment_signed_pos`, `semilocalFinitePrimeGradingGroundDefect`,
  `semilocalFinitePrimeActualGradingGroundDefect(_signed_pos, _one_eq_explicitResidue)` in
  `SoninSemilocalAllEvenJacobiResidue.lean` and `SoninSemilocalJacobiResidueCorollaries.lean`;
  the rank-one trace-class machinery is in `SoninSemilocalGradingNoGo.lean`
  (`isTraceClass_rankOne_lp`, `semilocalOnePrimeGroundRowOperator_isTraceClass`).
- **missing**: the semilocal *operator* framework — `H_P`, the bounded identity `J_P`, the number
  operators `N_P`, `N_∞`, and the semilocal Sonin projections `Q_{λ,P}`.  Only scalar moments and
  the one-prime `α`-smoothed row exist.  `T_P = −P_0^P J_P N_∞(N_∞+1)⁻¹` needs `J_P^* p_0^P ∈ ℓ²`,
  i.e. `∑_k |⟨p_0^P, J_P p_{2k}^∞⟩|² < ∞` — automatic once `J_P` is a bounded operator, but the
  corpus has no such `J_P`.
- `(5)` `Q_{λ,∞} → 1` strongly as `λ ↓ 0` reduces to a clean reusable lemma to build:
  **two-projection deficiency bound** — if `P, R` are orthogonal projections with `‖P R‖ ≤ c < 1`
  and `Q` projects onto `ker P ∩ ker R`, then `‖(1−Q)v‖² ≤ (‖P v‖² + ‖R v‖²)/(1−c)`.
  Proof: for `w ∈ (ker P ∩ ker R)ᗮ` approximate `w` by `a + r`; `‖w‖² = ⟨P w, a⟩ + ⟨R w, r⟩`,
  `P w = P v`, `R w = R v`, and `‖a‖² + ‖r‖² ≤ ‖a + r‖²/(1−c)`.  The corpus already owns
  `centralSoninProjection = soninIntersectionProjection (physical) (fourier)` and
  `isCompactOperator_centralFourierPhysicalBlock`, so `‖A_λ R_λ‖ → 0` is within reach.

### Card 14 brick landed (2026-08-23)

`formal/GaloisForLFunctions/HTGeometry/TwoProjectionDeficiency.lean` (wired, axiom-clean):

- `norm_sq_add_le_of_angle` — `(1−c)(‖a‖² + ‖r‖²) ≤ ‖a+r‖²` from the angle bound;
- `two_cauchy_schwarz`;
- `norm_sq_le_of_mem_closure` — the **Friedrichs angle deficiency bound**: for `w` in the closure
  of `U ⊔ V`, `‖w‖² ≤ (‖P_U w‖² + ‖P_V w‖²)/(1−c)`;
- `norm_sub_intersectionProjection_sq_le` — the form card 14 `(5)` needs:
  `‖v − P_{(U⊔V)ᗮ} v‖² ≤ (‖P_U v‖² + ‖P_V v‖²)/(1−c)`;
- `angle_of_norm_starProjection_mul_le` — the angle hypothesis from `‖P_U P_V‖ ≤ c`.

With `U = physicalForbidden`, `V = fourierForbidden` this gives `Q_{λ,∞} v → v` as soon as
`‖A_λ v‖, ‖R_λ v‖ → 0` and `‖A_λ R_λ‖ → 0`; the corpus already owns
`centralSoninProjection = soninIntersectionProjection …` and
`isCompactOperator_centralFourierPhysicalBlock`.

**Still missing for card 14**: the semilocal operator framework `H_P`, `J_P`, `N_P`, `Q_{λ,P}`
(the corpus has only scalar moments).  That is the same framework cards 7 and 17 need.

## Card 1: discrete Liouville–Green, layer 1 landed (2026-08-23)

`formal/GaloisForLFunctions/HTGeometry/DiscreteLiouvilleGreen.lean` (wired, axiom-clean) now has
the whole *exact* algebra of the argument, for the unimodular recurrence
`IsLGSolution p v : ∀ n, lgDiff v (n+1) − lgDiff v n = −p (n+1) · v (n+1)`:

- `lgDiff`, `lgProd`, `lgEnergy p v n = lgDiff v n ² + p n · lgProd v n`;
- `lgEnergy_succ_sub` — the exact drift `E (n+1) − E n = (p (n+1) − p n) · lgProd v n`;
- `lgVirial`, `lgVirialTerm`, `lgVirialPrimitive`, `lgVirialTerm_succ` — the virial expression
  `d² − p v²` is the exact discrete derivative of `v (n+1) · lgDiff v n`;
- `lgEnergy_nonneg` (for `p n ≤ 4`), `sq_le_two_mul_lgEnergy_div` (`p v² ≤ 2E` for `p ≤ 2`),
  `sq_lgDiff_le` (`d² ≤ 2E` for `p ≤ 2`);
- `lgDrift p n = (p n − p (n+1))/(p n √(p (n+1)))`, `lgWeightRatio`, `lgRatioDefect`,
  `lgNormalizedEnergy p v n = E n / √(p n)`;
- `lg_increment_algebra` and `lgNormalizedEnergy_succ_sub` — the **exact** increment
  `F (n+1) − F n = lgDrift p n · (d n ² − lgWeightRatio p n · E n)`;
- `lgNormalizedEnergy_succ_sub_split` — the three-term split
  `F (n+1) − F n = lgDrift·lgVirialTerm/2 − lgDrift·(p v d)/2 + lgDrift·lgRatioDefect·E`.

**Remaining for the discrete Liouville–Green theorem (layer 2):**

1. size bounds `|lgVirialPrimitive v n| ≤ 3 · F n` and `|p n v n · lgDiff v n| ≤ 2 p n · F n`
   (from `sq_le_two_mul_lgEnergy_div` and `sq_lgDiff_le` plus Cauchy–Schwarz);
2. `|lgRatioDefect p n| = |p n − p (n+1)| / (2 (√(p n)+√(p (n+1)))²)`;
3. discrete Abel summation (`Finset.sum_range_by_parts`) of `∑ lgDrift p (n+1)/2 · Δ P` against
   `Δ (lgDrift)`, which for `p n ≍ c/n` is `O(n^{-3/2})` and summable;
4. the Gronwall bootstrap `sup_{n≤N} F ≤ 2 F_{N₀}` once the tail sums are `< 1/2`;
5. conclusion `v n ² ≤ 2 F n / √(p n)`, i.e. the amplitude `p^{-1/4}`.

**Then card 1 proper:**

6. symmetrization `u n = γ n · v n` with `γ (n+1) = γ (n−1) ρ (n−1)/ρ n`, turning the prolate
   Jacobi recurrence into `IsLGSolution` with `p n = 4πλ²/n + O(n⁻²)` (even and odd blocks alike);
7. explicit expansions of `ρ_n^±` and `q_n^±` with real (not `O`) error bounds;
8. λ > 0: `∑ |u n|² < ∞` for **every** solution ⟹ `jacobiDeficiency ≠ ⊥` ⟹ indices `(1,1)`
   via the corpus's `jacobi_deficiency_indices`;
9. λ = 0: indicial exponents `−1/4, −3/4` (the card's `−1 ± √13/4` is **wrong**: the exact
   discrete Wronskian forces the exponent sum `−1`).  Limit point needs, in addition, the classical
   "indeterminate ⟹ ℓ² for every `z`" lemma, since the deficiency space carries the `n = 0`
   boundary row.  That lemma is the one genuinely missing classical input for card 1.

## Card 1 — corrected mathematics and the four-module plan (session continuation)

The card's own "Lean route" section contains two errors that must NOT be formalised:

* `|u_n| ≍ C/n` for `λ>0` is **wrong**.  The frozen transfer matrices are asymptotically
  parabolic (discriminant `→0`), so the diagonalising basis degenerates like `n^{1/4}` and the
  card's "uniformly bounded condition number" (its item 2) is false.  The exact Wronskian
  `ρ_n(u_nw_{n+1}-u_{n+1}w_n) = const` forces the two amplitude exponents to sum to `−1`; with a
  conjugate pair this gives `|u_n| ≍ n^{-3/4}`.  Still `ℓ²`, so the limit-circle conclusion stands.
* The `λ=0` discriminant `13/(4n²)` and exponents `−1±√13/4` are **wrong** (they violate the same
  Wronskian identity).  The correct statement is exponent sum `−1`.

Correct normal form.  Writing the recurrence as a discrete Sturm–Liouville equation
`Δ(ρ_{n-1} Δu_{n-1}) + Q_n u_n = 0` with `Q_n = ρ_n + ρ_{n-1} + q_n − z` gives
`Q_n = 16πλ²n + O(1)`, `ρ_n = 4n² + O(n)`.  Liouville–Green amplitude `(ρQ)^{-1/4} ≍ n^{-3/4}`
for `λ>0`; for `λ=0` the potential is `Q_n = O(1)` and the solutions are `u_n → const` (dominant,
not `ℓ²`) and `u_n ≍ c/n` (recessive, `ℓ²`).

The one-step gauge `u_n = g_n v_n` with `g_n g_{n+1} ρ_n = 1` (equivalently `g_{n+1}ρ_n =
g_{n-1}ρ_{n-1}`) is **not usable**: the recursion `h_{n+1}h_n = ρ_{n+1}/ρ_n` for `h_n = g_n²ρ_n`
has a marginal `(-1)^n` mode which no explicit initial value kills.  So the Liouville–Green engine
must be built directly in Sturm–Liouville form.

### Module plan

1. `RHTower/JacobiWeylAlternative.lean` — the Weyl alternative, elementary and reusable.
   Core: the cross-Wronskian `X n = a n (f(n+1) g n − f n g(n+1))` for `f` a solution at `z` and
   `g` a solution at `ζ` obeys the exact increment law `X (n+1) = X n + (z−ζ) f(n+1) g(n+1)`.
   * **P1** (transfer): a fundamental system at `z₀` that is `ℓ²` forces every solution at every
     `z` to be `ℓ²`.  Cramer gives `u_n = A_nφ_n + B_nψ_n` with `A,B` built from cross-Wronskians;
     the increment law plus a discrete Gronwall product bound closes it.
   * **P2** (rigidity): a single nonzero `ℓ²` solution at non-real `z` **satisfying row 0** forces
     every solution at that `z` to be `ℓ²`.  Here `X n = (z−z̄)∑_{k≤n}|u_k|²` is bounded below by
     `2|Im z||u_0|² > 0`, and Cramer expresses any `w_n` as `(u_n V_n − ū_n W)/X_n`.
   Consequences: limit circle ⟸ two `ℓ²` solutions at one `z₀`;
   `jacobiDeficiency a b z = ⊥` ⟸ no two independent `ℓ²` solutions at `z`.
2. `λ=0` non-`ℓ²`: with `|Q_n| ≤ C` and `ρ_n ≥ c n²`, two independent `ℓ²` solutions are
   impossible.  Proof: `|D^u_N| ≤ |D^u_M| + C√N ε_M` with `D^u_n = ρ_nΔu_n` and
   `ε_M² = ∑_{n>M}|u_n|²`; hence `u_N → u_∞ = 0` with `|u_N| ≲ (|D^u_M| + C√N ε_M)/N`; the
   Wronskian `u_N D^w_N − w_N D^u_N = 1` then gives `1 ≲ 2C²ε_Mε'_M + O(N^{-1/2}) → 0`.
   Runs directly at `z = i`, so P1 is not needed for the `λ=0` half.
3. `HTGeometry/DiscreteSturmLiouvilleGreen.lean` — the variable-`ρ` Liouville–Green engine.
   `D_n = ρ_nΔu_n`, `W_n = ρ_nQ_n`, `E_n = D_n² + W_{n+1}u_nu_{n+1}`,
   `E_{n+1} − E_n = u_{n+1}u_{n+2}ΔW_{n+1} + Q_{n+1}Δρ_n·u_{n+1}Δu_n`, `F_n = E_n/√(W_n)`.
   Same architecture as `HTGeometry/DiscreteLiouvilleGreen.lean` (already complete for `ρ≡1`):
   virial primitive, one Abel summation, Gronwall bootstrap; the extra `QΔρ uΔu` term is
   pointwise `O(n^{-3/2})` relative and needs no Abel step.
4. Explicit prolate coefficients `ρ_n^±, q_n^±` with real error bounds, discharging the engine's
   hypotheses, and assembly against `jacobiDeficiency`.

### Layer 1 complete: `HTGeometry/DiscreteLiouvilleGreen.lean` (`ρ ≡ 1`)

Now closed end to end: `lg_abel_sum`, `lg_sum_telescope`, `lgEnergy_eq_normalized`,
`abs_mul_lgDiff_le`, `abs_weighted_mul_lgDiff_le`, `abs_lgVirialPrimitive_le`,
`lg_increment_tail_bound`, `lgControl`, `lg_window_estimate`,
`lgNormalizedEnergy_le_of_control` (the bootstrap `F ≤ 2·max(F_{N₀}, F_{N₀+1})`), and
`sq_le_of_lgControl` (`v_m² ≤ 4C/√(p_m)`, the amplitude `p^{-1/4}`).

### Card 1 modules 1–3 complete

* `HTGeometry/JacobiWeylAlternative.lean` — `IsJacobiRec`, `crossWronskian`, `crossWronskian_succ`
  (the increment law), `crossWronskian_const`, `crossWronskian_eq_zero_of_const`,
  `crossWronskian_cramer`, `gronwall_exp_bound`, `summable_sq_of_gronwall`,
  **`summable_sq_of_fundamental`** (P1, Weyl transfer), `IsJacobiRec.conj`,
  `crossWronskian_self_conj`, **`summable_sq_of_boundary_solution`** (P2, Weyl rigidity).
* `HTGeometry/JacobiLimitPointBoundedPotential.lean` — `slFlux`, `slPotential`, `slFlux_succ_sub`,
  telescoping tail estimates (`sum_Ico_inv_sq_le`, `sum_Ico_sqrt_div_sq_le`),
  `sum_range_le_sqrt_mul` (Cauchy–Schwarz), `norm_slFlux_le` (flux grows at most like `√n` times
  the `ℓ²` tail), `norm_le_tail_decay`, `le_of_le_add_div_sqrt`, `crossWronskian_eq_flux`, and
  **`crossWronskian_eq_zero_of_both_summable`** — the `λ=0` half: with `a_n ≥ c₀n²` and bounded
  potential, two square-summable solutions have zero Wronskian.
* `HTGeometry/DiscreteEnergyBootstrap.lean` — `abel_sum_Ico`, `telescope_Ico`,
  `abstract_window_estimate`, `abstract_energy_bootstrap`: an abstract normalized-energy
  bootstrap taking `F, P, Dr, ctrl` with `|P| ≤ 4F`, a controlled step, small drift and small
  total control, and concluding `F m ≤ 2·max(F_{N₀}, F_{N₀+1})`.
* `HTGeometry/DiscreteSturmLiouvilleGreen.lean` — `slgFlux`, `slgWeight`, `IsSLGSolution`,
  `slgEnergy`, `slgVirial`, `slgPrimitive`, `slgEnergy_succ_sub` (exact drift law),
  `slgVirial_succ`, `two_mul_sq_slgFlux_sub_energy`, the three positivity bounds,
  `slgNormalizedEnergy`, `slgDrift`, `slgWeightRatio`, `slgRatioDefect`, `slgExtra`,
  `slgNormalizedEnergy_succ_sub(_split)`, `abs_mul_slgFlux_le`, `abs_slgPrimitive_le`,
  `slgAbelDrift`, `slgControl`, `slg_increment_tail_bound`, **`slg_bootstrap`**, and
  **`sq_le_of_slgControl`**: `u_m² ≤ 4C/√(ρ_m Q_m)`.

Remaining for card 1: module 4 — the explicit prolate coefficients `ρ_n^±`, `q_n^±`, their real
error bounds, discharge of `hbdry`/`hsum`, and assembly against `jacobiDeficiency`.

### Card 1 module 4 — the plan that makes the asymptotics tractable

`slg_bootstrap` was generalised so that the Abel drift may be replaced by **any** approximation
`Dr` with a summable deviation `dev`; `abstract_energy_bootstrap`'s step hypothesis now reads
`≤ ctrl k * (F k + F (k+1))`.  This is what makes the prolate estimates feasible: only ONE sharp
estimate is needed, and every other bound may be crude.

Exact algebra of the prolate coefficients (both parities):

* `(4n+1)(4n+2)(4n+3)(4n+4) = t_n² − 1` with `t_n = 16n²+20n+5`
  (because `(4n+1)(4n+4) = t_n − 1` and `(4n+2)(4n+3) = t_n + 1`);
* `(4n+3)(4n+4)(4n+5)(4n+6) = s_n² − 1` with `s_n = 16n²+36n+19`.

So `ρ_n = ¼√(t_n²−1) = t_n/4 − δ_n` with `0 < δ_n = 1/(4(t_n + 4ρ_n)) ≤ 1/(4t_n)`, and the
Sturm–Liouville potential is **exact**:

`Q_n = ρ_n + ρ_{n−1} + q_n − z = 3/4 + 2πλ²(8n + c) − z − δ_n − δ_{n−1}`,  `c = 1` (even), `5` (odd),

since `(t_n + t_{n−1})/4 + q_n = 3/4 + 2πλ²(8n+1)` and `(s_n+s_{n−1})/4 + q_n^- = 3/4 + 2πλ²(8n+5)`
are polynomial identities.  In particular `Q_n` is **bounded** at `λ = 0` — exactly the hypothesis
of `crossWronskian_eq_zero_of_both_summable` — and `Q_n = An + B + O(n^{-2})` for `λ>0` with
`A = 16πλ²`, `B = 2πλ² + 3/4 − z`.

Sharp estimate (the only one): with `Dr n = −6/(√A √n)`,
`|slgAbelDrift n − Dr n| ≤ C n^{-3/2}`.  Proof route: a relative-approximation calculus
(`|x − y| ≤ e·y`, closed under `*`, `/`, and `√` with the error halving trivially since
`|√x − √y| = |x−y|/(√x+√y) ≤ e√y`), applied to the four ingredients
`ΔW_n ≈ 12An²`, `ρ_n ≈ 4n²`, `W_n ≈ 4An³`, `W_{n+1} ≈ 4An³`, each with relative error `O(1/n)`,
and then `slgAbelDrift n = −ΔW_n ρ_n/(W_n √(W_{n+1})) ≈ −6/(√A √n)`.
`∑|ΔDr|` telescopes because `n^{-1/2}` is decreasing; `∑ dev` and `∑ slgControl` are `O(n^{-3/2})`
and are summed by the already-proved `sum_Ico_sqrt_div_sq_le` (`√k/k² = k^{-3/2}`).

### Card 1: the `λ = 0` half is CLOSED

`HTGeometry/RelativeApproximation.lean` — `RelApprox x y e := |x − y| ≤ e·y`, with
`nonneg_error`, `lower`, `upper`, `pos`, `abs_le_of_lt_one`, `mul`, `div`, `sqrt`, `mono`,
`of_abs_le`.

`HTGeometry/JacobiSolutionConstruction.lean` — `jacobiPair`, `jacobiSol` (two-step recursion over
any field), `jacobiSol_succ_succ`, `jacobiSol_rec`, `IsJacobiRecR`, `isJacobiRecR_jacobiSol`,
`isJacobiRec_ofReal`, `isSLGSolution_of_jacobi`, `crossWronskian_standard`.

`RHTower/ProlateJacobiLimitCircle.lean` — `prolateBase`, `prolateRho`, `prolateDefect`,
`prolateBase_ge`, `prolateRho_eq_sub`, `prolateDefect_mul` (the exact identity
`4δ(t + √(t²−1)) = 1`), `prolateDefect_pos`, `prolateDefect_le`, `prolateDefect_lt_quarter`,
`four_sq_le_prolateRho` (`4n² ≤ ρ_n`), `prolateRho_pos`, `prolatePotential`,
`prolatePotential_eq`, `prolate_diag_sum_bound`, and

**`prolate_jacobiDeficiency_eq_bot`** — for any `β ≥ 0`, `γ ≥ 2` and any diagonal `q` satisfying
`(t_{n+1}+t_n)/4 + q_{n+1} = 3/4`, the deficiency space at every non-real spectral parameter is
trivial.  Instantiated as `prolateEven_jacobiDeficiency_eq_bot` and
`prolateOdd_jacobiDeficiency_eq_bot` for `(β,γ) = (20,5)` and `(36,19)` with
`prolateDiagEven 0`, `prolateDiagOdd 0`.  `prolateRho_even` / `prolateRho_odd` certify that these
are literally the parent paper's `ρ_n^±`.

This is the card's statement "At `λ=0`, both parity blocks are in the limit-point case".

Remaining: the `λ>0` half (limit circle) via `slg_bootstrap`.  Needed estimates, all with `n ≥ N₀`:
`RelApprox (ρ n) (4n²) (K₁/n)`, `RelApprox (Q n) (A n) (K₂/n)` with `A = 16πλ²`,
`RelApprox (W n) (4An³) (K₃/n)`, `RelApprox (W (n+1)) (4An³) (K₄/n)`,
`RelApprox (Q(n+1)−Q n) A (K₅/n)`, `RelApprox (ρ(n+1)−ρ n) (8n) (K₆/n)`,
`RelApprox (ΔW n) (12An²) (K₇/n)`, `RelApprox (√(W(n+1))) (2√A·n√n) (K₄/n)`, and finally
`RelApprox (−slgAbelDrift n) (6/(√A √n)) (K₈/n)`; plus crude `O(n^{-3/2})` bounds on the three
`slgControl` terms.  `RelApprox.add` and `RelApprox.trans` still need to be added.

## CARD 1 CLOSED — `archimedean-prolate-jacobi-limit-circle-transition` promoted to stage 3

Both halves are proved, unconditionally, without Pruckner's Theorem 2.

`RHTower/ProlateJacobiLimitCircleAmplitude.lean` (the `λ>0` half) contains, in order:
`forall_ge_succ`, `prolateDefect_le_sq`, `relApprox_prolateRho`, `prolatePotential_succ_linear`,
`relApprox_prolatePotential`, `prolateErr` + `seven_le_prolateErr` + `prolateErr_pos`,
`relApprox_rho_err`, `relApprox_Q_err`, `relApprox_shift_sq`, `relApprox_shift_cube`,
`prolateWeight` + `prolateWeight_succ_sub`, `prolateRho_succ_sub_eq`,
`prolatePotential_succ_sub_eq`, `relApprox_drho`, `relApprox_dQ`, `relApprox_weight_succ`,
`relApprox_rho_succ2`, `relApprox_weight_succ2`, `relApprox_sqrt_weight_succ2`, `relApprox_dW`,
`neg_drift_form`, `sqrt_weight_ref`, **`relApprox_slgAbelDrift`**, `relApprox_sqrt_weight_succ`,
**`slgControl_le`**, `prolateDrift`, `prolateDev`, `prolate_dev_bound`, `prolateDrift_bdry`,
`prolateDrift_diff`, `inv_succ_le_sqrt_div_sq`, `prolateTotalConst`, **`prolate_sum_le`**,
`prolate_e_le`, `prolatePotential_pos`, `prolatePotential_le_rho`, `sqrt_weight_lower`,
**`prolate_summable_of_pos`**, **`prolate_jacobiDeficiency_ne_bot`**, `prolate_A_pos`,
`prolateEven_jacobiDeficiency_ne_bot`, `prolateOdd_jacobiDeficiency_ne_bot`,
**`prolate_limit_circle_transition`**, `rank_jacobiDeficiency_eq_one`,
`prolateEven_deficiency_indices`, `prolateOdd_deficiency_indices`,
`prolate_deficiency_indices_zero`.

Design notes worth keeping:

* `slg_bootstrap` was generalised to accept **any** approximation `Dr` of the Abel drift with a
  summable deviation `dev`; `abstract_energy_bootstrap`'s step hypothesis is
  `≤ ctrl k * (F k + F (k+1))`.  This is what reduces the whole `λ>0` analysis to ONE sharp
  estimate (`relApprox_slgAbelDrift`) with everything else crude — the explicit drift
  `Dr n = −6/(√A √n)` has a telescoping total variation, so `∑|ΔDr|` is free.
* `RelApprox` bookkeeping (relative error `|x−y| ≤ e·y`) is what makes the composite
  `slgAbelDrift = −ΔW·ρ/(W√(W'))` estimate a five-line composition instead of a page of
  interval arithmetic.  Normalise every error to `m·K/x` with `K = prolateErr` and small integers
  `m` via `RelApprox.mono` at each step; `100K ≤ x` keeps every error below `1/100`.
* Traps hit: `set` does not fold occurrences created *after* it (gather all `RelApprox` facts
  first, then `set`); `positivity` never uses hypotheses, so `0 ≤ prolateErr …` must be supplied by
  `prolateErr_pos`; `ring` will not prove `a/(b*c) = a/b * (1/c)` (use `div_mul_div_comm` then
  `div_eq_div_iff` with **explicit** `≠ 0` arguments, then `linear_combination … * hsA2`);
  `summable_of_sum_range_le` needs its bound `c` given explicitly.

Remaining in this folder: cards 5, 7, 11, 14, 17.

## Cards 14, 17, 7 CLOSED (2026-08-23)

* **14** `sonin-small-cutoff-ground-row-survival` → stage 3.
  New module `RHTower/SoninSmallCutoffGroundRow.lean`: the two archimedean strong limits
  (`tendsto_norm_sub_centralSoninProjection_of_tendsto_zero` for `λ↓0` via the Friedrichs angle
  and the exact time-band area `‖A_a F_a‖ ≤ 2a`; `tendsto_norm_centralSoninProjection_atTop` for
  `λ→∞` via `‖Q g‖ ≤ ‖g − A_a g‖`), the rank-one ground-row algebra (`groundRow`, `corner_eq`,
  `norm_corner`, `corner_ne_zero`, `groundRow_eq_rankOne`), trace class, and the concrete
  one-prime and finite-prime ground-row vectors with their nonvanishing.
  The one-prime `v_P` is the corpus's own `semilocalOnePrimeGroundRowVector p 1` — the
  `alpha = 1` case of the already-proved `3/4 < alpha` summability, whose coefficients are exactly
  `2k/(2k+1)` times the ground moment.
* **17** `transported-prolate-relative-resolvent-corner` → stage 3.
  The corpus already owned `SoninSylvesterFactorization` (factorization, Schatten bound, vanishing
  criterion, cfc intertwining) and `HTGeometry/DisjointSpectrumIntertwiner`.  New module
  `RHTower/TransportedProlateResolventCorner.lean` adds `conjOp`, `memSchattenClass_conjOp`,
  `conjOp_mul`, `conjOp_reduces`, `conjOp_idem`, `mul_ne_zero_of_not_isCompactOperator` (a
  noncompact crossing survives a compact complement — the card's `H_P E_- ≠ 0` step),
  `sylvester_ne_zero_of_compressed`, and the assembled `transported_relativeResolvent_corner`.
* **7** `route-b-semilocal-sonin-interim-verdict` → stage 3.  Every theorem-bearing bullet is now
  Lean-backed; the table in the card lists the declaration for each.  The one bullet that had no
  Lean support, `[DIRECT CYCLIC FORM DOMAIN CLOSED]`, is closed by the new module
  `RHTower/SemilocalCyclicFormDomain.lean` (`weighted_lintegral_bounds`,
  `exists_isSelfAdjoint_representative`) on top of the corpus's
  `semilocalFinitePrimeEulerDensity_bounds`.

Remaining: **5** `prime-tail-copoisson-essential-boundary-bockstein` and
**11** `sonin-burnol-conductor-cutoff-bounded-graph-law`.

### Card 5 in progress: `RHTower/PrimeTailCoPoissonBoundary.lean`

Landed and wired (axiom-clean):

* `primeTailSeed n z x = n^{-z} x^{-z} 1_{[1/n,1]}(x)` and Burnol's centred cell `burnolCell`;
  **`primeTailSeed_eq_burnolCell`** is card `(7)`.
* **`integral_primeTailSeed`** is card `(5)`: `∫_{1/n}^1 g_{n,z}(x) x^{w-1} dx =
  (n^{-w} − n^{-z})/(z−w)`, via `integral_cpow` on a branch-cut-free interval plus
  `Complex.inv_cpow`.
* `monodromyGerm`, `monodromyGermJet` (cards `(23)`, `(24)`), `reflectedGerm` `(29)`,
  `normalizedDilation` `(25)`, `multiplicativeInversion` `(28)`, `conj_ofReal_cpow`,
  `ofReal_sqrt_eq_cpow`, `ofReal_mul_cpow`;
  **`normalizedDilation_monodromyGerm`** `(26)`–`(27)`,
  **`normalizedDilation_reflectedGerm`** `(30)`–`(31)`,
  **`multiplicativeInversion_conj_monodromyGerm`** `(29)`,
  `dilation_characters_eq_iff` (the two characters agree in radial type iff `Re ρ = 1/2`).
* `primeTailCurrent` is card `(3)`; `norm_primeTailSeed` and **`norm_primeTailSeed_mul_le`**
  give the pointwise majorant `‖g_{n,z}(x) x^{w−1}‖ ≤ (n^{−σ}+n^{−τ}) x^{−1}` on `(0,1]`,
  uniform in the sign of `τ−σ` (the case `τ<σ` uses `x^{τ−σ} ≤ n^{σ−τ}` on `[1/n,1]`).

The corpus already owns `P(z)`: `eulerLogDirichletCoeff n = Λ(n)/log n`,
`canonicalEulerLogZeta = LSeries eulerLogDirichletCoeff`, `canonicalEulerLogZeta_summable`,
`exp_canonicalEulerLogZeta_eq_riemannZeta` in `HTGeometry/CanonicalEulerLog.lean`, and
`logDeriv_riemannZeta_eq_neg_LSeries` for the diagonal `(9)`.

Next for card 5: the `∫ ∑ = ∑ ∫` interchange (`MeasureTheory.integral_tsum` with the majorant
above and `∑ n^{-σ} log n < ∞`), giving `(8)`; then `(16)`/`(17)` from PNT, `(20a)`–`(20n)` from
PNT with error, and the `log ζ` monodromy `(22)`–`(24)`.

### Card 5: gates 1, 2, 3, 5, 6 CLOSED (2026-08-23)

`RHTower/PrimeTailCoPoissonBoundary.lean` now proves, unconditionally and axiom-clean:

| card item | declaration |
|---|---|
| `(2)` seed, `(6)` Burnol cell, `(7)` their identity | `primeTailSeed`, `burnolCell`, `primeTailSeed_eq_burnolCell` |
| `(5)` seed right Mellin transform | `integral_primeTailSeed` |
| `(3)` all-prime condensation | `primeTailCurrent` |
| pointwise majorant, uniform in `sign(τ−σ)` | `norm_primeTailSeed`, `norm_primeTailSeed_mul_le` |
| `∑ n^{-σ} log n < ∞` and the full majorant | `summable_rpow_neg`, `summable_rpow_neg_mul_log`, `summable_primeTail_majorant` |
| term integrability and its `L¹` mass | `integrableOn_primeTailTerm`, `integral_norm_primeTailTerm_le`, `integrableOn_primeTailFullTerm`, `integral_norm_primeTailFullTerm_le` |
| **`(8)` the divided-log Mellin scalarization** | `primeTailCurrent_mellin` |
| **`(9)` the diagonal `= L(Λ, z) = −ζ'/ζ`** | `primeTailCurrent_mellin_diag`, `eulerLogDirichletCoeff_mul_log`, `integral_primeTailSeed_diag` |
| `(21)` the single-valued finite part and the decomposition | `primeTailFinitePart`, `primeTailCurrent_eq_finitePart`, `differentiable_primeTailFinitePart` |
| **`(22)` the divisor Bockstein** | `primeTailCurrent_monodromy` |
| `(23)` the nonzero germ | `monodromyGerm`, `monodromyGerm_ne_zero` |
| **`(24)` every logarithmic jet** | `monodromyGermJet`, `iteratedDeriv_monodromyGerm` |
| `(25)`, `(28)` the two actions | `normalizedDilation`, `multiplicativeInversion` |
| **`(26)`–`(27)`, `(29)`, `(30)`–`(31)`** | `normalizedDilation_monodromyGerm`, `multiplicativeInversion_conj_monodromyGerm`, `normalizedDilation_reflectedGerm` |
| the two characters agree in radial type iff `Re ρ = 1/2` | `dilation_characters_eq_iff` |

Reusable helpers: `conj_ofReal_cpow`, `ofReal_sqrt_eq_cpow`, `ofReal_mul_cpow`,
`setIntegral_Ioc_indicator`, `integral_indicator_inv`, `integrableOn_indicator_inv`,
`measurable_ofReal_cpow`, `aestronglyMeasurable_primeTailTerm`.

**Still open on card 5** (gate 4 and section 3A):

* `(11)`–`(16)`: `J(X) = ∑_{2≤n≤X} a_n ~ X/log X` from PNT, Abel summation `(13)`, the integral
  asymptotic `(14)`, hence `G_z(x) ~ 1/((z−1) x log(1/x))`.
* `(17)`: the half-weight `L²` wall, and `(18)`, `(20)`.
* `(20a)`–`(20n)`: the pole vacuum `V_z`, `V = E_1(z−1)`, `(20d)`, the holomorphy of `P − V` at
  `z = 1`, and the all-orders flatness of the vacuum-normalized remainder from PNT with error.

Available corpus inputs for these: `chebyshevPsi_sub_id_isBigO` (PNT with `exp(−c√log x)` error),
`tendsto_chebyshevPsiReal_div`, `exists_psi_error_eventually`, and the vendored `PNTPlus`.
The remaining work is the Abel-summation transfer from `ψ` to `J`, and the two integral
asymptotics.

### Card 11 remains

`sonin-burnol-conductor-cutoff-bounded-graph-law` still needs its own unchecked gate:
Burnol's Mellin spectral law (`H_∞ = M + JMJ` is multiplication by the log-derivative of the even
Tate Gamma factor), `h_∞ ∈ BMO`, and the Coifman–Rochberg–Weiss / Nehari BMO commutator theorem.
The algebraic reflection layer is already Lean (`SoninBurnolConductorReflection`,
`SoninBurnolConductorConcrete`).
