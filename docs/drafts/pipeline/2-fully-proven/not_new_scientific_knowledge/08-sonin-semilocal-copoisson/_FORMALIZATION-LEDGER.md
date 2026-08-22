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
