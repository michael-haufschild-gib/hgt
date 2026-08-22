# 08-sonin-semilocal-copoisson — stage-2 → stage-3 formalization ledger

Goal: formalize unconditionally in Lean every proven theorem of every card in this folder, add the
missing infrastructure, then move each card to
`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/08-sonin-semilocal-copoisson/`.

Rules in force: no added hypotheses standing for analytic inputs, no axioms, no `sorry`;
never full builds / umbrella builds (`lake env lean <file>` to check, `lake build <module>` only for
the oleans an `#print axioms` scratch needs); search the corpus before building anything.

## Card triage (17 cards) — 5 promoted, 12 remain

| # | card | state | notes |
|---|---|---|---|
| 1 | archimedean-prolate-jacobi-limit-circle-transition | TODO | needs discrete limit-circle theory; card's λ=0 exponents are wrong (see below) |
| 2 | boolean-sonin-full-history-mate-fracture-law | **PROMOTED 2026-08-22** | `HTGeometry/BooleanSoninFullHistory.lean` |
| 3 | connes-semilocal-finite-part-orbital-source-class | **PROMOTED 2026-08-22** | `HTGeometry/QuantizedDifferentialCocycle.lean` + `RHTower/ConnesSemilocalOrbitalSourceClass.lean`; `(1)`–`(3)` stay literature (Connes) and are *not* assumed by any Lean statement |
| 4 | finite-euler-connection-cauchy-phase-chambers | **PROMOTED 2026-08-22** | `RHTower/FiniteEulerConnectionCauchyPhaseChambers.lean`; the card's "Kronecker hitting theorem missing" note was stale |
| 5 | prime-tail-copoisson-essential-boundary-bockstein | TODO | |
| 6 | rectangular-semilocal-observer-tail-separation | **PROMOTED 2026-08-22** | `RHTower/RectangularSemilocalObserverTailSeparation.lean` |
| 7 | route-b-semilocal-sonin-interim-verdict | TODO | |
| 8 | semilocal-dual-pair-euler-connection-source-law | TODO | |
| 9 | semilocal-euler-kernel-chart-differentiability | TODO | |
| 10 | semilocal-jacobi-linear-growth-prolate-domain-gate | **PROMOTED 2026-08-22** | `HTGeometry/MonicOrthoExtremalComparison.lean` + `RHTower/SemilocalJacobiLinearGrowthProlateDomainGate.lean` |
| 11 | sonin-burnol-conductor-cutoff-bounded-graph-law | TODO | |
| 12 | sonin-place-transition-cutoff-dichotomy | TODO | |
| 13 | sonin-prime-seam-exterior-factorization | TODO | |
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
is available and `IsCompactOperator` means what the card means.
