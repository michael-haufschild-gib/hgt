# Bucket X8 — Lean ledger footholds (index)

**Bucket grade:** organizational index (SEARCH channel pointing at the LEDGER). Sorted from
`docs/support-extraction-log.md` + `docs/architecture.md`.
**Scope (one line).** Every axiom-clean Lean theorem/module named in the corpus, indexed against the
bucket (gatekeeper / cross-cutting theme) it supports — so each work package knows its existing
machine-checked floor.
**Work package this seeds.** For each bucket, the **next Lean target** is the first Tier-A/B fragment
above its current floor; this index makes those boundaries explicit.

> **Note on the count.** The audit gate is `scripts/check_axioms.sh` (it counts
> `#print axioms` lines and requires the allowed axiom subset `[propext, Classical.choice,
> Quot.sound]`). The corpus cites **conflicting totals** (CLAUDE.md "19 theorems"; testing.md "69";
> #99 "28 + 35 computations"; #102 "203 axiom-clean outputs"). *Do not quote a single number as fact* —
> the build + `check_axioms.sh` PASS is the only ground truth. Treat the list below as the *named*
> footholds, not a complete or counted census.

---

## Footholds by bucket

### [[G1-difference-holder]] — the obstruction's floor
- `Core` / `logPrime_no_rat_relation` — `{log p}` is ℚ-linearly independent (via `Nat.factorization`).
  *The rigorous floor under "ζ needs all `q_p` at once."*
- `MultiQDifference` / `localEulerFactor_q_difference` — the local first-order q-difference equation for
  one Euler factor (the single-factor base case).
- `OrbitFreeness`, `Resonance` — additive "no diagonal resonance" corollaries; `Λ=0` finite slices.

### [[G2-multi-q-siegel-shidlovsky]] / [[bucket-A1-A2-unification-the-carrier]] — secular coordinates
- `SecularMoments` / `li_secular_pointwise`, `secular_li_pointwise_inv` — the Li↔secular ℤ-triangular
  change of basis, **both directions** (the `{P_k}↔{λ_n}` equivalence; "first SEARCH→LEDGER crossing").
- `SpectrumGenericity` / `spectrum_esymm_algIndep` — finite DSS face: elementary-symmetric coords of `n`
  indeterminate points alg. independent over ℚ (the A2 finite anchor).
- `MultiplicityEstimate` / `multiplicity_det_criterion`; `DSSDeterminant` /
  `matrix_nontrivial_kernel_iff_det_eq_zero` — the DSS auxiliary-vanishing determinant criterion.
- `SmoothNumbers` / `boundedExponentVectorEquivSmooth`, `diagonalAuxiliaryForm_eq_dirichletPolynomial` —
  the friable-Dirichlet-polynomial auxiliary base (object N5).
- `SecularNewton`, `MultisetNewton`, `MomentReconstruction`, `PowerSumTorelli` / `powerSum_torelli`,
  `SpectralTorelli` — Newton/Torelli inversion (`{p_k}↔{e_k}`, faithfulness of secular coords).
- `DiagonalCharacter` — Bohr character / diagonal auxiliary sums become Dirichlet polynomials.
- `BohrGenerators` / `bohrCharacter_scaleAllCoordinates`, `bohrCharacter_archimedeanSquareScale` —
  finite-support Bohr character scaling, including the `x_p ↦ p^{-2}x_p` product-formula scale slice.
- `BohrGenerators` / `twoAxisMode_support_eq`, `bohrCharacter_twoAxis_product`, `twoAxisMode_ne_zero` —
  finite two-axis product support, the Lean floor under combination modes.
- `BohrGenerators` / `scaleCoordinate_commute`, `scaleAllCoordinates_commute`,
  `scaleCoordinate_scaleAllCoordinates_commute` — finite coordinate-scaling commutation, the algebraic
  floor under the completed-base scaling system.
- `FamilyCrossResonance` / `familyTwistedProduct_split`, `familyPrimeBalance_*` — finite family
  cross-resonance split and shared-prime modulus balance.
- `MoritaGamma` / `moritaGammaFinite_succ` and supporting recurrences — finite positive-integer
  Morita Gamma recurrence, the Lean floor under the per-place `Γ_v` carrier row (#196/#197).

### [[G3-holonomy-dichotomy]] / [[G4-multi-q-picard-vessiot-and-langlands-group]] — connection & cohomology
- `FlatConnection` — pairwise cocycle/curvature algebra, finite-truncation integrability, the
  co-extension flatness identity 47.1 (`σ_i(A_j)A_i=σ_j(A_i)A_j`).
- `HolonomyAbelian` — commuting monodromy ⟹ abelian subgroup (the inverse-Galois finiteness lemma's
  core).
- `RankOneCohomology`, `KoszulCohomology` — rank-1 cocycles/coboundaries; additive Koszul differentials
  + Euler-characteristic rank count.
- `EHKoszulDuality` / `eh_koszul_duality` — the `∧•⊣Sym•` (`e–h`) Koszul duality, all degrees (welds B30
  operations ↔ B5 cohomology; the finite shadow of `ω`).

### [[G4-multi-q-picard-vessiot-and-langlands-group]] / [[bucket-function-field-proving-ground]] — Satake λ-ring (the clean half)
- `AdamsOperations` / `adamsPowerSum_tensor`, `adamsPowerSum_isobaricSum`, `adamsPowerSum_comp`,
  `adamsPowerSum_one` — the Adams/power-sum λ-ring algebra (⊗ multiplicative, ⊕ additive, Adams monoid).
- `SymPowerPlethysm` / `chebyshevU_eval_plethysm` — `p_m(Sym^k π)=U_k(p_m/2)` (machine-proved).
- `SatakeSymPower` / `symPowerGL2_eq_chebyshevS`; `SatakeInterval` / `satake_trace_re_mem_Icc` (unitary
  trace ∈[−2,2]); `ExteriorSatake`, `CompleteHomogeneous`, `LocalFactorDuality`, `SatakeReality`,
  `SatakeTensor` — the local-factor / Satake skeleton.
- `SatoTateMoment` — μ_ST moments vanish + `U_k` orthonormality (the Sato–Tate analytic core, measure
  level).
- `functionField_esymm_FE`, `functionField_localFactor_FE`, `multiset_esymm_map_mul` — the Weil FE of
  the L-polynomial over `F_q` (the Door-5 calibration).

### [[G5-unitarity-gatekeeper]] / [[bucket-the-no-margin]] — the carrier / positivity toolchain
- `CarrierCauchy` / `multiPair_carrier_exact_neg_inertia`, `multiPair_carrier_linearIndependent` —
  **`κ₋ = #off-line conjugate pairs` exactly** (the radial/RH coordinate as an integer; RH = `k=0`).
- `KreinLangerInertia` — abstract Hermitian inertia bounds, negative-subspace witnesses, FE
  conjugate-pair `κ₋`/`κ₊` factorizations.
- `CarrierPickKernel`, `MeasureCarrier`, `CayleySchur` — finite Herglotz/Pick skeleton + Cayley/Schur
  disk bridge + Blaschke/Szegő positivity (the Stage-2 infinite-carrier infrastructure start).
- `SecularHankel` / `secularHankel_posSemidef` — finite real-spectrum Hankel = PSD Gram.
- `SigmaOrbit` / `sigmaConj_fixed_iff_critical` — critical line = fixed locus of `σ∘conj` (pointwise
  `ι=κ`).
- `ArakelovW`, `WCoordinate` — `|w|=1 ⟺ Re=½`, FE inversion `w↦1/w`, `w(z)w(1−z)=1` (the CMV/height
  coordinate).
- `BerryKeating` / `berryKeatingU_sigma`, `..._re_ge_quarter_on_critical`, `..._nonreal_of_offCritical` —
  `u=s(1−s)=¼+γ²` (the positive-spectrum H–P coordinate).
- `BoundaryModulus` — `|x_p|=|q_p|^{1/2} ⟺ Re=½` (the σ-fixed-modulus floor).
- `OscillatorAlgebra` — Weil-rep commutators `[H,X]=2X,[H,Y]=−2Y,[X,Y]=−4H` (the Hodge–Riemann face's
  algebra).
- `MultiplierScaling` / `sigmaScale_splits` — `σ_p` preserves real-rootedness (the LP-multiplier floor).

### [[bucket-realization-and-fake-family]] — firewall & inverse problem
- `EulerProduct` — the **First Theorem**: Euler product ⟺ Bohr-lift factorization, with a concrete mod-5
  fake coefficient witness (the pre-spectral fake filter, the (A) cut).
- `SuperzetaResolvent` / `superzeta_eq_sum_resolvent`, `superzeta_coeff_eq_powerSum` — the superzeta is
  the additive resolvent trace `Σ_i(1−r_iX)^{−1}` with k-th coeff `P_k` (the Σ-vs-∏ seam, a Lean
  theorem; the superzeta-is-a-fake verdict).

### [[door-C5-irreducibility-and-door-2-retest]] — the σ-parity = FE-parity weld (candidate native)
- `FunctionalEquationParity` / `fe_odd_moment_vanish`, `fe_centered_odd_moment_vanish` — FE-reflection
  ⟹ vanishing odd / centered-odd moments.
- `ExteriorParity` / `exteriorPower_map_neg_id` — `∧ⁿ(−id)=(−1)ⁿ·id` (the genuine exterior-power level
  of the σ-parity weld; the candidate native theorem to re-test against Door-2).
- `GluingWitness` / `gluing_per_prime_same_but_joint_distinct` — the C3 bridge witness: two rank-2,
  two-prime rational matrix pairs have identical per-prime conjugacy data but no simultaneous joint
  conjugacy, detected by `tr(A₂A₃)=3 ≠ 5/2=tr(B₂B₃)`. This formalizes the finite witness only; the
  Procesi/Artin generation and C5★ reduction remain paper/import-level.

### Statement-level (no conjecture axioms)
- `FieldConjectures` — Lean `Prop`s for DSS and the realization problem, plus the proved finite alias
  `carrierHerglotz_iff_onLine` (`= carrier on-line iff Herglotz`, finite). *Conjectures live as `Prop`s,
  never as `axiom`/`theorem` — the two-channel rule.*

---

## The boundary every bucket shares (what is NOT in Lean)
- **Tier C never enters the ledger:** RH, LI/DSS, archimedean positivity. All `κ₋=0`, `m_ξ` Herglotz,
  `Q_W⪰0`, `{P_k}` independence statements are draft-only.
- **The infinite passage (the recurring mathlib gap):** Nevanlinna `N₀`/Krein–Langer `N_κ`, regularized
  Hadamard/`ξ`, infinite-node Pick — needed to lift the finite carrier theorems
  ([[G5-unitarity-gatekeeper]] Stage 2) to the actual `ξ`. `MeasureCarrier`/`CayleySchur` are the start.

## Cross-references
- Every `[[G…]]` and `[[bucket-…]]` file lists its own footholds inline; this is the consolidated index.
- [[door-C5-irreducibility-and-door-2-retest]] — which footholds back the Door-2 NATIVE candidates.
