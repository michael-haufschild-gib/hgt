# CHMD growth–positivity collapse (2026-10-15, MUST-1529)

Module `formal/GaloisForLFunctions/RHTower/CHMDGrowthPositivityCollapseAndTwoPointCriterion.lean`
(namespace `RHTower.CHMDGrowthCollapse`; imports CHMD Stage 15; wired in `RHTower.lean` after Stage 15;
standard axioms; `lake build --old` green). Card: `docs/drafts/pipeline/3-formalized/chmd-stage16-growth-positivity-collapse-2026-10-15.md`.

Statement. Let `φ_Λ(y) = cosineShiftFn Λ sechHalf y` (the CHMD causal wave), `ρ_ρ = rhoC (gammaOf ρ) = √(γ_ρ²+2)`,
`w_ρ = specSq sechHalf (gammaOf ρ) = sech²(γ_ρ/2)`. Unconditionally:
- `(φ_Λ(y) : ℂ) = Σ' m_ρ cos(y ρ_ρ) w_ρ`; `Re ρ_ρ > 1`, `|Im ρ_ρ| < ½`; `|φ_Λ(y)| ≤ kgMass e^{|y|/2}`.
- Laplace transform on `Re s > ½`: `kgPoleSeries s = Σ' m (w/2)(1/(s−iρ)+1/(s+iρ))`; analytic off `{±iρ_ρ}` (locally finite);
  `kgPoleSeries(−iρ_ρ + d) = A/d + B(d)`, `‖A‖ ≥ ‖w_ρ‖/2`, `‖B‖ ≤ C`.
- Exact growth law (`chmdWave_growth_law`, `0 ≤ a < ½`): `∃M, φ_Λ ≤ M e^{au}` on `u ≥ 0` ⟺ `∃M, −M e^{au} ≤ φ_Λ` ⟺ all zeros have
  `|Im ρ_ρ| ≤ a` ⟺ `∃K, |φ_Λ| ≤ K e^{a|u|}`.
- `a = 0`: RH ⟺ bounded above ⟺ bounded below ⟺ bounded ⟺ `φ_Λ(y) ≤ φ_Λ(0)` ⟺ `|φ_Λ(y)| ≤ φ_Λ(0)` ⟺ Stage 13 two-point
  difference packets nonneg (`riemannHypothesis_iff_forall_twoPointDiff_nonneg`) ⟺ `kgPoleSeries` positive-real on `Re s > 0`;
  `exists_sechHalf_measure_iff_chmdWave_bddAbove`.

Mechanism: corpus Landau theorem `exists_differentiable_extension_of_le_exp` (FiniteOffLineLandau) + new generic tilted-ray lemma
`false_of_extension_of_blowup` + real frequencies ⟹ nonneg zero-side summands ⟹ Stage 4/14 Toeplitz criterion.

Route consequence: the CHMD "Needs" (all Toeplitz forms / Bochner measure) collapses to ONE one-sided bound on the KG prime wave
`Σ Λ(n)/√n K_S(log n, y) ≥ P(y) + A(y) − φ_Λ(0)` — Wall 1 (one-sided √x prime counting) in Klein–Gordon coordinates.
Do not add finite-N Toeplitz positivity beyond N = 2. The other agent's Stages 16–21 (strip kinematics, cosh–sinh squares) are complementary.

Lean notes: `integral_tsum_of_summable_integral_norm` over `zetaZeroConfig.carrier` needs
`WeilConditional.countable_carrier.to_subtype`; `IntegrableOn.congr_fun` must be called explicitly (dot notation lands on `And`);
`tsum_of_norm_bounded` takes a `HasSum`; `Summable.le_tsum` for the residue lower bound; `pow_le_pow_left` is gone — use
`mul_self_le_mul_self`; `push_neg` is deprecated (use `not_le.mp`); `Set.diff_subset` → `sdiff_subset`.
