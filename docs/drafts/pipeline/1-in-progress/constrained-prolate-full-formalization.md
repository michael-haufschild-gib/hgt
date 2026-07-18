# Full Lean formalization campaign: the six constrained-prolate cards

- **ID:** `constrained-prolate-full-formalization`
- **Stage:** 1-in-progress (formalization campaign card; the six mathematical cards stay in
  `2-fully-proven/new_scientific_knowledge`)
- **Goal:** formalize in Lean, unconditionally, every `[PROVED HERE]` theorem of
  `constrained-prolate-two-mode-ground-state`, `constrained-prolate-fourier-parity-floor-separation`,
  `constrained-prolate-fixed-mode-spectral-ladder`, `constrained-prolate-radial-leakage-divisibility-spectrum`,
  `constrained-prolate-full-radial-prime-charge-law`, `constrained-prolate-arithmetic-dilation-operator-limit`.
- **Rule:** no `sorry`/`axiom`; classical analytic parent inputs (Fuchs, Slepian/prolate-to-Hermite,
  Dunster) must themselves be formalized, not assumed, before a card's operator-form headline is
  claimed as fully formalized.  Intermediate layers may state theorems with explicit rate hypotheses;
  those bank the card's own derivations but do not close the card.

## Layer DAG (bank each layer bottom-up; tick when built, lint-clean, axiom-clean)

- [x] **L0 — model layer** (existing): secular algebra (`ProlateSecularEquation`), Fuchs rate model
  (`FuchsProlateScale`), Hermite constants (`ConstrainedProlateHermiteContrast`), two-mode Fuchs
  limits 8/11, 3/11, 8/13, 5/13, parity ratio (`TwoModeFuchsLimit`), ladder rung limit
  (`LadderLimitSecular`), arcsine measure tails + 4/11 mass (`RadialLeakageArcsineMeasure`),
  arithmetic projective limit from weighted hypothesis (`ArithmeticDilationProjectiveLimit`),
  λ⁸ adjacent separation (`LadderAdjacentScaleSeparation`), operator carrier
  (`ConstrainedProlateOperator`, `ConstrainedProlateSignedSpectrum`,
  `ConstrainedProlateConstrainedSpectrum`), scalar arithmetic spectrum
  (`ArcsineZetaDerivativeSpectrum`, `ConstrainedProlateExteriorWeil`).
- [x] **L1 — infinite secular transfer** (`ConstrainedProlateInfiniteSecular.lean` +
  `ConstrainedProlateFuchsModelTransfer.lean`; 18 theorems, axiom-clean):
  the exact secular function `F(μ) = Σ_{j≥0} ℓ_j²/(d_j−μ)` on the full index set; summability,
  continuity, strict monotonicity on `(d_0,d_1)`; existence + uniqueness of the exact root `μ_0`;
  the quantitative two-mode comparison `0 ≤ μ_2mode − μ_0 ≤ T·d_1²/(ℓ_0²(d_2−d_1))` (card 1 eq (18));
  the family theorem `μ_0/d_1 → a_0²/(a_0²+a_1²)` under explicit rate hypotheses
  (d_0/d_1 → 0, λ·d_1/(d_2−d_1) → 0, ℓ_0→a_0, ℓ_1→a_1, Bessel Σℓ²≤2λ); every other secular root
  ≥ d_1; gap corollary; CCM 8/11 + 3/11 instances; Fuchs-model instance.  This is the named
  "uniform infinite-tail secular estimate" gate of cards 1–3.
  Delivered: `infiniteSecular`/`infiniteSecularTail`/`infiniteSecularRoot`; summability, tail
  bound `T/(d_2−μ)`, monotonicity, `continuous_tsum` continuity; strict monotonicity on the gap;
  IVT existence below `μ_2mode` (`infiniteSecular_exists_root`), uniqueness, spec; the
  quantitative estimate `μ_2mode − μ_0 ≤ T·d_1²/(ℓ_0²(d_2−d_1))`
  (`infiniteSecularRoot_twoMode_gap`); positivity below `d_0` and `infiniteSecular_other_root_ge`
  (all other roots ≥ d_1); the family master theorem `infiniteSecularRoot_ratio_tendsto`
  (hypotheses: eventual ordered triple + floor, Σℓ² summable, Bessel ≤ 2λ, d_0/d_1 → 0,
  λ·d_1/(d_2−d_1) → 0, ℓ_0→a_0, ℓ_1→a_1); gap ratio `a_1²/(a_0²+a_1²)`; quantified spectral gap;
  CCM instances 8/11, 3/11, `c < 3/11` (`ccm_infiniteSecularRoot_*`); Fuchs-model discharge of
  the whole `d`-side (`fuchsRate_radial_struct`, `fuchsRate_radial_tail_ratio_tendsto_zero`,
  `ccm_fuchsModel_infiniteSecularRoot_*` — under `A_2 ≤ C^j A_{j+2}`, `C ≥ 1`).
  Remaining inputs feeding L1's CCM Fuchs-model theorems are exactly the ℓ-side facts of
  L5/L7: Σℓ(λ)² summable, Bessel bound, ℓ_0 → 2^{1/4}, ℓ_1 → √3·2^{−5/4}.
- [x] **L2 — eigenvector transfer** (`ConstrainedProlateSecularVector.lean` +
  `ConstrainedProlateEigenvectorAngle.lean`, 9 theorems banked):
  coordinate eigen-equation, constraint membership `Σℓ_jv_j = 0` at the exact root, squared tail
  bound `T/(d_2−μ)²` (card 1 eq (20)), head floor `ℓ_0²/d_1²`, two-mode head orthogonality at
  `μ_2mode`, the family collapse `Σ_{j≥2}v_j²/v_0² → 0` at rate `(λd_1/(d_2−d_1))²` (eq (21)),
  the exact head–constraint pairing `ℓ_0v_0+ℓ_1v_1 = −tail(μ_0)` with bound `T/(d_2−d_1)`
  (eq (22)'s content), and the normalized head-defect collapse
  `(ℓ_0v_0+ℓ_1v_1)²/((v_0²+v_1²)(ℓ_0²+ℓ_1²)) → 0` at rate `(λd_1/(d_2−d_1))²`.  Together these
  are eq (4) in projective form (direction convergence to the two-mode seed).  Cosmetic residue:
  the literal normalized-ℓ²-distance/sign-choice phrasing.
- [~] **L3 — negative sector + parity** (`ConstrainedProlateParityExactTransfer.lean`,
  9 theorems banked): negative Hermite weight 8/13 + complement 5/13; offset radial family
  (indices 4j+2) struct + step-4 tail rate at every base index; exact negative floor `8/13`,
  gap `5/13`, quantified gap; exact parity collapse `μ_+/μ_- → 0` and sharp
  `λ⁴μ_+/μ_- → 13A_4/(11A_6)`.  Card 2 is Fuchs-model complete (ℓ-side hypotheses remain).
- [x] **L3b — all-depth ladder (card 3 eqs (8),(9)) via the flattening sandwich**
  (`ConstrainedProlateDepthSecular.lean` + `ConstrainedProlateLadderExactTransfer.lean`,
  13 theorems, axiom-clean): offset tail lemmas with abstract floor; `depthSecular` (Finset head
  + shoulder + tsum tail), continuity, strict monotonicity, uniqueness on the k-th gap;
  `flattenedScales`/`flattenedCoords` with mass-preserving aggregation
  (`tsum_flattenedCoords_sq`); pointwise sandwich; `depthSecularRoot_bracket` (existence via IVT
  between the flattened roots + trapping); `depthSecularRoot_ratio_tendsto`
  (`μ_k/d_{k+1} → S_k/(S_k+a_{k+1}²)`); CCM instance `θ_k`; Fuchs-model depth struct at every k
  (finitely many head thresholds via `eventually_all_finset`); exact-root `λ⁸` adjacent law with
  coefficient `(θ_{k+1}/θ_k)·A_{k+2}/A_{k+1}`.  Original design notes:
  on the k-th gap `(d_k, d_{k+1})`, the full secular function `F` is sandwiched pointwise
  between two aggregated two-pole models — head poles flattened DOWN to `0` (upper bound `F̌`)
  and UP to `d_k` (lower bound `F̂`), each with head mass `Σ_{j≤k}ℓ_j²` — because
  `1/(d_k−μ) ≤ 1/(d_j−μ) ≤ 1/(0−μ)` for `0 ≤ d_j ≤ d_k < μ`.  Both flattened models are
  literal `infiniteSecular` instances (families `(0, d_{k+1}, d_{k+2},…)` and
  `(d_k, d_{k+1}, d_{k+2},…)` with coords `(√Σ_{j≤k}ℓ_j², ℓ_{k+1}, ℓ_{k+2+j})`), so the L1
  master theorem gives both roots ratio → `S_k/(S_k+a_{k+1}²) = θ_k` (via
  `constrainedProlateHermiteTheta_eq_square_ratio`).  Root ordering: `F ≤ F̌` ⇒ `ř ≤ r_k`
  (mono), `F ≥ F̂` ⇒ `r_k ≤ r̂`; existence of `r_k` by IVT on `[ř, r̂]` once `ř > d_k`
  eventually (from `ř/d_{k+1} → θ_k > 0`, `d_k/d_{k+1} → 0`); uniqueness by strict mono on the
  gap; then squeeze.  Needs offset-general tail lemmas (abstract floor `B ≤ d_{j+m}`), a
  `depthSecular` def (Finset head + shoulder + tail), and negative-denominator div monotonicity.
  Then Fuchs-model discharge at depth k and the exact-root `λ⁸` adjacent law.
- [x] **L4 — operator identification** (`ConstrainedProlateOperatorIdentification.lean`,
  6 theorems, axiom-clean): square-summability ⇒ `Memℓp _ 2`; the real `lp 2` inner product as
  coordinate series; no secular pole meets the gap; the exact eigenvector is a genuine `ℓ²`
  vector, orthogonal to the constraint vector in `lp 2`, and satisfies the weak compressed
  eigen-equation `Σ d_jv_jw_j = μ_0·Σ v_jw_j` against every `ℓ²` test vector annihilated by the
  constraint (forward direction, coordinates (13)/(14)); conversely any nonzero square-summable
  span-form eigen-system solution in the gap with the constraint forces `F(μ) = 0`
  (`infiniteSecular_eq_zero_of_constrained_eigen`) — the constrained spectrum in `(d_0,d_1)` is
  exactly the secular root set.  (Interlacing `d_k ≤ μ_k ≤ d_{k+1}` at every depth is already
  the bracket theorem of L3b.)
- [x] **L5 — true-operator Bessel side** (`ConstrainedProlateBesselBound.lean`, 9 theorems,
  axiom-clean): `‖evenCentralIndicator a‖² = 2a` exactly; the true constraint coordinate
  `evenProlateConstraintCoord a n = ⟨1_[-a,a], e_n⟩` with its integral identity
  `= ∫_{-a}^a e_n` (card 1 eq (1)'s pairing form); the nonzero signed modes are orthonormal;
  Bessel `Σ_n ‖ℓ_n(a)‖² ≤ 2a` (card 1 eq (2)) + summability, in the eventual-aperture forms
  matching the exact transfer theorems' `hsum`/`hbessel`; and the injective-subfamily version
  for the parity/`4j` renumberings L9 will use.  Still open from the original L5 scope: the
  eigenvalue-evaluation identity `ℓ_j = χ_j e_j(0)` (needs pointwise mode evaluation — part of
  the L6/L7 analytic layer).
  Original scope: from the existing concrete operator layer
  (`ConstrainedProlateOperator`/`SignedSpectrum`): the evaluation identity `ℓ_j = χ_j e_j(0)`
  (card 1 eq (1)) and the Bessel bound `Σ_j ℓ_j² ≤ 2λ` (card 1 eq (2)).  Discharges hypothesis
  (S5) of L1 for the true operator.
  Design: `ℓ_j` is `inner (evenProlateSignedMode a j) (evenCentralIndicator a)` (both live in
  `evenSubspace` over ℂ; take real parts / norms as the file's conventions dictate).  The modes
  satisfy `evenProlateSignedMode_orthogonal_of_ne` and `evenProlateSignedMode_norm_zero_or_one`
  — mathlib's `Orthonormal` needs norm exactly 1, so restrict Bessel to the norm-one subfamily
  (the norm-zero modes have `ℓ_j = 0` and contribute nothing): either build the subtype
  orthonormal family and apply `Orthonormal.tsum_inner_products_le`, or prove the Finset form
  `Σ_{j∈s} ⟨e_j, χ⟩² ≤ ‖χ‖²` directly by expanding `0 ≤ ‖χ − Σ proj‖²` and pass to the tsum.
  `‖evenCentralIndicator a‖² = 2a` should be in/near `ConstrainedProlateOperator`
  (`evenCentralIndicator` section).  Deliverable: `Σ' j, ℓ_j(a)² ≤ 2a`, matching L1's
  `hbessel` with `lam := a`.
- [x] **L6c — the minimal leakage contract** (`ConstrainedProlateLeakageStructure.lean`,
  16 theorems, axiom-clean).  Isolates exactly what the transfer theorems need, as the
  `FuchsEnvelope D e` structure: step-four ladder `e(j+1) = e j + 4` (covers `4j` AND `4j+2`),
  `D ≥ 0`, `D` monotone in the index, and a two-sided fixed-index envelope
  `fuchsRate c_j (e j) λ ≤ D λ j ≤ fuchsRate C_j (e j) λ` eventually, with `0 < c_j, C_j`
  UNRELATED across indices.  KEY SIMPLIFICATION: monotonicity supplies the ordered head and the
  floor outright (the greedy singular values are antitone, so `1−χ²` is monotone), so the sharp
  asymptotic is never needed — only a two-sided envelope at each fixed index.  Derived:
  `lt_succ`, `ratio_tendsto_zero` (λ⁻⁸), `tail_tendsto_zero` (λ⁻⁷), `first_struct`,
  `depth_struct k`; then EVERY constrained law as a `FuchsEnvelope` method — `ccm_ground_ratio`
  (8/11), `ccm_gap_ratio` (3/11), `ccm_spectralGap_eventually`, `ccm_negativeSector_ratio`
  (8/13), `ccm_negativeSector_gap_ratio` (5/13), `ccm_depth_ratio` (θ_k at every depth).
  `fuchsEnvelope_fuchsRate` checks the model family is enveloped.
  **L6 is now reduced to a single concrete obligation**: exhibit a `FuchsEnvelope` for the true
  leakage `D λ j = 1 − χ_{e j}(λ)²`, i.e. prove two-sided fixed-index bounds (L6a upper via
  Hermite trial functions, L6b lower via min–max) plus antitonicity of the concentration values
  (already available as `evenProlateConcentrationValue_antitone`).
- [x] **L6c' — clock generalization** (`ConstrainedProlateClockEnvelope.lean`, 16 theorems,
  axiom-clean).  The Gaussian factor is inert: every ratio the transfer forms cancels the factor
  common to all indices.  `clockRate E A n λ = A·λ^(2n+1)·E λ` and `ClockEnvelope D e E` assume
  NOTHING about the clock `E` beyond eventual positivity; all five structural facts and all
  seven CCM capstones are reproved over it, and `FuchsEnvelope.toClockEnvelope` exhibits the
  Gaussian as the special case.  WHY THIS MATTERS: the exponential produced by this project's
  Fourier normalization has not been verified to be `e^(−4πλ²)`, so hard-coding it could have
  made the L6 contract unsatisfiable for the true operator.  The contract now depends only on
  the polynomial ladder, which is normalization-independent.
- [ ] **L6a/L6b — the two-sided fixed-index envelope** for the true prolate eigenvalues
  `1−χ_n(λ)² ~ A_n λ^{2n+1} e^{−4πλ²}` (card 1 eq (8)).  Mountain: needs PSWF spectral theory +
  Bessel/WKB asymptotics; nothing in mathlib.
  TARGET (now fully precise, thanks to L6c/L6c'): construct a term of type
  `ClockEnvelope (fun lam j => 1 − evenProlateSignedValue lam (ν j) ^ 2) ν E`
  for the radial index maps `ν j = 4j` and `ν j = 4j+2` and SOME eventually positive clock `E`.
  Its five fields: `step` (arithmetic), `nonneg` (χ² ≤ 1, from `norm_evenTimeBandFourier_le`),
  `mono` — the modes are SIGNED greedy values, so route through `|sgVal|`: the signed spectrum
  file proves `ContinuousLinearMap.abs_sgVal n : |sgVal S n| = sgOrthSup S _ n`, and
  `CompactSelfAdjointEigenvalue.orthSup_antitone` gives antitonicity of the orth-sup; hence
  `sgVal²` is antitone and `1−sgVal²` is monotone (verify the exact `sgOrthSup` antitone name
  first) — and `lower`/`upper` = the two-sided envelope.
  So only `lower`/`upper` remain.  Sub-layers:
  L6a MECHANISM DONE (`ConstrainedProlateTrueLeakage.lean`, 5 theorems, axiom-clean):
  `evenProlateLeakageValue a n = 1 − evenProlateConcentrationValue a n` where the concentration
  value is literally `svVal (evenProlateConcentration a) n`, i.e. an `orthSup` — so
  `GreedyCourantFischer.le_orthSup_of_trial` applies verbatim.  Delivered:
  `le_evenProlateConcentrationValue_of_trial`, `evenProlateLeakageValue_le_of_trial`
  (leakage ≤ 1 − M), `inner_evenProlateConcentration_eq` (the concentration form IS the retained
  Fourier mass `‖Tₐf‖²`), `norm_evenProlateConcentration_ge_of_form` (Cauchy–Schwarz bridge from
  the form estimate to the operator bound), and the interface theorem
  `evenProlateLeakageValue_le_of_form_trial`:

```text
  V of dim > n,  ∀ f ∈ V, (1−ε)‖f‖² ≤ ‖Tₐ f‖²   ⟹   d_n(a) ≤ ε.
```

  ALSO NOTE: `nonneg` and `mono` of the ClockEnvelope contract are ALREADY THEOREMS for this
  family (`evenProlateLeakageValue_nonneg`, `evenProlateLeakageValue_monotone` in
  `ConstrainedProlateOperator`).  So of the five contract fields, only the two-sided ENVELOPE
  remains, and its upper half is now purely the analytic estimate below.
  L6a AGGREGATION DONE (`HTGeometry/OrthonormalTrialSpan.lean`, 2 theorems, axiom-clean):
  `finrank_span_orthonormal` (an orthonormal `Fin m`-family spans dimension exactly `m`, so it is
  an admissible Courant–Fischer trial space) and `norm_sq_apply_le_of_orthonormal_span`
  (`‖R (g k)‖ ≤ η` for each `k` ⟹ `‖R f‖² ≤ m·η²·‖f‖²` on the whole span, via Bessel +
  Chebyshev's sum inequality).  So an explicit family with small INDIVIDUAL defect now suffices;
  no uniformity over the span has to be proved by hand.

  ### L6a GAUSSIAN: **BUILT** (`HTGeometry/GaussianSchwartz.lean`, axiom-clean)

  The blocking object now exists.  `gaussianSchwartzReal : 𝓢(ℝ, ℝ)` and
  `gaussianSchwartz : 𝓢(ℝ, ℂ)` for `x ↦ exp(−πx²)`.  The `decay'` field is discharged by:
  `exists_poly_iteratedDeriv_gaussReal` (every iterated derivative is a polynomial multiple of
  the Gaussian — induction via `hasDerivAt_poly_mul_gaussReal`, `p ↦ p' − C(2π)·X·p`),
  `abs_pow_two_mul_gaussReal_le` (`|x|^{2j} e^{−πx²} ≤ j!/π^j`, from a SINGLE term of the
  exponential series via `Real.pow_div_factorial_le_exp` — no limits needed), and
  `exists_bound_poly_mul_gaussReal` (polynomial induction).  Complex version via
  `Complex.ofRealLI.norm_iteratedFDeriv_comp_left` (isometry preserves derivative norms).

  Then the payoff chain, all proved:
  * `fourierIntegral_gaussianSchwartz` — `𝓕 (e^{−πx²}) = e^{−πx²}` pointwise (`b = 1` case of
    `fourier_gaussian_pi`).
  * `fourier_gaussianSchwartz` — the same as Schwartz maps.
  * **`fourier_gaussianSchwartz_toLp : 𝓕 (gaussianSchwartz.toLp 2) = gaussianSchwartz.toLp 2`**
    — the Gaussian's `L²` class is Fourier-invariant, via `SchwartzMap.toLp_fourier_eq`.
    Since the project's `fourierUnitary` IS `Lp.fourierTransformₗᵢ`, this is directly usable.

  ### L6a TAIL: **BUILT** (`HTGeometry/GaussianTailBound.lean`, axiom-clean)

  `integral_Ioi_gauss_sq_le (ha : 0 < a) : ∫_{Ioi a} e^{−2πx²} ≤ e^{−2πa²}/(4πa)` — an EXPLICIT
  exponentially-small tail, proved by `1 ≤ x/a` on `x ≥ a` plus the exact first moment
  `integral_Ioi_id_mul_gauss : ∫_{Ioi a} x e^{−2πx²} = e^{−2πa²}/(4π)` (antiderivative
  `−e^{−2πx²}/(4π)`, via `integral_Ioi_of_hasDerivAt_of_tendsto`).  Also
  `tendsto_integral_Ioi_gauss_sq` (tail → 0).  NOTE the exponent: the L² mass of the Gaussian
  `e^{−πx²}` involves `e^{−2πx²}`, so the tail is `e^{−2πa²}` — this is the clock, and is exactly
  why `ClockEnvelope` was generalized off the hard-coded `e^{−4πλ²}`.

  REMAINING for the L6a envelope: dilate/translate to the aperture scale, truncate to `[−a,a]`,
  assemble `n+1` near-orthonormal such functions,
  feed `OrthonormalTrialSpan.norm_sq_apply_le_of_orthonormal_span`, then
  `evenProlateLeakageValue_le_of_form_trial`.  Higher `n` needs `𝓕 h_n = (−i)^n h_n`, provable
  by induction with the creation operator `(x − d/dx)` reusing the polynomial induction above.

  ### Original sub-plan (findings verified 2026-07-18)

  The project's `fourierUnitary` is *definitionally* `MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ`
  (`SoninL2Model.lean:85`).  Mathlib therefore already supplies the bridge:

  * `SchwartzMap.toLp_fourier_eq (f : 𝓢(E,F)) : 𝓕 (f.toLp 2) = (𝓕 f).toLp 2`
    (`Mathlib/Analysis/Fourier/LpSpace.lean:98`) — transports a pointwise Fourier identity for a
    Schwartz function to the `L²` class, i.e. to `fourierUnitary`.
  * `fourier_gaussian_pi (hb : 0 < b.re) : 𝓕 (fun x ↦ cexp (-π*b*x^2))
       = fun t ↦ 1/b^(1/2) * cexp (-π/b*t^2)`
    (`Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean:230`).  At `b = 1` this is
    exactly `𝓕 (exp (-π x²)) = exp (-π x²)`: the Gaussian is a Fourier fixed point.
    (Note `𝓕` is the `e^{-2πixξ}` convention; the Gaussian is even so the project's sign
    convention is immaterial — but check evenness is used, not assumed.)

  ROUTE IS FORCED (searched 2026-07-18): `Mathlib/Analysis/Fourier/LpSpace.lean` contains **no**
  `MemLp`/`Integrable` bridge — there is no lemma saying the `L²` Fourier transform agrees a.e.
  with `Real.fourierIntegral` on `L¹ ∩ L²`.  The ONLY available passage from a pointwise Fourier
  identity to `fourierUnitary` is `SchwartzMap.toLp_fourier_eq`.  So constructing the Gaussian as
  a `SchwartzMap` is unavoidable, not merely convenient.

  The concrete obligation is the `decay'` field:
```text
  decay' : ∀ k n : ℕ, ∃ C, ∀ x, ‖x‖^k * ‖iteratedFDeriv ℝ n (fun x => cexp (-π*x^2)) x‖ ≤ C
```
  (`SchwartzSpace/Basic.lean:84`).  The `iteratedFDeriv` of the Gaussian is
  (Hermite polynomial)·(Gaussian), so the induction that produces those derivatives is the same
  induction that produces the Hermite functions — build them together, not separately.
  Useful precedents for the `decay'` pattern: `SchwartzSpace/Basic.lean:566` and `:600`.

  GAP CONFIRMED EXHAUSTIVELY (searched from both sides 2026-07-18): no Gaussian `SchwartzMap`
  anywhere in mathlib (searched `Mathlib` for `Schwartz.*[Gg]aussian`, for files mentioning both
  a Gaussian expression and `SchwartzMap`, and `NumberTheory/` for `SchwartzMap` — all empty);
  and NO Fourier relation in this project's own Hermite files
  (`HermiteOscillatorEigen`, `SpurHermite`, `HermiteTwoTerm`, `ScaledHermiteContradiction`,
  `XiGuinandWeilFiniteHermiteCriterion` contain no `fourier`), nor any Gaussian in
  `SoninL2Model`.  Nothing to reuse from either direction: the object must be built.

  USEFUL PATTERN FOUND: `HasCompactSupport.toSchwartzMap` (`SchwartzSpace/Basic.lean:559`) shows
  the idiom for discharging `decay'` — but it does NOT apply here, because the trial estimate
  needs the *untruncated* Gaussian's Fourier identity (the truncated one is not even smooth).
  The `decay'` proof therefore needs a genuine bound on `iteratedFDeriv ℝ n` of the Gaussian;
  in one real dimension, route it through `iteratedDeriv` (Hermite polynomial × Gaussian) and the
  `norm_iteratedFDeriv`/`iteratedDeriv` comparison, then `‖x‖^k · poly · e^{−πx²}` bounded.

  Legacy note: mathlib has **no** Gaussian as a `SchwartzMap` (no `gaussianSchwartz`,
  nothing Schwartz-shaped in `SpecialFunctions/Gaussian/`).  So the one construction to build is

```text
  gaussianSchwartz : 𝓢(ℝ, ℂ),  gaussianSchwartz x = cexp (-π * x^2)
```

  i.e. the Schwartz seminorm bounds `‖x‖^k * ‖iteratedDeriv n f x‖` bounded — the derivatives are
  (Hermite polynomial)·(Gaussian), so this is where `Polynomial.hermite` and
  `HermiteOscillatorEigen.hermiteFun` enter.  Once `gaussianSchwartz` exists:
  `fourierUnitary (gaussianSchwartz.toLp 2) = gaussianSchwartz.toLp 2`, giving the `n = 0` trial
  function; higher `n` needs the Hermite-function eigenrelation `𝓕 h_n = (-i)^n h_n`, provable by
  induction using the creation operator `(x - d/dx)` — also not in mathlib.
  Then: truncate to `[-a,a]`, bound the Gaussian tail (`∫_{|x|>a} e^{-2πx²}`) to get the
  individual defect `η`, feed `norm_sq_apply_le_of_orthonormal_span`, then
  `evenProlateLeakageValue_le_of_form_trial`.

  Superseded note: exhibit, for each fixed `n`, an `(n+1)`-dimensional subspace
  of aperture-supported even functions with concentration deficit `ε_n(a)` of the right size —
  variational, Hermite trial functions against the leakage form
  `⟨(I−T²)f, f⟩ = ‖f‖² − ‖Tf‖²`; needs Hermite functions as Fourier eigenfunctions
  (mathlib: `Polynomial.hermite` exists; Gaussian Fourier transform exists —
  `fourierIntegral_gaussian`; the Hermite-function eigenrelation must be built, seed
  `HermiteOscillatorEigen`) plus Gaussian tail integrals.
  L6b CORE DONE (`HTGeometry/GreedyCourantFischer.lean`, 2 theorems, axiom-clean):
  `exists_mem_ne_zero_orthogonal_of_finrank_lt` (a subspace of dimension > n contains a nonzero
  vector orthogonal to any n prescribed vectors — the n test functionals cannot be jointly
  injective on it) and `le_orthSup_of_trial` (if `S` is bounded below by `M` on a trial subspace
  of dimension > n then `M ≤ orthSup S v n`).  This is the min–max input for bounding prolate
  concentration from below by an explicit trial space, independent of which trial space.
  What L6b still needs: the concentrated trial space itself (n+1 truncated Hermite functions)
  and the passage `orthSup → sgVal` for the signed family.
  Superseded design note:
  `svVal S n ≤ M` whenever there is an `(n+1)`-dimensional `V` with `‖S x‖ ≤ M‖x‖` on `V`… —
  more precisely the standard direction available from `norm_apply_le_of_orth` plus a dimension
  count showing any `(n+1)`-dim `V` meets `(span of the first n svVecs)^⊥` nontrivially.
  `GreedySingularValues` already has `norm_apply_le_of_orth`, `svVal_antitone`,
  `inner_svVec_svVec_of_ne`, `isGreedyStep_svVec`.
  Prerequisite shared with L7: the mode-numbering identification (positive signed subsequence
  ↔ `4j` prolate modes) — the open problem named in `ConstrainedProlateSignedSpectrum`.
- [ ] **L7 — prolate-to-Hermite limits** `ℓ_j(λ) → a_j` (card 1 eq (10), card 2 eq (17), card 3
  eq (3)).  Mountain: Hermite eigenfunction theory (`HermiteOscillatorEigen` is the seed).
  ATTACK: route through the L5 integral identity
  `ℓ_j(λ) = ∫_{-λ}^{λ} e_j = ⟨1_{[-λ,λ]}, e_j⟩` (`evenProlateConstraintCoord_eq_integral`);
  the evaluation identity `ℓ_j = χ_j e_j(0)` (card 1 eq (1)) follows from the eigen-equation
  evaluated at 0 once modes have continuous representatives.  The limit needs: mode convergence
  `e_j(λ·) → h_j` in `L²` (operator-norm convergence of `T_λ` to the Hermite oscillator
  resolvent after scaling — seed `prolateSLAction_sqrtScale_tendsto` in `FuchsProlateScale`,
  which already proves the pointwise Sturm–Liouville action convergence) + the Hermite values
  `h_{4j}(0)` (algebra already in `ConstrainedProlateHermiteContrast`).
- [ ] **L8 — radial/Dunster layer** (cards 4–6): uniform Bessel-envelope expansion, weak
  convergence `ν_λ → ν_∞` (card 5 eq (4)), off-diagonal vanishing (card 5 eq (23)), weighted
  projective convergence (card 6 eq (3)), high-radial BV bound (card 4 eq (8a)).  Mountain.
- [ ] **L9 — assembly**: each card's headline theorem stated and proved in its own form;
  update all six cards to stage 3 (`3-formalized`) once their statements are hypothesis-free.

## Status log

- 2026-07-18 (session A): L0 completed through `RadialLeakageArcsineMeasure`,
  `ArithmeticDilationProjectiveLimit`, `LadderAdjacentScaleSeparation` (14 theorems, axiom-clean).
- 2026-07-18 (session B, this card created): L1 in progress —
  `ConstrainedProlateInfiniteSecular.lean`.
- 2026-07-18 (session B, cont.): L1 complete (`ConstrainedProlateInfiniteSecular` +
  `ConstrainedProlateFuchsModelTransfer`); L2a banked (`ConstrainedProlateSecularVector`);
  L3 banked (`ConstrainedProlateParityExactTransfer` — card 2 Fuchs-model complete);
  L3b complete (`ConstrainedProlateDepthSecular` + `ConstrainedProlateLadderExactTransfer` —
  card 3 eqs (8),(9) for exact roots, Fuchs-model complete); L5 banked
  (`ConstrainedProlateBesselBound` — true-operator Bessel bound `Σ‖ℓ_n(a)‖² ≤ 2a`,
  discharging the `hsum`/`hbessel` hypotheses of every exact transfer theorem); L2 completed
  (`ConstrainedProlateEigenvectorAngle` — head-defect collapse, eq (4) projective); L4 banked
  (`ConstrainedProlateOperatorIdentification` — both directions of the operator/secular
  equivalence on `lp 2`).  All modules umbrella-wired and
  axiom-clean.  Next: L2b (eigenvector normalized distance, card 1 eq (4)); L4 (lp2 operator
  identification); L5 (true-operator Bessel bound + evaluation identity from
  `ConstrainedProlateOperator`/`SignedSpectrum`); then L6/L7 mountains.

## Working rules (carry across sessions)

- One lake build at a time, foreground, `nice -n 19`, `LEAN_NUM_THREADS=2`; batch edits before
  building; verify every mathlib name in a scratch file first.
- After each module: `#print axioms` in scratch, umbrella import in `RHTower.lean`
  (or `HTGeometry.lean` for reusable analysis), `formal_tools.py index`, lint check,
  card Lean-decision + gates update, tick the layer here.
- Dead routes and design decisions land in this card, not in memory.
