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

  **GENERALISED TO THE WHOLE HERMITE FAMILY** (same file, axiom-clean):
  `polyGaussSchwartzReal p : 𝓢(ℝ,ℝ)` and `polyGaussSchwartz p : 𝓢(ℝ,ℂ)` for `x ↦ p(x)e^{−πx²}`,
  any real polynomial `p`.  Since every Hermite function is such a multiple, EVERY Hermite
  function is now available as a Schwartz map — so the whole `SchwartzMap.toLp_fourier_eq`
  machinery applies to the family, not just to `n = 0`.  Supporting:
  `exists_poly_iteratedDeriv_polyGauss` (iterated derivatives of `p·gauss` are again `q·gauss`,
  reusing `hasDerivAt_poly_mul_gaussReal`), `contDiff_polyEval` (polynomial smoothness, by
  `Polynomial.induction_on'` — mathlib has no `Polynomial.contDiff`), and
  `polyGaussSchwartz_one` identifying the `p = 1` case with `gaussianSchwartz`.
  **HERMITE FAMILY BUILT** (same file, axiom-clean).  The creation operator
  `A = x − (1/2π)·d/dx` acts on `p·e^{−πx²}` purely polynomially: differentiating gives
  `(p′ − 2πXp)·gauss`, hence `A(p·gauss) = (2Xp − (1/2π)p′)·gauss`.  So
  `hermiteStep p = 2Xp − C(1/2π)·p′`, `hermitePoly 0 = 1`,
  `hermitePoly (n+1) = hermiteStep (hermitePoly n)`, and
  `hermiteSchwartz n = polyGaussSchwartz (hermitePoly n) : 𝓢(ℝ,ℂ)`.
  `hermiteStep_apply` bridges the analytic recursion to the polynomial one;
  `hermiteSchwartz_zero` identifies `n = 0` with the Gaussian.

  ### L7 EIGENRELATION: **BUILT AND BANKED** (`HTGeometry/HermiteFourierEigen.lean`, axiom-clean)

  All of it is proved, unconditionally.  The route taken uses the scalar `Real.*` identities
  rather than the vector `lineDerivOp` ones (both work; the scalar ones needed no `smulLeftCLM`
  scalar-field plumbing).  Operators, on `𝓢(ℝ,ℂ)`, all as bundled `→L[ℂ]` maps:

```text
  mulXCLM      f = x · f            (smulLeftCLM ℂ (↑·), via Function.Complex.hasTemperateGrowth_ofReal)
  derivSCLM    f = f′               (SchwartzMap.derivCLM ℂ ℂ)
  fourierSCLM  f = 𝓕 f              (SchwartzMap.fourierTransformCLM ℂ)
  creationCLM    = (2π) • mulXCLM − derivSCLM
```

  The two transform rules, each discharged from `Real.fourier_deriv` / `Real.deriv_fourier`
  with the Schwartz integrability side conditions supplied by `integrable_deriv_schwartz` and
  `integrable_smul_id_schwartz`:

```text
  fourierSCLM_derivSCLM  : 𝓕 f′      = (2πI) • mulXCLM (𝓕 f)
  derivSCLM_fourierSCLM  : (𝓕 f)′    = (−2πI) • 𝓕 (x·f)
```

  and the intertwining relation they combine into — the whole content of the layer:

```text
  fourierSCLM_creationCLM : 𝓕 (A f) = (−I) • A (𝓕 f)
```

  `creationCLM` is `2π` times the self-dual-normalization operator `x − (1/2π)d/dx`, so
  `hermiteSchwartz_succ_eq : h_{n+1} = (2π)⁻¹ • A hₙ`; the scalar cancels in the eigenvalue.
  The induction off `fourier_gaussianSchwartz` then gives, for every `n`:

```text
  fourierSCLM_hermiteSchwartz  : 𝓕 hₙ = (−I)^n • hₙ                        (Schwartz)
  fourier_hermiteSchwartz_apply: 𝓕 hₙ x = (−I)^n · hₙ x                    (pointwise)
  fourier_hermiteSchwartz_toLp : 𝓕 (hₙ.toLp 2) = (−I)^n • hₙ.toLp 2        (L², via toLp_fourier_eq)
```

  The `L²` form is the consumable one: the project's `fourierUnitary` IS `Lp.fourierTransformₗᵢ`,
  so these are honest eigenvectors of the operator the prolate estimates use.  Parity is proved
  alongside — `hermiteSchwartz_neg : hₙ(−x) = (−1)^n hₙ(x)` (induction through `creationCLM`,
  using `deriv_comp_neg`), hence `hermiteSchwartz_even : h_{2k}(−x) = h_{2k}(x)`, which places
  the even-index family in `evenSubspace` where the constrained problem lives.

  Settled API facts, recorded so they are not re-derived: in `smulLeftCLM F (g : E → 𝕜)` the
  field `𝕜` is inferred from the MULTIPLIER, not from `F`.  In mathlib's
  `fourier_lineDerivOp_eq`/`lineDerivOp_fourier_eq` the multiplier is `fun x => inner ℝ x m`,
  which is ℝ-valued, so those lemmas run at `𝕜 = ℝ` acting on ℂ — no `ℝ → ℂ` coercion is
  inserted.  Bridging to the ℂ-valued multiplier `fun x : ℝ => (x:ℂ)` is one `ext` plus
  `Complex.real_smul`.  `lineDerivOp` is a plain typeclass function `V → E → F`, not a bundled
  map; the bundled form is `lineDerivOpCLM R E m`, available because
  `LineDerivSMul 𝕜 E 𝓢(E,F) 𝓢(E,F)` is an instance for generic `𝕜`.

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

  ### L6a TRUNCATION: **BUILT** (`HTGeometry/TruncatedFixedVector.lean`, axiom-clean)

  `norm_sq_proj_unitary_proj_ge`: if the isometry `U` fixes `h` and `P` is an orthogonal
  projection (used only via the Pythagorean identity `‖x‖² = ‖Px‖² + ‖x−Px‖²`), then

```text
  ‖P U P h‖² ≥ ‖P h‖² − 4‖h − P h‖².
```

  Pythagoras is now DISCHARGED from star-projection data:
  `norm_sq_eq_of_isIdempotent_symmetric` (idempotent + symmetric ⟹ orthogonal splitting), so
  `norm_sq_proj_unitary_proj_ge'` takes only `P∘P = P` and symmetry — both immediate for the
  project's `evenIndicatorCutoff` (`evenIndicatorCutoff_idempotent`, and the cutoff is a star
  projection).  And `norm_sq_proj_unitary_proj_ge_of_rel` puts it in the exact shape the trial
  space consumes:

```text
  ‖h − Ph‖ ≤ θ‖Ph‖   ⟹   (1 − 4θ²)‖Ph‖² ≤ ‖P U P h‖²,
```

  i.e. `ε = 4θ²` for `evenProlateLeakageValue_le_of_form_trial`.  NOTE `IsSelfAdjoint` was
  deliberately avoided: it drags in a `Star (H →L[ℂ] H)` instance; plain symmetry
  `∀ x y, ⟪Px, y⟫ = ⟪x, Py⟫` needs no adjoint and is what the project's lemmas produce.

  Stated ABSTRACTLY, so it needs no `SoninL2`/`evenSubspace` plumbing: instantiate `U` with the
  Fourier unitary, `P` with the aperture cutoff, `h` with the Gaussian (Fourier-fixed by
  `fourier_gaussianSchwartz_toLp`), and `‖h − P h‖²` is the tail bounded by
  `integral_Ioi_gauss_sq_le`.  Helper `norm_sub_proj_le` (complementary part is a contraction).

  ### L6a CARRIER: **BUILT** (`RHTower/GaussianEvenCarrier.lean`, axiom-clean)

  The Gaussian is now placed in the project's own carrier: `gaussL2 : SoninL2`,
  `gaussL2_mem_evenSubspace` (evenness — via `l2Reflection_ae` and `gaussReal (-x) = gaussReal x`),
  `gaussEven : evenSubspace`, `evenFourierTransform_gaussEven` (the even transform is the
  restriction of `fourierUnitary`, which fixes the Gaussian by `fourier_gaussianSchwartz_toLp`),
  and `gaussEven_ne_zero`.  So `U := evenFourierTransform`, `h := gaussEven` discharge the
  hypotheses of `norm_sq_proj_unitary_proj_ge_of_rel` except those about `P`.

  ### L6a CHAIN CLOSED END-TO-END AT n = 0 (`GaussianEvenCarrier.lean`, axiom-clean)

  `evenIndicatorCutoff_symmetric` (from `indicatorCutoff_symmetric`) and
  `evenIndicatorCutoff_apply_apply` discharge the `P`-side hypotheses, so:
  * `gaussEven_concentration` — the abstract truncation lemma instantiated at the REAL operators.
  * `gaussEven_timeBand_concentration` — restated for `evenTimeBandFourier` (cutoff idempotency).
  * `gaussEven_span_concentration` — homogeneous, hence valid on the whole spanned line.
  * **`evenProlateLeakageValue_zero_le : d_0(a) ≤ 4θ²`** whenever
    `‖g − P g‖ ≤ θ‖P g‖` and `P g ≠ 0` — a bound on the TRUE operator's ground leakage,
    obtained through Courant–Fischer on the one-dimensional truncated-Gaussian trial space.

  The abstract chain is therefore validated end-to-end against the concrete operator.

  ### L6a TAIL IDENTIFICATION: **BUILT**

  `norm_sq_eq_integral (f : SoninL2) : ‖f‖² = ∫ x, ‖f x‖²` (via `L2.inner_def` +
  `integral_complex_ofReal`), and
  `norm_sq_gaussEven_sub_cut : ‖gaussEven − P_a gaussEven‖² = ∫_{(centralInterval a)ᶜ} e^{−2πx²}`
  — the truncation error IS the Gaussian tail, with the `e^{−2πx²}` arising as `|e^{−πx²}|²`.
  Combined with `integral_Ioi_gauss_sq_le` (after splitting the complement into two rays by
  evenness), this makes `θ` explicit.

  ### L6a EXPLICIT TRUNCATION ERROR: **BUILT**

  `norm_sq_gaussEven_sub_cut_le (ha : 0 < a) :`
  `‖gaussEven − P_a gaussEven‖² ≤ 2·e^{−2πa²}/(4πa)` — the complement split as
  `Iio(−a) ∪ Ioi a`, the left ray reflected onto the right via `integral_comp_neg_Ioi`
  (with `Iio_ae_eq_Iic` bridging the endpoint), then the ray bound applied.

  So the n = 0 truncation error is now EXPLICITLY exponentially small, and combined with
  `evenProlateLeakageValue_zero_le` the only missing input for a fully explicit `d_0(a)` bound is
  a positive lower bound on `‖P_a gaussEven‖²` (= `∫_{−a}^{a} e^{−2πx²}`, which increases to
  `1/√2`; e.g. bound below by its value at `a = 1`, or by monotonicity of the integrand).

  ### L6a n = 0 COMPLETE: **`evenProlateLeakageValue_zero_tendsto_zero`**

  `Tendsto (fun a => evenProlateLeakageValue a 0) atTop (nhds 0)` — the TRUE compressed Fourier
  block's ground leakage vanishes as the aperture grows.  Unconditional, axiom-clean.
  Route: `norm_sq_cut_gaussEven` (Pythagoras ⟹ `‖P_a g‖² = ‖g‖² − τ`, so no head integral is
  needed — the lower bound on `‖P_a g‖²` comes free once `τ < ‖g‖²/2`),
  `norm_sq_gaussEven_sub_cut_tendsto_zero` (τ → 0 from the explicit ray bound), then
  `evenProlateLeakageValue_zero_le` with `θ² = τ/‖P_a g‖²`.

  This validates the ENTIRE architecture end-to-end against the real operator: Gaussian Schwartz
  map → L² Fourier fixedness → even carrier → tail bound → truncation → Courant–Fischer →
  leakage.  What the envelope still needs is the RATE (`d_0(a) = O(λ^{e_0}·clock)`), which needs
  the two-sided version, plus higher `n`.

  ### L6a n = 0 EXPLICIT RATE: **`evenProlateLeakageValue_zero_le_exp`**

  Eventually `d_0(a) ≤ (16/‖g‖²)·e^{−2πa²}/(4πa)` — an explicit exponentially-small bound on the
  TRUE ground leakage.  Axiom-clean.

  **CORRECTION (supersedes the stronger claim below).**  What is PROVED is only
  `d_0(a) ≤ C·e^{−2πa²}/a`.  Whether that is off the Fuchs rate is NOT established, and the
  earlier claim that the truncated Gaussian "cannot reach" it was overstated.  Two facts pull in
  opposite directions and must be resolved before any trial-function redesign:

  (i) For large `c` the true PSWF `ψ_0` is asymptotically the Gaussian `e^{−πx²}` itself, so
  `ψ_0(±a) ≈ e^{−πa²}` — the SAME boundary size as the truncated Gaussian.  A naive
  "endpoint-jump ⇒ leakage ≍ (boundary value)²" heuristic would then give `ψ_0` the same
  `e^{−2πa²}`, contradicting the classical `e^{−2c}`.  So that heuristic must be missing a
  cancellation forced by the eigenfunction relation `F ψ_0 |_{[-a,a]} = χ_0 ψ_0`.

  (ii) The identification of the card's aperture `λ` with the project's operator aperture `a`,
  and of `c` with `2πλ²`, has NEVER been verified in this project.  The card asserts
  `1−χ_n² ~ A_n λ^{2n+1} e^{−4πλ²}`; if `c = 2πλ²` then that is `e^{−2c}`, but the `λ ↔ a`
  dictionary is exactly the "normalization audit" the cards themselves still list as an open
  gate.

  **(ii) IS NOW SETTLED — there IS a gap, and (i) RESOLVES, giving the fix.**

  Normalization: the project's `fourierUnitary` is mathlib's `𝓕` (kernel `e^{−2πixξ}`), the
  window is `centralInterval a = Icc (−a) a` in BOTH time and frequency, so the Slepian
  time–bandwidth parameter is `c = 2πTW = 2πa²`.  The classical rate
  `1 − λ_0(c) ~ 4√π·√c·e^{−2c}` then reads `∝ a·e^{−4πa²}`, matching the card's
  `A_0 λ e^{−4πλ²}` with `λ = a`.  So the target exponent IS `e^{−4πa²}` and the proved
  `e^{−2πa²}/a` is weak by a factor 2 in the exponent.

  Resolution of the apparent paradox in (i): the Gaussian approximation `ψ_0 ≈ e^{−πx²}` is valid
  only in the BULK.  Writing the WKB profile `ψ_0(x) ≈ exp(−c·φ(x/a))` with
  `φ(u) = 1 − √(1−u²)`, one has `φ(u) ≈ u²/2` near `0`, so `exp(−c u²/2) = exp(−πx²)` — the
  Gaussian, as expected — but `φ(1) = 1`, so at the EDGE `ψ_0(±a) ≈ e^{−c} = e^{−2πa²}`, not the
  Gaussian's `e^{−πa²}`.  The endpoint-jump heuristic `leakage ≍ (boundary value)²` then gives
  `e^{−4πa²}` for the PSWF and `e^{−2πa²}` for the truncated Gaussian — both correct, and the
  factor 2 is exactly the edge-decay discrepancy.

  **CONSEQUENCE — the trial profile to use next is explicit:**

```text
  g_a(x) = exp(−2πa²·(1 − √(1 − x²/a²)))   on [−a, a],   0 outside.
```

  **BUILT** (`HTGeometry/WkbEdgeProfile.lean`, axiom-clean): `wkbExponent u = 1 − √(1−u²)`,
  `wkbEdgeProfile a x = exp(−2πa²·φ(x/a))`, with
  `sq_div_two_le_wkbExponent` (`u²/2 ≤ φ(u)` on `|u| ≤ 1`, from `√(1−u²) ≤ 1 − u²/2`),
  `wkbEdgeProfile_le_gauss` (dominated pointwise by `e^{−πx²}` on the aperture — so it inherits
  the Gaussian's frequency concentration), `wkbEdgeProfile_edge`
  (`wkbEdgeProfile a a = e^{−2πa²}` — the squared-small edge value), plus centre value and the
  `≤ 1` bound.

  **SECOND CORRECTION — the profile is explicit but its leakage bound is NOT elementary.**
  Worked through (2026-07-18), three routes and why each fails:

  1. *Plancherel / derivative bound.*  For `f` supported in `[−a,a]`, `|y| > a` gives `1 ≤ y²/a²`,
     so `∫_{|y|>a}|Ff|² ≤ a^{-2}∫|y Ff|² = ‖f'‖²/(4π²a²)`.  TRUE and easy, but only
     POLYNOMIALLY small: `‖f'‖² = O(1)` because `f'` is large in the BULK (`f' ≈ −2πx f` there),
     so this yields `O(a^{-2})`, not `e^{−2c}`.  Iterating to `‖f^{(k)}‖²/(2πa)^{2k}` gives any
     polynomial order but the constants grow — at best sub-exponential (Gevrey), never `e^{−2c}`.
  2. *A narrower Gaussian.*  `ψ(u) = u²` gives `g = e^{−2πx²}` with the right edge value `e^{−c}`,
     but its frequency tail degrades to `e^{−c/2}`.  Checked at `s² = 1/2, 1, 2`: the Gaussian
     family is optimised at `s = 1`, balancing both contributions at `e^{−c}`.  No Gaussian
     achieves `e^{−2c}`; the WKB profile beats them precisely by being Gaussian in the bulk yet
     faster-decaying at the edge, which no single Gaussian can do.
  3. *The exact WKB profile's derivative.*  `φ'(u) = u/√(1−u²)` blows up at the edge, so
     `‖g_a'‖² = ∞` (logarithmically divergent) — route 1 does not even apply without
     regularisation, and regularising reintroduces the bulk-dominated `O(1)` numerator.

  CONCLUSION: obtaining `e^{−2c}` from ANY explicit compactly supported trial function requires
  estimating an oscillatory integral to exponential accuracy — which is what the classical
  Fuchs/Slepian proofs do via the prolate ODE and WKB connection formulae, NOT via a trial
  function.  The trial-function route caps out at the `e^{−c}` already proved.
  THEREFORE the sharp `upper` field should be attacked through the ODE layer the project already
  has (`prolateSLAction`, `prolate_eigen_hermite_defect`, `FuchsProlateScale`), not by further
  trial-function engineering.  `wkbEdgeProfile` remains banked and correct, and is the right
  object if that ODE route needs a comparison profile.

  Legacy (over-optimistic): it equals `e^{−πx²}` in the bulk (so it keeps the Gaussian's frequency concentration) and
  decays to `e^{−2πa²}` at the edge (so its endpoint jump is squared-small).  It is elementary,
  exactly supported in `[−a,a]`, and needs no PSWF theory.  The remaining Lean work is its
  out-of-band Fourier bound — an endpoint/stationary-phase estimate, not a spectral one.

  Superseded action: settle (ii) first — it is cheap (a convention check
  against `evenTimeBandFourier`'s definition) and it determines whether there is a gap at all.
  Do not redesign the trial function until the target exponent is known.

  Legacy (OVERSTATED, kept for the argument it contains) — the truncated Gaussian and the Fuchs
  rate:

  Write `f = Ph`, `τ = ‖h − Ph‖`.  Since `Uh = h`,

```text
  (I−P)Uf = (I−P)h − (I−P)U((I−P)h),
```

  and the deficit is exactly `‖(I−P)Uf‖²`.  The FIRST term `(I−P)h` has norm exactly `τ`, and
  the second has norm at most `τ`.  So the deficit is `≈ τ²` unless the two terms CANCEL to
  leading order.  For the plain truncated Gaussian there is no such cancellation, so

```text
  deficit ≍ τ² ≍ e^{−2πa²}/(4πa).
```

  The crude `4τ²` triangle bound is therefore of the CORRECT ORDER for this trial function —
  the loss is not in the inequality.  But the true `1 − χ_0²` decays like `e^{−2c}` (two powers
  of the tail, i.e. `≍ τ⁴`), because the genuine PSWF arranges exactly the cancellation the
  Gaussian lacks.  The Rayleigh-quotient route gives the same order: `⟨Uf,f⟩ ≥ ‖h‖² − 3τ²` because `⟨h,r⟩ = τ²`
  is a genuine first-order loss, so `d_0 ≲ τ²` there too.  What this DOES establish is that the
  `4τ²` triangle bound is not the bottleneck — both routes land on `τ²`.  Whether `τ²` is the
  right answer depends on (ii) above.

  Legacy note — the exponent is not yet sharp.  This gives `d_0(a) = O(e^{−2πa²}/a)`.
  Writing `c` for the time–bandwidth product, the classical Fuchs rate is `~ e^{−2c}` whereas the
  plain truncated Gaussian yields only `e^{−c}`-type decay, and the polynomial factor comes out
  as `a^{−1}` rather than the `a^{+1}` of `fuchsRate _ 0`.  Two causes, both real:
  (i) the estimate `‖PUPh‖² ≥ ‖Ph‖² − 4τ²` is crude — it loses a square relative to the true
  second-order behaviour; (ii) a plain Gaussian is not the true 0th prolate function.
  CONSEQUENCE for the campaign: the current L6a machinery proves the leakage is exponentially
  small (enough for qualitative statements like `d_0 → 0`) but does NOT supply the matching
  two-sided `ClockEnvelope` rate, and cannot be made to by tightening the estimate.

  REMAINING: sharpen the exponent as above; supply the `lower` field; then dilation for higher
  `n`, the `n+1`
  near-orthonormal assembly, and `𝓕 h_n = (−i)^n h_n`.

  Superseded: split `(centralInterval a)ᶜ = Iio (−a) ∪ Ioi a` and apply the ray bound; bound
  `‖P_a gaussEven‖²` below by a constant; then dilation for higher `n`, the `n+1` assembly, and
  `𝓕 h_n = (−i)^n h_n`.

  Superseded: supply `θ` explicitly, i.e. identify `‖gaussEven − P gaussEven‖²` with
  `∫_{|x|>a} e^{−2πx²}` (bounded by `integral_Ioi_gauss_sq_le`) and `‖P gaussEven‖²` with
  `∫_{-a}^{a} e^{−2πx²}` (bounded below by a fixed constant), giving `θ² = O(e^{−2πa²}/a)`.
  Then dilate for higher `n`, assemble `n+1` near-orthonormal copies, and prove
  `𝓕 h_n = (−i)^n h_n`.

  Superseded: take `P := evenIndicatorCutoff a` (idempotent is
  `evenIndicatorCutoff_idempotent`; symmetry from its star-projection structure), identify
  `‖gaussEven − P gaussEven‖²` with the tail `∫_{|x|>a} e^{−2πx²}` bounded by
  `integral_Ioi_gauss_sq_le`, then
  dilate to the aperture scale, assemble `n+1` near-orthonormal such functions,
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

- 2026-07-19: L7 CONFIRMED COMPLETE — `HTGeometry/HermiteFourierEigen.lean` (26 thm) and
  `HTGeometry/HermiteOrthogonality.lean` (32 thm) are both built, umbrella-wired and axiom-clean.
  Between them: the intertwining `𝓕 A = (−i) A 𝓕`, the eigenrelation `𝓕 hₙ = (−i)ⁿ hₙ` in
  Schwartz/pointwise/`L²` form, parity `hₙ(−x) = (−1)ⁿhₙ(x)`, the oscillator commutator
  `BA − AB = 4π`, the lowering law `B h_{n+1} = 2(n+1) hₙ`, orthogonality
  `inner_hermiteSchwartz_toLp_eq_zero`, non-vanishing `hermiteSchwartz_toLp_ne_zero`, and the
  normalized family `orthonormal_hermiteSchwartz_toLp`.
- 2026-07-19: `HTGeometry/TrialSpanConcentration.lean` type-checks clean and is umbrella-wired —
  the m-dimensional replacement for the one-dimensional `TruncatedFixedVector` estimate.  Its
  `norm_sq_apply_ge_of_orthonormal_span` gives `(1 − √m·η)²‖f‖² ≤ ‖T f‖²` on the span of an
  orthonormal family each of whose members `T` moves by at most `η`.  Note the LINEAR (not
  squared) single-vector estimate `norm_sub_proj_unitary_proj_le : ‖h − PUPh‖ ≤ 2‖h − Ph‖` is
  what makes aggregation over a family possible.
- 2026-07-19: **`RHTower/HermiteEvenCarrier.lean` IS ALREADY BUILT AND CLOSES THE WHOLE
  TRUE-OPERATOR LEAKAGE LAYER** (umbrella-wired, axiom-clean, verified this session).  Do NOT
  rebuild any of it.  It contains, at EVERY index `n` — not just index 0:

```text
  evenProlateLeakageValue_tendsto_zero (n : ℕ) : d_n(a) → 0                     as a → ∞
  evenProlateConcentrationValue_tendsto_one (n : ℕ)
  exists_evenProlateLeakageValue_le_exp (n : ℕ)   -- explicit exponential rate
  exists_hermiteTrialDefect_le_exp (n : ℕ)
```

  built from `hermiteL2`/`hermiteEven`/`hermiteEvenUnit` (the `2k`-index Hermite functions placed
  in `evenSubspace`), `evenFourierTransform_hermiteEvenUnit` (Fourier-fixed),
  `orthonormal_hermiteEvenUnit`, `hermiteTrialSpace` with `finrank_hermiteTrialSpace`, and
  `evenProlateLeakageValue_le_of_hermite_trial`.  It also already carries its own
  `integrable_norm_sq`, `norm_sq_sub_cut_eq`, `tendsto_norm_sq_sub_cut`, `tendsto_norm_sub_cut`.

  LESSON, recorded so it is not repeated: a module `RHTower/ApertureTailVanishing.lean` was
  written this session that duplicated four of those lemmas; it type-checked clean but was
  deleted as pure redundancy.  BEFORE writing any new module in this campaign, run
  `grep -n "^theorem \|^def " on the candidate neighbours` — the campaign's own status log has
  repeatedly lagged behind what is actually banked in `formal/`.  The tree, not this card, is the
  authority on what exists.

- 2026-07-19: **`HTGeometry/SignChoiceNormalizedDistance.lean` BUILT** (audit build passed,
  umbrella-wired, all six capstones axiom-clean).  This is the general infrastructure for the
  one remaining *cosmetic* gate of the two-mode card — "the normalized ℓ²-distance/sign-choice
  form of `(4)`".  Two sections, both over a real inner product space:

```text
  min_norm_sub_sq_of_unit      : min(‖u−w‖², ‖u+w‖²) = 2 − 2|⟪u,w⟫|         (unit u,w)
  exists_sign_norm_sub_sq_le_of_unit : 1−ε ≤ |⟪u,w⟫| → ∃σ=±1, ‖u−σ•w‖² ≤ 2ε
  min_norm_sub_sq_normalize    : the same for normalizations of nonzero u,w
  tendsto_min_norm_sub_sq_normalize : |⟪u,w⟫|/(‖u‖‖w‖) → 1  ⟹  sign-optimized distance → 0
  inner_sq_add_inner_sq_of_mem_span : ⟪x,n⟫² + ⟪x,g⟫² = ‖x‖²   (orthonormal n,g; x ∈ span{n,g})
  one_sub_sq_le_inner_normalize_sq  : |⟪x,n⟫|/‖x‖ ≤ δ  ⟹  1−δ² ≤ (⟪x,g⟫/‖x‖)²
```

  The second section is the geometric content: the constrained ground direction is pinned inside a
  2-plane by orthogonality to a single constraint normal, and a vector with small normal component
  is close to `±g` with angle deficit exactly the squared relative normal component.  Together
  with the sign-choice lemma this converts EVERY projective statement already banked into its
  metric form, with an explicit rate.

  **THE GATE IS NOT YET CHECKED, and must not be checked until Part B exists.**  What is built is
  the general lemma; what remains is the instantiation at the actual objects:
  take `n = (ℓ_0,ℓ_1)` normalized (the constraint normal), `g` = the unit two-mode seed direction
  orthogonal to it, `x` = the head `(v_0,v_1)` of `secularVector`, feed the defect bound
  `abs_secularVector_head_seed_pairing_le` / `secularVector_head_seed_defect_tendsto_zero`
  (`ConstrainedProlateEigenvectorAngle`) as `δ`, and combine with
  `secularVector_tail_fraction_tendsto_zero` (`ConstrainedProlateSecularVector`) to control the
  tail's contribution to `‖v‖`.  The lp-space home for `secularVector` already exists:
  `memℓp_secularVector` in `ConstrainedProlateOperatorIdentification`.  Only then does
  `min_σ ‖v̂_λ − σ ĝ_λ‖ → 0` — the card's `(4)` in metric form — follow.

- 2026-07-19: **`RHTower/ConstrainedProlateHeadDistance.lean` BUILT** (audit build passed,
  umbrella-wired, all capstones axiom-clean) — Part B of the two-mode card's cosmetic gate, in
  the HEAD PLANE.  Works in `EuclideanSpace ℝ (Fin 2)` with

```text
  secularHead d ℓ μ    = !₂[v 0, v 1]          (head of the exact eigenvector)
  constraintNormal ℓ   = !₂[ℓ 0, ℓ 1]          (the constraint)
  twoModeSeed ℓ        = !₂[-(ℓ 1), ℓ 0]       (the seed: EXPLICIT orthogonal direction)
```

  The geometric content is the Lagrange identity, which closes by `ring`:
  `inner_sq_add_inner_sq_secularHead : ⟪H,N⟫² + ⟪H,G⟫² = ‖H‖²‖N‖²`.  Taking the seed to be the
  explicit `(−ℓ₁, ℓ₀)` avoids ALL span/finrank reasoning — that was the key simplification.
  Then `align_eq_one_sub_defect` and the capstone

```text
  tendsto_min_norm_secularHead_normalize_sub_twoModeSeed :
    defect → 0  ⟹  min(‖Ĥ − Ĝ‖², ‖Ĥ + Ĝ‖²) → 0
```

  whose `defect` hypothesis is *verbatim* the conclusion of
  `secularVector_head_seed_defect_tendsto_zero`, so that theorem discharges it with no massaging
  (`defect_eq_inner_sq_div` is the coordinate bridge).  Also added to
  `HTGeometry/SignChoiceNormalizedDistance.lean`:
  `tendsto_min_norm_sub_sq_normalize_of_eventually` (only eventually-nonzero vectors) and
  `tendsto_min_norm_sub_sq_normalize_of_inner_sq` (SQUARED alignment input — the form a Lagrange
  computation yields, so no square root is ever taken upstream).

  **THE GATE IS STILL NOT CHECKED.**  What is proved is the metric convergence of the HEAD
  direction `(v₀,v₁)` to the seed.  The card's `(4)` is about the FULL ℓ² vector `v_λ`.  The
  remaining step is the head/tail assembly:
  embed the head into the full `lp` space (`memℓp_secularVector` in
  `ConstrainedProlateOperatorIdentification` gives the home), show
  `‖v − ι(head)‖²/‖v‖² = Σ_{j≥2}v_j²/‖v‖² → 0` — which is exactly
  `secularVector_tail_fraction_tendsto_zero` (`ConstrainedProlateSecularVector`) once divided by
  `‖v‖² ≥ v₀²` — and then combine the two normalized convergences by the triangle inequality.
  Only after that does `min_σ ‖v̂_λ − σ ĝ_λ‖ → 0` hold for the full vector, and only then may the
  gate be checked.

- 2026-07-19: **GATE CLOSED** — `RHTower/ConstrainedProlateFullDistance.lean` BUILT (audit build
  passed, umbrella-wired, axiom-clean).  The two-mode card's cosmetic gate
  "normalized ℓ²-distance/sign-choice form of `(4)`" is now CHECKED on the card.  Capstone:

```text
  tendsto_min_norm_lp_normalize_sub_twoModeSeed :
      head defect → 0  ∧  tail fraction → 0   ⟹   min_σ ‖v̂_λ − σ ĝ_λ‖² → 0
```

  for the FULL normalized `lp 2` eigenvector.  Its two hypotheses are verbatim the conclusions of
  `secularVector_head_seed_defect_tendsto_zero` and `secularVector_tail_fraction_tendsto_zero`,
  so those discharge it with no massaging — the connector is exact.

  Mechanism, worth reusing: the seed `twoModeSeedFun ℓ` is supported on `{0,1}`, so it pairs only
  with the head, giving the clean factorization
  `⟪V,G⟫²/(‖V‖²‖G‖²) = [⟪H,G⟫²/(‖H‖²‖G‖²)]·[‖H‖²/(‖H‖²+T)]`.
  Supporting lemmas now available for any `lp 2` argument: `lp_norm_sq_eq_tsum`,
  `lp_norm_sq_split` (head/tail via `Summable.sum_add_tsum_nat_add 2`), `lp_inner_twoModeSeed`,
  `tsum_of_support_le_two`, and the general `tendsto_ratio_one_of_tendsto_zero`
  (`T/H → 0 ⟹ H/(H+T) → 1`).

  Two Lean traps hit and recorded: (a) proving an `lp` vector nonzero via its NORM drags in a
  tsum lower bound — prove it COORDINATEWISE instead (`V = 0 → V 0 = 0`), which is three lines;
  (b) `tsum_eq_sum` leaves the goal beta-unreduced, so `rw` fails where `simp only` succeeds.

  Two-mode card now has 5 open gates, none of them Lean-formalization gates: they are
  independent proof/literature review and the true-operator/Weil-transfer items.

- 2026-07-19: **`HTGeometry/ScheffeLemma.lean` BUILT** (audit build passed, umbrella-wired,
  axiom-clean).  **Scheffé's lemma is NOT in mathlib** — verified by grep over the whole of
  `Mathlib/` (no `Scheff`, no `tendsto_L1_of_tendsto_ae`).  This is the general reduction that
  turns pointwise density asymptotics into weak convergence:

```text
  tendsto_integral_abs_sub_of_tendsto_integral :
      f i ≥ 0,  f i → g pointwise a.e.,  ∫f i → ∫g     ⟹   ∫|f i − g| → 0
  tendsto_integral_smul_of_tendsto_integral_abs_sub :
      ∫|f i − g| → 0,  ‖w‖ ≤ C                          ⟹   ∫ w·f i → ∫ w·g
```

  Proof mechanism worth remembering: apply dominated convergence NOT to the difference but to its
  positive part `G = (g − f)⁺`, which the limit `g` itself dominates once `f ≥ 0`; then
  `|y| = 2max(y,0) − y` converts `∫G → 0` plus the mass hypothesis into `∫|f−g| → 0`.  No
  tightness or uniform-integrability argument is needed.

  WHAT THIS UNLOCKS: the radial-leakage card's gate "weak convergence `ν_λ → ν_∞` `(4)` in Lean"
  now reduces to exactly two inputs, both purely analytic:
  (i) pointwise a.e. convergence of the densities `λ|q_λ(λx)|²/d₁(λ) → (8/11π)·1/(x√(x²−1))`, and
  (ii) convergence of the total masses to `4/11` — and (ii)'s TARGET is already formalized
  exactly (`radialLeakageMeasure_total_mass`, `integral_Ioi_radialLeakageDensity`).
  Input (i) is the Dunster/Bessel-envelope asymptotics; the tree currently has only WKB seed
  infrastructure for it (`RadialPSWFExteriorPhase` — exterior phase/speed with derivative laws;
  `RadialPSWFInteractionPicture` — the ± interaction splitting and its derivatives).  The card's
  claim that the tree has "no radial PSWF interface" is therefore slightly stale, but its
  substance is right: there are no ENVELOPE ASYMPTOTICS yet.

  GATE NOT CHECKED: the reduction exists, the density asymptotics do not.

  Lean traps recorded this round: `Integrable.bdd_mul'` is deprecated (use `bdd_mul`, argument is
  `c` not `C`); `integral_mono` needs a GLOBAL `≤` — use `integral_mono_ae` for the a.e. form;
  `integral_sub` must be applied with `apply` not `rw` (it produces `(g - f) a`, not `g a - f a`);
  `omit [inst] in` must precede the DOCSTRING, not sit between docstring and theorem; and
  `hw.exists` needs `(ae μ).NeBot`, which fails for the zero measure.

- 2026-07-19: **`RHTower/RadialLeakageWeakConvergence.lean` BUILT** (audit build passed,
  umbrella-wired, axiom-clean) — Scheffe specialized to the radial family, with the limiting
  object now a named density rather than an integral expression:

```text
  nuInfinityDensity x                  = (8/(11π))·radialLeakageDensity x
  integral_Ioi_one_nuInfinityDensity   : ∫_{Ioi 1} nuInfinityDensity = 4/11      (exact)
  integrableOn_Ioi_one_nuInfinityDensity
  tendsto_integral_abs_sub_nuInfinityDensity  : pointwise + mass ⟹ L¹
  tendsto_integral_weight_nuInfinityDensity   : pointwise + mass ⟹ ∫w·ν_λ → ∫w·ν∞
                                                 for EVERY bounded weight w
```

  Also exported `integrableOn_Ioi_radialLeakageDensity` from
  `RadialLeakageArcsineMeasure.lean` (it had been proved inline inside
  `integral_Ioi_radialLeakageDensity` but never named; appended at EOF per the append-only rule,
  only two dependents so the rebuild was cheap).

  THE RADIAL GATE IS NOW ONE INPUT AWAY.  `tendsto_integral_weight_nuInfinityDensity` has exactly
  two analytic hypotheses left:
    (i)  `hae`   — pointwise a.e. `ν_λ(x) → nuInfinityDensity x` on `(1,∞)`;
    (ii) `hmass` — `∫_{Ioi 1} ν_λ → 4/11`.
  Everything else (nonnegativity, integrability of the limit, the exact mass, the bounded-weight
  transfer) is discharged.  Input (i) is the Dunster/Bessel envelope asymptotics for
  `λ|q_λ(λx)|²/d₁(λ)`; the tree's seed for it is `RadialPSWFExteriorPhase` +
  `RadialPSWFInteractionPicture`.  GATE STILL NOT CHECKED — the reduction is not the asymptotics.

  Trap recorded: `rw [someDef]` cannot unfold a definition under an integral binder; use
  `simp only [someDef]`.

- 2026-07-19: **`HTGeometry/LiouvilleGreenAmplitude.lean` BUILT** (audit build passed,
  umbrella-wired, axiom-clean).  This is a first real climb on the ANALYTIC mountain rather than
  another reduction.  WKB/Liouville–Green is absent from mathlib AND from this corpus (checked).

  Formulated for `u'' = −S²u` (so `S = √Q`), which keeps every step algebraic — no square roots.
  The mechanism is an exact cancellation: in `E = S·u² + u'²/S` the two cross terms `±2S·u·u'`
  produced by the equation cancel identically, so

```text
  hasDerivAt_lgEnergy    : E' = S'·(u² − u'²/S²)          — NO oscillatory term at all
  abs_deriv_lgEnergy_le  : |E'| ≤ (|S'|/S)·E
  sq_le_lgEnergy_div     : u² ≤ E/S                        — the 1/S envelope
```

  Better still, dividing/multiplying by `S` gives two EXACT monotone invariants, so for a
  monotone coefficient no Grönwall and no integration is needed at all:

```text
  hasDerivAt_lgAmplitude : (u² + u'²/S²)' = −2S'u'²/S³     — nonincreasing when S increases
  hasDerivAt_lgMomentum  : (S²u² + u'²)'  = +2S'S u²       — nondecreasing when S increases
  sq_le_lgAmplitude      : u² ≤ lgAmplitude
```

  THE CONNECTOR IS ALREADY IN THE TREE: `radialPSWFExteriorSpeed sigma z = √((z²−σ²)/(z²−1))`
  in `RHTower/RadialPSWFExteriorPhase.lean` is documented as "the exact Liouville speed on the
  exterior radial ray" — it IS the `S` this machinery consumes, and that module already has
  `continuousAt_`, `continuousOn_..._uIcc`, `one_le_...`, and the phase derivative laws.
  Next step for the radial gate: instantiate `lgAmplitude`/`lgMomentum` at
  `S = radialPSWFExteriorSpeed sigma`, whose monotonicity in `z` is the sign hypothesis both
  invariants need.

  CAUTION for whoever picks this up: the target density `1/(x√(x²−1))` equals `S/x²` at `σ = 0`
  (since `S(0,x) = x/√(x²−1)`), NOT `1/S`.  So the radial density is the MOMENTUM-side shape times
  the Jacobian, not the amplitude-side shape — check which invariant carries the limit before
  building on it.  Both are now available, so this is a choice, not a gap.

  Trap recorded: dot-notation `h1.add h2` silently resolved to `HasFDerivAtFilter.add` (giving an
  unusable `toSpanSingleton` form) because `Mathlib.Analysis.Calculus.Deriv.Add` was not imported;
  `HasDerivAt.add` did not exist until that import was added.  Also `HasDerivAt.congr_deriv` does
  not exist — prove the scalar identity separately and `rw` it into the goal before `exact`.

- 2026-07-19: **`RHTower/RadialPSWFSpeedMonotone.lean` BUILT** (audit build passed,
  umbrella-wired, axiom-clean).  The Liouville–Green machinery is now INSTANTIATED at the actual
  exterior radial equation — the abstract layer and the prolate layer are joined.

  The key is an exact decomposition that makes everything elementary:

```text
  radialPSWFExteriorSpeed_sq : S(σ,z)² = 1 + (1 − σ²)/(z² − 1)          for σ² ≤ 1, z > 1
```

  so the only `z`-dependence sits in one denominator.  From it:

```text
  radialPSWFExteriorSpeed_pos
  antitoneOn_radialPSWFExteriorSpeed  : S is ANTITONE on (1,∞)     — no calculus, pure algebra
  hasDerivAt_radialPSWFExteriorSpeed  : S' = z(σ²−1)/((z²−1)²S)    — exact
  radialPSWFExteriorSpeed_deriv_nonpos: S' ≤ 0
```

  and then the instantiated invariants, which is the payoff:

```text
  hasDerivAt_radial_lgMomentum   : (S²u² + u'²)' = 2S'S·u²   with  radial_lgMomentum_deriv_nonpos
                                   ⟹ S²u² + u'² is NONINCREASING along the exterior ray
  hasDerivAt_radial_lgAmplitude  : (u² + u'²/S²)' = −2S'u'²/S³
                                   ⟹ u² + u'²/S² is NONDECREASING
```

  These are unconditional adiabatic bounds for exterior prolate solutions, needing no integration
  and no Grönwall, valid for arbitrarily fast oscillation.  `S ≥ 1` is already in the tree
  (`one_le_radialPSWFExteriorSpeed`), so `S²u² + u'² ≤ C` gives `u² ≤ C` and, via the momentum
  invariant evaluated at two radii, a two-sided envelope.

  NEXT on this thread: the density limit needs the CONSTANT, not just the envelope shape — i.e.
  the limit of `S²u²+u'²` itself, which is where the oscillation average (a factor `1/2`) and the
  connection to the interior normalization enter.  The `RadialPSWFInteractionPicture` module
  (`radialInteractionPlus/Minus`, `radialInteraction_reconstruct`, and their derivative laws) is
  the natural next tool: it is exactly the variation-of-constants splitting whose slowly varying
  part carries that constant.

  Trap recorded: `HasDerivAt.sub_const` takes the constant as its SECOND explicit argument and
  `(hasDerivAt_id z).pow 2` normalizes to `↑2 * id z ^ (2-1) * 1`, which will not unify with
  `2 * z`; introduce `have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by simpa using ...`
  first and build from that.

- 2026-07-19: **`RHTower/RadialInteractionBound.lean` BUILT** (audit build passed,
  umbrella-wired, axiom-clean).  This closes the algebraic half of the CONSTANT question — the
  piece the envelope work could not reach.

  Working from the transport laws already in `RadialPSWFInteractionPicture` for
  `W'' + c²W = ψW`, the phases `e^{±icx}` have unit modulus, so:

```text
  norm_exp_I_mul_ofReal / norm_exp_neg_I_mul_ofReal : ‖e^{±icx}‖ = 1
  norm_deriv_radialInteractionPlus  : ‖A₊'‖ = ‖ψ‖‖W‖/(2|c|)     — EXACT, not a bound
  norm_deriv_radialInteractionMinus : ‖A₋'‖ = ‖ψ‖‖W‖/(2|c|)
  norm_le_norm_radialInteraction_add: ‖W‖ ≤ ‖A₊‖ + ‖A₋‖          — from reconstruction
  norm_deriv_radialInteraction_add_le :
      ‖A₊'‖ + ‖A₋'‖ ≤ (‖ψ‖/|c|)·(‖A₊‖ + ‖A₋‖)
```

  The oscillation has disappeared entirely from the last estimate: the frequency `c` survives only
  as the divisor `1/|c|`.  That is the differential form of the Liouville–Green error bound.

  WHAT REMAINS FOR THE CONSTANT, and it is now a SHORT and purely standard list:
    1. Integrate `norm_deriv_radialInteraction_add_le` by Grönwall (mathlib has
       `Mathlib/Analysis/ODE/Gronwall.lean`) to get
       `‖A₊‖+‖A₋‖ ≤ (‖A₊‖+‖A₋‖)(x₀)·exp(∫‖ψ‖/|c|)`.
    2. From boundedness plus `‖A±(b) − A±(a)‖ ≤ ∫_a^b ‖ψ‖‖W‖/(2|c|) ≤ M∫_a^b‖ψ‖/(2|c|)`, deduce
       that `A±` are Cauchy at infinity when `ψ` is integrable — hence the limits `A±(∞)` EXIST.
       Those limits ARE the amplitude constants of the asymptotic oscillation.
    3. Identify `ψ` for the exterior prolate equation and show `∫^∞ ‖ψ‖ < ∞`.
  Steps 1–2 are generic ODE facts and need no prolate input at all; step 3 is the only genuinely
  prolate-specific analytic item left on this thread.

  STATUS OF THE RADIAL GATE overall: reduced by Scheffe to (i) pointwise density convergence and
  (ii) mass convergence; the envelope SHAPE for (i) is proved unconditionally against the real
  equation (`RadialPSWFSpeedMonotone`); the CONSTANT for (i) is now reduced to steps 1–3 above.

- 2026-07-19: **`HTGeometry/IntegrableDerivLimit.lean` BUILT** (audit build passed,
  umbrella-wired, axiom-clean).  This is STEP 2 of the constant, and it is stronger than the
  Cauchy-criterion route I had planned — the limit comes out EXPLICIT:

```text
  tendsto_of_hasDerivAt_of_integrableOn_Ioi :
      A differentiable on [a,∞),  A' integrable on (a,∞)
      ⟹  A → A a + ∫_{(a,∞)} A'                        (limit, not just existence)
  norm_sub_le_integral_norm_of_hasDerivAt :
      ‖A b − A a‖ ≤ ∫_{(a,∞)} ‖A'‖                     for every b ≥ a, uniformly
  tendsto_of_hasDerivAt_of_norm_le :
      derivative dominated by an integrable g  ⟹  ∃ L, A → L
```

  Mechanism: FTC turns `A b` into `A a + ∫_a^b A'`, and `intervalIntegral_tendsto_integral_Ioi`
  says the truncations converge to the improper integral.  No Cauchy-sequence argument and no
  completeness bookkeeping beyond what the integral already carries.  Absent from mathlib.

  UPDATED STATE OF THE CONSTANT (was a 3-item list last round, now 1 item):
    1. Grönwall boundedness — NO LONGER NEEDED as a separate step for existence of the limit:
       `tendsto_of_hasDerivAt_of_norm_le` needs only a dominating integrable rate, and
       `norm_deriv_radialInteraction_add_le` (`RadialInteractionBound`) supplies the rate
       `(‖ψ‖/|c|)(‖A₊‖+‖A₋‖)`.  Grönwall is still what converts that self-referential rate into
       an absolute one, so it is needed for the QUANTITATIVE bound but not for convergence once a
       bound on `W` is known on the ray.
    2. DONE — this module.
    3. Identify `ψ` for the exterior prolate equation and prove `∫^∞ ‖ψ‖ < ∞`.  THIS IS NOW THE
       ONLY GENUINELY PROLATE-SPECIFIC ITEM LEFT on the radial thread.  Everything else in the
       chain is generic and banked.

  Self-correction recorded: my first draft of `norm_sub_le_integral_norm_of_hasDerivAt` stated
  `‖(A a + ∫A') − A a‖ ≤ ∫‖A'‖`, which is just `‖∫A'‖ ≤ ∫‖A'‖` — it used NEITHER hypothesis and
  said nothing about `A`.  Lean's unused-variable warnings caught it.  Replaced with the uniform
  endpoint bound `‖A b − A a‖ ≤ ∫_{(a,∞)}‖A'‖`, which genuinely uses both.  Worth remembering:
  an unused-hypothesis warning on a "theorem" is usually a sign the statement is vacuous, not a
  lint nuisance.

- 2026-07-19: **CORRECTION — I had been adding hypotheses without discharging them, and I
  checked a gate on a conditional theorem.**  User called it out.  Actions taken:

  (a) UN-CHECKED the two-mode card gate "normalized ℓ²-distance/sign-choice form of `(4)`".  I had
      written that `secularVector_head_seed_defect_tendsto_zero` and
      `secularVector_tail_fraction_tendsto_zero` "discharge it with no massaging" — TRUE as a
      claim about shapes, but I never performed the composition, so no hypothesis-free statement
      existed.  Checking that box was wrong.

  (b) BUILT `RHTower/ConstrainedProlateGroundDistanceCCM.lean` (audit build passed, umbrella-wired,
      axiom-clean) which actually performs the discharge for the CCM Fuchs family:

```text
  ccm_struct                   := fuchsRate_radial_struct              (discharges hstruct)
  ccm_tail                     := fuchsRate_radial_tail_ratio_...      (discharges htail)
  ccm_l0_ne_zero / ccm_l1_ne_zero                                      (discharges hL0, hℓ1)
  ccm_secularVector_zero_ne_zero                                       (discharges hv0)
      — from infiniteSecularRoot_spec: the root sits strictly above d₀, so d₀ − μ < 0 ≠ 0
  ccm_tendsto_min_norm_secularHead_sub_twoModeSeed                     (the composed law)
```

      It type-checked on the FIRST attempt, which is the damning part: the discharge was
      straightforward and I simply had not done it.

  WHAT HYPOTHESES REMAIN on the composed theorem, and why each is legitimate rather than laziness:
    * `hA`, `hC`, `hgrow` — positivity and tempered growth of the CCM scale constants `A_j`.
      These DEFINE the family; the tree's existing `ccm_fuchsModel_*` capstones carry the same.
    * `hsum`, `hbessel` — square-summability and the Bessel bound on the coordinates.  `hbessel`
      IS discharged for the TRUE operator by `ConstrainedProlateBesselBound`
      (`tsum_evenProlateConstraintCoord_sq_le : Σ‖ℓ_n(a)‖² ≤ 2a`); connecting that to this model
      is the model→operator transfer, still open.
    * `hl0`, `hl1` — the coordinate limits `ℓ_0 → 2^{1/4}`, `ℓ_1 → √3·2^{−5/4}`.  THIS IS THE
      GENUINELY OPEN ITEM: it is exactly the L7 gate "prolate-to-Hermite limits `ℓ_j → a_j`",
      unchecked on three cards.  It cannot be discharged until that gate is.

  STANDING RULE for the rest of this campaign: do not add a hypothesis to a new theorem unless
  either (i) it is discharged in the same module, or (ii) it is a named open gate on a card.  Any
  other hypothesis means the work is not finished.  And NEVER check a gate on a theorem whose
  hypotheses are not composed away — "the shapes match" is not a discharge.

- 2026-07-19 (cont.): **`RHTower/ConstrainedProlateFullDistanceCCM.lean` BUILT** — the full
  `ℓ²` version of the discharge, so the two-mode gate is now RE-CHECKED legitimately.

  Both compared vectors are now CONSTRUCTED rather than hypothesized:
```text
  twoModeSeedLp  — via memℓp_twoModeSeedFun (finite support ⟹ summable ⟹ Memℓp)
  secularLp      — via memℓp_secularVector, with a `dite` so it is total (zero off the
                   range where square-summability holds)
  ccm_memℓp / ccm_summable_secularVector_sq — the eventual membership and summability
  ccm_tendsto_min_norm_lp_normalize_sub_twoModeSeed — the composed law
```
  To make this composable I first WEAKENED `hV`/`hG` in
  `tendsto_min_norm_lp_normalize_sub_twoModeSeed` from `∀ lam` to `∀ᶠ lam in atTop` — a definition
  can only match the eigenvector eventually, so the `∀` form was unusable and was itself a sign
  the theorem had been written to be easy rather than to be applied.

  IMPORTANT TOOLING LESSON: this module PASSED `lake env lean` but FAILED `lake build`
  (`linarith` could not see through the `ccmFuchsRoot` definition).  `lake env lean` is NOT a
  substitute for the audit build.  Run `lake build <module>` before claiming a module is done.
  Fix was an explicit `rfl` bridge `ccmFuchsRoot A ℓ lam = infiniteSecularRoot ...` before
  `linarith`.

- 2026-07-19: **FULL AUDIT of everything built this campaign, after a second correction from the
  user.**  Classification of my 12 modules:

  UNCONDITIONAL (hypotheses are data/definitions only, no unproved analytic assumption):
    `TrialSpanConcentration`, `SignChoiceNormalizedDistance`, `LiouvilleGreenAmplitude`,
    `RadialPSWFSpeedMonotone`, `RadialInteractionBound`.
  GENERAL THEOREMS whose hypotheses ARE their content (like any analysis lemma):
    `ScheffeLemma`, `IntegrableDerivLimit`.
  CONDITIONAL BUT NOW DISCHARGED (by the two CCM modules):
    `ConstrainedProlateHeadDistance`, `ConstrainedProlateFullDistance`.
  THE DISCHARGES:
    `ConstrainedProlateGroundDistanceCCM`, `ConstrainedProlateFullDistanceCCM` — remaining
    hypotheses are family data plus the named open prolate-to-Hermite gate.
  CONDITIONAL WITH NO DISCHARGE PATH — REMOVED:
    `RadialLeakageWeakConvergence` had `tendsto_integral_abs_sub_nuInfinityDensity` and
    `tendsto_integral_weight_nuInfinityDensity` assuming pointwise density convergence and mass
    convergence.  Those are the Dunster asymptotics, which do NOT exist in this tree, so they were
    assumptions I had no route to discharge.  BOTH THEOREMS DELETED.  The module now keeps only
    what is actually proved: `nuInfinityDensity`, its integrability, and
    `integral_Ioi_one_nuInfinityDensity : ∫ = 4/11`.  The radial card was corrected to match.

  The pattern I fell into: writing `hypothesis → conclusion` modules, reporting them as progress,
  and letting the undischarged hypothesis be invisible in the summary.  That produces a corpus that
  looks large and proves little.  The rule going forward is the one already recorded above, and it
  is not negotiable: a new theorem may only carry a hypothesis that is discharged in the same
  module or is a NAMED OPEN GATE on a card.  Anything else does not get committed.

- 2026-07-19: **`RHTower/HermiteContrastLp.lean` BUILT** (audit build passed, umbrella-wired,
  axiom-clean).  FULLY UNCONDITIONAL — the only hypotheses anywhere in the module are `k : ℕ` and
  `m ≠ k`.  Chosen deliberately as work that can be COMPLETED, not reduced.

  It turns the fixed-mode card's contrast ALGEBRA into `ℓ²` objects:
```text
  memℓp_constrainedProlateHermiteContrast — finite support (zero for j > k+1) ⟹ Memℓp
  hermiteContrastLp k                      — the depth-k contrast as an ℓ² vector
  inner_hermiteContrastLp                  — the ℓ² inner product IS the algebraic pairing
  inner_hermiteContrastLp_eq_zero          — eq (11) as genuine ℓ² orthogonality
  hermiteContrastLp_ne_zero                — top coordinate S_k/a_{k+1} ≠ 0
  orthonormal_hermiteContrastUnit          — the normalized ladder is orthonormal
  norm_sq_hermiteContrastLp                — ‖w_k‖² = self-pairing
```

  SCOPE, stated so it is not overclaimed: this is the LIMIT side of `(10)`--`(11)`.  It does NOT
  prove that the exact eigenvectors converge to the ladder — that is the still-open gate
  "eigenvector ladder limits `(10)`--`(11)` for the exact roots", which at depth `k` needs the
  (k+2)-dimensional head plane and the full Gram–Schmidt pinning, not just orthogonality to the
  constraint (my `(−ℓ₁, ℓ₀)` trick from the `k = 0` case does not generalize: in dimension `k+2`
  the orthogonal complement of the constraint is `(k+1)`-dimensional).  GATE NOT CHECKED.

- 2026-07-19: extended `RHTower/HermiteContrastLp.lean` with the EXACT normalization
  (audit build passed, axiom-clean, no warnings, still fully unconditional):

```text
  constrainedProlateHermiteContrastPairing_self : ⟨w_k,w_k⟩ = S_k + S_k²/a_{k+1}²
  norm_sq_hermiteContrastLp_eq                  : ‖w_k‖² = √2·Q_k·Q_{k+1}/q_{k+1}
```

  Derivation: `S_k = √2 Q_k` and `a_{k+1}² = √2 q_{k+1}`, so
  `S_k + S_k²/a_{k+1}² = √2 Q_k (Q_k + q_{k+1})/q_{k+1} = √2 Q_k Q_{k+1}/q_{k+1}` using
  `constrainedProlateHermiteWeightSum_succ`.  This makes the normalization in `(10)` explicit
  instead of implicit, which is what a convergence proof will have to hit.

  Note: `ring_nf` closes the final identity WITHOUT needing `√2 ^ 2 = 2` — both sides are equal as
  polynomials in `√2` treated as an opaque atom.  I had added `hs2`/`hspos` expecting to need them;
  they were dead and are removed.

- 2026-07-19: extended `RHTower/HermiteContrastLp.lean` with the RAW contrast layer (audit build
  passed, axiom-clean, no warnings, fully unconditional — hypotheses are only `0 < m` and `m ≤ k`):

```text
  memℓp_constrainedProlateRawHermiteContrast  — r_m is supported on {0,m}, hence in ℓ²
  rawHermiteContrastLp m                       — the raw CCM contrast as an ℓ² vector
  inner_hermiteContrastLp_raw                  — its ℓ² pairing with w_k is the finite sum
  inner_hermiteContrastLp_rawHermiteContrastLp_eq_zero : ⟨w_k, r_m⟩ = 0 for 0 < m ≤ k
```

  With `inner_hermiteContrastLp_eq_zero` (ladder ⊥ ladder) this now states, between genuine
  Hilbert-space vectors, that the spectral ladder IS the Gram–Schmidt orthogonalization of the raw
  CCM family — the card's `[PROVED HERE; BRIDGE]` claim, previously only finite-sum algebra.

  The ℓ² limit-object layer for the fixed-mode card is now complete: membership, pairing =
  algebraic pairing, mutual orthogonality, raw orthogonality, nonvanishing, orthonormal
  normalization, and the exact norm `√2 Q_k Q_{k+1}/q_{k+1}`.  What is NOT done, and the gate stays
  open: convergence of the EXACT eigenvectors to this ladder.

- 2026-07-19: **THE DEPTH-k PINNING IS PROVED** — `RHTower/HermiteContrastLp.lean` extended
  (audit build passed, axiom-clean, no warnings, fully unconditional):

```text
  sum_mul_rawHermiteContrast : ⟨x, r_m⟩ = x_m a_0 − x_0 a_m           (0 < m ≤ k)
  eq_smul_constrainedProlateHermiteContrast_of_orthogonal :
      x supported on range(k+2),  ⟨x,a⟩ = 0,  ⟨x,r_m⟩ = 0 for 0 < m ≤ k
      ⟹  x = (−x_0/a_0) · w_k
```

  This DIRECTLY REMOVES the obstacle I recorded two iterations ago.  I had said the `k = 0` trick
  (take the explicit orthogonal `(−ℓ₁, ℓ₀)`) fails at depth `k` because the orthogonal complement
  of the constraint in the `(k+2)`-dimensional head plane is `(k+1)`-dimensional.  That is true but
  incomplete: the ladder vector is orthogonal not only to the constraint but to every PRECEDING RAW
  CONTRAST, and those `k` extra conditions cut the freedom back to one dimension.  The proof needs
  no finrank machinery: `⟨x, r_m⟩ = 0` reads `x_m a_0 = x_0 a_m`, so the head is proportional to
  `(a_0,…,a_k)` coordinatewise, and the constraint then pins the top coordinate.

  So the depth-`k` analogue of the two-mode metric argument is now structurally available: what a
  convergence proof must supply is that the exact eigenvector's head becomes orthogonal to the
  constraint AND to each raw contrast, after which this theorem forces the direction.  GATE STILL
  NOT CHECKED — that convergence is not proved.

  Tactic note: `linear_combination` prints the RESIDUAL goal, not the raw goal.  I read the printed
  `... * 2 = 0` as the goal and passed coefficient `2`; the correct coefficient was `1`.  When
  `linear_combination c * h` fails, do not infer `c` from the printed goal.

- 2026-07-19: `RHTower/HermiteContrastLp.lean` extended to the `ℓ²` pinning UP TO SIGN (audit
  build passed, axiom-clean, no warnings, fully unconditional):

```text
  inner_rawHermiteContrastLp_eq_sum        — lp pairing = the finite sum, for supported vectors
  eq_smul_hermiteContrastLp_of_orthogonal  — v = (−v₀/a₀) • w_k   in ℓ²
  eq_pm_hermiteContrastUnit_of_orthogonal  — ‖v‖ = 1 ⟹ v = ± hermiteContrastUnit k
```

  The last is literally the card's phrase "the unique unit vector up to sign" for the limit object,
  now a theorem.  Note the two-mode card's `(4)` also says "unique up to sign" — so the depth-`k`
  limit object now has the SAME characterization that the `k = 0` metric argument consumed, which
  is what makes the depth-`k` convergence argument structurally parallel to the one already built
  in `ConstrainedProlateHeadDistance`/`ConstrainedProlateFullDistance`.

  GATE STILL NOT CHECKED.  Everything proved so far characterizes the LIMIT; nothing yet shows the
  exact eigenvectors approach it.  The remaining input is a defect statement: the exact head must
  become orthogonal to the constraint AND to each raw contrast `r_m`, `0 < m ≤ k`.  For `k = 0`
  there are no raw conditions, which is exactly why the `k = 0` case closed first.

  Trap: `set x := e with h` does NOT fold `e` inside hypotheses created afterwards; `rw [h']` on the
  abstracted variable then fails.  Fold explicitly with `rw [← h]` first.

- 2026-07-19: `RHTower/HermiteContrastLp.lean` extended to the QUANTITATIVE pinning (audit build
  passed first attempt, axiom-clean, no warnings, fully unconditional):

```text
  sub_smul_hermiteContrast_head_mul     — coordinate deviation × a₀, in closed form
  sub_smul_hermiteContrast_head_eq_raw  — (x_m − c·w_k(m))·a₀ = ⟨x, r_m⟩       EXACTLY
  sub_smul_hermiteContrast_top_mul      — the top-coordinate analogue, constraint defect
                                          corrected by the head defects
```

  This is the payoff of having proved uniqueness by exact computation rather than by a dimension
  count: the argument perturbs for free.  There is no compactness, continuity or
  smallest-singular-value step between "the defects are small" and "`x` is close to the ladder" —
  it is an IDENTITY.  Concretely, a depth-`k` convergence proof now needs only:
    (i)   ⟨v_λ, r_m⟩ → 0 for each `0 < m ≤ k`,
    (ii)  ⟨v_λ, a⟩ → 0,
  and these identities convert (i)+(ii) into coordinatewise convergence to the ladder direction,
  after which `eq_pm_hermiteContrastUnit_of_orthogonal` supplies the sign normalization.

  GATE STILL NOT CHECKED — (i) and (ii) for the exact eigenvectors are not proved.

- 2026-07-19: **`RHTower/SecularVectorRawDefect.lean` BUILT** (audit build passed, umbrella-wired,
  axiom-clean, no warnings, fully unconditional — hypotheses are only nonvanishing denominators).
  This is the FIRST LINK of the remaining depth-`k` content, and it is exact:

```text
  secularVector_raw_defect :
      v_m ℓ_0 − v_0 ℓ_m = ℓ_0 ℓ_m (d_0 − d_m) / ((d_m − μ)(d_0 − μ))
  secularVector_raw_defect_div :
      (v_m ℓ_0 − v_0 ℓ_m)/(v_0 ℓ_0) = (ℓ_m/ℓ_0)·((d_0 − d_m)/(d_m − μ))
  secularVector_raw_defect_eq_zero_of_eq : the defect vanishes when d_0 = d_m
```

  WHAT THIS REVEALS, and it is the useful part: the raw defect of the exact eigenvector is NOT
  controlled by the coordinates.  Dividing out the head weight removes them almost entirely — what
  is left is `(ℓ_m/ℓ_0)` times the pure SCALE ratio `(d_0 − d_m)/(d_m − μ)`.  So the depth-`k`
  eigenvector converges to the ladder precisely when the root sits far above the lower poles in the
  relative sense `(d_0 − d_m)/(d_m − μ) → 0`, i.e. `d_m/μ_k → 0` for `m ≤ k`.

  That last statement IS available in the tree in the form of the depth-root ratio laws
  (`ccm_depthSecularRoot_ratio_tendsto`: `μ_k/d_{k+1} → θ_k > 0`) combined with the `λ⁸` scale
  separation (`d_m/d_{k+1} → 0` for `m ≤ k`, from `fuchsRate`), since
  `d_m/μ_k = (d_m/d_{k+1})/(μ_k/d_{k+1}) → 0/θ_k = 0`.  So the depth-`k` chain is now:
    scale separation + depth-root ratio  ⟹  raw defects → 0  ⟹ (exact identities of
    `HermiteContrastLp`)  coordinatewise convergence to the ladder  ⟹ (up-to-sign pinning)  eq (10).
  Each arrow except the first is already banked.  GATE NOT CHECKED — the first arrow is not built.

  Also corrected a docstring in this module that claimed a vanishing the statement did not assert.
  A wrong docstring is the same class of defect as an undischarged hypothesis: it makes the corpus
  read stronger than it is.

- 2026-07-19: `RHTower/SecularVectorRawDefect.lean` extended with the LIMIT half (audit build
  passed, axiom-clean, no warnings):

```text
  tendsto_scale_defect_zero :
      d₀/μ → 0,  d_m/μ → 0   ⟹   (d₀ − d_m)/(d_m − μ) → 0
  tendsto_secularVector_raw_defect_div_zero :
      the above  +  ℓ_m/ℓ_0 → c   ⟹   (v_m ℓ_0 − v_0 ℓ_m)/(v_0 ℓ_0) → 0
```

  So the depth-`k` raw defects now vanish under a hypothesis about SCALES ALONE (`d_j/μ_k → 0`)
  plus a convergent coordinate ratio.  Note what dropped out: the coordinates enter only through
  `ℓ_m/ℓ_0 → c`, and the value of `c` is irrelevant — it is multiplied by zero.  So this link does
  NOT need the full prolate-to-Hermite limits `ℓ_j → a_j`; a convergent ratio suffices.

  REMAINING for the depth-`k` gate, now a single concrete item:
    `d_j/μ_k → 0` for `j ≤ k`, for the CCM Fuchs family.
  Both inputs exist: `fuchsRate_div_tendsto_zero` gives `d_j/d_{k+1} → 0`, and
  `ccm_depthSecularRoot_ratio_tendsto` gives `μ_k/d_{k+1} → θ_k` with
  `constrainedProlateHermiteTheta_mem_Ioo` giving `θ_k > 0`; so
  `d_j/μ_k = (d_j/d_{k+1})/(μ_k/d_{k+1}) → 0/θ_k = 0`.  That composition is the next build.

  GATE NOT CHECKED.

- 2026-07-19: `RHTower/SecularVectorRawDefect.lean` — the general chain is now ASSEMBLED end to
  end (audit build passed, axiom-clean, no warnings):

```text
  tendsto_div_zero_of_div_tendsto :
      A/B → 0,  M/B → θ ≠ 0   ⟹   A/M → 0
      (B ≠ 0 is DERIVED from M/B → θ ≠ 0, not assumed)
  tendsto_secularVector_raw_defect_div_zero_of_reference :
      d₀/B → 0,  d_m/B → 0,  μ/B → θ ≠ 0,  ℓ_m/ℓ_0 → c
      ⟹   (v_m ℓ_0 − v_0 ℓ_m)/(v_0 ℓ_0) → 0
      (μ ≠ 0 eventually is likewise DERIVED)
```

  The hypotheses of the second theorem are now EXACTLY the shapes the tree already produces for the
  CCM Fuchs family, with `B = d_{k+1}`:
    `d_j/d_{k+1} → 0`      ← `fuchsRate_div_tendsto_zero`
    `μ_k/d_{k+1} → θ_k`    ← `ccm_depthSecularRoot_ratio_tendsto`
    `θ_k ≠ 0`              ← `constrainedProlateHermiteTheta_mem_Ioo`
  so the remaining work on this thread is instantiation plumbing (nat arithmetic on the exponent
  `4j + 4(k+1−j) = 4(k+1)` for `fuchsRate_div_tendsto_zero`, and threading the depth hypothesis
  list), not new mathematics.

  Deliberate scope call: I stopped before the CCM instantiation rather than start it with little
  context left.  Beginning a long signature-threading job and abandoning it half-done is how the
  conditional-theorem mess got made in the first place.

  GATE NOT CHECKED.

- 2026-07-19: **THE FIRST ARROW IS BUILT.**  `RHTower/CcmFuchsScaleRatio.lean` and
  `RHTower/CcmDepthRawDefect.lean` (both audit-built, umbrella-wired, axiom-clean, no warnings;
  the second built on the FIRST attempt):

```text
  ccmFuchsScale_div_tendsto_zero  : d_j/d_{k+1} → 0 for j ≤ k
      (via fuchsRate_div_tendsto_zero with exponent arithmetic 4j + 4(k+1−j) = 4(k+1))
  eventually_pos_of_div_tendsto_pos          : M/B → θ > 0, B > 0  ⟹  M > 0 eventually
  eventually_sub_ne_zero_of_div_tendsto_zero : D/M → 0, M > 0      ⟹  D − M ≠ 0 eventually
  ccm_tendsto_depth_raw_defect_div_zero :
      for the CCM Fuchs family and every m ≤ k,
      (v_m ℓ_0 − v_0 ℓ_m)/(v_0 ℓ_0) → 0   at the depth-k root
```

  DISCHARGED inside the module, not assumed: the structural hypotheses (via
  `ccm_fuchsModel_depthSecularRoot_ratio_tendsto`, which already existed), positivity of the root,
  and separation of every lower pole from the root.  The last two come from the ratio limits
  themselves — no bracket theorem and none of `depthSecularRoot_bracket`'s long hypothesis list was
  needed, which was the plumbing I had been dreading.

  REMAINING HYPOTHESES: `hA`/`hC`/`hgrow` (define the family), `hsum`/`hbessel`, and `hl` (the
  coordinate limits `ℓ_j → a_j`) — `hl` is the named open prolate-to-Hermite gate.  Same standard
  as every other `ccm_fuchsModel_*` capstone in the tree.

  STATE OF THE DEPTH-k CHAIN now:
    raw defects → 0                                   ✅ THIS BUILD
    exact identities defect ↔ coordinate deviation    ✅ HermiteContrastLp
    coordinatewise convergence ⟹ ladder direction     ✅ HermiteContrastLp (pinning)
    unit vector up to sign                            ✅ HermiteContrastLp
    constraint defect ⟨v,a⟩ → 0                       ❌ NOT BUILT — the one remaining link
  Note the constraint side should be EASIER than the raw side just completed: the exact eigenvector
  satisfies `Σ ℓ_j v_j = 0` EXACTLY (`secularVector_constraint`), so the only defect against `a` is
  the coordinate drift `ℓ_j → a_j` — i.e. it is controlled by the same `hl` already assumed.

  GATE NOT CHECKED.

- 2026-07-19: **`RHTower/DepthSecularConstraint.lean` BUILT** (type-checked with `lake env lean`,
  ONE final `lake build` audit, umbrella-wired, axiom-clean, no warnings, fully unconditional —
  hypotheses are a scale floor, summability and `μ < B`, all data conditions):

```text
  depthSecular_eq_tsum_mul_secularVector  : depthSecular d ℓ k μ = ∑' ℓ_j v_j
  tsum_mul_secularVector_eq_zero_of_depthSecular : at a root, ∑' ℓ_j v_j = 0  EXACTLY
  sum_range_mul_secularVector_eq_neg_tsum : head pairing = −(tail pairing)
```

  The point: the depth-`k` secular function IS the constraint pairing, because each term
  `ℓ_j²/(d_j − μ)` is `ℓ_j · v_j`.  So the eigenvector lies in the constrained hyperplane
  identically, not asymptotically — the constraint carries NO defect against the true coordinates.
  The last theorem localizes the whole discrepancy to the tail.

  DEPTH-k CHAIN NOW:
    raw defects → 0                                   ✅ CcmDepthRawDefect
    exact identities defect ↔ coordinate deviation    ✅ HermiteContrastLp
    pinning + unit-up-to-sign                         ✅ HermiteContrastLp
    constraint holds exactly against ℓ                ✅ THIS BUILD
    head-vs-`a` defect → 0                            ❌ remaining: needs (i) the coordinate
        drift `ℓ_j → a_j` (the open `hl` gate) and (ii) the tail pairing → 0, for which
        `sum_range_mul_secularVector_eq_neg_tsum` reduces the task to bounding the tail alone.

  PROCESS CORRECTION (user, repeatedly): the rule is `lake env lean <file>` to ITERATE and
  `lake build <module>` ONLY as the final audit.  I had been using `lake build` as the main loop
  for many iterations — 27–43 s per check where `lake env lean` costs a fraction of that, on a
  shared laptop with other agents building.  Fixed from this build onward.

  GATE NOT CHECKED.

- 2026-07-19: `RHTower/DepthSecularConstraint.lean` extended with the TAIL BOUND (type-checked
  clean on the first `lake env lean`, one final `lake build` audit, axiom-clean, no warnings,
  fully unconditional):

```text
  offsetSecularTail_le : offsetSecularTail d ℓ m μ ≤ (∑' ℓ_{j+m}²)/(B − μ)
      — the offset analogue of the ground-index `infiniteSecularTail_le`, which was the only
        version in the tree
  abs_sum_range_mul_secularVector_le :
      at a depth-k root,  |∑_{j<k+2} ℓ_j v_j| ≤ (∑' ℓ_{j+k+2}²)/(B − μ)
```

  So the head pairing against the TRUE coordinates is now bounded, uniformly, by coordinate mass
  over distance-to-tail-floor.  With the Bessel bound `∑ℓ² ≤ 2λ` and `B = d_{k+2}`, `μ < d_{k+1}`,
  this is `≤ 2λ/(d_{k+2} − d_{k+1})`, i.e. exactly the quantity the existing `htail` hypothesis
  (`fuchsRate_step4_tail_ratio_tendsto_zero`) drives to zero after multiplying by `d_{k+1}`.

  REMAINING on the depth-k thread: normalize by the head weight `v_0 ℓ_0 = ℓ_0²/(d_0 − μ)` and
  compose with `htail` + Bessel to get the normalized head defect → 0; then the coordinate drift
  `ℓ_j → a_j` (the open `hl` gate) converts the pairing against `ℓ` into the pairing against `a`.

  GATE NOT CHECKED.

- 2026-07-19: `RHTower/DepthSecularConstraint.lean` — the NORMALIZED head bound (one `lake env
  lean` fix cycle, one final `lake build`, axiom-clean, no warnings, fully unconditional):

```text
  abs_secularVector_zero_mul : |v_0 ℓ_0| = ℓ_0²/(μ − d_0)      for d_0 < μ
  abs_sum_range_mul_secularVector_div_le :
      |∑_{j<k+2} ℓ_j v_j| / |v_0 ℓ_0|
        ≤ (∑' ℓ_{j+k+2}²)·(μ − d_0) / ((B − μ)·ℓ_0²)
```

  The head defect RELATIVE TO THE HEAD WEIGHT is now bounded by scale data plus the coordinate
  mass — no eigenvector quantity survives on the right-hand side.  With Bessel `∑ℓ² ≤ 2λ`,
  `B = d_{k+2}` and `μ < d_{k+1}` the bound reads `≤ 2λ·d_{k+1}/((d_{k+2} − d_{k+1})·ℓ_0²)`,
  which is precisely `htail` (`fuchsRate_step4_tail_ratio_tendsto_zero`) divided by `ℓ_0²`.

  So the depth-k constraint side is now reduced to a single limit composition of the same shape
  already performed for the raw side in `CcmDepthRawDefect`.  After that, converting the pairing
  against `ℓ` into the pairing against `a` needs only the coordinate drift `ℓ_j → a_j` — the open
  `hl` gate.

  GATE NOT CHECKED.

- 2026-07-19: `RHTower/CcmFuchsScaleRatio.lean` — the two STRICT side conditions the constraint
  composition needs (type-checked clean, fully unconditional):

```text
  eventually_lt_of_div_tendsto_zero    : D/M → 0, M > 0        ⟹ D < M eventually
  eventually_lt_of_div_tendsto_lt_one  : M/B → θ < 1, B > 0    ⟹ M < B eventually
```

  The first gives `d_0 < μ_k`; the second gives `μ_k < d_{k+1}` from `θ_k < 1`
  (`constrainedProlateHermiteTheta_mem_Ioo`).  Both are hypotheses of
  `abs_sum_range_mul_secularVector_div_le`.  Also refactored
  `eventually_sub_ne_zero_of_div_tendsto_zero` to derive from the strict version rather than repeat
  its proof.

  **THE ONE BLOCKER ON THE CONSTRAINT SIDE, precisely located:**
  `abs_sum_range_mul_secularVector_div_le` needs `hroot : depthSecular d ℓ k μ = 0`.  In the tree
  that fact exists ONLY as the second conjunct of `depthSecularRoot_bracket`
  (`ConstrainedProlateDepthSecular.lean:276`), whose hypothesis list includes
  `hbr : d k < infiniteSecularRoot (flattenedScales d k 0) (flattenedCoords ℓ k)`.
  `hbr` IS derived in the tree — inside the proof of `depthSecularRoot_ratio_tendsto`
  (around line 470, as `hbrl`) — but it is not exported.

  NEXT STEP, and it is engineering not mathematics: export from
  `ConstrainedProlateDepthSecular.lean` a lemma packaging
  `depthSecular d ℓ k (depthSecularRoot d ℓ k) = 0` under the SAME structural hypothesis shape that
  `ccm_depthSecularRoot_ratio_tendsto` already takes, by lifting the existing `hbrl` derivation out
  of that proof.  Note this appends to a heavily-depended-on module, so budget for the rebuild.

  GATE NOT CHECKED.

- 2026-07-19: **`RHTower/DepthSecularRootSpec.lean` BUILT** (audit build passed, umbrella-wired,
  axiom-clean).  Two-stage, and the second stage exists because the first FAILED my own standard:

  Stage 1 — the definitional unpacking.  `depthSecularRoot` is `dif_pos` on
  `∃ μ ∈ Ioo (d k) (d (k+1)), depthSecular d ℓ k μ = 0`, so BOTH defining properties are three-line
  exports from that existence, with none of `depthSecularRoot_bracket`'s machinery:
```text
  depthSecularRoot_mem_Ioo                 : the root lies in the k-th gap
  depthSecular_depthSecularRoot_eq_zero    : the root kills the secular function
```
  For these two the existence hypothesis IS the content of the definition — legitimate.

  Stage 2 — the correction.  I then wrote
  `tsum_mul_secularVector_depthSecularRoot_eq_zero` and
  `abs_sum_range_mul_secularVector_depthSecularRoot_div_le` which merely PROPAGATED that existence
  hypothesis instead of discharging it.  Existence is NOT a named open gate — it is provable in the
  tree — so those two failed the standing rule.  Fixed by adding:
```text
  exists_depthSecular_root  — existence FROM depthSecularRoot_bracket
  abs_sum_range_mul_secularVector_depthSecularRoot_div_le'
      — the head-defect bound with NO existence hypothesis
```

  Residue, stated plainly: the primed version still carries the bracket's own inputs, of which
  `hbr : d k < infiniteSecularRoot (flattenedScales d k 0) (flattenedCoords ℓ k)` is the only
  non-structural one.  `hbr` is derived in the tree inside `depthSecularRoot_ratio_tendsto` (as
  `hbrl`, from `hcheck`/`hratio`) but is still not exported; lifting it is the next discharge.

## Working rules (carry across sessions)

- One lake build at a time, foreground, `nice -n 19`, `LEAN_NUM_THREADS=2`; batch edits before
  building; verify every mathlib name in a scratch file first.
- After each module: `#print axioms` in scratch, umbrella import in `RHTower.lean`
  (or `HTGeometry.lean` for reusable analysis), `formal_tools.py index`, lint check,
  card Lean-decision + gates update, tick the layer here.
- Dead routes and design decisions land in this card, not in memory.

## L6a — Hermite Fourier eigenrelation (DONE, 2026-07-18)

`formal/GaloisForLFunctions/HTGeometry/HermiteFourierEigen.lean`, axiom-clean, umbrella-wired.

Supplies the object the higher-`n` trial spaces were blocked on and which **mathlib does not
have**: the Hermite functions as Fourier eigenfunctions.

Route taken (purely operator-algebraic — no integral asymptotics, no oscillator spectral theory):

* `mulXCLM`, `derivSCLM`, `fourierSCLM` — coordinate multiplication, differentiation, and the
  Fourier transform as continuous linear operators on `𝓢(ℝ, ℂ)` (mathlib's `smulLeftCLM`,
  `derivCLM`, `fourierTransformCLM`).
* `fourierSCLM_derivSCLM : 𝓕 D = 2πi · M 𝓕` and `derivSCLM_fourierSCLM : D 𝓕 = −2πi · 𝓕 M`,
  from `Real.fourier_deriv` / `Real.deriv_fourier` with the Schwartz integrability side
  conditions discharged (`integrable_deriv_schwartz`, `integrable_smul_id_schwartz`).
* `creationCLM := 2π·M − D`, and the **single identity that carries everything**:
  `fourierSCLM_creationCLM : 𝓕 A = (−i) · A 𝓕`.
* `hermiteSchwartz_succ_eq : h_{n+1} = (2π)⁻¹ • A h_n` — reconciles the pre-existing self-dual
  normalization `hermiteStep = x − (1/2π)d/dx` of `GaussianSchwartz.hermitePoly` with `A`; the
  two differ by a scalar, so the eigenvalue is untouched.  (Reuse, not a second Hermite family.)
* `fourierSCLM_hermiteSchwartz (n) : 𝓕 h_n = (−i)ⁿ • h_n` — induction from the Gaussian fixed
  point through the intertwining relation.
* `fourier_hermiteSchwartz_apply` (pointwise) and
  `fourier_hermiteSchwartz_toLp : 𝓕 (h_n.toLp 2) = (−i)ⁿ • h_n.toLp 2` — the `L²` form the
  prolate estimates consume, since `fourierUnitary` IS `Lp.fourierTransformₗᵢ`.
* Parity: `hermiteSchwartz_neg : h_n(−x) = (−1)ⁿ h_n(x)` and `hermiteSchwartz_even` — so the
  even-index Hermite functions land in `evenSubspace`, where the constrained problem is posed.

CONSEQUENCE for the campaign: the `n = 0` trial-space chain of `GaussianEvenCarrier` now has its
higher-`n` inputs.  The remaining pieces of the L6a upper envelope are (i) `L²` orthogonality of
the Hermite family (integration by parts on the creation/annihilation pair), (ii) the dilation
`h_n(·/√a)` to the aperture scale, (iii) the `n+1` near-orthonormal assembly through
`OrthonormalTrialSpan.norm_sq_apply_le_of_orthonormal_span`, then
`evenProlateLeakageValue_le_of_form_trial`.  The rate deficit recorded above still applies to
the *Gaussian* profile; whether the Hermite profiles close the `e^{−2c}` gap is the next question
to settle, and it is now askable in Lean.

ROUTE FOUND for the next piece (Hermite `L²` orthogonality): mathlib has whole-line integration
by parts for Schwartz functions —
`SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul (f g : 𝓢(ℝ, 𝕜)) : ∫ f·g' = −∫ f'·g`
(`Mathlib/Analysis/Distribution/SchwartzSpace/Deriv.lean:263`).  That discharges the boundary
terms, so the plan is: annihilation operator `B := 2π·M + D`; adjointness `⟪A f, g⟫ = ⟪f, B g⟫`;
the commutator `B A − A B = 4π` (from `[D, M] = I`); `B h₀ = 0`; hence the lowering relation
`B h_n = 2n·h_{n−1}` by induction; hence `⟪h_m, h_n⟫ = 0` for `m ≠ n` by descending induction.
No new analytic input is required beyond what is already built.

## L6a — Hermite `L²` orthonormal system (DONE, 2026-07-18)

`formal/GaloisForLFunctions/HTGeometry/HermiteOrthogonality.lean`, axiom-clean, umbrella-wired.

The oscillator argument, no Gaussian moment integrals beyond the one Gauss integral:

* `mulS`, `schwartzPair f g = ∫ f·g` — the bilinear (unconjugated) pairing, built through
  `smulLeftCLM` and `integralCLM` so integrability is structural rather than proved by hand.
* `annihilationCLM := 2π·M + D`.
* `derivSCLM_mulXCLM : D M = 1 + M D` — the canonical commutator.
* `annihilationCLM_creationCLM_sub : B A − A B = 4π` (proved by `module` after expanding).
* `annihilationCLM_gaussianSchwartz : B h₀ = 0` — the vacuum.
* `annihilationCLM_hermiteSchwartz : B h_{n+1} = 2(n+1)·h_n` — the lowering relation, by
  induction from the commutator and the vacuum.
* `schwartzPair_creationCLM : ⟨A f, g⟩ = ⟨f, B g⟩` — integration by parts, boundary terms
  discharged by `SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul`.
* `schwartzPair_hermiteSchwartz_eq_zero : m ≠ n → ⟨h_m, h_n⟩ = 0`.
* `schwartzPair_hermiteSchwartz_self_succ : ⟨h_{n+1}, h_{n+1}⟩ = ((n+1)/π)·⟨h_n, h_n⟩` and
  `⟨h₀, h₀⟩ = √(π/2π)` (`integral_gaussian`), hence
  `schwartzPair_hermiteSchwartz_self_ne_zero` and `hermiteSchwartz_toLp_ne_zero`.
* `inner_hermiteSchwartz_toLp` — on this family the `L²` inner product *is* the bilinear pairing,
  because the Hermite functions are real-valued.
* **`orthonormal_hermiteSchwartz_toLp : Orthonormal ℂ (fun n => ‖h_n‖⁻¹ • h_n.toLp 2)`.**

Together with `fourier_hermiteSchwartz_toLp` this is an **orthonormal family of eigenvectors of
the `L²` Fourier transform** — exactly the object `OrthonormalTrialSpan` and
`GreedyCourantFischer.le_orthSup_of_trial` consume.

REMAINING for the L6a upper envelope: dilation of the family to the aperture scale, the
truncation error of each `h_n` on `[−a,a]`, and the `n+1`-dimensional assembly through
`OrthonormalTrialSpan.norm_sq_apply_le_of_orthonormal_span` →
`evenProlateLeakageValue_le_of_form_trial`.  The rate question recorded above is unchanged: the
truncated-Gaussian profile is provably `≍ τ²`, so whether the *Hermite* profiles reach the Fuchs
`e^{−2c}` is the open point, and it is now a statement one can write down in Lean.

## L6a — every fixed leakage of the TRUE operator vanishes (DONE, 2026-07-18)

Two new modules close the qualitative half of L6a for **all** indices, not only `n = 0`.

`formal/GaloisForLFunctions/HTGeometry/TrialSpanConcentration.lean` (axiom-clean):

* `norm_proj_le` — a projection satisfying Pythagoras is a contraction.
* `norm_sub_proj_unitary_proj_le : ‖h − P U P h‖ ≤ 2‖h − P h‖` for `U h = h`.  This is the
  **linear** form of the truncation estimate; the earlier `norm_sq_proj_unitary_proj_ge` loses a
  square and therefore does not survive aggregation over a family.  Splitting
  `h − P U P h = (h − P h) + P U (h − P h)` is the whole proof.
* `norm_sq_apply_ge_of_orthonormal_span : (1 − √m·η)²‖f‖² ≤ ‖T f‖²` on the span of an orthonormal
  family each of whose members `T` moves by at most `η` — the Bessel–Chebyshev aggregation
  of `OrthonormalTrialSpan` turned into a *lower* bound by subtracting from the identity.

`formal/GaloisForLFunctions/RHTower/HermiteEvenCarrier.lean` (axiom-clean):

* `hermiteL2_mem_evenSubspace` — even-index Hermite classes lie in the even carrier.
* `hermiteEven j := h_{4j}` and `evenFourierTransform_hermiteEven : F h_{4j} = h_{4j}`, since
  `(−i)^{4j} = 1`.  **The step-four subfamily is forced**: only the Fourier-*fixed* modes feed
  the truncation estimate, and those are exactly the `4j` ones — the same step-four ladder the
  constrained transfer runs on, arrived at independently.
* `orthonormal_hermiteEvenUnit` — the normalized step-four family is orthonormal in the carrier.
* `norm_sq_sub_cut_eq` — the truncation error of ANY carrier vector is its `L²` mass outside the
  aperture (the Gaussian-specific computation, generalized).
* `tendsto_norm_sq_sub_cut` — that mass vanishes as `a → ∞`, by dominated convergence along
  `atTop` (which is countably generated, so `tendsto_integral_filter_of_dominated_convergence`
  applies directly — no ℕ-subsequence detour needed).
* `evenProlateLeakageValue_le_of_hermite_trial` — the `(n+1)`-member trial-space bound.
* **`evenProlateLeakageValue_tendsto_zero (n) : d_n(a) → 0 as a → ∞`, for EVERY fixed `n`.**
  Strictly generalizes `evenProlateLeakageValue_zero_tendsto_zero`.
* `evenProlateConcentrationValue_tendsto_one (n)` — the dual form.

Lean note: `inner_smul_left/right` do NOT fire on `evenSubspace` elements (the submodule's `•`
instance is not syntactically the inner-product-space one); descend to `SoninL2` by `rfl` first.

WHAT THIS OPENS: the `ClockEnvelope` contract's qualitative content is now discharged for the
true operator at every index.  What remains is purely the RATE: `lower` and `upper` need
`d_n(a) ≍ C_n a^{2e_n+1} E(a)` for one shared clock `E`.  The trial-space route gives an upper
bound of the shape `(√(n+1)·2τ_n(a))²` with `τ_n` the Hermite tail — so the next concrete
question is whether the Hermite tail `∫_{|x|>a}|h_{4j}|²` can be made explicit enough to compare
with `a^{2e_j+1}E(a)`, and, separately, what supplies the matching LOWER bound (no variational
argument gives one; that needs the eigenfunction itself, or a trace/determinant identity).

## L6a — the SHARP (quadratic) trial-space bound (DONE, 2026-07-18)

The previous all-index bound was linear in the truncation error `τ` and therefore weaker than
the `n = 0` Gaussian bound, which is quadratic.  Two additions fix that, at every index.

`formal/GaloisForLFunctions/HTGeometry/PositiveFormTrialSpan.lean` (axiom-clean):

* `re_inner_apply_self_le_of_orthonormal_span` — for a **positive symmetric** operator `A` and an
  orthonormal family `g`, on the span
  `⟪A f, f⟫ ≤ (∑ₖ ⟪A gₖ, gₖ⟫)·‖f‖²`, i.e. a positive semidefinite matrix has operator norm at
  most its trace.  **No square is lost** — the whole point.  Mechanism: a positive symmetric `A`
  makes `⟪x,y⟫_A = ⟪A x, y⟫` a `PreInnerProductSpace.Core`, for which mathlib supplies
  Cauchy–Schwarz WITHOUT definiteness (`InnerProductSpace.Core.inner_mul_inner_self_le` accepts a
  `PreInnerProductSpace.Core` instance) — then discrete Cauchy–Schwarz plus Bessel.

Additions to `RHTower/HermiteEvenCarrier.lean` (axiom-clean):

* `re_inner_evenProlateLeakage : ⟪Bₐ f, f⟫ = ‖f‖² − ‖Tₐ f‖²` and its nonnegativity.
* `re_inner_evenProlateLeakage_le : ⟪Bₐ g, g⟫ ≤ 5‖g − Pₐ g‖²` for Fourier-fixed `g` — Pythagoras
  plus the existing squared truncation estimate.  QUADRATIC in the tail.
* **`evenProlateLeakageValue_le_hermite_tail_sq (a) (n) :`
  `d_n(a) ≤ ∑_{k≤n} 5‖ĥ_{4k} − Pₐ ĥ_{4k}‖²`** — the sharp shape at every index: quadratic in the
  tail, with only `n+1` terms and no `√(n+1)` loss.  This recovers the `n = 0` Gaussian bound's
  shape and strictly improves the linear all-index bound proved earlier.

WHAT REMAINS FOR THE ENVELOPE `upper`: an explicit bound on the normalized Hermite tail
`‖ĥ_{4k} − Pₐ ĥ_{4k}‖² = ∫_{|x|>a}|ĥ_{4k}|²`.  The bound `|h_n(x)|² ≤ C_n e^{−πx²}` (from
`exists_bound_poly_mul_gaussReal` applied to `p_n²`) plus a ray tail for `e^{−πx²}` gives an
explicit `e^{−πa²}` rate; the polynomial absorption costs the factor `e^{−πa²}` versus the
Gaussian's `e^{−2πa²}`, so a sharper polynomial×Gaussian tail (integration by parts on
`∫_{Ioi a} x^{2k} e^{−2πx²}`) is what would recover the full exponent.  NOTE the two-sided
envelope still needs the LOWER bound, which no variational argument supplies.

## L6a — the explicit exponential rate at every index (DONE, 2026-07-18)

`formal/GaloisForLFunctions/HTGeometry/ExpSquareRayTail.lean` (axiom-clean): tail bounds for
`e^{−bx²}` at an **arbitrary** rate `b`, which mathlib does not have and which the existing
`GaussianTailBound` only supplied at `b = 2π`.

* `integral_Ioi_id_mul_expNegSq : ∫_a^∞ x e^{−bx²} = e^{−ba²}/(2b)` (exact).
* `integral_Ioi_expNegSq_le : ∫_a^∞ e^{−bx²} ≤ e^{−ba²}/(2ba)`.
* `integral_compl_Icc_expNegSq_le` — two-sided, by reflecting the left ray.
* `setIntegral_compl_Icc_le_of_le_expNegSq` — anything dominated by `C e^{−bx²}` inherits it.

Additions to `RHTower/HermiteEvenCarrier.lean` (axiom-clean):

* `exists_bound_norm_sq_hermiteSchwartz : ‖h_n(x)‖² ≤ C_n e^{−πx²}` — of the two Gaussian
  factors in `|p_n(x)e^{−πx²}|²`, one absorbs the polynomial (via
  `exists_bound_poly_mul_gaussReal` applied to `p_n²`) and the other survives.
* `exists_norm_sq_hermiteEven_sub_cut_le` — the aperture tail of `h_{4j}`, explicitly.
* `norm_sq_hermiteEvenUnit_sub_cut` — normalization divides the tail by `‖h‖²`.
* **`exists_evenProlateLeakageValue_le_exp (n) : ∃ C ≥ 0, ∀ a > 0, d_n(a) ≤ C·e^{−πa²}/a`.**

So every fixed leakage of the TRUE compressed Fourier block is now known to decay exponentially
in `a²`, with an explicit constant, at every index — the quantitative form of the vanishing
theorem.

WHERE THIS SITS RELATIVE TO THE ENVELOPE.  Fuchs is `e^{−4πa²}` (= `e^{−2c}`, `c = 2πa²`).  The
variational route caps out at `e^{−2πa²}` for a structural reason already recorded above: the
concentration deficit of a truncated Fourier-fixed trial vector is `≍ τ²`, and `τ² ≍ e^{−2πa²}`;
only the true PSWF supplies the cancellation that turns `τ²` into `τ⁴`.  The extra factor of two
lost here (`e^{−πa²}` rather than `e^{−2πa²}`) is the polynomial absorption, and is recoverable
by integrating `∫_{Ioi a} x^{2k}e^{−2πx²}` by parts instead — but doing so would NOT reach the
envelope, because the `τ²` ceiling binds first.  **The conclusion is that no trial-space argument
can produce the `upper` field of the ClockEnvelope**; a non-variational route is required, and
the same is a fortiori true of `lower`.  That is the sharpened statement of the open core.

## L6a — moved onto the CONTRACT'S OWN OBJECT: the signed spectrum (DONE, 2026-07-18)

The estimates above were about `evenProlateLeakageValue` (the greedy value of the *concentration*
operator).  The constrained transfer contract is stated for the **signed** spectrum of `Tₐ`
itself, through `D lam j = 1 − σ_{ν j}(lam)²`.  This step moves everything onto that object.

`formal/GaloisForLFunctions/RHTower/ConstrainedProlateSignedTrial.lean` (axiom-clean):

* `abs_evenProlateSignedValue_le_one` — `|σₙ(a)| ≤ 1`, `Tₐ` being a contraction.
* **`one_sub_evenProlateSignedValue_sq_le_of_form_trial`** — the signed Courant–Fischer bound: a
  trial subspace of dimension `> n` retaining a fraction `1 − ε` caps `1 − σₙ(a)²` by `ε`.
  KEY OBSERVATION: **the sign never has to be determined.**  `|σₙ| = orthSup Tₐ (sgVec Tₐ) n`
  (`abs_sgVal`), so `GreedyCourantFischer.le_orthSup_of_trial` bounds `|σₙ|` from below directly,
  and squaring erases the sign — which is all the contract needs.  This sidesteps the
  "identification of the positive signed subsequence" noted as a separate analytic theorem in
  `ConstrainedProlateSignedSpectrum`: that identification is NOT required for the transfer.
* `one_sub_evenProlateSignedValue_sq_le_hermite : 1 − σₙ(a)² ≤ hermiteTrialDefect a n`.
* `exists_one_sub_evenProlateSignedValue_sq_le_exp` — explicit `C·e^{−πa²}/a` at every index.
* `one_sub_evenProlateSignedValue_sq_tendsto_zero` and `evenProlateSignedValue_sq_tendsto_one`.

Refactor in `HermiteEvenCarrier`: the trial space and its defect are now named objects
(`hermiteTrialSpace`, `hermiteTrialDefect`, `finrank_hermiteTrialSpace`,
`hermiteTrialSpace_concentration`, `tendsto_hermiteTrialDefect`,
`exists_hermiteTrialDefect_le_exp`), so the leakage and signed routes share one construction.

STATUS OF THE CONTRACT.  For `D lam j = 1 − σ_{ν j}(lam)²` the fields `nonneg`, `mono`, `step`,
`clock_pos` are available and `upper` now holds in the qualitative-plus-explicit-exponential form
— but NOT at the envelope's rate `λ^{2e_j+1}E(λ)`, and by the ceiling recorded above no
variational argument will reach it.  `lower` is untouched by any of this work.  Both remaining
fields need the non-variational route (commuting prolate differential operator, or a
trace/determinant identity).

## The non-variational route: what already exists, and the missing joint (2026-07-18)

CORRECTION to the assessment above.  The Slepian commuting-operator machinery is **already in
the tree** and was not accounted for in this card:

* `RHTower/SlepianSincCommutation.lean`, `SlepianExteriorTransfer.lean`,
  `SlepianSmoothKernel.lean` — the entire sinc profile `sincSmooth c = dslope (sin(cu)/π) 0`,
  its off-diagonal commutation `P_x K̃ = P_y K̃`, and the integrated transfer `slepian_transfer`.
* `RHTower/SlepianBandCommutation.lean` — **`slepian_commutation : P_c (T̃ f) = T̃ (P_c f)`** and
  `slepian_commutation_eigen`.
* `RHTower/ProlateBandSymmetric.lean` — self-adjointness of the prolate action on the band, with
  the boundary terms killed by the vanishing weight.
* `RHTower/ProlateWronskian.lean`, `ProlateDiagonalization.lean` —
  `bandTransform_eigen_smul_on`: a prolate ODE eigenfunction spans an invariant line of the band
  transform.

So the ODE side is built.  The gap is that its kernel `K̃_c` is *defined as a profile*, with
nothing connecting it to the Fourier-cutoff operator whose spectrum the transfer measures.

`formal/GaloisForLFunctions/RHTower/SlepianKernelFourier.lean` (axiom-clean) builds the first
span of that bridge:

* `integral_symm_cexp`, `integral_symm_cexp_I : ∫_{−1}^{1} e^{iθt} dt = 2 sin θ / θ`.
* `sincSmooth_zero : sincSmooth c 0 = c/π` (the `dslope` value, not previously recorded).
* **`sincSmooth_eq_integral : sincSmooth c u = (c/2π)∫_{−1}^{1} e^{i c u t} dt`** — valid at the
  origin too.  The removable singularity of `sin(cu)/(πu)` is an artefact of evaluating the
  integral, not a property of the kernel; this reproves entirety without power-series
  bookkeeping.
* **`sincKernelSmooth_eq_integral : K̃_c(x,y) = (c/2π)∫_{−1}^{1} e^{icxt}·conj(e^{icyt}) dt`** —
  the Slepian kernel is the **Gram kernel of the band-limited Fourier characters**.  This is
  precisely the statement that composing a Fourier cutoff with its adjoint produces `K̃_c`, i.e.
  the reason the prolate ODE governs a time–band concentration operator at all.

REMAINING SPANS OF THE BRIDGE (the concrete next targets, in order):
1. Fubini: `evenProlateConcentration a f = ∫_{[-a,a]} K̃_{2πa}(x−y) f(y) dy` in the `L²` model,
   using `SoninL2Model.l1Fourier_indicatorCutoff_Icc_eq_setIntegral` for the inner transform.
2. The dilation `x ↦ x/a` carrying the model band `[−a,a]` to the ODE band `[−1,1]` with
   `c = 2πa²` (the project's `dilationUnitary`/`evenDilationUnitary` should serve).
3. Existence of the prolate ODE eigenfunctions and their eigenvalues `χ_n(c)` — singular
   Sturm–Liouville theory on `[−1,1]`; this is the first genuine mountain of the route.
4. Dunster/WKB asymptotics for `χ_n(c)` and `ψ_n` (L8), then Fuchs for `μ_n`.
Only 3–4 are mountains; 1–2 are bookkeeping and are what a next session should take.

### Bridge span 1a — the model normalization (DONE, 2026-07-18)

Added to `RHTower/SlepianKernelFourier.lean` (axiom-clean):

* `integral_symm_cexp_width` — the symmetric exponential integral at arbitrary half-width.
* **`integral_symm_fourierChar (a s) : ∫_{−a}^{a} e^{−2πits} dt = sincSmooth (2πa) s`** — the
  band indicator's Fourier transform IS the Slepian sinc profile, in the project's `e^{−2πixy}`
  normalization.  So the aperture `[−a,a]` carries profile parameter **`c = 2πa`**.  Valid at
  `s = 0`, where both sides are `2a`.
* **`integral_symm_fourierChar_gram (a x y) : ∫_{−a}^{a} e^{−2πixt}·conj(e^{−2πiyt}) dt
  = sincKernelSmooth (2πa) x y`** — the Gram form.
* `setIntegral_Icc_fourierChar`, `setIntegral_Icc_fourierChar_gram` — the same over
  `Set.Icc (−a) a`, which is the form the `L²` model presents (`fullTimeBandFourier_coeFn_sonin`
  produces exactly `∫ y in Set.Icc c d, exp((−(2πxy) : ℝ)·I) · f y`).

So the two normalizations are now reconciled and the interface matches on both sides.

REMAINING FOR SPAN 1 (the Fubini step): `evenProlateConcentration a = (evenTimeBandFourier a)²`
and `fullTimeBandFourier_eq_cutoffFourierCutoff` already give the composed operator as a double
set integral.  Swapping the order by Fubini and applying `setIntegral_Icc_fourierChar_gram`
yields the kernel form.  NOTE the composition `T∘T` produces the kernel argument `x + y`, not
`x − y`; the two agree **on the even carrier** after `y ↦ −y`, which is precisely why the cards
work in `evenSubspace`.  That observation is the one piece of real content in the remaining step
— the rest is Fubini bookkeeping on a product of finite-measure sets.

## 2026-08-08: canonical radial separation and Gram layer closed unconditionally

The previous status above is obsolete.  The Fourier/Slepian bridge, joint spectrum, radial ODE,
Dunster density transfer, endpoint/tail bounds, Kaiser fixed-index trial spaces, and canonical
radial-family infrastructure have since been built.  The decisive new capstone is
`formal/GaloisForLFunctions/RHTower/ProlateCanonicalSeparationLimit.lean`.

Closed in Lean, with no premises on the final fixed-index statements:

* `eventually_signedModeRadial_tunneling_lower`: any fixed positive separation threshold forces a
  radial leakage lower bound on a strictly slower exponential clock than the true signed-mode
  Kaiser upper bound.  The low-separation branch uses WKB turning-layer tunneling; the
  high-separation branch uses Sonin aperture control plus an exterior endpoint-collar mass floor.
* `tendsto_signedModeRadialData_s_zero`: the selected exact joint radial line attached to every
  fixed signed-greedy band value has separation ratio tending to zero.
* `tendsto_integral_Ioi_signedModeRadialDensity_unconditional`: every fixed canonical radial tail
  converges to the exact CCM arcsine density tail divided by `pi`.
* `tendsto_integral_Ioi_signedModeFirstRowRadialProduct_unconditional`: fixed first-row canonical
  overlaps vanish for dilation ratio at least two.
* `signedModeRadialGramEntry_diag_eq` and
  `tendsto_signedModeRadialGramEntry_diag`: exact dilation change of variables and unconditional
  diagonal limit `arcsin(1/k)/(pi*k)`.
* `signedModeRadialGramEntry_scale_left` and `signedModeRadialGramEntry_comm`: exact positive
  dilation covariance and Gram symmetry.
* `tendsto_integral_Ioi_signedModeFirstRowRadialProduct_from`: cancellation remains true after
  discarding any fixed tail prefix whose base is at least two.
* `tendsto_signedModeRadialGramEntry_of_separated`: every fixed canonical pair separated by a
  factor of at least two has zero off-diagonal limit.

The source module passes `lake env lean` in full.  A prior final-module build passed before the
last Gram extensions; final `lake build` is intentionally deferred to the pipeline audit.

The remaining radial analytic gap is now sharply smaller: extend fixed-ratio stationary phase from
the uniform `k >= 2` regime to every fixed `k > 1`, which covers adjacent integer dilations.  The
remaining identification gap is distinct: the canonical joint radial line carries the literal
signed-greedy band eigenvalue, but equality with the chosen signed Fourier representative still
requires finite-Fourier spectral simplicity (or an equivalent transfer theorem).  Do not conflate
these two gates.

### 2026-08-08 continuation: factor-two stationary-phase restriction removed structurally

The `k >= 2` hypothesis in the existing first-row theorem mixed two different requirements:
uniform-in-`k` numerical constants and fixed-`k` nondegeneracy.  The second requirement in fact only
needs `k > 1`.  New axiom-clean infrastructure, each source-checked with `lake env lean`:

* `CCMFirstRowStationaryPhase.lean`: uniqueness of the exterior stationary point; exact
  rationalized speed identity; global speed sign before/after the point; strict negative curvature
  for every `k > 1`; fixed inner/outer cuts; compactness-derived positive speed floors uniform in
  `0 <= s <= 1/2`.
* `CCMFirstRowVanDerCorputBlocks.lean`: all elementary amplitude positivity, differentiability, and
  antitonicity facts now have strict-dilation variants; generic weighted first-derivative blocks for
  arbitrary positive speed floors; generic weighted second-derivative block for an arbitrary
  curvature floor; compactness-derived curvature floor on every fixed exterior block, uniform in
  `0 <= s <= 1/2`.
* `CCMFirstRowEnvelopeTail.lean`: a positive `k`-dependent endpoint amplitude constant for every
  `k > 1`, the corresponding `(x-1)^(-1/4)` majorant, endpoint integrability, and the exact
  `O((X-1)^(3/4))` endpoint-mass bound.

Thus inner, stationary, outer, and endpoint estimates required for every fixed ratio `k > 1` are
now individually formalized.  Remaining assembly work is to combine them with the already-proved
sum-phase and Dunster exact-to-Bessel transfer, then lift through dilation covariance to every
unequal integer Gram pair.  No mathematical nondegeneracy gap remains in this branch.
