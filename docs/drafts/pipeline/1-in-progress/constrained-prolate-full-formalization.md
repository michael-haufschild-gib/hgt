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
