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
- [~] **L2 — eigenvector transfer** (`ConstrainedProlateSecularVector.lean`, 6 theorems banked):
  coordinate eigen-equation, constraint membership `Σℓ_jv_j = 0` at the exact root, squared tail
  bound `T/(d_2−μ)²` (card 1 eq (20)), head floor `ℓ_0²/d_1²`, two-mode head orthogonality at
  `μ_2mode`, and the family collapse `Σ_{j≥2}v_j²/v_0² → 0` at rate `(λd_1/(d_2−d_1))²`
  (eq (21)).  Remaining L2b: head-direction Lipschitz (22) and the normalized ℓ²-distance form
  of eq (4).
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
- [ ] **L4 — operator identification (lp 2)**: the compression of the diagonal leakage operator to
  `ℓ^⊥` on `lp 2`; its eigenvalues in `(d_0,d_1)` are exactly the secular roots with coordinates
  (14)/(13); min–max interlacing `d_k ≤ μ_k ≤ d_{k+1}` at operator level.  Closes the cards'
  operator-form phrasing.
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
- [ ] **L6 — Fuchs fixed-index asymptotics** for the true prolate eigenvalues
  `1−χ_n(λ)² ~ A_n λ^{2n+1} e^{−4πλ²}` (card 1 eq (8)).  Mountain: needs PSWF spectral theory +
  Bessel/WKB asymptotics; nothing in mathlib.  Sub-plan to be written when L1–L5 are banked
  (`prolate_eigen_hermite_defect` in `FuchsProlateScale` is the seed).
- [ ] **L7 — prolate-to-Hermite limits** `ℓ_j(λ) → a_j` (card 1 eq (10), card 2 eq (17), card 3
  eq (3)).  Mountain: Hermite eigenfunction theory (`HermiteOscillatorEigen` is the seed).
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
  discharging the `hsum`/`hbessel` hypotheses of every exact transfer theorem).  All modules umbrella-wired and
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
