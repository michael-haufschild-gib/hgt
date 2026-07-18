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
- [ ] **L1 — infinite secular transfer** (`ConstrainedProlateInfiniteSecular.lean`, current phase):
  the exact secular function `F(μ) = Σ_{j≥0} ℓ_j²/(d_j−μ)` on the full index set; summability,
  continuity, strict monotonicity on `(d_0,d_1)`; existence + uniqueness of the exact root `μ_0`;
  the quantitative two-mode comparison `0 ≤ μ_2mode − μ_0 ≤ T·d_1²/(ℓ_0²(d_2−d_1))` (card 1 eq (18));
  the family theorem `μ_0/d_1 → a_0²/(a_0²+a_1²)` under explicit rate hypotheses
  (d_0/d_1 → 0, λ·d_1/(d_2−d_1) → 0, ℓ_0→a_0, ℓ_1→a_1, Bessel Σℓ²≤2λ); every other secular root
  ≥ d_1; gap corollary; CCM 8/11 + 3/11 instances; Fuchs-model instance.  This is the named
  "uniform infinite-tail secular estimate" gate of cards 1–3.
- [ ] **L2 — eigenvector transfer**: coordinates `v_j = ℓ_j/(d_j−μ_0)`; tail/head ℓ² ratio bound
  (card 1 eqs (20)–(22)); normalized-direction convergence to the two-mode seed and to the `w_k`
  contrast ladder (card 1 eq (4), card 2 vector claim, card 3 eqs (10),(22)–(23)).
- [ ] **L3 — negative sector + all-depth instances of L1/L2**: card 2 eqs (6),(9),(10) for the exact
  optimizer (indices 4j+2, 8/13, 5/13, parity floor ratio); card 3 eqs (8),(9) for exact `μ_k` at
  every depth (aggregate head; `θ_k`; λ⁸ ladder for the exact roots).
- [ ] **L4 — operator identification (lp 2)**: the compression of the diagonal leakage operator to
  `ℓ^⊥` on `lp 2`; its eigenvalues in `(d_0,d_1)` are exactly the secular roots with coordinates
  (14)/(13); min–max interlacing `d_k ≤ μ_k ≤ d_{k+1}` at operator level.  Closes the cards'
  operator-form phrasing.
- [ ] **L5 — true-operator scalar inputs**: from the existing concrete operator layer
  (`ConstrainedProlateOperator`/`SignedSpectrum`): the evaluation identity `ℓ_j = χ_j e_j(0)`
  (card 1 eq (1)) and the Bessel bound `Σ_j ℓ_j² ≤ 2λ` (card 1 eq (2)).  Discharges hypothesis
  (S5) of L1 for the true operator.
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

## Working rules (carry across sessions)

- One lake build at a time, foreground, `nice -n 19`, `LEAN_NUM_THREADS=2`; batch edits before
  building; verify every mathlib name in a scratch file first.
- After each module: `#print axioms` in scratch, umbrella import in `RHTower.lean`
  (or `HTGeometry.lean` for reusable analysis), `formal_tools.py index`, lint check,
  card Lean-decision + gates update, tick the layer here.
- Dead routes and design decisions land in this card, not in memory.
