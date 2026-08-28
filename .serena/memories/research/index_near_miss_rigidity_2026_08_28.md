# Index/parity rigidity — the near-miss programme (2026-08-28)

Card: `1-in-progress/index-parity-near-miss-rigidity.md` (full exploration; parent hub
`source-contraction-two-volterra-domination`, cycle 7).

## The one-line summary
Between zero-density and RH sits an unowned rigidity class. Exact dictionary:
κ_T (max negative eigenvalues of theta-Bezoutian sections, |Im nodes| ≤ T) = N_off(T)
(off-line zeros counted individually; TWO negative squares per off-line quadruple — verified on
the model quartic; Hurwitz-stable P ⟹ P′/P positive-real, index 0). Ladder: ≤ 0.583·N(T)
(Conrey line, known) → o(N(T)) (open) → κ < ∞ (open, beyond all literature) → κ = 0 (RH).

## C8 [CONJECTURE]: κ ∈ {0, ∞} — RH cannot fail finitely often
Equivalents: h = ξc′/ξc ∉ N_κ(ℂ₊) for 0 < κ < ∞ (Krein–Langer); no Ξ = Q·Ξ̃ with Q a finite
product of on-line-positive quartics and Ξ̃ real-rooted; no Φ = Q(−i∂)Φ̃ onto the LP cone.
Strictly weaker than RH. Finite κ ⟹ Lindelöf-grade upgrades + every schedule anomaly becomes an
EXACT κ-frequency Bohr polynomial (the compactness resource for contradiction-mining).

**Counterfeit boundary (crucial):** Ξ·(τ²−ρ²)(τ²−ρ̄²)/((τ²−γ₁²)(τ²−γ₂²)) is an even real
order-one FE-real entire with exactly one quadruple (κ = 2) — C8 is FALSE for the bare analytic
class; any proof must use the Euler orbit. Calibrates all claimed proofs (one unrefereed 2026
Academia.edu doc claims the statement — unverified; refereed literature: absent; Π_κ-de-Branges
structure theory exists (Kaltenbäck–Woracek), no zeta rigidity application).

## Live attack surfaces
- **A (Bohr vs subhalf):** finite spectra are syndetic-recurrent with exact torus-measure
  sublevel densities (κ=1-dominant: bad-set density 1/2). C8 ⟸ one unconditional source
  inequality "carrier ≥ −ε on log-scale density > 1 − η". This is verbatim the T2 lane's
  "signed subhalf continuation" frontier; RBH's separated-sign machinery is the corpus's
  finite-frequency classifier. Missing piece: a carrier with BOTH an unconditional
  positive-density one-sided bound AND single-quadruple sensitivity at matching normalization
  (CCM-FU PNT carrier: unconditional but insensitive; FCRJ floor: sensitive but unbounded —
  the gap between them is the target).
- **B (C9, FF/Perron–Frobenius template):** FF-RH = Lorentz index-1 (Hodge) + cone-preserving
  Frobenius + PF. Number-field slots corpus-present: SC's one-negative-square-per-fibre Krein
  form (Lorentz slot); Z = Σn^{−1/2}S_{log n} manifestly cone-preserving (Frobenius slot).
  [OPEN CORE]: the weld presenting the Weil form as Z's PF-complement on an SC fibre. First
  test: the two-atom truncation (all explicit; Lean witness
  `xiCentTwoAtomTruncation_witness_zero` must appear as a cone-boundary phenomenon of
  `1 + 2^{−1/2}S_{log 2}`).

## Killed this exploration
Shift-orbit amplification (half-line window term breaks packet shift-stability); abstract
Toeplitz/Smirnov 0-or-∞ dichotomy (S_κ classes realize every finite κ; surviving structure:
strip poles ⟺ the closed two-Volterra graph acquires a Beurling infinite-dim multivalued part);
Pontryagin symmetry-compression (form's symmetry group is only (ℤ/2)²); det-sign mod 2
(= counting).

## Queued Lean bricks
c-independence + nested monotonicity of section index (from the tilt congruence + corpus
inertia layer); the κ=2 counterfeit as a formal object (relocation machinery); the two-atom PF
cone test for C9.
