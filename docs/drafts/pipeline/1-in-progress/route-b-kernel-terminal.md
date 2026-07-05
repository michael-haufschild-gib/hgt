# Route B ground to terminal state — (CR-density) via the mollified dip, full Lean or detailed refutation

**Claim under grind.** Route B (doc 56, doc 60 §4 W5, revived doc 82 §5): the
mollified carrier P = F_N·M_y (BV taper, y = N^θ) closes (CR-density) with
ε(c) = O(√c), conditional on the kernel (K-bdd) × (K-mild). Terminal states
admitted: (a) the kernel proven and the chain fully formalized in Lean;
(b) Route B refuted in all details (doc-82 grade: unsound link located or the
kernel walled against the certified instrument class).

**Status: IN PROGRESS** (goal opened 2026-07-05, session seed 1111089585816317988).

## Banked substrate (verified this session)
- Counting layer machine-checked: `MollifiedDip.lean` (`dip_measure_lower`,
  `separated_dips_count_le`, `sliverCount_le_of_average_kernel`,
  `sliverCount_card_le_of_average_kernel`) — (K-bdd) is the only real hypothesis.
- L² supply: `SecondMoment.lean` (dpoly/MV). Parity: `ParityCounting.lean`.
  Registration: `Registration.lean` — mollified class REGISTERS (κ² = O(1)).
- Numerics (doc 56 §9): P1/P2/P3 all passed; (K-bdd) empirically true, C ≈ 0.5,
  flat 2D density ≈ 0.1, N-stable; BV is the theorem object (sharp-μ variance grows).

## New this grind (cycle 52)
- **The line-zero atom wall [PROVED HERE (sketch), negative].** Any (K-bdd)
  route through ζ-sublevel transfer (R–S half-sum, doc 70 bricks) inherits
  ζ's on-line zeros as a linear atom: meas{|ζM_y| ≤ ρ} ≳ ρ·U — exponent 1,
  strictly below the needed >1 (doc 56 §5). Moment/Chernoff cannot beat it:
  E[(log⁻|ζ|)^{2k}] ~ (2k)!·polylog from the zero singularities. Parity
  excision of the atom reopens exactly ζ's own near-line pair census —
  circular. **The kernel is polynomial-native; doc 58 §4's split
  (K-bdd-∞) × (SPEC-decay) is FORCED, not optional.**

## Open items (the grind list)
1. Doc 56 §4 bookkeeping audit, doc-82 method: per-cell zero cap
   [lemma-shape], anchor pruning, (K-mild) consumption. Unsound-link hunt.
2. (K-bdd-∞): two-phase co-area + scale induction (task #9 write-out) —
   prove or refute. Engine constants from P4.
3. (TRANSFER)/(SPEC-decay): window↔model at MV level for the fixed smooth
   functional — prove or wall (degree-2 wall bounds the naive route).
4. (K-mild) native closure (Boutroux–Cartan deep tier + fixed-scale tier).
5. Numerics first (rng-picked): P4a/P4b/P5/P6 per prereg
   (computations/mwm_kbdd/prereg.md).
6. Lean: formalize every closing link; classical imports as typed interfaces.
7. Terminal doc + this card moves to 2-fully-proven(+3-formalized) or 5-failed.

## Dead routes (do not re-walk)
- ζ-transfer for the kernel (atom wall, above).
- Naive Fourier/moment expansion of φ_P (degree-2 wall, doc 58 §2).
- Naked-F_N small-ball (AC) (doc 56 §10 — FALSE as typed).

## UPDATE (cycle 52, verdict phase)
Doc 85 Part I written: Route B AS TYPED is REFUTED — doc 56 §3's V = O(1)
premise is (a) an unsupported citation on the boundary band (Graham covers
complete sums only), (b) measured false (V = −1.58 + 2.27·loglogN, six
designs, retrodicts V_BV(400) = 2.48), (c) derivation-backed:
V_bd ≥ c₀·loglogN via the singleton-window sub-family (b_{pd} = λ_d exactly,
no cancellation possible). In-class seed exhaustion complete (7 mechanisms,
each failure derivation- or measurement-backed). Lean:
RouteBSupport.lean — 6 endpoints axiom-clean (coefficient-vanishing,
squarefreeness, window-diagonal-only, singleton-window). Remaining: the
P-F5 fork (runpod) decides Part II — heir (K-bdd-n-log) vs total-class
refutation; then this card moves.
