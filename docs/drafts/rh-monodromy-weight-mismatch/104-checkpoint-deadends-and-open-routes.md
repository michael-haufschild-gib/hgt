# 104 — Checkpoint: dead ends, open routes, research targets

**Register: SEARCH** (orientation page; every claim below carries its verdict-doc or Lean anchor;
nothing new is asserted here). Purpose: one page a fresh session reads *before* choosing an attack,
so no refuted branch is re-walked and every open core is named with its entry point. Supersedes
nothing; companions: `00-approach.md` (thesis), `05-task-board.md`, `lean_updates_codex.md` /
`lean_updates_codex2.md` (the formal change ledgers).

---

## 1. Machine-checked dead ends — Lean verdicts, do not re-attempt

- **[REFUTED, Lean] Weight-mismatch parity invariant** (doc 90; `WeightMismatchRefutation.lean`).
  The FE and Schwarz involutions on the zero-quadruple generate `V₄ ⊂ A₄` — every element even, no
  4-cycle on or off the line — and the quadruple carries total weight `4·ord(ρ)`, ℤ₂-trivial always
  (`quadruple_weight_parity_refuted`). The doc-89 route-b moonshot in its original ℤ₂ form is dead
  at theorem grade.

- **[REFUTED, Lean] Sharp MV-anchored pinning certificates beyond depth 3**
  (`RHTower/ShortWindowNoGo.lean`, 2026-07-06). Two global facts collide:
  the pinning geometry (quadratic containment + radii chain) forces every anchor window to length
  `U < 1` (`pinning_geometry_short_window`); and at `U ≤ 1` the sharp-carrier mean-value energy
  face is false for every `N ≥ 4` — the adjacent pairs alone put `N − 1` into the off-diagonal
  (`sharp_offDiagonal_ge`) against a diagonal supply capped at `U(1 + log N)`
  (`harmonic_Icc_le_one_add_log`). Capstone `sharp_pinning_certificate_depth_lt_four`: **any**
  window certificate carrying both faces has `N ≤ 3`, for every zero, height, and parameter
  assignment. The entire decoupled-ledger endpoint family is vacuous in its sharp MV
  instantiation. Redirect: anchors must come from designed coefficients with controlled
  off-diagonal (§3, window lane) or from non-mean-value sources (ball floors / minimum modulus).

## 2. Paper-grade verdicts — derivation- or measurement-backed (docs 79–85)

- **[REFUTED] Route C-direct** (doc 82): the registration gap — shallow creation events of the
  sharp carrier do not register at any fixed threshold; the honestly patched chain fails by
  `≥ 3–13×` at every threshold and height (exponential registration cost vs polynomially-walled
  certification). Links C-1..C-4 (ladder, window relation, domination, thick-dip counting) are
  sound, Lean-banked, and remain in service of other lanes.
- **[REFUTED as typed] Route B** (doc 85): the `V = O(1)` fixed-variance premise is false —
  `V(N) ≍ loglog N`, with a derivation-backed lower bound (singleton windows,
  `RouteBSupport.singleton_window_coeff`) and the corrected seed identity Lean-banked
  (`RouteBSeedGap.lean`). The heir **Route B′** (normalized program) survives with one analytic
  gate (§3).
- **[SUPERSEDED] Spur/DISC reader** (doc 79): replaced by the Rouché + Euler–Maclaurin counting
  island; `(S-mono)` survives only as a standalone conjecture.

## 3. Open routes and their named cores

- **Route A — GAF universality** (docs 55, 88). Bridge decomposed: a conditional-CLT part
  (provable-shaped, upward martingale over the prime filtration) × the **scalar-mixture identity**
  (the true residue: the conditional variance carries an `Θ(1)` relative fluctuation — the same
  mixture law as doc 87 §3, so Routes A and B′ share one open object). Entry: doc 88 §§1–2.

- **Route B′ — normalized mollified program** (docs 86, 87, 103). Open analytic gate
  **(SMOOTH-LOW)**: small-ball / 2D density of the smooth multiplicative packet with row masses
  `M_q ≍ e^{−γ}/2q`. Doc 103 built the missing brick class — the single-phase harmonic engine and
  its degradation law for non-isolated small primes. Open core: compose the engine across the
  packet (small primes enter every multiple's coefficient; the isolated-prime bricks do not
  apply). Entry: doc 103; consumer chain is machine-checked and waits on this gate alone.

- **Window-certificate / ladder lane** (docs 89, 91–101 + the formal spine). Status after this
  session: the sign face of the per-zero certificates is closed-form **except the anchor** — the
  short-interval second-moment face `S_b` is no longer independent data (point-to-mass converter,
  `CarrierMassFloor.lean`), envelope/first-moment/line-sup constants are theorems
  (`WindingFloor/WindingAmplitude/WindingCurvature/ResonanceClosedForm/EnvelopeDerivBound/
  CarrierLineSup`), and the whole arc is carrier-abstract (`MollifiedCarrier.lean`,
  `AnchorSupply.lean`: arbitrary real coefficients `b`, sharp = `b ≡ 1`). §1's no-go then pins the
  open core exactly where doc 89 put it: **the on-line anchor at short windows**, now as a global
  design constraint on the carrier as a whole —
  `offDiagonal(b) + orthogonal-correction < U·diagonal(b)` at `U < 1` —
  which the sharp carrier provably violates and a designed `b` must satisfy *jointly with the
  Jensen/engine/EM faces*. Either exhibiting such a `b` or proving a second no-go for a coefficient
  class is global knowledge.

- **Rung 1 of the ladder — `RHLadder 1`** (docs 91–93) — **NOT a shortcut route; RH-hard, with a
  mechanism-level obstruction to any forcing.** Statement: *no odd-order ξ-zero right of the line*,
  equivalently ξ has an analytic square root on `Re > ½` (`rhLadder_one_iff_even_order`,
  `rhLadder_iff_root`). The obstruction, sharper than doc 91's "no owned lever":
  - Every off-line zero `ρ` (`Re > ½`, order `m`) has its conjugate `ρ̄` **also** in the right half
    (same `Re > ½`) with `ord(ρ̄) = m` (Schwarz). Every structural input that could constrain the
    order is conjugation-symmetric and so factors through the **pair-sum `2m`**: symmetry orbits
    (FE+Schwarz), the deck cocycle on any conjugation-symmetric loop, and the Weil explicit formula
    (the one multiplicity-counting handle) all group `{ρ,ρ̄}` into `2m` — even for every `m`, hence
    blind to `m mod 2`. The only object isolating one `ρ` (a small loop's deck class `= m mod 2`)
    is Rung 1 itself, not a constraint on it.
  - The symmetry class **permits** odd `m`: a real even order-1 entire function — the shape of
    `Ξ(t)=ξ(½+it)` — can have *simple* off-line zeros (the real even quartic with roots `±(a±bi)`
    gives a simple quadruple `{ρ,1−ρ,ρ̄,1−ρ̄}`). So reality+FE+order-1 does not force even order;
    only ζ-specific arithmetic could, and all of it is blind to individual multiplicity parity
    (value-independence is jet-blind, doc 10 §7.1; the explicit formula is conjugate-paired).
  - **Terminal, no conjecture.** *Forcing* `RHLadder 1` as a strict intermediate (without assuming
    RH) has no handle — the obstruction above is a mechanism-level no-go — and it cannot be refuted
    either (an odd-order off-line zero requires disproving RH). But as a *consequence* it is already
    settled in Lean: `RiemannHypothesis → ∀ k, RHLadder k` is the forward half of
    `rh_iff_forall_ladder` (RiemannTower.lean — vacuous: RH leaves no right-half zeros), and
    `(R1)–(R7) → RiemannHypothesis` is `riemannHypothesis_of_residual_faces` (ResidualFaces.lean);
    composing, **`RHLadder 1 ⟸ (R1)–(R7)` is a proven corollary of the complete route.** There is
    thus no independent Rung-1 target: the standalone forcing is a mechanism no-go, and the corollary
    is already machine-checked.

- **Valuation-measure lane** (docs 98–101; `ValuationProfile/ValLimit/ValDefect` modules): the
  limit valuation measure, its Stieltjes form, mean-valuation density, and the density–depth
  defect are built; each doc names its next objects in its closing section (doc 101 §5 is the
  current tip).

- **Static skeleton — rank–codimension law** (doc 102): the value-orbit dimension equals the
  prime-exponent rank (finite case, promotion-grade proof + Lean brick); its honest boundary and
  the (XLD) connection are §4 of that doc.

## 4. The formal spine — route-free layering (pivot principle)

Three layers, enforced so that pivoting between routes replaces only the top one:

1. **Instruments** (route- and carrier-free): point-to-mass converter
   (`sq_integral_floor_of_anchor_slope`), moment-gap sign engine (`HardySignChange`), oscillation
   engines (`FirstMoment`), the archimedean envelope/winding calculus (digamma/trigamma verticals,
   winding floor/amplitude/curvature — properties of ξ's Γ-factor, shared by every route), phase
   collapse + energy split for any `w + χ·conj w` (`AnchorSupply` §1), generic MV floor, the
   general-coefficient mean-value theory (`SecondMoment`).
2. **Carrier families**: `completedMollG b N` for arbitrary real coefficients; the sharp carrier
   is the instance `b ≡ 1` (`completedMollG_one`).
3. **Endpoints / gates** (thin, route-specific): the pinning gates and ledger endpoints — the only
   layer a pivot rewrites, and the layer §1's no-go acts on.

A route candidate is an assignment of carrier + witnesses to the named faces; the closed forms make
failed assignments cheaply falsifiable (that is how the sharp instantiation died) and the face
vocabulary is how a **new** route enters without new infrastructure.

## 5. Research targets, ranked

1. **(SMOOTH-LOW) composition** — the single gate between Route B′ and its machine-checked
   consumer chain (doc 103's engine → full-packet small-ball bound).
2. **The mixture identity** — the shared residue of Routes A and B′ (docs 87 §3, 88 §2); one
   object, two routes pay.
3. **Designed-carrier anchor, settled globally** — exhibit a coefficient class satisfying the §3
   design constraint jointly with the remaining certificate faces, or prove the second no-go.
   Both outcomes are statements about the constraint system as a whole.
4. ~~**Rung 1 forcing**~~ — **removed from ranked targets** (§3): standalone forcing is a
   mechanism-level no-go (all structural inputs are conjugation-paired `→ 2m`, blind to `m mod 2`),
   and `RHLadder 1` is anyway a proven corollary of the complete route
   (`rh_iff_forall_ladder` ∘ `riemannHypothesis_of_residual_faces`). No independent target remains.
5. **Residual enumeration** — substitute the banked closed forms into the surviving gate once,
   globally, and exhibit `RH ⟸ ⟨short list of named ∀-statements⟩`: the formal answer to "what
   exactly does this constraint still ask of the world?"

The constraint-not-flow discipline for all five: each target is a *global* statement about the
system (a gate, an identity, a design law, a forcing, an enumeration) — per-window witnesses and
satisfiability examples are not progress and are not accepted as such.

---

## Addendum (same day): target 5 delivered

**[PROVED HERE]** `RHTower/ResidualFaces.lean : riemannHypothesis_of_residual_faces` — the
residual enumeration exists as a single axiom-clean theorem. RH follows from per-zero
certificates whose only non-formula content is carrier data: (R1) a line anchor
`m_J ≤ ‖g_N‖` at some height of the window, (R3a) a `g_N` sphere sup, (R5) a completed-carrier
sphere sup, (R7) EM closeness on spheres — plus four scalar comparisons among named closed-form
quantities ((R2) the sign-face budget inequality, (R3b/c) Jensen quotient and engine, (R6) the
outer cross/EM budget) and (R4) the archimedean floor. Every other estimate in the sign face is
internal. Ranked target 5 is closed; targets 1–4 stand, and target 3 (the designed-carrier
anchor) is now precisely "supply (R1) jointly with (R2)/(R3) at short windows" — the question
the no-go of §1 sharpened.

---

## Addendum 2: Rung 1 verdict — target 4 struck

**[VERDICT, verified against the tree]** `RHLadder 1` is not an independent target. (i) The
standalone forcing has a mechanism-level no-go: every conjugation-symmetric input (FE+Schwarz
orbits, symmetric-loop deck classes, the explicit formula) sees only the pair-sum `2m` of
`{ρ, ρ̄}` — even for every `m`, blind to parity — and the sole parity-separating object (the
non-symmetric small-loop deck class) *is* Rung 1, not a constraint on it. (ii) The symmetry
class permits odd order: a real even order-`≤1` function with a simple off-line quadruple
(quartic shape) satisfies every abstract constraint, so only parity-blind arithmetic could
force it. (iii) It cannot be refuted without disproving RH. (iv) As a consequence it is
subsumed: `(R1)–(R7) ⟹ ∀ k, RHLadder k` typechecks as
`rh_iff_forall_ladder.mp (riemannHypothesis_of_residual_faces hwin)` — verified in scratch,
not banked (pure composition, no quantifier moved). §3's Rung-1 bullet and ranked target 4
are hereby struck; the remaining ranked targets are (SMOOTH-LOW) composition, the mixture
identity, and the designed-carrier anchor — now sharpened by the anchor-disc coupling laws
(`AnchorZeroBudget.lean`, `WindingRigidity.lean`): any (R1) supplier must certify at radii
below the carrier's sign-change spacing, whose rate floor is the banked winding floor.
