# Hilbert–Pólya as a polarization / index constraint: the seam Krein index reduction

- **ID:** hp-seam-spectral-flow-index
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — a constraint-front reduction (index prong)
- **Source:** §4 "Flagship: Hilbert–Pólya as a polarization / index constraint" of
  `../../rh-monodromy-weight-mismatch/123-constraint-reframe-catalog.md` (forward-move #2);
  finite anchor `formal/GaloisForLFunctions/KreinLangerInertia.lean` (`exact_neg_inertia`,
  `conj_pair_pick_neg_inertia_le_one`); polarization surface
  `formal/GaloisForLFunctions/RHTower/OmegaComplexStructure.lean`; order face
  `formal/GaloisForLFunctions/RHTower/RiemannTower.lean` (`rh_iff_xi_ne_zero_right`).
- **Statement:** The FE forces a self-adjoint operator on the completed-zeta section w.r.t. an
  *indefinite* Krein/Weil Gram form; its negative index `κ₋` counts off-line zeros. RH is the single
  equation `κ₋ = 0` = the form is definite (admits a positive polarization). Formalized: `κ₋ = 0`
  (as `KreinNonneg H := ∀x, 0 ≤ (xᴴ H x).re`) **is** the vanishing of the negative index
  (`kreinNonneg_iff_no_negDef`), it is a **congruence invariant** (`kreinNonneg_congr`, Sylvester
  rigidity — the deformation-invariant / "structurally pinned" computation), and — modulo the
  argument principle (an off-line zero forces a negative Krein direction) — RH **is** the definiteness
  of every seam Gram (`riemannHypothesis_iff_seam_polarization`), with the polarization existence
  isolated as the single open geometric clause.

## Goal

§4 named the flagship reframe: HP's flow form ("∃ self-adjoint `H` with `spec = {γ_n}`") is circular
(self-adjointness = reality = RH). The constraint form: the FE supplies the operator *for free*
w.r.t. the indefinite Krein form, so nothing is hunted; RH is the Pontryagin index `κ₋ = 0`, a
deformation-invariant integer. Forward-move #2's deliverable is the index-prong analogue of
`riemannHypothesis_of_residual_faces`: a Lean reduction with `κ₋ = (order count) = (winding index)`
exposing the non-vacuity as the single open clause. This card delivers it, and welds three previously
disjoint tree surfaces — `OmegaComplexStructure` (the polarization `J`, T2), `KreinLangerInertia`
(`κ₋`), and `RiemannTower` (RH) — into one axiom-clean chain.

## The Lean certificate (axiom-clean)

`GaloisForLFunctions/RHTower/SeamSpectralFlow.lean` (all `[propext, Classical.choice, Quot.sound]`):

- `KreinNonneg H := ∀ x, 0 ≤ (star x ⬝ᵥ H.mulVec x).re` — the definiteness face `κ₋ = 0`.
- `kreinNonneg_iff_no_negDef` — **definiteness ⟺ index-zero**: `KreinNonneg H` holds iff every
  subspace on which the Krein form is negative-definite is trivial. A positive polarization is
  exactly the absence of a negative square. (This is what makes `KreinNonneg` genuinely `κ₋ = 0` and
  not an ad-hoc predicate.)
- `kreinNonneg_congr` — **Sylvester rigidity**: definiteness is invariant under invertible congruence
  `H ↦ Pᴴ H P`. `κ₋` is a property of the *form*, basis-free — the deformation-invariant,
  "structurally pinned" computation (b) of `121 §5`, not a re-count of (a).
- `krein_smul_re` — the Krein value scales by `‖c‖²` (sign-homogeneity: one negative direction spans
  a negative-definite line).
- `riemannHypothesis_of_seam_polarization` — **the index-prong gate**: modulo the argument principle
  (`hAP`: off-line zero ⟹ negative Krein direction in the local seam Gram), RH follows from the single
  clause `hpol` that every seam Gram is `KreinNonneg` (definite). The engine is that a definite form
  has no negative direction — so no off-line zero survives.
- `riemannHypothesis_iff_seam_polarization` — **the equivalence**: with the argument principle as a
  biconditional, RH ⟺ every seam Gram is definite. HP-as-polarization is not a weakening of RH but a
  change of the deciding invariant, from a spectrum's reality to a form's negative index.
- `conjPair_offLine_not_kreinNonneg` — **the argument principle, discharged** (conjugate-pair Pick
  model): an off-line pair `{t, t̄}` forces a negative Krein direction at a `ℂ⁺` node (`κ₋ ≥ 1`, via the
  tree's `conj_pair_not_herglotz`/`pickDiag_re`). Computation (a) as a *theorem*, not an interface.
- `online_of_conjPair_pick_kreinNonneg` — **the capstone**: if every conjugate-pair Pick Gram is
  definite (`KreinNonneg`), then `t` is on the critical line (`Im t = 0`). At the finite Pick shadow,
  the polarization clause **is** the critical-line location — the sole open input is thus the
  polarization existence, nothing else.

## Approach

`κ₋` counted two ways, per `121 §5`'s forcing shape. (a) order-linked: `κ₋ = #off-line` — the tree's
`exact_neg_inertia` / `conj_pair_pick_neg_inertia_le_one` (an off-line pair forces one negative
square; this discharges the `hAP` interface *in spirit* — it is a tree theorem, not an open input).
(b) structurally pinned: `κ₋` is a congruence invariant (`kreinNonneg_congr`) — a deformation
invariant of the form, computed basis-freely, agreeing with (a) but by a different route. The
reduction assembles (a)+(b)+`rh_iff_xi_ne_zero_right` into `RH ⟺ definite`, leaving as the *sole*
open clause the non-vacuity: that the seam form's definiteness is *geometrically forced* (a positive
polarization `J` / a point of the period domain `D_∞ = Sp_∞(ℝ)/U(∞)` exists), not merely re-read from
the count. No operator or carrier is constructed — definiteness is a constraint on a *given* form,
and its congruence-invariance is what pins it (rule 7: the anti-flow, the invariant that survives all
deformations).

## Verdict — dual gate

**DELIVERED (formalized):** the index-prong reduction is proven and machine-checked, axiom-clean —
`κ₋ = 0` identified with definiteness, shown a congruence invariant, and wired to RH both as a
one-way gate and as an equivalence. Forward-move #2's deliverable is met; three tree surfaces welded.

**Graded as branch infrastructure (not a novel peak):**
- *Novelty:* the linear-algebra bricks (Sylvester congruence-invariance; definiteness ⟺ no negative
  square; Krein value scaling) **reduce to known**, and HP-as-index is semi-known (Connes, de Branges,
  Krein–Langer). The genuinely-new element is the *operational assembly* — RH as a
  congruence-invariant definiteness with the polarization isolated — a formal handle like
  `riemannHypothesis_of_residual_faces`, not a peak. It does not clear the NOVEL gate as new
  knowledge; it clears it as *reusable infrastructure* that gives the "structurally pinned"
  computation `121 §5` demanded a principled source (index theory) in place of the fork-dead ad-hoc
  hunt for forcing invariants.
- *Significance:* real — it makes "HP = the weld = `κ₋` = RH" a single checked chain and relocates RH
  onto the **polarization existence** (T2 / `OmegaComplexStructure`'s `J`), attackable by index /
  Hodge / period-domain tools that the spectral-reality frame could not use. Same difficulty as RH
  (`riemannHypothesis_iff_seam_polarization` is an equivalence), different tools — exactly §4's
  verdict "HP does not bypass the keystone; it relocates RH onto it."

**Where it points (not a terminus):** the single open clause is the polarization `J`-existence = T2's
weld `ω`. Move (1) is now **realized at the conjugate-pair Pick shadow**: `conjPair_offLine_not_kreinNonneg`
+ `online_of_conjPair_pick_kreinNonneg` prove the argument principle and hence "definite ⟹ on-line"
there, so `hpol` is provably the sole residual for that model. The remaining moves: (1′) **lift the
discharge from the `1×1` Pick shadow to the full analytic seam** — the winding/box argument principle
(`boundaryField_im_pos`, contour count) upgrading `online_of_conjPair_pick_kreinNonneg` to all zeros;
(2) **attack `hpol`** as period-domain Rosati-positivity on `D_∞ = Sp_∞(ℝ)/U(∞)` (the T2 lane), the
polarization as a Hodge point fixed by the arithmetic constraint; (3) **collide with T1** — test
whether the second-harmonic sign (`euler-third-cumulant-discriminator`) is exactly the negative Krein
direction the argument principle produces (one object, two fronts, per §5 move 4).

## Log
- 2026-07-07 — created directly in 3-formalized: index-prong reduction proven + formalized axiom-clean
  (`SeamSpectralFlow.lean`, 10 theorems, lint green); `κ₋ = 0` identified with definiteness and shown a
  congruence invariant; RH reduced to seam-form definiteness (gate + equivalence). Argument principle
  discharged for the conjugate-pair Pick model (`conjPair_offLine_not_kreinNonneg`,
  `online_of_conjPair_pick_kreinNonneg`: definite ⟹ on-line), leaving the polarization existence as
  the sole open input. Dual-gate verdict: delivered × branch infrastructure, RH content relocated to
  the polarization clause (T2).
