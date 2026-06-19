# Library ticket — index/status updates for the gauge-reframe + ω-coupling crux (two new 0-backlog cards)

- **Owner:** librarian (index/status keeper)
- **Filed by:** session agent (gauge-constraint thread)
- **Date:** 2026-06-19

## What happened
A chat thread read the completed `(σ_p,∂_s)`-system as a **constrained gauge theory** (Dirac/BRST). SO-1
check done: the `ω`-as-multiplicative-anomaly *computation* is already banked (`compute-omega-h2-gl.md`
§S–§W; `substrate-hypothesis.md` §6–§7), so it was **not** re-filed. Two **genuinely new** items were carded
in `0-backlog` (grep-confirmed the gauge/BRST/Wilson/Wess–Zumino/inflow framing and the coupling-vs-
orthogonality collision were absent from `drafts/`):

1. **`0-backlog/gauge-constraint-brst-reframe.md`** — STRUCTURAL (organizing lens), FOUNDATIONAL. The
   gauge dictionary (`{σ_p},∂_s`=gauge potential; `F_{pq}`=field strength; holonomic=pure gauge/flat;
   non-holonomic=curved; FE=Gauss-law first-class constraint; `G_L`=gauge group; **`ω∈H²(G_L)`=Schwinger/
   Mickelsson–Faddeev gauge anomaly**; G5 unitary holonomy=Wilson-loop unitarity; A2=WDW timelessness).
   Load-bearing content beyond analogy: (a) **BRST mechanism** "compute the obstruction, not the quotient" =
   a *mechanism* for the substrate-hypothesis D-axis verdict; (b) **anomaly-inflow recipe** `ω(ℚ)` =
   `F_q`-bulk trivializer subtracted; (c) **Wilson-loop reading of G5**. Pure-analogy parts graded EMBASSY;
   the three handles graded STRUCTURAL. Does **not** re-derive the `ω` computation.

2. **`0-backlog/omega-rh-coupling-vs-orthogonality.md`** — CONJECTURE (native), FOUNDATIONAL. Names a
   **collision the pipeline never posed**: `compute-omega-h2-gl.md` §U/§V's chain `ω=0⟺DSS⟺RH` (**coupling**,
   hence DSS⟺RH) vs `faces-orthogonality.md` #54 + foundations §3 (**orthogonality**, RH⊥DSS). New tool: the
   BRST mechanism reduces the decision to one implication **`ω≠0 ⟹ ι≠κ`** (#35). Flagged as the **soundness
   test of the A1∧A2 unification aim**. Conjectured answer: decoupling (II) — `ω` is the realization/Stieltjes
   anomaly; RH needs a separate archimedean polarization; the §U `⟹RH` link is the likely over-claim.

## Suggested status edits (00-status.md §C — assign next free row numbers, ~#165/#166)
- **New row (gauge reframe):** "completed `(σ,∂)`-system as a constrained gauge theory (Dirac/BRST); `ω`=gauge
  anomaly, G5=Wilson-loop unitarity, FE=Gauss law; BRST 'obstruction not quotient' = mechanism for the D-axis
  verdict; anomaly-inflow recipe `ω(ℚ)=F_q`-bulk trivializer subtracted" → bucket
  [[door-C5-irreducibility-and-door-2-retest]] / [[bucket-time-and-non-holonomic-time]] · Type STRUCTURAL
  (EMBASSY/STRUCTURAL split) · FOUNDATIONAL · card `gauge-constraint-brst-reframe.md`.
- **New row (coupling crux):** "is `ω` coupled to RH (`§U: ω=0⟺DSS⟺RH`) or orthogonal (`#54: RH⊥DSS`)? —
  reduces to `ω≠0⟹ι≠κ` (#35); soundness test of the A1∧A2 aim" → bucket
  [[door-C5-irreducibility-and-door-2-retest]] / [[bucket-A1-A2-unification-the-carrier]] · Type CONJECTURE ·
  FOUNDATIONAL · card `omega-rh-coupling-vs-orthogonality.md`.

## Suggested annotations on existing rows (cross-link the collision)
- **#27 (ω)** and **#71** (`ω=0⟺HP⟺RH`): add "the `⟺RH` (coupling) link is now explicitly contested by the
  coupling-vs-orthogonality crux (`omega-rh-coupling-vs-orthogonality.md`), which reduces it to `ω≠0⟹ι≠κ`."
- **#54 (faces-orthogonality)** and **#35 (`ι=κ⟺RH`)**: add "collided with the §U coupling chain in
  `omega-rh-coupling-vs-orthogonality.md`; the decider is `ω≠0⟹ι≠κ`."
- **#32 (`κ₋`=#off-line zero-pairs, Lean)** and **#33 (`m_ξ` Herglotz ⟺ `κ₋=0` ⟺ RH)**: add "read as the
  physical-Hilbert-space ghost count: `𝓗_phys`=the carrier, `κ₋`=negative-norm ghost states, RH=ghost-free
  `𝓗_phys`; the constrained-quantization two-step argument for decoupling (II) in
  `omega-rh-coupling-vs-orthogonality.md`."
- **#62/#138 (constraint-not-flow), #61 (WDW):** add the gauge row: "FE = the first-class (Gauss-law) constraint;
  the would-be flow is gauge (WDW); see `gauge-constraint-brst-reframe.md`."
- **substrate-hypothesis** linkage: note the BRST 'obstruction-not-quotient' lens supplies a *mechanism* for its
  D-axis verdict.

## Suggested index edit (door/00-index.md)
- In the [[door-C5-irreducibility-and-door-2-retest]] work-package list, add `gauge-constraint-brst-reframe.md`
  and `omega-rh-coupling-vs-orthogonality.md`. In [[bucket-A1-A2-unification-the-carrier]], add the coupling
  crux as the explicit test of whether A1 and A2 are one statement (the card challenges the unification aim).

## Grade / status caveat
No grade changes to any banked result. Both new items are 0-backlog. The crux card is a *question*, not a
claim; the gauge card is an organizing lens (EMBASSY/STRUCTURAL). The `ω`-computation status is unchanged.
