# Route T Maynard fixed-width gap-shell assembly

- **ID:** `route-t-maynard-fixed-width-gap-shell-assembly`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / THEOREM (Lean)
- **Source:** ordered-prime gap occupancy, fixed-width prime-free packet, spatial Mellin energy,
  selected-cell two-alternative count
- **Target:** unconditional consecutive-prime-gap square-prefix moment of exponent strictly below
  `3/2`, hence unconditional Route-T critical log-mesh energy.

## Corpus state

Corpus already proves separately:

1. one dyadic ordered-prime gap shell has square mass at most eight times its prime-free occupancy
   measure;
2. fixed proportional prime-freeness produces one large rung of a fixed-source adjacent Mellin
   packet;
3. all possible rungs lie in one finite canonical union;
4. every fixed packet splits exactly into base-amplitude and positive dyadic amplitude layers;
5. base layer obeys spatial `L²`, positive layers obey receiver-normalized selected-cell counts,
   and spatial `L⁴` retains exact additive energy `R*`.

No module composes these facts into a measure bound for an actual prime-gap shell or into the final
prefix second moment.

## Heavy conjecture loop

### C1 — fixed-width shell cover `[ACTIVE]`

For each admissible fixed proportional width, literal prime-free bases in the canonical physical
block lie in a finite union of fixed-source packet superlevel sets. The union and every packet are
chosen before the physical base varies.

This removes the quantifier-order obstruction between pointwise Perron localization and spatial
integration.

### C2 — base/positive energy cover `[PENDING]`

Split every rung superlevel set into the canonical base-amplitude bad set and the complement. Bound
the former by the exact base `L²` theorem. Cover the latter by positive dyadic bands and force the
second selected-cell alternative before applying spatial energy. Retain `L⁴/R*` as an independent
additive-energy branch rather than replacing it by a cubic cardinality bound.

### C3 — shell square-mass theorem `[PENDING]`

Compose C1–C2 with ordered-prime occupancy. Sum the length shells without losing the strict
sub-`3/2` exponent. Then pass through `XiHeatCassiniPrimeGapMomentBigOBridge` to critical Route-T
mesh energy.

### Failure rule

If C2 cannot close, isolate an explicit finite-energy obstruction: exact base or band term, exact
scale, and whether the obstruction is cardinal, additive-energy, or quantifier-order. Do not pivot
to cutoff or constant optimization.

## Novelty status

Maynard--Peck's final prime-gap moment is classical. The fixed-source spatial cover and its exact
base/positive/additive-energy trichotomy are corpus-native and appear not to be stated in the
literature. External novelty is not claimed until the completed theorem is compared with current
literature.

## Formal status

Not yet formalized. Frontier map remains read-only.

## 2026-08-28 C1/C2 frontier update

- C1 is Lean-closed in `MaynardFixedWidthPrimeGapRungCover`: one canonical source packet family,
  chosen before physical base, covers every fixed-width prime-free base.
- Exact low/high ordinate-shell refinement is Lean-closed. Reparameterization preserves the
  Heath--Brown eligibility threshold; it does not assume the canonical support cutoff is exactly a
  height power.
- Central and quadratic-tail cell extraction are Lean-closed with source cutoff `M` independent of
  physical Mellin cutoff `N`. This removes a hidden scale identification in the earlier receiver
  path.
- Arbitrary spaced-sequence receiver and first-alternative exclusion now reach the natural
  `mu ≤ 11/5` physical-cutoff ceiling.
- Central-shell C2 is Lean-closed: every arbitrary central interval of length at least two carrying
  fixed positive signed defect forces Maynard's second alternative, with exact even-cell partition,
  no endpoint trimming, and source/physical cutoff independence.
- Active conjecture `C2-tail-normalized`: quadratic Mellin decay should turn an outer-shell defect
  `B` into normalized receiver mass `D` whenever
  `65*C*(N/R)^2/U^2 ≤ 4*B/D`; then the same `11/5` forced-second theorem applies. This is the next
  open mathematical core, followed by summing the finite low/high/rung cover in measure.

## 2026-08-28 C2 receiver closure

- `C2-tail-normalized` is Lean-closed, first for aligned gap sequences and then for every outer
  interval of length at least two. Quadratic tail cost converts raw defect `B` to arbitrary positive
  receiver mass `D`, after which the second Maynard alternative is forced.
- The canonical support/receiver mismatch is resolved rather than assumed away. For adaptive
  amplitude below one, receiver scale enlargement costs only its fixed support distortion; above
  one, the negative first-alternative exponent makes enlargement cheaper. Canonical ceiling support
  and real eligibility scale are within factor `4/3`.
- Every matched shell height in `[T₀^(8/11),T₀]` has exponent in `[4/3,11/5]`, and its Möbius-cutoff
  scale is exactly transported. The resulting canonical height-matched receiver theorem has no
  exact-support-power premise.
- Fixed defect was removed from first-exclusion. A deterministic selector-budget theorem and its
  variable-threshold forced-second receiver allow `D` and band budget `Q` to depend on height. This
  is required by literal rung and ordinate-shell pigeonholing.
- Remaining open core: choose a terminal-shell convention with no sub-length-two residue; prove the
  rung-count and shell-count selector budget for the literal variable defect; then sum low/base,
  positive second-count, and additive-energy bad measures over the fixed cover.

## 2026-08-28 literal selector and terminal-shell closure

- The literal selector budget is Lean-closed. Canonical packet-width admissibility bounds the
  stopped-width ratio by ambient height; both width-rung and ordinate-shell counts are linear-log.
  Together with amplitude-band depth and degree-60 box selection, the exact defect left by the
  finite cover is absorbed uniformly on every height-matched shell.
- The resulting high-shell receiver is Lean-closed with no fixed-defect or selector-cost premise:
  the actual rung-divided and shell-divided defect forces Maynard's second alternative.
- Terminal-shell obstruction is Lean-closed by a dyadically aligned lower ordinate. Moving the
  desired floor upward by less than factor two makes the upper/lower ratio an exact power of two.
  Every positive-defect shell is then exactly `[T,2T]` and has length at least two; all later
  stopped indices are zero packets. No short residual interval remains.
- Remaining C2 core is measure-theoretic/analytic rather than combinatorial: apply base `L²`,
  positive-band second-count `L²`, and independent `L⁴/R*` bounds to every literal cover member,
  then sum the finite family and feed ordered-prime gap occupancy.
