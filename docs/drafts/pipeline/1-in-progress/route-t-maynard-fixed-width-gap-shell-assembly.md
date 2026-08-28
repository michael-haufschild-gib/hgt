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

## 2026-08-28 natural-cell spatial and trivial-boundary closure

- Real-endpoint shells have been replaced by a ceiling-naturalized dyadic ladder. Every high shell
  is an exact integer-cell interval before physical base varies, telescopes exactly, has length at
  least two, and lies in a receiver band of ratio at most two. Equation-(111), equation-(112), and
  parity fibres now act on the literal same packet.
- A canonical prime-free cover by one low packet and finitely many fixed-source natural high shells
  is Lean-closed. No endpoint trimming, moving cell family, or terminal short shell remains.
- The historical low-amplitude seam was genuine: transition-strip receiver covered only
  `mu ≤ 19/9`, while the physical high-band receiver reached `mu ≤ 11/5` only from `alpha ≥ 3/4`.
  Corpus exponent audit showed the latter floor was non-sharp. The over-height zeta/log atom
  exclusion, subheight selection, colored fibre Montgomery estimate, global label sum, physical
  cutoff parity transport, and amplitude-band receiver are now Lean-closed from the exact
  trivial-count boundary `(1 + nu)/2` through `mu ≤ 11/5`.
- Consequently every positive natural-shell amplitude band has a frozen-source, original-base,
  amplitude-free forced-second bad-measure bound. The exact trivial-boundary base layer has the
  matching bound because `card (Ico A B) ≤ A` whenever `B ≤ 2A`.
- Remaining C2 core: combine the base layer and finitely many positive bands at the literal
  rung/shell defect threshold, use the already-proved selector budget to discharge every band
  first-exclusion premise, and sum the finite natural-shell cover. The independent `L⁴/R*` theorem
  is retained as equation-(112), but no longer needed to patch a low-amplitude receiver gap.

## 2026-08-28 whole-shell amplitude closure

- The canonical amplitude cap is now structural rather than endpoint-specific. For every fixed
  polynomial support exponent `mu < 4`, the complete frozen-source polylog envelope is strictly
  below the exact trivial-boundary base times the canonical dyadic depth. Thus `mu = 11/5` is an
  interior case, and no extra endpoint band is needed.
- Exact base-plus-band bad-set assembly is Lean-closed for arbitrary fixed-source physical packets.
  A large whole packet lies either in the base bad set or in one of finitely many band bad sets at
  threshold `D/(2Q)`; restricted real measures add with no independence assumption.
- One literal selector inequality now excludes the first Maynard receiver simultaneously on every
  exact trivial-boundary band. This is proved from the adaptive-envelope cancellation, not by a
  three-quarter amplitude floor.
- The whole canonical natural-shell equation-(111) is Lean-closed: base and every positive band
  have amplitude-free forced-second bounds, and their finite bad measures assemble into the full
  packet bound.
- The actual fixed-width rung/shell selector theorem has been welded to this result. At defect
  `((D_floor / rungCount) / 2) / shellCount`, rung loss, ordinate-shell loss, amplitude depth, and
  degree-60 box cost are all discharged internally. No amplitude-band, cap, or selector premise
  survives in `eventually_volume_routeT_fixedWidth_canonicalNaturalShell_full_forcedSecond`.
- Remaining C2/C3 burden is outside amplitude decomposition: sum these whole-shell bounds over the
  finite rung/natural-shell cover, add the low packet, then combine with ordered-prime occupancy
  without losing the strict sub-`3/2` moment exponent.

## 2026-08-28 hostile low-packet audit and common-mode replacement

- `[FALSIFIED]` The natural-cutoff low-cell cube does **not** close the actual fixed-width cover
  uniformly.  Its hypothesis `K * 2R/N <= 1` holds at the terminal target width but fails on the
  early wide rungs.  Consequently the isolated `11/5`, order-500 phase arithmetic is not an actual
  cover theorem and is not counted as Route-T progress.
- `[CONJECTURE]` Replace the whole width ladder by one fixed-reference common-mode split.  At one
  physical block with left endpoint `x`, put

  `r_x = 8 * x^(routeTPhysicalSliceHandoffTheta - 1)` and `U_x = x^(1/8)`.

  For `lambda in [x,2x]`, both additive widths `lambda*r_x` and `lambda*H0` are proportional to
  `lambda`, so the source packet remains frozen before `lambda` varies.  On `[-U_x,U_x]`, write
  each normalized Mellin kernel as the common point-mass character `lambda^(iy)` plus its width
  error.  The common character cancels exactly between reference and target.
- `[PAPER-PROVED]` The resulting endpoint defect has the exact decomposition

  `Full_r - Full_H = (Low_r - Low_H) + (High_r - High_H)`,

  where `High_w` is the full one-width integral minus its central `[-U_x,U_x]` integral.  If the
  full defect has norm at least `B` and the two low errors have total norm at most `B/2`, then
  `B/4 <= ||High_r||` or `B/4 <= ||High_H||`.  Proof: triangle inequality gives
  `B/2 <= ||High_r|| + ||High_H||`, followed by a two-term pigeonhole.  No width telescope or rung
  loss occurs.
- `[PAPER-PROVED]` The low errors are uniformly negligible on the literal Route-T schedule.  The
  corpus kernel estimate gives

  `||Low_w|| <= 8 * P_x * U_x^2 * w`,

  with `P_x` the frozen-source polylog envelope.  For `H0 <= r_x`, their sum is at most
  `16 * P_x * U_x^2 * r_x = 128 * P_x * x^(theta-3/4)`.  The corpus proves `theta < 3/4`, and its
  fixed-envelope absorption theorem makes `P_x` smaller than every positive power, so this tends
  to zero.  The common-band premise also holds because `U_x*r_x = 8*x^(theta-7/8) -> 0`.
- `[PAPER-PROVED]` The fixed reference has uniform positive density.  For
  `R=lambda*r_x`, let `z=lambda+R/2`.  Eventually `R<=lambda/4`; the corpus every-base handoff
  theta-mass interval at `z` lies inside the central plateau `[lambda+R/2,lambda+3R/2]`.  Since
  `lambda in [x,2x]`, one has `lambda^theta >= R/16`.  Hence the reference smooth von Mangoldt mass
  is at least

  `routeTSmoothWindowCentralMargin * R / 262144`.

  Together with the already-closed prime-power leakage theorem, a prime-free target supplies a
  fixed endpoint defect `B>0`.  Therefore every prime-free base lies in one reference high-tail
  bad set, common to all target widths in the block, or in its own target high-tail bad set.
- `[NOVELTY-UNCERTAIN]` Maynard's 2012 paper uses a width-independent `A(y)` calibrated at a
  reference scale and then proves its reference error small.  The fixed-source, fixed-relative
  reference formulation above, with a single reference exceptional set charged across all target
  widths and no width telescope, was not located in the audited literature.  Do not label it new
  until the full `mu in (11/5,8]` tail receiver and external comparison are complete.
- New hard core: prove the one-width high-tail measure theorem from `U_x=x^(1/8)` through the
  existing `mu<=8` derivative/grouping infrastructure.  This is the genuine large-values problem;
  no cutoff-order or constant optimisation can substitute for it.

## 2026-08-28 cancellation-preserving paired-annulus and uniform-shell closure

- `[FALSIFIED]` Separating reference and target high tails before localization is not a viable
  high-ordinate receiver. It destroys the normalized-kernel cancellation; at the endpoint
  `mu = 8` the resulting generic two-alternative exponent demand is false for every logarithmic
  power. The route is retired in that form.
- `[LEAN-CLOSED POSITIVE SURVIVOR]` Prime-freeness instead forces the norm of the **paired**
  high-tail difference. An arbitrary-order, non-comparable paired-kernel tail theorem needs only
  `H <= R`, so the existing order-50 cutoff removes the far tail without the historical
  comparability hypothesis `R <= 2H`. The surviving defect is a literal finite two-sided annulus
  between `routeTCommonModeCutoff x` and `routeTPrimeGapPacketCutoff T`.
- `[LEAN-CLOSED]` Exact conjugate reflection sends that paired annulus to one positive ordinate
  interval without splitting its kernel. Fixed-source height reparameterization then selects a
  dyadic shell and preserves the support identity `T1^mu1 = T^(8/5)`.
- `[LEAN-CLOSED]` The selector is canonicalized: every physical base `lambda` lands in one shell
  from a single finite ladder depending only on ambient `T`, with one common lower threshold.
  This removes the moving-shell quantifier obstruction before any spatial `L2/L4` summation.
- Main capstone:
  `exists_eventually_routeT_primeFree_fixedSource_commonMode_pairedShell_canonicalCount` in
  `MaynardCommonModePairedAnnulus.lean`. Targeted module build passed; axiom audit reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- `[OPEN CORE]` Split this fixed shell family at the buffered height-matched exponent. Shells above
  the buffer already carry paired-kernel negative-power `L2/L4`; shells below it require a new
  analytic weld from the frozen common-mode shell into the corpus arbitrary-order physical-slice
  receiver. Existing corpus proves the scalar reserve dichotomy but not this packet-level weld.
  Natural-cell conversion and derivative-excised count must be performed after that split.
- `[LITERATURE AUDIT / NOVELTY-UNCERTAIN]` No matching fixed-source, cancellation-preserving
  prime-free annulus-to-uniform-shell theorem was found in Maynard's 2016 large-gap paper or
  Guth--Maynard's 2026 large-value paper. Those sources treat sieve large gaps and Dirichlet-
  polynomial large values, respectively, but do not state this interface. Keep novelty marked
  uncertain until expert comparison and the buffered packet-level weld are complete.
