# 118 — The tilt-sweep discriminator: the Euler walk couples to the parity sheet at half rate

[PROVED HERE unless marked otherwise — machine-checked in
`formal/GaloisForLFunctions/RHTower/TiltSweepDiscriminator.lean`, axiom-clean
`[propext, Classical.choice, Quot.sound]`.]

## The object

The anchor's global canonical logarithm (doc 117) admits the power family

    anchorSweep P t = exp(t · anchorLog P),   t ∈ ℝ,

a multiplicative, nonvanishing, analytic-in-`s` interpolation from `1` (t = 0) to the
Euler head (t = 1) — `anchorSweep_zero/one/ne_zero/add/analyticAt`.  It never moves a
zero: `analyticOrderAt_anchorSweep_mul` (the hole count is a sweep invariant), and its
polar form is modulus `exp(t·Re anchorLog)` times phase `t·anchorTilt`
(`anchorSweep_polar`).  This is a constraint-side homotopy: the member is never
"flowed", only the anchor's phase is turned.

## The half-angle law

Because the branch is global, every chart square root transports EXPLICITLY:

    sweepRoot P t H = exp(t·anchorLog/2)·H,     (sweepRoot_sq: squares to A^t·f)

no continuation, no monodromy bookkeeping.  The transported root's phase advances at
exactly HALF the swept tilt (`sweepRoot_polar`).  Consequences, both machine-checked:

- `anchorSweep_pos_real_of_tilt_two_pi` + `sweepRoot_sign_flip_of_tilt_two_pi`: when
  the tilt at a point is `2π`, the full sweep returns the MEMBER multiplier to the
  positive-real ray while the ROOT's sign has flipped — the mod-2 coupling between
  the prime walk and the square-root sheet.
- `deckClass_sweepRoot`: the sweep is one global factor on both charts, so the deck
  class never moves.  (At `t = 1` this is constructive rigidity: the explicit
  anchored roots carry the member's class.)
- `deckClass_neg_one_zpow_root_log_mismatch`: at root resolution the class is
  `(−1)^{m_P − m_M}` with `πℤ`-quantized root-log mismatches — the winding dictionary
  at twice the resolution of doc 117's member-level `2πℤ`.

## The discriminator

    sweepHolonomy(P) := (anchorTilt P (ρ+ci)/2, anchorTilt P (ρ−ci)/2)

— the exact angles the two basepoint root readings turn under the full sweep.

- **Euler side** (`sweep_holonomy_pair_reachable`): dense — every nonnegative target
  box, every tolerance, primes beyond any bound (pair-reachability of doc 117 at
  half-angles).  `exists_near_half_turn_relative_holonomy`: the RELATIVE holonomy is
  steerable `ε`-close to a half turn: the cross-basepoint reading
  (`sweepRoot_cross_ratio`: positive scalar × rotation by half the endpoint tilt
  difference × the frozen ratio) approaches a sign flip while the deck class stays
  pinned.
- **D–H side** (`anchorLog_empty`, `anchorSweep_empty`, `sweepRoot_empty`): the
  anchor-free sweep is constant — nothing turns, every reading frozen.  Together with
  the banked quantization theorem (equivariant anchors have `2πℤ`-discrete defects),
  the trichotomy: no Euler head ⟹ no sweep; equivariant multiplier ⟹ discrete
  jumps only; Euler head ⟹ dense holonomy.

## The residual: the selection principle [OPEN CORE]

What the discriminator does NOT yet do: convert the dense rotation of the
cross-basepoint reading into a constraint on the chart-ratio signs (the parity).
The sweep rotates each basepoint reading but multiplies both charts' roots by the
same factor, so the overlap cocycle is untouched — by theorem, not by accident.  The
missing weld step is a SELECTION principle: a rule the full function (not the finite
member alone) imposes that ties the steered reading back to which square-root branch
the geometry selects — e.g. a positivity/argument-principle input on the annulus
boundary that breaks the two-fold ambiguity coherently across the sweep.  In these
coordinates the D–H test is exact: any candidate selection rule must USE the sweep
(else it applies verbatim to Davenport–Heilbronn and dies on its odd off-line zeros).
Next generative move: formalize the selection interface as a `Prop`-valued datum on
the annulus (what the rule must provide: a sweep-equivariant choice of root branch on
the boundary circle), and prove the conditional theorem "selection interface + odd
hole count ⟹ contradiction with near-half-turn steering".

## Addendum — the gluing criterion and the sweep-stable obstruction (Lean-green)

`AnnulusRootGluing.lean` (axiom-clean):

- The two slit charts cover the annulus; their overlap is exactly the upper and
  lower half-annuli, both preconnected (polar rectangles), each holding one
  basepoint (`annulus_subset_charts_union`, `chart_inter_subset_overlaps`,
  `isPreconnected_overlapTop/Bot`, `basepoints_mem_overlaps`).
- **The gluing criterion**, both directions:
  `exists_global_sqrt_of_deckClass_one` (class 1 ⟹ the chart roots assemble into
  a global analytic square root on the annulus — the top-basepoint sign corrects
  the left chart coherently across BOTH components) and
  `deckClass_eq_one_of_global_sqrt` (a global root trivializes the class).  The
  deck class IS the mod-2 obstruction to a global branch.
- **The sweep-stable obstruction** `no_global_sqrt_along_sweep_of_deckClass_ne_one`:
  nontrivial member class ⟹ NO stage `t` of the anchor sweep admits a global
  square root of `A^t·f` on the annulus.  The transported roots carry the member's
  class (`deckClass_sweepRoot`), so the gluing criterion fails uniformly in `t`.

Discriminator summary in one line: the Euler walk turns every boundary reading
densely (`sweep_holonomy_pair_reachable`) yet can never open the two-sheeted cover
(`no_global_sqrt_along_sweep_of_deckClass_ne_one`); an anchor-free FE analogue
cannot even turn the readings (`anchorSweep_empty`).  The weld's residual is the
selection principle of §"The residual" — everything on either side of it is now a
theorem.
