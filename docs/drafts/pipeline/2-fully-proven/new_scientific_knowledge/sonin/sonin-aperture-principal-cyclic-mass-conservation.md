# Sonin aperture principal cyclic-mass conservation law

- **ID:** `sonin-aperture-principal-cyclic-mass-conservation`
- **Stage:** 2-fully-proven
- **Formalized companion:** `../../../3-formalized/new_scientific_knowledge/sonin-aperture-principal-cyclic-mass-conservation.md`
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [SOURCE THEOREM] [NOT RH]`
- **Parent:** `sonin-aperture-area-rigidity-and-restriction-defect.md`
- **Statement:** Strict Sonin aperture restriction splits every crossing diagonal orbital shell
  into retained and lost noncompact principal shells, but their canonical cyclic logarithmic
  masses add exactly to the original orbital mass.  Lost mass is the additive aperture cocycle
  `log(b/a)`; all remaining aperture curvature is Schatten-1.

## Frontier changed

The prior result proved that no strict aperture step preserves every prime corner modulo the
trace-class relative ideal.  Its positive survivor asked for a cyclic reader on the necessarily
enlarged noncompact principal algebra.  That gate is now closed in the strict crossing chamber.
The lost layer is already a canonical scale-one live Sonin normal state, and the existing faithful
cyclic reader evaluates it exactly.

The remaining aperture problem is smaller: compute and weld the ordinary trace of the
Schatten-1 curvature counterterm.  Principal logarithmic mass needs no Burnol cancellation.

## Theorem

Let `0<a<b<r*a` and `r>1`.  Write

```text
S(s,t)=(A_t-A_s)+(R_t-R_s)
```

for the two-polarization shell.  At aperture `b`, define the three canonical scale-one live
windows

```text
W_keep  = W_b(b,r*a,1),
W_lost  = W_b(r*a,r*b,1),
W_total = W_b(b,r*b,1).                                  (1)
```

Their exact operators are

```text
Op(W_keep)  = S(b,r*a),
Op(W_lost)  = S(r*a,r*b),
Op(W_total) = S(b,r*b).                                  (2)
```

Therefore shell telescoping gives an equality of bounded operators, not a quotient identity:

```text
Op(W_total)=Op(W_keep)+Op(W_lost).                       (3)
```

For a scale-one live window, the faithful principal cyclic reader is logarithmic width:

```text
tau(W_b(s,t,1))=log t-log s.                             (4)
```

Consequently

```text
tau(W_lost)=log(r*b)-log(r*a)=log b-log a,               (5)

tau(W_keep)+tau(W_lost)
 =(log(r*a)-log b)+(log b-log a)
 =log r,                                                 (6)

tau(W_total)=log(r*b)-log b=log r.                       (7)
```

Thus aperture restriction transfers, but does not create or destroy, the prime orbital mass.
The transferred mass is independent of `r` and obeys the exact path law

```text
c(a,c)=c(a,b)+c(b,c),   c(a,b)=log b-log a.              (8)
```

## Operator cocycle and trace-class curvature

Let

```text
Delta(a,b;r)=G_b(r,r)-Q_b G_a(r,r) Q_b.                  (9)
```

For arbitrary nested `b<=c`, direct projection algebra gives the exact compressed cocycle

```text
Delta(a,c;r)=Delta(b,c;r)+Q_c Delta(a,b;r) Q_c.          (10)
```

In one strict crossing chamber `0<a<b<c<r*a`, each defect has its lost-shell representative.
Shell telescoping and `(8)` give

```text
Delta(a,c;r) =_r Delta(a,b;r)+Delta(b,c;r),              (11)
```

where `=_r` is congruence modulo the concrete Sonin principal-relative ideal.  Hence

```text
K(a,b,c;r)=Delta(a,c;r)-Delta(a,b;r)-Delta(b,c;r)        (12)
```

belongs to that ideal and is Schatten-1.  The noncompact principal quotient is flat; every
failure of literal path additivity is concentrated in one ordinary trace-class counterterm.

## Proof

For a general scale-one live window `W_a(s,t,1)` with `a<=s<t`, normalized dilation at scale one
is the identity.  Cutoff nesting gives

```text
(A_t-A_s)(1-A_a)=A_t-A_s,
(R_t-R_s)(1-R_a)=R_t-R_s,
```

which proves `(2)`.  Equation `(3)` follows by cancellation of the intermediate cutoffs at
`r*a`.  Equation `(4)` is the definition of the already-proved faithful normal-state trace, so
the positive logarithm product law proves `(5)`--`(7)`.  Equation `(8)` is additive cancellation.

For `(10)`, expand both defects and use `Q_cQ_b=Q_bQ_c=Q_c`.  In the crossing chamber, the exact
principal-relative lost-shell normal form identifies the three terms in `(11)` with
`S(r*a,r*c)`, `S(r*a,r*b)`, and `S(r*b,r*c)`.  Their sum telescopes exactly.  Membership and
Schatten-1 of `(12)` follow from closure of the concrete two-sided relative ideal.

No zero location, Weil sign, asymptotic estimate, numerical experiment, or RH premise is used.

## Terminal effect on Suzuki lane

This theorem rejects the previous candidate falsifier “no cyclic extension to aperture layers.”
The extension exists and conserves exact source mass.  It also rejects the idea that Burnol's
conductor must cancel a growing principal aperture anomaly: the principal anomaly is the exact
coboundary `(8)` and cancels internally between retained and lost shells.

Remaining source-complete terminal test is now:

```text
ordinary trace of K(a,b,c;r)
  + cutoff-dependent Burnol conductor counterterm
    -> canonical completed signed finite part
      -> uniform lower floor, or an explicit unbounded-below source sequence. (13)
```

A lower floor proves RH through the existing completed source endpoint.  An unconditional
unbounded-below sequence on that exact normalized source family kills the surviving Suzuki--Burnol
weld.  This theorem itself does neither.

## Lean

| Statement | Declaration |
|---|---|
| `(1)`: the three canonical scale-one live windows at aperture `b` | `soninScaleOneShellWindow`, `soninApertureRetainedLayerWindow`, `soninApertureCyclicLostLayerWindow`, `soninApertureTotalLayerWindow` |
| `(2)`: a scale-one live window represents its two-polarization shell **exactly** as bounded operators, not modulo compacts; the cutoff-nesting inputs `(A_t-A_s)(1-A_a)=A_t-A_s` and its Fourier twin | `soninScaleOneShellWindow_operator`, `evenIndicatorCutoff_shellComplementProduct`, `evenFourierCutoff_shellComplementProduct`, `evenTwoPolarizationShell` |
| `(2)` for the three windows | `soninApertureRetainedLayerWindow_operator`, `soninApertureCyclicLostLayerWindow_operator`, `soninApertureTotalLayerWindow_operator` |
| `(3)`: exact operator conservation, an equality of bounded operators | `soninApertureTotalLayerWindow_operator_eq_retained_add_lost` |
| `(4)`: the faithful cyclic reader of a scale-one live window is logarithmic width | `soninLiveWindowCyclicLogWeight_scaleOneShell` |
| `(5)`: the lost channel carries `log b - log a`, independently of the crossing scale `r` | `soninLiveWindowCyclicLogWeight_apertureCyclicLostLayer` |
| `(6)`--`(7)`: retained and total masses, and exact cyclic-mass conservation | `soninLiveWindowCyclicLogWeight_apertureRetainedLayer`, `soninLiveWindowCyclicLogWeight_apertureTotalLayer`, `soninAperture_cyclicMass_conservation` |
| `(8)`: the transferred mass is an additive one-cocycle on every nested triple | `soninAperture_cyclicMass_cocycle` |
| `(9)`: the aperture restriction defect | `evenSoninApertureRestrictionDefect` |
| `(10)`: the exact compressed cocycle for arbitrary nested `b ≤ c` | `evenSoninApertureRestrictionDefect_compressed_cocycle` |
| `(11)`: additivity modulo the concrete principal-relative ideal, through the crossing-chamber lost-shell normal form | `evenSoninApertureRestrictionDefect_principalRelative_cocycle`, `evenCentralSoninQuadraticCorner_restrictionDefect_principalRelativeEq_shell`, `evenSoninApertureLayer_principalRelativeEq_window` |
| `(12)`: the curvature lies in that ideal and is Schatten-1 | `evenSoninApertureRestrictionCurvature`, `evenSoninApertureRestrictionCurvature_mem_principalRelativeIdeal`, `evenSoninApertureRestrictionCurvature_memSchattenClass_one` |
| `(13)`, energy side: the packet curvature trace, its sign, and its unboundedness below on unit-weight source packets | `re_opTrace_soninAperturePacketCurvature`, `re_opTrace_soninAperturePacketCurvature_nonpos`, `exists_soninAperturePacketCurvature_re_opTrace_lt`, `eventually_le_hsNormSq_soninApertureCoupling`, `tendsto_hsNormSq_soninApertureCoupling_atTop` |
| `(13)`, completion side: the scalar Burnol counterterm, every fixed bounded channel, and every completion bounded above all fail to restore a floor; the exact summability criterion for one that could | `not_bddBelow_soninCompletedPacketValueVar_burnolCounterterm`, `not_bddBelow_soninCompletedPacketValueVar_fixedChannel`, `not_bddBelow_soninCompletedPacketValueVar_logShellChannelFamily`, `not_bddBelow_soninCompletedPacketValueVar_of_bddAbove`, `bddBelow_soninCompletedPacketValueVar_iff`, `tendsto_atTop_of_bddBelow_soninCompletedPacketValueVar` |

Files: `formal/GaloisForLFunctions/RHTower/SoninApertureCyclicMassConservation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninApertureRestrictionDefect.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLayerWindowNormalForm.lean`,
`formal/GaloisForLFunctions/RHTower/SoninEulerTripleShellOverlap.lean`,
`formal/GaloisForLFunctions/RHTower/SoninAperturePacketCurvatureTrace.lean`,
`formal/GaloisForLFunctions/RHTower/SoninUnboundedSourcePacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninBurnolCompletionNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFixedChannelNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelAnnulusBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionSummabilityCriterion.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingEnergyGrowth.lean`.

## Gates

- [x] prior aperture and normal-state trace corpus audited
- [x] exact retained/lost/total operator decomposition
- [x] exact cyclic-mass conservation
- [x] additive aperture cocycle
- [x] exact compressed operator cocycle
- [x] principal-relative flatness and Schatten-1 curvature
- [x] dependency-closed Lean formalization
- [x] compute the ordinary trace of the curvature on actual finite source packets —
      `re_opTrace_soninAperturePacketCurvature` in `SoninAperturePacketCurvatureTrace.lean`: for a
      finite weighted family of prime scales the real curvature trace is minus the weighted total
      coupling energy, and `re_opTrace_soninAperturePacketCurvature_nonpos` shows no nonnegative
      reweighting can make it positive
- [x] **exact unbounded-below source sequence constructed** —
      `exists_soninAperturePacketCurvature_re_opTrace_lt` in `SoninUnboundedSourcePacket.lean`:
      for every level `M` there is a finite **unit-weight** source packet, over explicit scales of
      the crossing clock, whose aperture curvature trace lies below `-M`.  The chain is
      `norm_sq_apply_le_hsNormSq` (HS energy dominates the action on a unit vector) plus the
      cofinal nonannihilation, giving the uniform floor
      `eventually_le_hsNormSq_soninApertureCoupling` (energy eventually at least `1/4`), summed
      over enough scales.  Unit weights matter: rescaling a single weight would make unboundedness
      vacuous.
      This settles the first branch of the disjunction below; Burnol cancellation is now the
      remaining question, and it must contend with an unbounded-below channel.
- [x] **the scalar Burnol counterterm is settled, negatively** —
      `not_bddBelow_soninCompletedPacketValueVar_burnolCounterterm` in
      `SoninBurnolCompletionNoFloor.lean`: the corpus counterterm is `log(b/a)`, one fixed real
      number per scale, hence a bounded completion, and the coupling energy is unbounded, so the
      completed packet channel has no lower floor at any strict flag.  The same holds for every
      prime-independent scalar (`..._const`).  This is the second branch of `(13)`: an
      unconditional unbounded-below sequence on the exact normalized source family, now also after
      the Burnol subtraction.  What survives is only a completion that grows with the scale —
      `tendsto_atTop_of_bddBelow_soninCompletedPacketValueVar` shows any working completion must
      tend to infinity along the scales — i.e. the regularized extended-trace pairing, not a
      counterterm
- [ ] prove Burnol cancellation in the regularized-pairing form, whose contribution must diverge —
      narrowed again by `not_bddBelow_soninCompletedPacketValueVar_fixedChannel` in
      `SoninFixedChannelNoFloor.lean`: pairing the source packets against **any fixed bounded
      operator** gives a contribution bounded by `||T||` times the (uniformly bounded) packet
      energy, so it cannot restore the floor either.  The concrete conductor channel at one
      aperture and one tower height is such an operator
      (`not_bddBelow_soninCompletedPacketValueVar_logShellConductor`).  Only a channel *family*
      whose norms grow with the scale remains — and that class is inhabited:
      `tendsto_norm_evenLogShellChannel_atTop` in `SoninLogShellChannelGrowth.lean` shows the
      conductor channel's norms diverge with the tower height, since it acts on the `k`-th layer
      unit by `log(r^k a)`.  So the remaining question is quantitative — whether the tower can be
      tied to the clock so that the contribution tracks the coupling energy with summable excess —
      not whether any candidate survives.  **Settled negatively for this channel**:
      `not_bddBelow_soninCompletedPacketValueVar_logShellChannelFamily` in
      `SoninChannelAnnulusBound.lean`.  The tower norms diverge, but the source packets all live in
      one *fixed* annulus — the frequency runs, the support does not — and on a fixed annulus only
      the finitely many layers meeting it contribute, every higher layer cancelling between its two
      cutoffs.  So the channel's pairing with the packets is bounded independently of the height,
      and no schedule of heights restores the floor.  A surviving completion must grow *on the
      fixed annulus*, which the logarithm of position cannot do — sharpened:
      `not_exists_lower_bound_soninAperturePacketCurvature_add_bounded` in
      `SoninCompletionUnboundedRequirement.lean` shows no counterterm that is bounded above on the
      packet family can restore a floor, even one depending on the packet.  So by
      `not_bddAbove_of_lower_bound_completion` the Burnol contribution must be *unbounded above*
      along the unit-weight packet family, and by `exists_packet_le_completion_of_lower_bound` it
      must exceed every level at some packet.  The remaining question is whether the conductor
      actually does that; boundedness of its contribution would now settle the disjunction
      negatively.  Sharper still, for an *extensive* completion contributing a fixed `kappa` per
      scale of the packet: `soninCompletedPacketValue_eq_sum` writes the completed value as
      `sum over the packet of (kappa - coupling energy at that scale)`, so the floor exists when
      `kappa` dominates every scale's energy (`soninCompletedPacketValue_nonneg`) and fails
      whenever `kappa < 1/4` (`not_exists_lower_bound_soninCompletedPacketValue`), the uniform
      energy floor.  In particular the aperture logarithm itself is below the threshold on short
      flags — `log(6/5) < 1/4` — so
      `not_exists_lower_bound_soninCompletedPacketValue_logCounterterm` rules out a `log(b/a)`
      per-scale completion at the flag `1 < 11/10 < 6/5 < 5/4`.  The threshold is the coupling
      energy, and it is now an explicit inequality rather than an open disjunction.  For a
      *scale-dependent* completion the criterion is exact:
      `bddBelow_soninCompletedPacketValueVar_iff` — the floor exists **iff** the excess of the
      coupling energy over the contribution is summable over the scales, so by
      `tendsto_min_sub_hsNormSq_of_bddBelow` any working completion must track the energy
      asymptotically.  What remains of `(13)` is a single summability question about one explicit
      sequence — and that sequence is now known to diverge: by
      `tendsto_hsNormSq_soninApertureCoupling_atTop` the coupling energy is unbounded along the
      crossing clock, so `not_bddBelow_soninCompletedPacketValueVar_of_bddAbove` rules out **every**
      completion bounded above on the scales, at every strict flag.  A surviving Burnol completion
      must therefore grow with the scale at least as fast as the coupling energy; a bounded
      archimedean contribution is now formally excluded.
- [ ] prove RH or terminally retire surviving Suzuki--Burnol weld

## Log

- 2026-08-01 — the logarithmic shell channel is closed as a completion, height schedule included.
  Its norms do diverge with the tower, but that divergence lives far out in position while the
  source packets stay in a fixed annulus; on that annulus the channel is a step multiplier with
  finitely many contributing layers, bounded independently of the height.  So the divergence the
  no-go demands cannot be supplied by the logarithm of position.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninChannelAnnulusBound.lean`.
- 2026-08-01 — the fixed-channel form is dead too.  A completion given by pairing the packets
  against one bounded operator is bounded above by `||T||` times the packet energy, which is
  uniform in the frequency, so the divergent coupling energy beats it.  The Burnol conductor read
  at fixed aperture and tower height is exactly such an operator.  What is left is a channel family
  with diverging norms.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninFixedChannelNoFloor.lean`.
- 2026-08-01 — the scalar form of the Suzuki--Burnol weld is dead.  The corpus's Burnol counterterm
  is a constant per scale, the coupling energy diverges, and a bounded completion cannot compensate
  a divergent one — so the completed channel is unbounded below at every strict flag.  Only a
  completion diverging along the scales can survive, which is the regularized pairing rather than
  any subtraction.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninBurnolCompletionNoFloor.lean`.
- 2026-08-01 — the summability question is settled on the energy side: the coupling energy tends to
  infinity (many disjoint annuli give many orthogonal packets the coupling preserves), so no
  completion bounded above on the scales can restore the floor at any strict flag.  The disjunction
  in `(13)` now demands an archimedean term growing with the scale.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninCouplingEnergyGrowth.lean`.
- 2026-08-01 — `(13)` is now a summability criterion, with no restriction on the shape of the
  completion.  Finite sums of a real sequence are bounded below exactly when the sequence's negative
  part is summable, so the completed channel has a floor exactly when the coupling energy exceeds
  the per-scale contribution by a summable amount — and any completion with a floor must track the
  energy asymptotically.  The general sequence lemma was missing from mathlib and is now in the
  corpus.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninCompletionSummabilityCriterion.lean`.
- 2026-08-01 — the terminal test `(13)` reduced to one inequality for extensive completions.  If the
  archimedean side contributes a fixed amount per scale, the completed packet value is literally the
  sum of `contribution - coupling energy` over the packet, so a floor exists exactly when the
  contribution dominates the energies and fails as soon as it drops below the uniform floor `1/4`.
  The aperture logarithm is below that threshold on short flags, which kills the most natural
  extensive candidate outright.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninCompletionEnergyThreshold.lean`.
- 2026-08-01 — the terminal test `(13)` is now one-sided in a usable way.  Earlier no-gos only ruled
  out counterterms depending on the aperture flag; the channel's unboundedness in fact defeats every
  counterterm bounded above on the packet family, including packet-dependent ones.  Equivalently,
  any completion with a lower floor is unbounded above along that family — a checkable property of
  the archimedean side rather than an open disjunction about the sum.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninCompletionUnboundedRequirement.lean`.
- 2026-07-31 — packet curvature trace computed.  The relative ideal is closed under finite sums, so
  the ordinary trace is additive over a weighted family of prime scales and the real trace is minus
  the weighted total coupling energy.  Nonnegative weights therefore cannot make the aperture
  curvature positive: the sign survives arbitrary finite source packets, not just single scales.
- 2026-07-22 — cyclic-extension falsifier failed; exact aperture mass conservation proved.
- 2026-07-22 — principal aperture quotient shown flat; remaining anomaly isolated in Schatten-1
  curvature.
