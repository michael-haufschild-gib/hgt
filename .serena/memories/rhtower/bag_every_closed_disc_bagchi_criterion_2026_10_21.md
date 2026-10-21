# BAG: Bagchi's criterion on every closed disc of the strip (2026-10-21, third pass)

- The doubled-closure margin `closedBall c (2r) ⊂ strip` of the disc-uniform Carlson tail laws
  (`eventually_eventually_volume_discTailBadSet_le`, `…_eulerDiscTailBadSet_le`) came from the planar
  mean-value discs of radius r. It is removed by a finite cover of `closedBall c r` by balls of radius
  `(R−r)/2` centred in it (`finite_cover_balls_of_compact`): the bad set of the big disc lies in the finite
  union of the small bad sets, densities add (`δ/(card+1)` each).
- Module `formal/GaloisForLFunctions/RHTower/ZetaDiscRecurrenceOnEveryClosedDiscOfTheStrip.lean` (wired):
  `eventually_eventually_volume_discTailBadSet_le_of_lt`, `eventually_eventually_volume_eulerDiscTailBadSet_le_of_lt`
  (hypotheses: r < R, 1/2 < Re c − R, Re c + R < 1), `zetaDiscStronglyRecurrentOn_of_zeroFree_of_lt`,
  `zetaDiscStronglyRecurrentOn_iff_headTargetUniformlyDense_of_lt`,
  `riemannHypothesis_iff_forall_closedBall_zetaDiscStronglyRecurrentOn`,
  `riemannHypothesis_iff_forall_closedBall_headTargetUniformlyDense`,
  `riemannHypothesis_iff_zetaDiscRecurrent` (RH ⟺ the receiver's `ZetaDiscRecurrent`).
- Together with the same-day passes (natural-rate Pechersky lemma, second-order windows), the chain
  Pechersky → Euler universality → tail laws → recurrence now works for every closed disc of the open strip
  with no artificial constraint. Not reached: `ZetaStronglyRecurrent` on arbitrary compacta (disc-based
  Hilbert-space universality step).
- Card: `docs/drafts/pipeline/3-formalized/bag-pechersky-natural-rate-half-scale-bagchi-2026-10-21.md`.
