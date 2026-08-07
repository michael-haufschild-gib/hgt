# The Suzuki–Burnol weld is terminally retired (2026-08-07)

## What closed

The frontier gate shared by four Sonin cards — "Burnol completion and completed lower floor",
"prove completed coercivity or terminally retire", "prove Burnol cancellation in the
regularized-pairing form", "prove RH or terminally retire surviving Suzuki–Burnol weld" — resolves
to **retirement**.  All four cards now have zero open gates.

`formal/GaloisForLFunctions/RHTower/SoninBurnolConductorNoFloor.lean` (8 declarations, wired into
`GaloisForLFunctions.RHTower`, axiom-clean):

- `evenBurnolConductorChannel a r np nf = evenLogShellChannel a r np + evenFourierLogShellChannel a r nf`
  — the **full** conductor, logarithm of position plus logarithm of frequency, each on its own
  geometric tower at an **independent and arbitrary** height;
- `adjoint_evenFourierLogShellChannel`, `adjoint_evenBurnolConductorChannel` — self-adjoint, so it
  is a legitimate archimedean channel;
- `not_bddBelow_soninCompletedPacketValueVar_burnolConductorFamily` — **no completion assembled
  from it restores the floor**, at any pair of height schedules;
- `not_bddBelow_soninCompletedPacketValueVar_of_sublinear_channel_add` — the excluded class is
  **closed under sums**, so no finite assembly of sublinear channels escapes;
- `exists_carrier_halfwidth_schedule` — the schedule's two scale conditions (carrier proportional
  to the scale, half-width × carrier bounded below) are simultaneously satisfiable, so the no-go is
  **not vacuous**.

## Why the corpus's channel-by-channel exclusions were not enough

Position and frequency halves had each been closed separately
(`..._logShellChannelFamily`, `..._fourierLogShellChannelFamily`), but a conductor is their *sum*
and neither statement covers it.  The two halves also fail for **opposite** reasons, so one might
have compensated the other:

- position: bounded outright, because the source packets sit inside a fixed outer radius and on a
  fixed annulus only the finitely many layers meeting it contribute — every higher layer cancels
  between its two cutoffs;
- frequency: does grow (the carrier runs with the scale even though the support does not) but only
  **logarithmically**, because a tall tower buys nothing against a rapidly decaying spectrum.

Constant + logarithm is still sublinear, while `exists_linear_hsNormSq_soninApertureCoupling` gives
the coupling energy a **positive slope in the scale**.  So the sum is defeated exactly as each half
is.  The key reuse was that the position-side annulus bound
`exists_bound_norm_evenLogShellChannel_of_annulus` applies to *any* vector fixed by the outer
cutoff, hence to the shell-cut rescaled packets the frequency argument uses — the two estimates can
be run on one family.

## What is *not* excluded

A hypothetical channel family whose Hilbert–Schmidt norms grow at least linearly in the scale
(`frequently_slope_lt_hsNorm_of_bddBelow` states the requirement).  The Burnol conductor is not one,
and no such family is exhibited in the corpus or in Burnol's construction.  A magnitude argument
alone cannot close that residue: the principal-relative ideal is a two-sided ideal of `B(H)` and so
contains finite-rank operators of arbitrary norm — the constraint has to come from *admissibility*,
i.e. from what the archimedean term is allowed to be, not from how big it may be.

## Stale card text corrected

The big card's "**Open.**" paragraph asked for a rate comparison (`hsNormSq Z_r` versus
`log(outer radius)`) that the corpus had *already* proved via
`exists_linear_hsNormSq_soninApertureCoupling` + `eventually_log_add_le_linear` +
`not_bddBelow_soninCompletedPacketValueVar_of_log_cap`.  Replaced with the settled statement.

See `mem:research/sonin_folder_stage3_complete_2026_08_07` for the formalization audit of the same
five cards.
