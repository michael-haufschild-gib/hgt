# Whole-child fractional payment attempt

- **ID:** rh-whole-child-fractional-payment
- **Owner:** critical-clock product task
- **Stage:** 1-in-progress
- **Type:** OPEN RESEARCH ATTEMPT; no new source theorem
- **Target:** Paid exhaustive continuation, with complete old-wall and intervening-cutoff control, yielding `MobiusDivisorSquareRootAbelBounded` and RH.

## Source evidence

The current full target is
`exists B>=0, forall M>=2, |mobiusDivisorSquareRootAbelMoment M / M|<=B`.
`CCMFUSuzukiMobiusDivisorAbelProducer.lean` proves its equivalence to RH.
`MobiusDivisorFiniteClockCountingCancellation.lean` identifies the complete
weighted clock with the original critical action square at integer walls.

`eventually_exists_mobiusDivisorFiniteDepth_uniform_prime_collar` supplies
an inward direction for every coefficient vector on a FIXED finite child
field. Its margin, collar and cutoff threshold depend on that field.
The full weighted insertion identity retains the copied-source squares
and every receiving cofactor. `MobiusDivisorSmallCoreInteractions` reduces
two-prime interactions to the active small core only when the joint prime
product reaches the cutoff; overlapping products remain in scope.

## Attempt and unresolved point

Use whole-child vector balancing to select many actual helper primes,
paying omitted-prime debt while child depth grows. The recent
[directional-variation balancing paper](https://arxiv.org/html/2609.11189v1)
provides a candidate geometric method, not an arithmetic payment theorem.
Its theorem concerns freely selected signs; section 1.2 explicitly does
not obtain control of every prefix. No result from this paper is assumed
in Lean.

The attempted reduction has two missing inputs:

1. A fractional arithmetic target with sufficiently small FULL weighted
   receiving energy has not been constructed. Interpreting arbitrary
   signs as prime inclusion/exclusion introduces a mean vector which the
   signing theorem does not bound. Even perfect rounding would leave it.
2. The existing inward-direction theorem applies after fixing the child
   field. Substituting the complete field at the current cutoff changes
   that field before its dependent onset is available. A smaller field
   leaves uncontrolled new child coordinates. Neither operation proves
   the required complete signed payment.

The elementary weighted merger diagnostic is exact. With parent a, copied
child b, receiving weight w, copied weight w+ell and selection fraction t,

`(1-t)*(w*a^2+(w+ell)*b^2)+t*w*(a-b)^2`
`= w*(a-t*b)^2+(1-t)*(w+ell)*b^2+t*(1-t)*w*b^2`.

Thus a fractional-merger bound cannot silently omit the final variance.
This one-coordinate identity does not assert that overlapping prime
insertions are independent; their further mixed terms remain to control.
It is a diagnostic, not new source knowledge or a promoted Lean module.

## Whole-route decision

No paid extension, depth-uniform source margin, or completed-action bound
has been proved by this attempt. The full RH objective is unchanged.
Do not formalize a generic signing receiver as a replacement for the
missing arithmetic construction. The next attack must construct the
full fractional source payment and account for rounding and copied-square
terms together before attempting Boolean prime selection or continuation.

## Diagnostic status

`lake env lean /tmp/hgt-paid-rounding-diagnostic.lean` verified both forms
of the weighted variance identity without warnings. It was kept as a
scratch diagnostic and removed after checking. No source module or
conditional payment receiver was added. No full or umbrella build ran.
All four owned searches and the owned Lean process exited. Logs remain
under `/tmp/hgt-paid-*-20260923.json` and
`/tmp/hgt-paid-rounding-diagnostic.log`.
