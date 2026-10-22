# HB literal time-lift stream realization

- **ID:** HB-B2-time-lift-stream-realization
- **Stage:** 3-formalized
- **Type:** BRIDGE
- **Source:** `ThetaCuspHawkingBMPhysicalLiftHorizonCurrent`, `ThetaCuspHawkingBMCapTraceAction`; HB B2

## Exact statement

For `q`, physical rate `s`, amplitude `a`, and covector component `j`, define on the
static exterior (`r>1`)

`L_j(t,r,z) = profile(s,a,r) * timeOnset(2s, t + tortoise(r)) * fullSquareCovector(q,j,z)`.

At an exterior point with `v = t + tortoise(r)`, the complete coordinate two-jet of
`L_j` is exactly

`liftJet q s a r v z j`.

Thus the two streams used by `lift_action_current` are literal C2 fields, not supplied
jet data. Via `metricIngoingCurrent_eq`, their reconstructed metric action is the
actual ingoing Einstein action current.

## Dependency-closed paper proof

Put `P(r)=profile(s,a,r)`, `χ(v)=timeOnset(2s,v)`, and `f=r²-1`. The existing
definitions and `static_radial_derivatives` give

`C=Pχ`, `C_t=Pχ'`, `C_r=P'χ+Pχ'/f`,

`C_tt=Pχ''`, `C_tr=P'χ'+Pχ''/f`,

`C_rr=P''χ+2P'χ'/f+Pχ''/f²-2rPχ'/f²`

for `C(t,r)=P(r)χ(t+tortoise(r))`. These are respectively the value, time,
radial, time-time, time-radial, and radial-radial slots in `separatedJet` used
by `liftJet`.

This is a genuine `C²` field statement, not a formal partial-derivative table.
`profile`, `profileFirst`, and `profileSecond` are continuous on the positive
radial domain (`profiles_continuous`), and `timeOnset`, `timeOnsetFirst`, and
`timeOnsetSecond` are continuous by their derivative witnesses. Hence every
displayed first and second partial is continuous on `r>1` (the factors `f⁻¹`
and `f⁻²` are continuous there). Thus the ordinary two-variable `C²`
criterion applies. The angular factor is the actual smooth
`fullSquareCovector` (`fullSquareCovector_smooth`); product and pullback give
precisely `liftJet` in all ordered coordinate slots. No limiting argument or
field equation is used.

`D4BMPhysicalLiftCurrent.lift_action_current` then evaluates the full ingoing
Einstein action of these exact jets, while `lift_current_add_contact` retains its
source contact. `D4BMCapTraceAction.traceFlux_eq_lift_angular` identifies the cap
trace with that contact-completed horizon current.

## Consequence for B2

The local cap-to-action leg is no longer permitted to hide behind formal jet data:

`cap scalar trace -> literal time-lift stream -> actual reconstructed metric current
 -> retained lift contact -> cap trace flux`.

The live B2 theorem is still global: identify the retarded/future-minus-cap two-leg
field with this lift current under noncompact polar/left-QNM cutoffs, and prove its
boundary holonomy is `contactField`. This result neither assumes nor proves that
identification.

## Lean status

Paper proof closed. Exact Lean leaf remains unwritten because direct import is blocked
by the absent transitive artifact
`ThetaCuspHawkingBMMixedRadialActionCurrent.olean`; a targeted direct compilation was
externally terminated without producing it, and a Lake target previously replayed the
repository. No Lean closure is claimed here.

## Formalized (2026-09-27)

`formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMTimeLiftStreamJet.lean`
(namespace `RHTower.D4BMPhysicalLiftCurrent`):

- `timeLiftStream q s a j x = profile(s,a,r) · timeOnset(2s, t + tortoise r) ·
  fullSquareCovector q j (X, Y)`;
- `timeLiftStream_contDiffAt`: a genuine `C²` field on `r > 1`, `Y > 0`;
- `ofField_timeLiftStream`: its complete coordinate two-jet is `liftJet q s a r v z j` with
  `v = t + tortoise r` (proved through `ofField_ingoing_comp` and the product rule, with the
  reusable one-coordinate and angular-block jet lemmas `ofField_coord`, `ofField_angular`);
- `metricIngoingCurrent_timeLiftStream`: the reconstructed metric Einstein current of two
  time-lift streams is `liftCurrent`;
- `metricIngoingCurrent_timeLiftStream_add_contact`: adding `liftContact` gives
  `liftAngularCurrent`.

Axioms `[propext, Classical.choice, Quot.sound]`.
