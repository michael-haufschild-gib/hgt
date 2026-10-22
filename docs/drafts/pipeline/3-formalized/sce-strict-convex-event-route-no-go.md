# SCE strict-convex event route no-go

- **ID:** SCE-NG1
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` route SCE
- **Statement:** Every nondegenerate real event cell admits a positive strictly convex reservoir with exact affine event law, unique interior checkpoint, positive source endpoints, exact Bregman drawdown, and exact endpoint recurrence, while checkpoint source is negative and restricted conjugate exceeds moment.

## Goal
Kill SCE as an independent convex/event route. Corpus chain is
literal Suzuki event history → strict convexity/checkpoint/Bregman/recurrence →
`SuzukiCheckpointConjugateLeMoment` → RH. The last implication is already an iff;
this theorem tests whether preceding source-independent structure can prove it.

## Gates
- [x] 0 → 1 in-progress: exact corpus chain, universal countermodel, primary-literature collision audit
- [x] 1 → 2 fully-proven: dependency-closed proof below
- [x] 2 → 3 formalized: Lean capstone and targeted build
- [ ] 3 → 4 publication-ready

## Approach
Given `a < b`, `0 < w`, put `d=b-a`, `v=(a+b)/2`, `η=wd/4`, `κ=2w/d`,
`F(t)=κ(t-v)^2-η`, `R(t)=F(t)+w(t-a)`, `q=wa`, and `L(t)=wt-R(t)`.
Then `F=R-wt+q`, `R'(v)=w`, and `R''=F''=2κ>0`. Moreover
`F(v)=-η<0`, while `F(a)=F(b)=η>0`, and
`F(u)-F(v)=R(u)-R(v)-w(u-v)=κ(u-v)^2`.
Thus `v` is the unique checkpoint and the exact Bregman law holds. Since
`L=q-F`, its restricted supremum is `q+η>q`. The affine identity also gives the
exact endpoint recurrence. Finally
`R(t)=κ(t-(a+d/4))^2+wd/8>0`, so failure is not caused by a negative reservoir.

## No-go closure
- **Exact killing theorem/mechanism:** positive curvature controls drawdown from the unique minimum but not its additive level; endpoint positivity does not fix that level.
- **Strongest positive survivor:** exact classification `conjugate - moment = -min F`; SCE can survive only through source-specific arithmetic control of the checkpoint level.
- **New insight:** all proved convex/event identities determine relative geometry. The missing absolute sign is precisely the RH-equivalent arithmetic datum, not a consequence of that geometry.
- **Status:** formalized in `RHTower/Suzuki/SuzukiCheckpointStrictConvexEventNoGo.lean`; targeted build green; capstones use only `propext`, `Classical.choice`, `Quot.sound`. Suzuki 2022–2026 primary papers contain RH-equivalent screw positivity criteria but no collision with this universal convex/event no-go.

## Log
- 2026-09-01 — corpus-derived conjecture SCE-NG1 frozen; paper proof closed.
- 2026-09-01 — universal countermodel and exact conjugate-excess classification formalized.
