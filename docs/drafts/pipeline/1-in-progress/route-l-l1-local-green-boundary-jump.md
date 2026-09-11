# Route L: the original local Green primitive and its complete boundary jump

- **ID:** L-C48
- **Date:** 2026-09-11
- **Stage:** 1-in-progress
- **Type:** source-forced domain enlargement / complete Green boundary comparison
- **Depends on:** C44 actual weighted source, C46 full Xi packet, C47 L1 circle injectivity
- **RH status:** unproved

Chain: complete original Green/BV source → fixed physical-reader agreement
→ conormal vanishing → RH. C46 closes full damped packet and Tate graph
admission for a>1 while preserving the fixed physical discriminator. C47
shows that common integrable original-prime primitives force an integrable
source to vanish. The remaining domain proposal must construct an actual
non-L1 primitive and retain its complete source boundary.

## Conjecture → paper mechanism under verification

For an integrable real-line source f and a fixed original period L>0,
construct the literal future Green series
`G_L^+(t)=sum_(j>=0) f(t+jL)` in L1 on each bounded interval. Absolute cell
integrals are summable, by partition of the real line. No pointwise
convergence outside the resulting AE set is assumed. Finite telescoping
then gives the original equation
`G_L^+(t)-G_L^+(t+L)=f(t)` almost everywhere.

On the original cell `(0,L]`, the positive translates
`G_L^+(t+NL)` tend to zero in L1; the negative translates
`G_L^+(t-NL)` tend to the complete original periodization `Per_L f(t)`.
Both claims should follow from the actual L1 tail of f. Therefore the
complete two-ended jump is exactly `Per_L f`, not zero. The same identity
must hold for every original prime period, without rescaling L or
changing Fourier coefficients.

A possible stronger positive classification uses one finite absolute
first moment of f: if `Per_L f=0`, the negative-tail representation gives
an integrable Green primitive; the cellwise integral bound counts each
source cell with its distance from the origin. Conversely an integrable
primitive has zero circle coefficients by C47. This would extend the
existing exponential Schwartz range/kernel theorem to an actual weighted
L1 domain containing C44's damping-two source. No such theorem is yet
claimed formalized.

The source is not repaired by declaring the local primitive a boundary.
Its full periodic jump must enter the original Green/BV boundary and be
compared with the fixed physical reader. The hard next identity is that
same-source comparison; a vanishing end term must not be inserted as a
hypothesis. The gluing paper in C46 likewise retains the derivative jump
when passing to a weak Green identity.

## Corpus audit

Read `DeningerExpSchwartz.deningerPeriodizationDefect_apply`: the literal
orientation is `1 - translation_L`. Read the actual `DeningerGreenSum`
and `DeningerGreenSumSource` source-domain description: the original
future sum decays at the positive end; its negative representation uses
zero periodization. The current stronger question concerns locally L1
limits of the actual weighted source, not assuming membership in the old
exponential Schwartz class.

Search `/tmp/route_l_c48_original_green_jump_deep.json` is terminal.
All 20 candidate statements, 20 source arguments and the proposed group
were inspected. Generation 876596; snapshot 876598 has 56963/56963 files;
semantic coverage not measured. Text/source retrieval and three iterative
queries are partial; source refresh was still running. The proposed group
uses `deningerGreenSeries_expBound` twice and asks for zero periodization
and exponential decay. It therefore assumes the central admission condition
and cannot be used to prove the needed boundary cancellation. The direct
L1 cell partition and norm-tail construction above is the pivot.
The returned cyclic-descent definition remains an existential requirement,
not an implementation of a physical reader. No C48 Lean module exists yet.
