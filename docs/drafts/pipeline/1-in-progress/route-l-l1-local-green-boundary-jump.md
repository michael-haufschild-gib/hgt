# Route L: the original local Green primitive and its complete boundary jump

- **ID:** L-C48
- **Date:** 2026-09-11
- **Stage:** 1-in-progress
- **Type:** source-forced domain enlargement / complete Green boundary comparison
- **Depends on:** C44 actual weighted source, C46 full Xi packet, [C47 L1 circle injectivity](../3-formalized/route-l-l1-original-circle-injectivity.md)
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
not an implementation of a physical reader.

Two further deep/method reports are terminal. The cell/Green query
(`/tmp/route_l_c48_cell_green_deep.json`, generation 876662) expired during
retrieval and ranking, with coverage pending. All 20 candidates and 20
source arguments were inspected; no proof ideas or ingredient groups were
returned. The integer-tail query
(`/tmp/route_l_c48_integer_tail_deep.json`, query generation 876699) reports
a later complete inventory of 56969 files (47367 Lean, 9602 prose), but
partial retrieval, a disconnected semantic worker and malformed judging
output. All returned declarations, candidates and source arguments were
inspected. Inventory completeness is not compiler or semantic completeness.
The fundamental-domain unfolding methods require actual integrability;
the Connes orbit-energy method additionally requires summability of the
product integrals and cannot manufacture the needed reader comparison.

The focused mathlib deep/method report
`/tmp/route_l_c48_mathlib_tail_deep.json` is also terminal. Its 19 candidates,
20 source arguments and proposed group were inspected. Retrieval and
reranking remain partial; generation 876727, later inventory snapshot
876731. It retrieves `tprod_of_nat_of_neg_add_one`; the source's
`to_additive` declaration supplies the additive integer decomposition used
in scratch. The proposed nonnegative-domination group requires a summable
majorant and injectivity, and is not a boundary-vanishing argument. The
actual source integral supplies the majorant here. `tendsto_sum_nat_add`
and `Lp.coeFn_tsum` are checked through their actual applications, not
accepted from source-index metadata alone.

Current scratch `/tmp/route_l_c48_green.lean` implements the original-cell
L1 vectors and integer tail decomposition. The source norm partition uses
mathlib's `Integrable.hasSum_intervalIntegral_comp_add_int`, with both
scaling factors cancelled explicitly to retain `(0,L]` and original
Lebesgue measure. `Lp.coeFn_tsum` is the intended bridge back to the literal
source. This scratch is still under validation; no C48 result is yet
claimed formalized.

## Stronger positive survivor under verification

For any two cellwise L1 primitives of the same original translation
equation, their difference is independent of the integer cell index.
Consequently every such primitive has the same complete two-ended jump,
even when its separate endpoints do not converge. The periodic freedom
cancels between matching endpoints. This strengthens the canonical future
sum construction to a classification of all cellwise primitives and a
source-forced boundary invariant. It supplies no vanishing boundary law.

## Distant-paper method audit

Broad arXiv intake used `scattering`, sorted by announcement date. The
September 3, 2026 paper [First Two-Hadron Form Factor from QCD](https://arxiv.org/html/2609.04142v1)
retains a finite-volume triangle correction and a residue normalization in
its exact relation between finite-volume current matrix elements and the
infinite-volume amplitude (equation 7). Its Ward identity uses a conserved
electromagnetic current. Neither that conservation premise nor its
finite-volume normalization has been derived for the fixed Route L reader;
no cancellation theorem is transferred. Only the method of retaining the
complete correction in the comparison is pertinent here. No numerical
part of the paper is used.
