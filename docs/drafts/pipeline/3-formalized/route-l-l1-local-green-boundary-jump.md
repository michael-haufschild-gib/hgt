# Route L: original local Green primitives and their complete boundary

- **ID:** L-C48
- **Date:** 2026-09-12
- **Stage:** 3-formalized
- **Type:** source-forced domain enlargement / complete boundary classification
- **Depends on:** C44 actual weighted source; C47 original L1 admission obstruction
- **RH status:** unproved

Chain: complete original Green/BV source → fixed physical-reader agreement
→ conormal vanishing → RH. C46 supplies the complete damped Xi packet.
C47 excludes common integrable original-prime primitives of a nonzero L1
source. This result constructs the actual larger primitive domain and
identifies the complete boundary it retains. Fixed-reader agreement remains
unproved.

## Constructed result

For any integrable real-line source f and any original period L>0, the
literal future sum `G(t)=sum_(j>=0) f(t+jL)` is integrable on every original
translated cell. It solves `G(t)-G(t+L)=f(t)` almost everywhere on each cell.
In L1 on `(0,L]`, with its original Lebesgue measure,

- `G(t+NL)` tends to zero;
- `G(t-NL)` tends to `Per_L f(t)=sum_(k in Z) f(t+kL)`;
- their complete two-ended difference tends to that same periodization.

Every cellwise L1 primitive of the original equation has the form
`u_m=G_m+c`, where c is a fixed element of original-cell L1. It can be an
arbitrary function on the cell; it is independent of the integer cell
index. Both endpoint limits follow: `c` and `Per_L f+c`. No endpoint limit
or zero-periodization condition is assumed. Every primitive therefore has
the same complete jump. Periodic freedom cannot remove it.

The jump's original Fourier coefficient is exactly
`L^(-1) Fourier(f)(k/L)`. For C44's actual damping-two source, every integer
mode at every original prime period `L=log(p)` is nonzero. The primitive
domain is enlarged without discarding any original source boundary.

## Dependency-closed paper proof

Put `C_L=L1((0,L],dt;C)` and let `v_k` be the restriction of `f(t+kL)`.
Translated cells partition the real line up to endpoints, giving
`sum_(k in Z) ||v_k|| = integral_R ||f(t)|| dt`.
In the formal proof the unit-cell partition is transported to the original
cell with both scaling factors cancelled explicitly. Neither the measure
nor the Fourier normalization is changed.

Define `G_m=sum_(j>=0) v_(m+j)` and `P=sum_(k in Z) v_k` in the complete
normed space `C_L`. Absolute norm summability makes these actual L1 sums.
Splitting the first summand gives `G_m-G_(m+1)=v_m`. Splitting the full
integer series gives
`P=G_m+sum_(j>=0) v_(m-j-1)`.
The positive sum is a tail at m=N, hence tends to zero. At m=-N the second
sum is a tail of the fixed negative-index sequence, hence tends to zero;
therefore `G_(-N)` tends to P. The Lp representative theorem identifies
these vectors almost everywhere with the literal source sums.

For any other cellwise primitive, `d_m=u_m-G_m` satisfies `d_(m+1)=d_m`.
A function on the integers of period one is constant, giving `u_m=G_m+c`.
This proves both endpoint limits and their invariant difference. Finally,
the existing original-scale L1 periodization formula identifies every
Fourier coefficient. C44's unconditional damping-two coefficients give the
actual-source nonvanishing instance.

## Unproved extensions and next attack

A finite absolute first moment may give a sharp global L1 range theorem:
zero periodization should be equivalent to existence of a globally
integrable primitive. Counting each source cell with its distance from the
origin supplies the prospective norm bound. This stronger moment theorem
is not claimed formalized here.

The next concrete comparison is the literal primitive's weighted Mellin
transform. For c>0, translation multiplies the weighted source norm by
`exp(-cL)`. A geometric norm sum should therefore give weighted L1 admission
and `M(G_L f)(s)=M(f)(s)/(1-exp(-sL))` on the actual admitted strip. The
periodic jump fixes the original boundary residues and must remain in the
Green/BV-to-physical comparison. Pointwise Xi readings do not establish a
full-packet norm bound for this new denominator.

Damping values must remain distinct. At damping two the original source is
unweighted L1; at damping one C44 only supplies the proved positive-weight
strip. Neither unweighted admission nor the periodization limits may be
transferred across damping without proof. Reader agreement and any
zero-damping passage remain open.

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

## Lean validation and optimization

The complete draft passed `lake env lean /tmp/route_l_c48_green.lean`
without diagnostics. Its initial final leaf audit also passed. Profiling
then attributed 91.3 seconds to imports and 2.31 seconds to elaboration,
with 285 milliseconds in tactics. No resource limit was raised.

The generic calculus now lives in
`formal/GaloisForLFunctions/RHTower/DeningerL1GreenCellCalculus.lean`
(286 lines, 17 public declarations), importing only L1 periodization and
the necessary mathlib summation modules. The two concrete source results
remain in `DeningerL1LocalGreenBoundary.lean` (41 lines). Importing that
original application module still exposes all 19 public declarations.
Both modules are wired once into `RHTower.lean` and all 19 declarations
appear in the refreshed `LEAN_API.md`.

The narrowed core passed `lake env lean /tmp/route_l_c48_core.lean --profile`
with import time 1.3 seconds and elaboration 2.14 seconds. These are observed
profile timings, not a claim that the concrete source's heavy dependencies
have disappeared. Neither module contains a heartbeat or recursion-limit
override.

The optimized final audit
`lake build GaloisForLFunctions.RHTower.DeningerL1LocalGreenBoundary`
passed: only the new core (60 seconds) and its application (82 seconds)
were built. Existing dependency diagnostics were replayed. No full or
umbrella build, numerical experiment, or axiom-print command was used.
`scripts/formal_tools.py index` completed.

Global `scripts/formal_tools.py lint` returned exit 1 because the separate
`HTGeometry.SecondEndpointMellinLaurentInterchange` module was unreachable
from its theorem-area umbrella. C48's imports were present. This global
lint failure is not reported as a pass.

The prior runtime's temporary scratch files, search reports and process
handles disappeared. Their inspected search audits above survive in this
card; the missing final scratch result was not treated as evidence.
The recovered proof was saved in the workspace and checked again.

Validation artifacts retained alongside this card: the original and
narrowed-core profiles, optimized build log, lint log and index log.

Next attack: [weighted original Green Mellin comparison](../1-in-progress/route-l-weighted-original-green-mellin.md).
