# PW-B complete signed adjoint response passage

- **ID:** PW-B-GAMMA-ADJOINT-PAIRED-RESPONSE-2026-09-11
- **Stage:** 3-formalized
- **Status:** Nineteen public theorems passed the final foreground Lean scratch without diagnostics. Exact source promoted and wired once; targeted leaf build passed in125s. All nineteen public names are indexed, and repository formal lint passed.
- **Scope:** Absolute joint admission of the complete signed backward response, original moving-cutoff mismatch limit and simultaneous native cutoff passage. Finite-cutoff gain transposition, full common-domain adjoints, Xi occurrence and independent Ward balance remain open. RH is not proved.
- **Depends on:** [complete reciprocal source bounds](pw-b-gamma-reciprocal-cutoff-source.md), [complete paired contact](pw-b-gamma-adjoint-paired-contact.md).

## Exact original-source statements

Retain the whole arithmetic source, with

`g_z(x)=M_z(x)/Q(x)`, `w(x)=exp(-x-1/x)/x`,

`S_z(t)=g_z(1/t)-1`,

`H_z(v,h)=exp(-h)*(S_z(v+h)-S_z(v))/h`,

`J_z,v(x,h)=w(x)*g_v(x)*conj(H_z(1/x,h))`.

For every two complex parameters z,v there are an integer r and a finite
C>=0 such that, for all positive x,h,

`|J_z,v(x,h)| <= C*x*exp(-x)*exp(-h)*(1+h)^r`.

Consequently J is absolutely integrable on the product of the two positive
rays. Every positive-x section is also absolutely integrable, not merely
almost every section.

For `a_delta(x)=delta/[x*(x-delta)]` on x>delta,

`integral_(x>delta) w(x)*g_v(x)*conj(integral_(a_delta(x)..delta) H_z(1/x,h) dh) dx -> 0`.

Both native cutoffs pass simultaneously:

`integral_(x>delta) w(x)*g_v(x)*conj(integral_(h>delta) H_z(1/x,h) dh) dx`

`-> integral_(x>0) w(x)*g_v(x)*conj(integral_(h>0) H_z(1/x,h) dh) dx`.

Limits are as delta tends to0 from above. Outer integrals in both cutoff
expressions and in the final response are admitted. The entire moving
mismatch layer and the originally omitted initial region remain in the
proof. The constant-field contact and its empty incoming constant loss
are retained separately in the previous paired-contact theorem.

## Proof

The source polynomial bound gives
`|g_v(x)|<=(1+A)*(1+1/x)^p`. The complete response estimate gives
`|H_z(1/x,h)|<=K*exp(-h)*(1/x+h)^r`.
Use

`(1/x+h)^r<=(1+1/x)^r*(1+h)^r`.

The elementary power bound and the original exponential factorial inequality

`w(x)/x^k<=(k+2)!*x*exp(-x)`

then absorb every inverse power in x. Gamma moments admit both factors
of the resulting product majorant. Global source measurability follows
from the actual atom sum; no pointwise numerical approximation is used.

Represent the two cutoff responses on one fixed positive product measure:

`J(x,h)*1_(x>delta,h>a_delta(x))`,

`J(x,h)*1_(x>delta,h>delta)`.

Each has norm at most |J|. For fixed positive x,h, both indicators are
eventually one, because a_delta(x) and delta tend to0. Dominated convergence
therefore takes both full product integrals to the integral of J.

Absolute admission justifies Fubini for each mask. The exact indicator
identities recover the original iterated integrals on x>delta. On every
such x, the difference of admitted tails is exactly the oriented interval
integral from a_delta(x) to delta. Subtracting the two limits proves the
mismatch theorem. Constants and complex conjugation commute with the actual
integrals, yielding the displayed original-source formulas.

## Remaining hard obstacle

The subsequent [complete gain transposition](pw-b-gamma-adjoint-gain-transposition.md)
retains the original triangle, reciprocal Jacobian and all integral admissions.
Together with this response passage and the retained logarithmic contact,
it now proves the [full original-current paired adjoint](pw-b-gamma-full-paired-adjoint.md).
A physical operator domain, source-forced geometry, a different justified Xi
realization and independent Ward balance remain requirements.

The precise corrected Gamma scalar ansatz is already excluded by the
[original-current valuation](../5-failed/pw-b-corrected-gamma-scalar-occurrence.md).
Neither the response admission nor a positive abstract dilation reverses
that obstruction.

## Verification and research

Leaf: `ThetaCuspHawkingParikhWilczekGammaAdjointPairedResponse.lean`.
Scratch: `/tmp/pwb-gamma-adjoint-response.lean`.
Key public theorems:

- `pwGammaMobiusAdjointResponseKernel_bound`;
- `pwGammaMobiusAdjointResponseKernel_integrable`;
- `pwGammaMobiusAdjoint_original_mismatch_integrable`;
- `pwGammaMobiusAdjoint_original_mismatch_tendsto`;
- `pwGammaMobiusAdjoint_original_native_tendsto`;
- `pwGammaMobiusAdjoint_original_response_integrable`.

The [whole-corpus search record](../1-in-progress/pw-b-gamma-adjoint-response-searches.json)
retains raw deep/method results with their partial coverage. Actual proof
mechanisms use complete source bounds, product integrability, exact interval
tail subtraction and dominated convergence from the installed corpus.
Broad recent arXiv dilation reading is recorded in the
[attack journal](../1-in-progress/pw-b-source-orientation-attack.md); its
strict-contraction dilation requires an independent exact source compression
and provides no Xi selection theorem here.

Final validation: exact scratch/promoted source equality, unique umbrella import,
all public API entries and local proof-card links checked. Only the requested
leaf was built; no full/umbrella build or numerical experiment was run.
All owned Lean and research processes are terminal.
