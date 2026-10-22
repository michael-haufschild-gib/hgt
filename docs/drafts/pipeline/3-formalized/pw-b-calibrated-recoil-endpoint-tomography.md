# PW-B calibrated recoil endpoint tomography

## Status

Formalized in Lean 4 on 2026-08-28. Frontier label: HC33.

## Route

Parikh–Wilczek/backreaction (PW-B).

## Problem

PW recoil holonomy detects critical-wall orientation at each grade, but prior finite and countable cross-grade reporters admit signed dark kernels. HC32 gives coefficient-faithful countable endpoint tomography, but only as a scalar winding reporter. Couple these two source-derived structures without losing either wall orientation or packet faithfulness.

## Result

The imaginary recoil holonomy factors at every grade as

\[
  \operatorname{Im}H_k(s)=W(s)R_k(s),
  \qquad W(s)=-2\operatorname{Im}(s)(2\operatorname{Re}(s)-1),
\]

where `R_k(s)>0` in the open critical strip. Define the calibrated orientation by the literal quotient `Im H_k(s) / R_k(s)` and couple it to the physical endpoint-winding basis. Lean proves:

\[
  \mathcal T_{c,s}(j)=W(s)\,\mathcal E_c(j),
\]

and, for every uniformly bounded packet `c` and nonreal open-strip `s`,

\[
  (\forall j,\;\mathcal T_{c,s}(j)=0)
  \Longleftrightarrow
  \bigl(\operatorname{Re}s=\tfrac12\bigr)\lor(c=0).
\]

Thus this source-exact calibrated family has no residual infinite dark sector.

For the canonical constant-one packet, the closed route endpoint has no hypotheses:

\[
  \mathrm{RH}
  \Longleftrightarrow
  \forall\rho\in\operatorname{supp}(\Xi),\ \forall j,\;
  \mathcal T_{\mathbf1,\rho}(j)=0.
\]

## Lean artifact

- Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekCalibratedRecoilEndpointTomography`
- File: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekCalibratedRecoilEndpointTomography.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Exact kernel: `schwarzschildParikhWilczekCalibratedRecoilEndpointResponse_eq_zero_iff`
- Premise-free endpoint: `riemannHypothesis_iff_schwarzschildParikhWilczekCalibratedRecoilEndpointResponse_zero`

## Proof

Strict positivity makes each residual divisor nonzero, so the calibrated per-grade phase equals `W(s)` exactly. Infinite-sum scalar extraction gives the reporter factorization. HC32 classifies simultaneous vanishing of all physical endpoint samples as `c=0`; at nonzero height, elementary factorization classifies `W(s)=0` as the critical line. Their product therefore has exactly the asserted union kernel. The canonical packet is bounded and nonzero, eliminating the packet branch on Xi support.

## Verification

- Direct `lake env lean` check: passed with no warnings.
- `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekCalibratedRecoilEndpointTomography`: passed (11,617 jobs).
- `#print axioms` on five public theorem endpoints: only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint`: no finding in HC33; only unrelated pre-existing unreachable-module failures.

## Corpus audit

Mandatory research searches found the exact recoil factorization and positive residual in `ThetaCuspHawkingParikhWilczekPositiveMatrixCrossGradeClassification`, the literal source holonomy in `ThetaCuspHawkingParikhWilczekBorelPartnerEndpoint`, HC32 countable endpoint injectivity, and older signed/countable dark-kernel no-go theorems. No corpus theorem divided out the exact residual and coupled the resulting common orientation to a coefficient-faithful countable physical endpoint basis.

## Literature audit

Primary-source searches included [Parikh–Wilczek, *Hawking Radiation as Tunneling*](https://arxiv.org/abs/hep-th/9907001), backreaction tunneling extensions, and [Connes–Consani, *The Scaling Hamiltonian*](https://arxiv.org/abs/1910.14368). These sources respectively motivate the nonthermal recoil law and an operator-theoretic RH setting; none supplies this residual-calibrated Borel-grade holonomy, countable physical winding tomography, or the joint-kernel/RH equivalence above. Absence is reported as a search result, not a proof of global priority.

## Significance and remaining burden

HC33 closes the PW-B reporter-design burden: oriented recoil and infinite bounded-packet faithfulness coexist in one source-exact countable family. It does not prove that Hawking/PW dynamics forces universal flatness of this family on Xi support. That source-side vanishing/positivity producer remains the substantive RH burden.
