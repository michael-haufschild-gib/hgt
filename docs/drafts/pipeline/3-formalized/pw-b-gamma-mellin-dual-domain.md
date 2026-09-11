# PW-B Mellin evaluation against the reversible source norm

- **ID:** PW-B-GAMMA-MELLIN-DUAL-DOMAIN-2026-09-11
- **Stage:** 3-formalized
- **Status:** All seven public theorems passed final foreground scratch without diagnostics. Exact checked source promoted and wired once; targeted leaf build passed in57s. All seven public names are indexed; final repository formal lint passed.
- **Scope:** Test the passage from admitted source pairing to a Mellin reader. This does not retire PW-B or establish Xi occurrence. RH remains unproved.

## Source derivation and conjecture test

The checked source pairing uses g=M/Q and w=exp(-x-1/x)/x,
where Q=sqrt(x)*exp(-x). Its literal Mellin functional has kernel
k_s(x)=x^(s-1)*Q(x) against g. The squared dual weight is therefore

`|k_s(x)|^2/w(x)=x^(2 Re s)*exp(-x+1/x)` for x>0.

Conjecture: this dual weight is admitted near zero at some complex s,
allowing the direct global weighted Cauchy--Schwarz estimate.

Proved failure: write a=Re s and choose a natural n>2a+1. For0<x<1,
exp(-x)>=exp(-1), and the full exponential bound gives
exp(1/x)>=x^(-n)/n!. Hence the dual weight is at least
exp(-1)/n!*x^(2a-n). The exponent is less than-1, so its integral
diverges. This defeats the proposed global norm estimate at every s.
A claim that no bounded reader exists would additionally require the
Riesz/duality identification or explicit normalized test vectors; that
stronger conclusion is not yet asserted.

Proved positive survivor: the exact dual-weight identity and absolute
admission on every compact interval bounded away from zero. The already
proved complete source pairing also admits w*|g_z|^2 for every complex z;
that source admission does not establish a global Mellin norm estimate.
The next proof must quantify the missing endpoint control or change the
reader/domain with complete source provenance retained.

## Lean and corpus evidence

Leaf: `ThetaCuspHawkingParikhWilczekGammaMellinDualDomain.lean`.
Scratch: `/tmp/pwb-gamma-mellin-dual-domain.lean`.
Key public theorems:

- `pwGammaMellinDualDensity_source_eq`;
- `pwGammaMellinDualDensity_source_not_integrable`;
- `pwGammaMellinDualDensity_compact_admission`;
- `pwGammaMobiusGroundQuotient_weighted_square_integrable`.

The divergence and weighted source-admission statements have no spectral or
balance premises. The norm of the already admitted complete self-pairing is
exactly w*|g_z|^2, proving source admission for every complex parameter.

The installed ImproperIntegrals file contains integrableOn_Ioo_rpow_iff.
The installed real exponential factorial bound supplies the comparison.
The full-source Mellin bridge is only proved for Re(s)>-1/2 and
Re(z+s)>1; the new adjoint identity does not extend this region.
The [deep/method records](../1-in-progress/pw-b-gamma-mellin-dual-searches.json) retain
partial coverage732050 and732074 with no execution errors. Generated
residue and inverse-Mellin plans keep unproved incidence/admission premises;
none establishes this source reader. The direct source calculation supplies
the checked dual weight. The [narrow failed estimate](../5-failed/pw-b-global-mellin-dual-estimate.md)
records the obstruction and its positive survivor. Physical operator-domain
closure, Xi incidence and independently forced Ward balance remain open.
