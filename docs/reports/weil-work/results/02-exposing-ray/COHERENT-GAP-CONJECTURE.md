# Exact geometric-completion gap — next source conjecture

Status: FORMALIZED; full scratch and final installed-source audits passed. The refinement below strengthens the initial fixed-step conjecture. This concerns the explicit cycle-9 family, not all possible repairs. The original opposite-ray production conjecture and universal WP02 lower bound remain OPEN.

## Exact conjecture

Use the actual definitions `q`, `gain`, `weight`, `mass`, `repair` in `WeilWorkExposingRayCoherentCompletion.lean`. There exists delta>0 such that, for every N>=1 and every 1/201<=s<=1/200,

    delta <= mass(N,s)^2 * archEnergy(farPolarTest(s)).

By the existing exact `energy_identity`, the right side is the TOTAL energy of farPolarTest(N*s) together with its explicit finite variance repairs. Thus the conjecture asserts that this exact coherent completion cannot approach zero total energy, even though its repair cost is uniformly bounded and its complete integer trace vanishes. It does not assert a lower bound for arbitrary alternative completions.

## Corpus evidence and attack

The current corpus proves `RHTower.one_tenth_le_ccmRestrictedWeilPolarGroundEnergy_halfLogTwo` and positivity slightly past that aperture. The actual short source has aperture s+17/50<=69/200<log(2)/2 and vanishes at both polar frequencies. Its nonzero real Fourier value at zero is governed by the actual factor `1-farPolarCoeff s`; s stays in a compact interval away from zero. The existing geometric weights give mass>=weight(0,0)>=1 since 0<q(s)<1 and N>=1. These suggest an unconditional positive gap.

Unpaid proof obligations: transfer the precise restricted-Weil ground inequality to this C2 source and the normalization of `archEnergy`; prove a uniform nonzero mass bound analytically; verify the exact constants or use a proved compactness minimum. No blanket continuity or smoothness assumption may replace these steps. Source `farPolarTest` is only known C2 here; do not silently apply a C-infinity-only bridge.

The 2026-10-07 deep query containing the exact ground-energy theorem and farPolarTest completed with partial=false and found both direct parents. Its generated ingredient set used unrelated packet/eigenvalue objects and is inapplicable. The preceding broad Green/coherent-residual query was partial due a local semantic deadline; available results did not supply the needed normalized bridge. No absence or novelty claim follows from these searches.

Attack verdict so far: BRIDGE candidate. The strict small-aperture gap is already established; the proposed new information is its exact, uniform consequence for the concrete completion mechanism. If the bridge is already present, cite it and move on. A successful gap would eliminate this mechanism's zero-cost endpoint; then return to construction of a genuinely different opposite-ray source, rather than claiming generic PBAP.

## Stronger conjecture exposed by the paper-to-Lean audit

For every N and every 0<=s<=1/200,

    (3*pi/25)*(1-farPolarCoeff(N*s))^2
      <= mass(N,s)^2 * archEnergy(farPolarTest(s)).

In particular, whenever N*s>=4 the total energy is at least the fixed positive constant `(3*pi/25)*(1-1/cosh(2))^2`, even under arbitrary step refinement s -> 0. This is stronger than the initial compact-step conjecture and needs its own audit.

The proposed invariant is exact: evaluate the already-proved geometric multiplier at frequency zero to obtain `mass(N,s)*(1-farPolarCoeff(s))=1-farPolarCoeff(N*s)`. The actual Fejer source equals one on the entire interval [-3/10,3/10], even after shifts by |s|<=1/200. Consequently the short polar source equals `1-farPolarCoeff(s)` on that interval. The existing ground gap then bounds its energy below by `(3*pi/25)*(1-farPolarCoeff(s))^2`; multiplying by mass squared cancels every small-step loss exactly. No limiting argument, compactness minimum, or energy-continuity assumption is required.

Attack checklist: verify the actual plateau including both shifts; transfer C2 sources with the exact Fourier normalization; use the exact finite-filter identity, without replacing the family by an arbitrary repair; prove the positive constant analytically. Fresh deep corpus query completed with partial=true (semantic timeout and malformed judge output); all 20 candidate lemmas and 20 source arguments were inspected. It returned the actual farPolarCoeff parents but no applicable gap producer among those hits. There were no proof ideas or ingredient sets. Inventory complete for 68,446 files; compiler freshness remains partial and coverage snapshot older than current generation. Scoped exhaustive text search found no prior matching identity in the RHTower sources. These facts do not establish absence or novelty. The exact stronger pointwise bound, the uniform positive-separation corollary and the original fixed-step conjecture all now pass Lean with standard axioms only. Final installed-source audit passed without warnings.

External primary-source audit: [Suzuki, Weil’s quadratic form via the screw function, v3](https://arxiv.org/abs/2606.09096) (23 September 2026) supplies context already developed by the corpus. The inspected primary source does not establish scientific novelty of this concrete finite-filter floor; no such claim is made. The proof uses the corpus’s analytic one-tenth ground-gap theorem and does not use numerical certificates.
