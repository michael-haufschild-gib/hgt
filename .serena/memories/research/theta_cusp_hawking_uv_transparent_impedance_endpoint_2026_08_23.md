# Theta-cusp Hawking UV-transparent impedance endpoint (2026-08-23)

## Correction / falsification
- `ThetaCuspHawkingHartleHawkingDoubleKMSEndpoint.lean` remains mathematically correct only as an occupation-aligned same-pair diagnostic.
- [FALSIFIED] Pure double-KMS thermality alone does not force `q_c=q_-c`: charged TFDs of complex scalars factor into independent positive/negative charge sectors with shifted ratios (Chapman–Chen, arXiv:1910.07508).
- File header/docs now explicitly state missing producer: prove real theta mirror has no independent charge-conjugate sector and same oscillator-pair alignment.

## New endpoint
New file:
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingUVTransparentImpedanceEndpoint.lean`

Primary physical source: Jaekel–Reynaud, “Causality, stability and passivity for a mirror in vacuum,” arXiv:quant-ph/0101080.
Their Laplace impedance:
`Z(p)=∫dΦ(ρ)(1-i p ρ)/(p-iρ)+k/p+p(m-μ)`.
Causal/unitary/high-frequency-transparent partial mirror gives nonnegative spectral measure; `μ≤m` gives positive-real impedance and stability.

Formalized:
- exact kernel real part `Re K_ρ(p)=Re(p)(1+ρ²)/|p-iρ|²`;
- finite atomic impedance strict positive-real for nonnegative weights/spring and strict mass margin `μ<m`;
- KMS/FDT dissipative transition intensities supply weights unconditionally;
- concrete structure `ThetaCuspHawkingUVTransparentKMSFDTImpedanceLimit` for locally uniform convergence of mass-renormalized finite impedances to exact `thetaCuspHawkingBornCausalFormFactor p = XiC(i p)` on `Re p>0`;
- weak positive-real sign passes to limit; source anchor `XiC(i/2)=1/2` plus minimum principle upgrades strict;
- positive theta horizon charge is excluded; reflected resonance excludes negative charge;
- theorem `riemannHypothesis_of_thetaCuspHawkingUVTransparentKMSFDTImpedanceLimit`.

## Exact open core
[OPEN CORE] Construct the source-specific locally uniform impedance limit. Perfect-mirror cutoff cannot tend to infinity at fixed mass because induced mass grows with cutoff; producer must co-renormalize mass while retaining exact theta response. This is strictly stronger and more causal than thermality, pointwise CCR, QEI, purity, or raw passivity.

## Verification
- Target module compiled via `lake env lean`.
- Double-KMS module recompiled.
- Axiom audit for main theorems: only `propext`, `Classical.choice`, `Quot.sound`.
- Full `scripts/formal_tools.py lint` blocked by unrelated shared-worktree module `GaloisForLFunctions.RHTower.MellinReflectionEquation` being unreachable from umbrella.
- New module imported in `formal/GaloisForLFunctions/RHTower.lean`.
