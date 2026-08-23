# Theta-cusp Hawking pair-density and partner-correlation endpoint (2026-08-23)

## Outcome
Created two source-faithful Hawking endpoints and hostile-audited the prior Nambu/KMS limit.

### Exact physical pair-emission density
File: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingPairEmissionSpectralDensity.lean`

For the literal theta moving-mirror Born pair kernel
`K(u,v)=2 i u v XiC(u+v)`, proved for all real `w`:
[
\int_0^w |K(u,w-u)|^2du=(2/15)w^5 Xi(w)^2.
]
At `w>0`, physical pair flux is dark iff `Xi(w)=0`. Also proved any unit-norm total-frequency phase dressing leaves the complete density invariant. Thus particle number/FDT noise is all-pass blind.

Defined entire source-calibrated continuation
`D(z)=(2/15)z^5 XiC(z)^2`; its zeros are exactly `z=0` or `XiC(z)=0`. Proved RH iff every dark resonance of `D` has zero imaginary part.

### Exact anomalous Hawking partner shell
File: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingPartnerCorrelationEndpoint.lean`

Defined coherent exterior/partner Born shell amplitude
[
C(w)=\int_0^w K(u,w-u)du.
]
Proved exact phase-sensitive law
[
C(w)=(i/3)w^3 XiC(w).
]
Unlike density, total-frequency phase dressing multiplies `C` linearly and is observable with a calibrated joint quadrature. Defined entire continuation `C(z)=(i/3)z^3 XiC(z)`; zeros are `z=0` or Xi zeros. Proved RH iff all analytic anomalous-shell dark resonances are physical.

Literature basis:
- Dudley--Fabbri--Anderson--Balbinot, arXiv:2008.01433: Hawking-partner density correlations use anomalous correlator `<a_ext a_int>`.
- Tomitsuka--Yamaguchi--Hotta, arXiv:1906.05009: moving-mirror partner modes depend on detector wavepacket design and can retain trajectory information.
- Butera, arXiv:2306.03813: moving-mirror influence kernels are quadratic/convolutional two-channel pair-frequency kernels, not `logDeriv` amplitudes.
- Bechhoefer, arXiv:1107.0071: causal stable responses may be non-minimum-phase/all-pass; causality cannot supply minimum phase.

## Hostile audit
File: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingNambuKMSInfluenceEndpoint.lean`

Removed improper `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` label. Marked thermodynamic convergence to `logDeriv XiC` as `[CIRCULAR] [OPEN CORE]`: every finite response is already anti-Herglotz, so convergence imports the RH-strength sign; known moving-mirror influence functionals produce quadratic convolutions, not a logarithmic derivative. Valid finite Nambu Hermiticity/KMS lemmas remain as conditional receiver/no-go diagnostic.

## Frontier
Hawking radiation is now used at correct two-mode level:
- particle flux gives exact positive quadratic density but erases all-pass phase;
- anomalous exterior/partner correlation retains phase linearly.

Missing producer is narrower: derive a canonical **source-locked partner quadrature plus independent rigidity law** that forbids nonreal dark resonances. Hawking thermality, CCR, Gaussian purity, passivity, generic causality, and ordinary Kramers--Kronig do not do this. Do not revive minimum-phase as a consequence of causality. Potential next audit: whether local moving-boundary trajectory equations, inverse scattering data, or a source-specific modular/QNEC identity fixes this quadrature and constrains its analytic zeros without restating RH.

## Verification
- `lake env lean` passed for both new files and audited Nambu file.
- Targeted `lake build` passed for both new modules.
- Axiom audit for core formulas, phase laws, and RH bridges: only `[propext, Classical.choice, Quot.sound]`.
- `scripts/formal_tools.py lint` fails only on unrelated shared-worktree issue: umbrella cannot reach `GaloisForLFunctions.RHTower.DeningerDynSysOmegaDomainRing`.
- Umbrella imports added to `formal/GaloisForLFunctions/RHTower.lean`.
