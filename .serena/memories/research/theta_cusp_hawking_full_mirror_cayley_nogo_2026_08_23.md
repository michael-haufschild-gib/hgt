# Full theta-mirror/Cayley no-go (2026-08-23)

Exact inertial-subtracted Davies–Fulling numerator for `p_λ(v)=v+λg(v)`, `g=thetaCuspFullSource`, was formalized in `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingFullMirrorCayleyNoGo.lean`.

With total frequency Ω=ω_in+ω_out, pointwise phase `exp(-iΩv-iλω_out g(v))` gives coupling jets
- `M'(0)=2 i ω_in ω_out Fourier(g)(Ω)` (angular convention), the existing Xi-valued Born channel;
- `M''(0)=2 ω_in ω_out^2 Fourier(g^2)(Ω)`.

For balanced positive sectors, `M''(0)=2ω^3 Fourier(g^2)(2ω)`. Since `g>0`, `Fourier(g^2)(0)=∫g^2>0`; continuity gives a positive interval where it is nonzero. Canonical Cayley transition is odd in λ, so every central second difference and second derivative vanish. Therefore exact full theta-mirror S cannot equal the sectorwise Cayley completion, even locally.

Lean closes pointwise derivative identities, exponential L1 domination, both differentiations under integral, square-Fourier normal form, positive-frequency nonvanishing, and theorem `no_fullThetaMirror_eq_canonicalCayley_at_all_balanced_frequencies`. Direct compile passes. Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.

Scientific survivor: canonical Cayley remains a valid repeated-interaction/KMS dilation of the Born tangent, not full moving-mirror S. Full nonlinear dynamics carries `Fourier(g^n)` channels and may lift a Xi/Born zero; hence unqualified full-S mixing is not RH-bearing. Remaining viable producer must isolate weak-coupling/Davies quadratic coefficient, or prove an exact projection/selection law that removes all `n≥2` channels and forces mixing to factor through Xi.

Primary literature audited: Obadia–Parentani, arXiv:gr-qc/0103061; Haro–Elizalde, arXiv:0709.3638. See `mem:research/theta_cusp_hawking_kms_cayley_scattering_mixing_endpoint_2026_08_23`.