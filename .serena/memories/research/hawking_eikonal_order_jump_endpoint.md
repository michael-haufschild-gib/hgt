# Hawking full-mirror eikonal/order-jump endpoint (2026-08-23)

File: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingFullMirrorEikonalOrderEndpoint.lean`.

Source-faithful exact identity for tilted trajectory `p(v)=v+lambda*k_a(v)`:
`M(a,lambda,out,in)=(-2*in)*Fourier(exp(-i*(lambda*out)*k_a)-1)((in+out)/(2*pi))`.
Therefore full Davies--Fulling mirror scattering is eikonal Fourier, not sectorwise scalar Cayley.

Define moments `I_n(a,w)=integral exp(-iwx) k_a(x)^n dx`. Strict log-concavity plus Schwartz decay gives strict unimodality and peak concentration, proving `I_(n+1)(a,w) != 0` eventually for every `|a|<1`, real `w`. Hence every tilted sector couples in some finite nonlinear jet unconditionally.

First moment satisfies `I_1(a,w)=XiC(w+a*I)`. Thus:
- `ThetaCuspHawkingAllOrderSectorJetMixing` is unconditional.
- `RiemannHypothesis ↔ ThetaCuspHawkingPrincipalSectorMixing`.
Interpretation: an off-line Xi zero is not an exactly dark full-scattering sector; it is a coupling-order jump (Born jet vanishes, nonlinear jet survives). RH is universal first-order onset / absence of order jumps.

Paper analytic corollary not yet formalized: eikonal Fourier is entire in coupling (bounded source + dominated differentiation), so a nonzero power moment makes exact amplitude nonzero for arbitrarily small generic nonzero coupling; coupling zeros are isolated.

Verification: direct Lean compile clean. Axiom audit for exact amplitude, all-order mixing, and RH equivalence reports only `propext`, `Classical.choice`, `Quot.sound`.

Route verdict: full dynamics does not select canonical Cayley and all-order mixing is too weak because unconditional. Remaining genuinely RH-bearing producer must independently select the first/Born (quadratic FGR/Davies) channel as exact operative resonance observable or suppress nonlinear channels at Born zeros; Hawking KMS/scattering alone does not supply this.