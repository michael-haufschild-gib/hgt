# Parikh–Wilczek Borel-partner Hawking endpoint (2026-08-24)

Mission constraint: seek genuinely Hawking/evaporation-specific RH producer, not generic KMS/CCR/Cayley/classic-route relabeling.

## New exact core

For first Bose winding of the Parikh–Wilczek tunneling factor exp(-n x + ε n x²), the kth Mellin recoil derivative has Gamma shift Γ(s+2k)/n^(s+k). After Taylor and Borel normalization define

b_k(s) = Γ(s+2k)/(k!)²,
R_k(s) = ((s+2k)(s+2k+1))/(k+1)².

Exact recurrence: b_(k+1)(s)=R_k(s)b_k(s).

Functional-equation partner difference:
R_k(s)-R_k(1-s)=4(2k+1)(s-1/2)/(k+1)².
Therefore Re R_k(s)=Re R_k(1-s) iff Re(s)=1/2.

First-winding Borel transform is hypergeometric up to constants:
Γ(s)·₂F₁(s/2,(s+1)/2;1;4ξ),
with first singularity ξ=1/4 and local exponent 1/2-s. Partner exponent is s-1/2. This is a genuinely Hawking-specific reporter/invariant. Hostile audit later falsified ordinary two-sided temperedness as a producer: off-critical wall powers remain locally integrable, and exact tunnelling contractivity does not bound a Borel density. Generic KMS/CCR/group/inverse/Krein laws do not contain the quadratic entropy correction or 2k Gamma shift.

## Formalization

Created:
formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekBorelPartnerEndpoint.lean

Added umbrella import:
formal/GaloisForLFunctions/RHTower.lean

Recorded endpoint:
docs/reports/endpoints.md

Targeted Lean compile passed. New theorem axiom audit: only propext, Classical.choice, Quot.sound. Formal lint has no error from the new endpoint. Latest lint found only unrelated reachability errors in the concurrently changing HTGeometry umbrella: HorizontalLayerBlaschke and HorizontalLayerProjective.

## Full-winding wall isolation (paper-proved)

For 0<Re(s)<1:
B_s(ξ)=Σ_{k≥0} Γ(s+2k)ζ(s+k)ξ^k/(k!)²
decomposes as
Γ(s)(ζ(s)-1)+Γ(s)·₂F₁(s/2,(s+1)/2;1;4ξ)+H_s(ξ),
where H_s is holomorphic on |ξ|<1/2. This follows from Γ(s+2k)/(k!)²=O_s(4^k k^(Re(s)-3/2)) and ζ(s+k)-1=O_s(2^-k). Gauss continuation gives a nonzero (1-4ξ)^(1/2-s) branch at ξ=1/4 (logarithm at s=1/2), so higher windings cannot cancel first-wall monodromy.

Physical source weld: with x=8πME, ε=1/(16πM²), cutoff E≤M gives x=1/(2ε). Winding n+1 phase there is -(n+1)/(4ε), so Borel walls n+1 over 4 are exact finite-energy endpoint actions. Lean now proves endpoint action formula, exponential winding identity, A_0=1/4, and strict ordering.

For s≠1/2, B_s bounded approaching first wall iff Re(s)≤1/2; B_s and B_(1-s) both bounded iff Re(s)=1/2. Ordinary lateral Borel summability is too weak because off-critical divergences remain locally integrable.

Euler transformation gives the exact mirror gauge
F_s(z)=(1-z)^(1/2-s)F_(1-s)(z).
Writing g_s=exp(r_s+iφ_s), r_s=(1/2-Re(s))log(1-z), gives canonical doubled Hawking completion
S_s=e^(iφ_s)[[cosh r_s,sinh r_s],[sinh r_s,cosh r_s]].
It is SU(1,1)/Krein-unitary for every tilt; its pair coefficient vanishes iff Re(s)=1/2. Lean proves zero/nonzero mixing classification and cosh²-sinh²=1.

## Endpoint verdict

Full dynamics forces every tilted sector to mix; ordinary Hawking passivity does not exclude it. Pointwise Borel contractivity was a false hoped-for producer. A remaining RH-strength law would be a microscopic theta-dark-mode no-pair-creation theorem, but positive Parikh–Wilczek jets activate every zeta-zero sector, giving contrary evidence. Preserve wall hierarchy and mixing classification as positive survivors; do not claim RH proof.

Open only if new physics arises:
1. Derive a genuine winding-condensate cancellation making divisor-dark modes no-pair states.
2. Or prove a different singularity boundary condition incompatible with nonzero squeeze without merely assuming Hilbert–Pólya reality.
3. Verify literature novelty more deeply.

## Killed variants

- QNM chirp selective amplification: real-axis scattering bounded; QNM poles are off-shell.
- Fixed-Ξ evaporation blow-up: physical frequency comoves as 1/M and cancels temperature scaling.
- Late recoil/passivity: recoil repairs negative cubic at finite depth.
- Generic QEI/relative entropy: circular without exact raw multi-shell kernel weld.
