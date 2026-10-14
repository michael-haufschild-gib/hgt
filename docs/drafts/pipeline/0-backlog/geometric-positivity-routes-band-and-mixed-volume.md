# Geometric positivity routes: hyperbolic band structure (Route D) and mixed volumes (Route MV)

- **ID:** geometric-positivity-routes-band-and-mixed-volume
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** route-tt-loop-2026-10-13 rows 244, 251–253, 256, 263–266, synthesis S231–256
- **Statement:** RH follows if ζ's zeros are realized either as the first-band 1-form Ruelle resonances of a hyperbolic flow with constant expansion rate 1 (Route D), or as the multiplier spectrum of a mixed-area form of an arithmetic (F-)convex body (Route MV). Both inequalities are proven theorems: Faure–Tsujii band structure, and the Minkowski / Alexandrov–Fenchel inequalities.

## Goal
Weil positivity is extremal: inf W = 0 is attained, for example by Ξ-divisible blind tests (route-tt row 239). So positivity must come from an IDENTITY-level mechanism. Two proven identity-level mechanisms are absent from the corpus (zero hits):
1. **Band structure** (Faure–Tsujii; Dyatlov–Faure–Guillarmou). For contact Anosov flows, Ruelle resonances at large |Im s| lie in vertical bands. The first band sits at Re s ≈ −½·(expansion rate), where the ½ is the transverse metaplectic zero-point energy. A gap separates it from the rest, giving a UNIFORM resonance-free half-plane created by hyperbolicity.
2. **Hodge index for convex bodies.** The planar mixed area V(K,L) = π Σ_n (1−n²) ĥ_K(n) conj ĥ_L(n) has signature (+; 0, 0; −, −, …). For F-convex sets in Minkowski space 𝕄^{1,1}, the kernel modes cosh x, sinh x are translations. After x ↦ x/2 they are exactly Weil's pole terms e^{±x/2}. So Weil positivity has the form of a reversed Minkowski inequality on boost-orbits of a virtual body.

Neither mechanism is an average, a perturbation or a group-theoretic gap, and both pass the corpus walls 6 and 7 and the amenability obstruction (row 238).

## Gates
- [ ] 0 → 1  in-progress: needs a concrete candidate flow or body built from arithmetic, not from the zeros.
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
**Route D.**
- Zeros enter the explicit formula with the odd-degree (H¹) sign, as in #C(F_q) = q + 1 − Σα_i. So the correct sector is Dyatlov–Zworski 1-forms (k = 1), where the Selberg zeros of hyperbolic surfaces live. The 0-form/emission sector gives only the Γ_ℝ poles (row 252).
- The adelic scaling flow (x, ξ) ↦ (e^t x, e^{−t} ξ) has constant expansion rate 1. Its Guillemin–Sternberg orbit weights log p·√p/(p−1) are Selberg's sinh weights.

**Route MV.**
- For any virtual body K, the kernel Φ_K(x) = V(K, B_x K) is Lorentzian. Its Fourier multiplier is a fixed-sign factor times |ĥ_K|².
- Polygonal K has kinks of Φ_K exactly at the edge-alignment rapidities.

## Obstructions found (route-tt rows 251, 252, 265)
- **Dimension ("ζ is a pure cusp").**
  - First-band Weyl laws grow like T^{d+1} on (2d+1)-dimensional contact manifolds. ζ has T log T.
  - Bowen–Ruelle (δ = h/λ = 1 for entropy h = 1 and expansion λ = 1) predicts an area law, ~T².
  - The T log T is the scattering signature of a cusp (SL₂(ℤ): (T/π) log T from φ′/φ). The transverse directions of the adelic flow are p-adic and isometric, so the flow is a compact group extension.
- **Cusp resonances.** On SL₂(ℤ)\H, ζ's zeros are scattering poles at s = ρ/2 (Re s = ¼ under RH). They are parabolic and outside every hyperbolic band. Maass–Selberg positivity holds automatically there (row 257).
- **Route MV.**
  - Matching the atomic zero measure forces ĥ_K to be supported on the zeros, so the body is built from the zeros.
  - Polygonal kinks occur at log(n/m) for all rational ratios, and convex edge lengths are positive, so they cannot cancel.
  - Fuchsian Alexandrov–Fenchel reduces to Laplacian self-adjointness (Fillastre), which leads back to the cusp.

## Open questions (precise)
1. Is there a partially hyperbolic system (a compact group extension with p-adic fibres) with a band-structure theorem whose base is the 1-dimensional scaling flow, i.e. "d = 0 plus a logarithm"?
2. Is there a virtual body K whose kink weights at non-integral rationals log(n/m) cancel exactly while those at log n are Λ(n) n^{−½}?
3. A Bohr-idempotent reformulation (row 266): under RH with simple zeros, M ⋆_mean M̃ = M for the Weil distribution M. Is there a geometric reason for idempotence?

## Log
- 2026-10-14 — created in 0-backlog from route-tt-loop rows 244–266. Both routes are OPEN; their three natural realizations are killed, with named obstructions.

## Route RZ (Ruelle realization), added 2026-10-14 (route-tt rows 297–298)
- **Theorem (paper; Pollicott's meromorphic extension).** If ζ is the Ruelle zeta Π_γ(1−e^{−sℓ_γ})^{−1} of a suspension flow over a mixing finite-alphabet SFT with Hölder roof, then ζ ≠ 0 on Re s > 1−ε for some ε > 0, i.e. quasi-RH, the TT core.
  - Proof idea: flat traces give ζ_R = Π_i(1−λ_i(s))^{−1}·exp(analytic). This is meromorphic and zero-free wherever the essential radius θ^α e^{P(−σr)} is below 1.
- **Obstruction.** Livšic periodic data are coherent: the targets log p(w₁^a w₂^b) ≈ a log p₁ + b log p₂ + C₁₂. Also, a bijection between orbits and primes forces π(x) = #orbits at every scale, so the realization implies the PNT with a power saving. Realization is therefore quasi-RH-hard.
- **Real-analytic (nuclear, Mayer-type) case.** ζ_R = Π_k det(1−L_{s,k})^{(−1)^k}, and its zeros come only from the k = 1 (odd) factor.
  - ζ_R is zero-free on Re s > σ₁, where P(−σ₁r − log|T′|) = 0.
  - For geodesic-type roofs (r = log|T′|) with entropy 1, σ₁ = 0. Then ζ_R would be zero-free on Re s > 0, so ζ is not such a Ruelle zeta.
  - At σ₁ = ½, Wielandt/non-lattice forbids zeros on the line, contradicting Hardy.
- **RH in RZ language:** the eigenvalue-1 locus of the 1-form transfer operator is exactly Re s = ½.
