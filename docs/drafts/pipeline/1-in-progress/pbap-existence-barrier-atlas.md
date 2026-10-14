# Prime-blind positivity: the existence problem and its barriers

- **ID:** pbap-existence-atlas
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (open-core map with proved laws)
- **Source:** route-tt loop rows 380–459 (`1-in-progress/route-tt-loop-2026-10-13.md`)
- **Statement:** RH is equivalent to PBAP, the nonnegativity of ζ's pole and archimedean functional on PD tests blind at every log n. Uniqueness of the Weil cone is complete and unconditional. Existence is the entire RH content; this card maps where existence can and cannot come from.

## Goal
A producer of PBAP (equivalently of a positive spectral measure with atoms at the zeros) from ζ-free or automorphic data. The non-circularity requirement is that the producer must not encode the zero locations.

## What is proved (Lean unless marked)
- RH ⟺ PBAP (`TwistedArcMinimumPrincipleProof`).
- PBAP_S ⟺ RH ∧ S ⊇ {prime powers} (`PrimeBlindNodeCriticality`).
- Pole-weight window ⊆ {1}, unconditional (`WeilPoleWeightForcedOne`, built on `WeilPoleWeightWindow`).
- Degree classification: the only Γ_ℝ^d member with RH is ζ^d (`WeilConeDegreeHerglotzClassification`).
- Anomaly bound: Re P + γ(0)‖f‖² ≤ weilArchRe. Strong violators are pole-negative (`WeilBlindPoleSignLaw`).
- Positive classes far from the null face: separated narrow bumps (`SeparatedBumpPrimeBlindPositivity`, another lane) and windows (corpus ground energy ≥ 1/10).
- [P] Null face analytic part = one ray G₀ = (E′ geodesic profile) ⋆ (arc kernel). Index law: cusp +1, corner +1, kernel −2, excluded mode +1.
- [P] The arc-TMP mechanism exists only for SL₂(ℤ):
  - Dirichlet characters q ≥ 2: the Fricke circle radius 1/q fails to separate.
  - Fricke groups Γ₀(2)⁺, Γ₀(3)⁺: the central L-function ζ²(1+p^{½−w}) is never a square.
  - Non-arithmetic Hecke groups: no Euler product.

## Proved laws on where positivity can come from [P]
1. **Two budgets.** On blind tests, arch ≥ (Ω(0) + Cap)·g(0), where Cap < |Ω(0)| ≈ 5.37 is the integers' Lévy capacity (strictness certified by G₀). The pole must cover the remainder. Every deformation (pole weight, conductor, node dilation, Hecke/Fricke group) is critical exactly at ζ's data.
2. **The pole carries the sign, not the index.** W = M + P with M Markovian (archimedean and prime jumps) and P of signature (1,1).
   - RH ⟹ (ind₋(M_even), ind₋(M_odd)) = (1, 0) at every level.
   - k off-line quadruples ⟹ ind₋(M_even) ∈ [k, k+1] and ind₋(M_odd) ≥ k − 1.
   - So "at most one bound state" excludes only ≥ 2 quadruples; it is not equivalent to RH (row 460 corrects row 454).
   - Soft bound-state counts diverge.
3. **Null edge at infinity.** Under RH the moment region's lower boundary is the half-line {(P, −P) : P ≤ P₀}. Only G₀ attains it; the rest is a Tauberian limit of chirp-scale tests that interpolate zeta's zero set up to the Nyquist height (no smooth blow-up, by Titchmarsh). Every explicit positive class sits at positive distance from this edge.
4. **Atoms versus densities.** Every proven positivity in reach yields densities that vanish at zeros, or bounds kept away from the edge. This covers unitarity, Maass–Selberg, Rankin–Selberg, Kuznetsov with Weil/Salié bounds, Lévy energy and Pitt/Beckner. RH needs a positive measure with atoms at the zeros, i.e. a point spectrum (wall 12).
5. **Incompatible algebras.** On Dirichlet-polynomial tests the arithmetic part is divisibility-triangular (Smith/GCD-positive, product-type symbols) while the archimedean part is quotient-type multiplicative Toeplitz, so no divisibility Cholesky factorization exists.

## Open sub-problems (sharp, ζ-free or explicit)
- **Cores.** Do Ψ-blind compact cores (ζ-divisible wandering vectors with compactly supported Möbius inverse) exist for large support ratio?
  - The dimension count gives threshold 2, which matches the proven no-go.
  - The dual separators are Hurwitz-type combs; bounded separators are impossible beyond ratio ≈ 5.83.
  - Only ≈ 215 = e^{|Ω(0)|} constraints resonate.
- **Sign of S = Σ Λ(n)n^{−½} log n · G₀′(log n).** It decides whether node dilation is doubly critical at ζ.
- **Quasi-RH ladder.** PBAP(t) ⟸ (zero-free strip Re s > 1 − t/2) + anomaly fill. The converse has no mechanism.
- **Bound-state form.** A nonlocal oscillation theory for arithmetic jump operators would bound ind₋(M_even) and so the number of off-line quadruples. The last quadruple needs the sign content of the pole (row 460).

## No-go closure
- **Killing mechanisms:** wall 12 (forced dual measure), atoms/densities (law 4), the null edge at infinity (law 3).
- **Strongest positive survivor:** the Lean anomaly bound and pole-sign law (`WeilBlindPoleSignLaw`), the unconditional window ⊆ {1}, and the uniqueness of ζ in the arc mechanism.
- **New insight:** the existence problem is concentrated on a single geometric locus (the null edge at infinity), whose tests are chirp-scale zero interpolants. No finite-scale, unitary or Markovian positivity reaches it.
- **Status:** OPEN. The paper laws are in the route-tt log rows 435–459.

## Log
- 2026-10-14 — created from route-tt rows 380–459.
- 2026-10-14 (opus loop row 1211, MUST-1467): `SeparatedBumpPrimeBlindPositivity` is now uniform in the number of bumps (`exists_primeBlind_nonneg_bumpSum`, packing lemma `natCast_le_one_add_div_of_separated`). Support-blind tests have Lévy gain Θ(log 1/δ) against pole loss O(√δ log 1/δ). Violators must be blind by cancellation. Open: the critical separation scale. The crude bound needs s ≳ 9.3√δ. Is there a support-blind violator at s ≍ √δ, or does positivity persist down to s ≍ δ?
