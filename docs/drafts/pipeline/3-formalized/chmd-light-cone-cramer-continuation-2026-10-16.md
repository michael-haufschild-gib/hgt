# CHMD light-cone decomposition and Klein–Gordon Cramér continuation

- **ID:** chmd-lc-cramer
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** CHMD route, frontier map; follow-up of chmd-stage16-growth-positivity-collapse (loop step 6 candidates (a), (b))
- **Statement:** (2) the prime kernel K_y(u) = (1/π)∫cos(y√(r²+2)) sech²(r/2) cos(ru) dr splits exactly as
  D(u+y) + D(u−y) − y² ∫_{−1}^{1} B(2y²(1−t²)) D(u−yt) dt with D(v) = 2v/sinh(πv) > 0 and the entire Bessel kernel
  B(w) = Σ (−w/4)^k/(k!(k+1)!) (J₁(x) = (x/2)B(x²)); (1) the zero-side wave Φ(z) = Σ_ρ m_ρ w_ρ cos(z ρ_ρ),
  analytic on |Im z| < 1, continues across the boundary of the unit strip, with leading simple-pole singularities at
  ±log n ± i whose residues are (2i/π)Λ(n)/√n (up to the symmetric signs).
- **Status:** both parts formalized unconditionally (STATUS MUST-1534–1538, CANNOT-560); standard axioms;
  `lake build --old` green; wired into the HTGeometry and RHTower umbrellas. Corrected reading of (1): the
  genuine simple poles at all four families ±log n ± i belong to the massless wave Φ₀ (continued to all
  Re v ≠ 0); the Klein–Gordon wave Φ has the exact singularity R/(z−p) − zR Log(z−p) + O(1) there and provably
  no meromorphic continuation; the boundary singular set of both waves is exactly {±log n ± i : n = 1 or Λ(n) ≠ 0}.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof = the Lean development)
- [x] 2 → 3  formalized: `masslessZeroWave_cramer`, `kgZeroWave_cramer`, `tendsto_kgZeroWave_boundary_four`,
  `exists_kgZeroWave_boundary_expansion`, `not_meromorphicAt_kgZeroWave_four`,
  `masslessZeroWave_boundary_singular_set`, `kgZeroWave_boundary_singular_set`,
  `chmdPrimeKernel_eq_free_sub_tail`, `chmdPrimeWave_eq_lightConeTransmute`, `cos_mul_eq_lightCone`
- [ ] 3 → 4  publication-ready

## Goal
Structural identities (not bounds, not RH equivalences): the light-cone transmutation L[A](z) = A(z) − (z²/2)∫_{−1}^{1}
B(2z²(1−t²)) A(zt) dt maps the massless (d'Alembert) sech² wave to the Klein–Gordon wave, on the zero side, the
archimedean side and the prime side simultaneously. The prime channel is a positive free part minus a Bessel tail;
the zero-side wave carries the primes as its boundary singularities (Cramér in Klein–Gordon coordinates).

## Plan (modules)
1. `HTGeometry/KleinGordonLightConeBesselKernel.lean`: B entire, bounds, B(0)=1; Beta integral
   ∫_{−1}^{1}(1−t²)^k t^{2j} dt = 4^{k+1}k!(2j)!(k+j+1)!/(j!(2k+2j+2)!); light-cone identity
   cos(zw) = cos(zr) − (c z²/4)∫_{−1}^{1} B(c z²(1−t²)) cos(zrt) dt for w² = r² + c (power series + Cauchy product).
2. CHMD prime-kernel light-cone decomposition: D via dslope of sinh(π·); (1/2π)∫sech²(r/2)cos(vr)dr = D(v);
   K_y(u) decomposition; prime wave = L[massless prime wave]; free part > 0.
3. Massless explicit formula (cos(vz)sech² = 2 specSq(cos(vz/2)sechHalf) − specSq sechHalf), archimedean u-form via
   the corpus Lévy–Khintchine identity: A₀(v) = gB(0)D(v) + ∫_0^∞ ω(u)[2D(v) − D(v+u) − D(v−u)] du.
4. Archimedean continuation across Im v = 1 (Re v > 1/2) by the rectangle contour [a, a+i/2] ∪ [a+i/2, ∞+i/2).
5. Massless continuation theorem on W = {|Im v| < 3/2, |Im v| < 1 ∨ 2|Re v| > |Im v|} minus poles; residues.
6. KG continuation L[F₀] on the slit domain, Φ = L[Φ₀] on the strip, radial residue law ε·Φ(log n + i − iε) → i·R_n.

## Log
- 2026-10-16 — created; corpus inventory: real `besselJ` only (no complex/entire), sech² transform
  `sechSqHalfSymbol_eq`, Lévy form `gammaHardyPhaseRate_sub_zero_eq_integral`, holomorphy under integrals
  `differentiableAt_integral_of_cauchy_dominated`, rectangle tools; no light-cone identity, no massless explicit
  formula, no continuation beyond the strip in the corpus.
- 2026-10-16 — modules compiled (lake env lean clean): `HTGeometry/KleinGordonLightConeBesselKernel` (B entire,
  Beta integrals, complex + real light-cone identity, `besselJ_one_eq`), `RHTower/CHMDDAlembertSechKernel` (D = 2/S,
  S = dslope sinh(π·), zeros of S = iℤ∖0, D > 0, D ≤ 8(1+|v|)e^{−π|v|}, Fourier identity, (w−i)D(w) → −2i/π),
  `RHTower/CHMDLightConePrimeKernelDecomposition` (light-cone splitting of sech²-weighted KG integrals by Fubini;
  K_y(u) = D(u+y)+D(u−y) − y²∫B·D(u−yt); chmdPrime/Pole/ArchWave = L[massless]; P₀ > 0),
  `RHTower/CHMDMasslessZeroWaveExplicitFormula` (Φ₀, Φ holomorphic on |Im z| < 1; massless explicit formula
  Φ₀(v) = (2/cos²¼)cosh(v/2) + A₀(v)/2π − P₀(v)). Next: module 4 (Lévy translate form of A₀, complex bounds),
  module 5 (contour continuation), module 6 (KG).
- 2026-10-16 — all ten modules built and audited (axioms propext/Classical.choice/Quot.sound only):
  `HTGeometry/KleinGordonLightConeBesselKernel`, `RHTower/CHMDDAlembertSechKernel`,
  `RHTower/CHMDLightConePrimeKernelDecomposition`, `RHTower/CHMDMasslessZeroWaveExplicitFormula`,
  `RHTower/CHMDArchimedeanLevyTranslateForm`, `RHTower/CHMDMasslessContinuationPieces`,
  `RHTower/CHMDMasslessCramerContinuation`, `RHTower/CHMDKleinGordonTransmutationComplexTime`,
  `RHTower/CHMDKleinGordonCramerContinuation`. Final statements:
  (2) `K_y(u) = D(u+y) + D(u−y) − y²∫_{−1}^{1}B(2y²(1−t²))D(u−yt)dt`; prime, pole, archimedean and zero-side waves
  are light-cone transmutations of their massless counterparts; the free prime wave `P₀ > 0`.
  (1) massless: continuation to `Re v > 1/2, −1/2 < Im v < 3/2`, simple poles exactly at `log n + i` with residue
  `(2i/π)Λ(n)/√n`; Klein–Gordon: holomorphic continuation across `x + i` (`x > 1/2`, `x ≠ log n`),
  `ε·Φ(±log n ± i(1−ε)) → −(2/π)Λ(n)/√n`. Honest scope: the KG singularity is pole + log branch (leading rate
  proved); the archimedean point `±i` and the strip `0 < |Re| ≤ 1/2` of the boundary are not treated.
  Plan deviation: the continuation domain is the rectangle-strip `Re v > 1/2` (all prime points lie there since
  `log 2 > 1/2`), not the bow-tie domain W of the plan; the KG continuation is stated pointwise at regular
  boundary points and by the vertical residue law at prime points, which avoids slit-domain bookkeeping.

- 2026-10-16 — review of (1): "simple poles of the KG wave" is false as stated; closed the gap in three steps.
  E1 `RHTower/CHMDMasslessBoundaryContinuation`: cutoff-`a` continuations agree (`archContinuation_congr`), the
  pointwise cutoff `min(1/2, Re v/2)` glues them on the quadrant, `Φ₀(−v) = Φ₀(v)`, `Φ₀(v̄) = conj Φ₀(v)` give all
  four quadrants: `masslessZeroWave_cramer` — holomorphic at every `|Im v| < 3/2`, `Re v ≠ 0`, non-prime point;
  simple poles with residue `s₂(2i/π)Λ(n)/√n` at all `s₁ log n + s₂ i`. KG continuation `kgBoundaryWave = L[F]`
  holomorphic wherever `[0, z]` avoids the singularities (`LightConeRegular`), so at every boundary `x ± i`, `x ≠ 0`,
  non-prime. E2 `RHTower/CHMDKleinGordonBoundarySingularity`: exact expansion
  `Φ(p − iε) = R/(−iε) − (p − iε)R Log(−iε) + O(1)` (`exists_kgZeroWave_boundary_expansion`); hence
  `‖Φ − R/(z − p)‖ → ∞` and no meromorphic continuation at any of the four families
  (`not_meromorphicAt_kgZeroWave_four`; order ≠ 1 killed by the leading law, order 1 by the log term via dslope);
  `kgZeroWave_cramer` collects everything. E3 `RHTower/CHMDArchimedeanBoundarySingularity`: sector positivity
  `Re cosh(yγ)/cosh²(γ/2) ≥ e^{−(1−y)|Re γ|}`, Hardy's infinitude (`exists_riemannZeta_line_zero_dyadic`) ⇒
  `Σ m_ρ e^{−δ|Re γ|} → ∞`, so `Re Φ₀((1−δ)i) → +∞`; Bessel kernel ≥ 0 on the negative axis ⇒ `Re Φ((1−δ)i) → +∞`.
  Final: `masslessZeroWave_boundary_singular_set`, `kgZeroWave_boundary_singular_set` — on `|Im v| = 1` the points
  without a continuous extension are exactly `|Re v| = log n`, `n = 1` or `Λ(n) ≠ 0`. All standard axioms,
  `lake build --old` green, `lake env lean` clean, wired (RHTower umbrella), lint clean for these modules.
- 2026-10-16 — Klein–Gordon coordinates (MUST-1539), `RHTower/CHMDKleinGordonInverseLightCone`: inverse light-cone
  identity at mass² −2; `Φ₀ = L⁻¹[Φ]` on the strip, `L`, `L⁻¹` mutually inverse; `kgZeroWave_inverseLightCone_cramer`:
  `L⁻¹[Φ]`, built from the KG wave alone, continues beyond the strip with simple poles (`MeromorphicAt`,
  `meromorphicOrderAt = −1`) at all `±log n ± i`, residues `s₂(2i/π)Λ(n)/√n`. Φ itself stays pole + log (CANNOT-560).
- 2026-10-16 — pivot of (1) to the true statement (MUST-1540), `RHTower/CHMDKleinGordonPrimeBranchStructure`:
  `kgZeroWave_cramer_branch` — Φ continues beyond the strip (segment-regular points), boundary singular set exactly
  `±log n ± i` (n = 1 or Λ(n) ≠ 0), and at each prime point `Φ = L/(z−q) − L z B(2(z²−q²)) Log(1 − z/q) + H`, H
  holomorphic, cut along the ray through q, jump `2πi L z B(2(z²−q²))`. Ingredients: Bessel divided difference Q
  (entire), log integral along the light-cone segment, polar split of the massless continuation.
