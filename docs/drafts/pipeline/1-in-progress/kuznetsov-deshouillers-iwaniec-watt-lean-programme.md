# Kuznetsov → Deshouillers–Iwaniec → Watt: Lean programme for Matomäki–Teräväinen Lemma 3.5

- **ID:** KDIW-LEAN
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme — classical mathematics, formal frontier only
- **Source:** `../2-fully-proven/route e/_lean-programme.md` (the two route-E cards are closed mod E1/E2);
  Deshouillers–Iwaniec, Invent. Math. 70 (1982) 219–288 (GDZ scans, canvases 243–312 of
  PPN356556735_0070; page p ↔ canvas p+24); Watt, J. Number Theory 53 (1995) 179–210 (not accessible;
  its bound is quoted in Bettin–Bui–Li–Radziwiłł arXiv:1609.02539, Lemma 3.2);
  Matomäki–Teräväinen arXiv:2207.05038 Lemma 3.5.
- **Statement:** prove `MTDeshouillersIwaniecBound` (E1) and `MTWattBound` (E2) of
  `Sieve/MatomakiTeravainenTwistedFourthMoments.lean` unconditionally (E1 may be weakened to the range
  actually consumed: twist length `A ≤ T^{1/5}`, see below).

## Why this is unavoidable
- MT's Harman sieve discards `I₂(ε)` with `I₂(0) ≤ 0.99`; the Type I/II range `M₂ ≤ X^{1/4−ε}` enters
  the discarded region's boundary (`q₁ < X^{1/4−2ε}`), so it cannot be shrunk to `X^{1/5}`.  Type I/II
  therefore needs the twisted fourth moment `≪ T^{1+ε}` for twists up to `T^{1/4}` with bounded
  coefficients — Watt's theorem (DI alone: `T^{1/5}`; Weil alone (Iwaniec 1980): `T^{1/10}`).
- Type I consumes DI only through the prime-power amplifier with `(2P)^k ≤ T^{1/5}`
  (`integral_unitBlock_fourth_amplifier_le`), i.e. ℓ²-twists of length `≤ T^{1/5}`: the DI numerator
  `T + A²√T + A^{5/4}T^{3/4} ≤ 3T` there.

## Dependency DAG (top down)
1. **E1/E2 from the `N ≤ √T` forms.**  MT's proof: `T < N` done in Lean
   (`MatomakiTeravainenWattDIOverHeight`); `√T < N ≤ T` by the approximate functional equation for the
   partial sum (reflection to length `T/N`); `N ≤ √T` is Watt (4.7) / DI power-mean (14).
2. **Twisted fourth moment for `N ≤ √T`** from the Kloosterman-fraction bounds: expand
   `|N|⁴|A|²`, diagonal `m₁n₁n₂ = m₂n₃n₄`, off-diagonal `h ≠ 0` → Poisson in the long variables →
   sums of Kloosterman fractions `e(±h c r v/(s p))` → Watt's bound (BBLR Lemma 3.2) resp. DI Thm 12.
3. **Watt's bound** (BBLR Lemma 3.2 form) and **DI Theorems 10–12** from DI Theorems 6/7 (weighted
   large sieve for exceptional eigenvalues, averaged over the level) and Theorems 8/9.
4. **DI Theorems 2, 5–9** (spectral large sieve, exceptional-eigenvalue weighted large sieve, sums of
   Kloosterman sums with smooth weights) from Kuznetsov's formula (DI Thm 1) + Proposition 3
   (quadratic forms `B_a(θ,c,N)` in Kloosterman sums) + Weil's bound (corpus
   `WeilKloostermanBound`) + Bessel-transform estimates (DI §7).
5. **Selberg's 3/16 for Γ₀(q)** (DI Thm 4): corpus has Γ(N) (`SelbergThreeSixteenths`); transfer.
6. **Kuznetsov's formula** (DI Thm 1, (1.19)/(1.20)) for Γ₀(q), cusps 𝔞, 𝔟, test `φ ∈ C³_c(0,∞)`:
   - (1.20) (`S(m,−n)`): Poincaré series `U_{𝔞m}(z,s)` + Parseval in `L²(Γ\ℍ)` + K-Bessel
     (Kontorovich–Lebedev) inversion;
   - (1.19) (`S(m,n)`): additionally the holomorphic Petersson formula for Γ₀(q) at cusps, all even
     `k ≥ 2` (weight 2 via Hecke's trick), and the Neumann decomposition `φ = φ_B + φ_H`.
7. **Spectral decomposition** `L²(Γ\ℍ) = ℂ ⊕ L²_cusp ⊕ L²_Eis` (Parseval form) — for Γ(N) (all cusps
   SL₂(ℤ)-equivalent; Γ₀(q) data by projecting to Γ₀(q)-invariants):
   - cuspidal: ONB of Maass cusp forms — corpus `MaassFiniteDeckCuspidalFriedrichs` (self-adjoint,
     compact resolvent at 0 on `CuspidalL2 N`); need the compact spectral theorem (mathlib
     `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`, corpus
     `CompactOperatorDiscreteSpectrum`) and the Fourier/K-Bessel expansion of eigenvectors at every
     cusp (1-D ODE regularity of each Fourier mode — no 2-D elliptic regularity needed);
   - Eisenstein: `L²_cusp^⊥` = closure of incomplete Eisenstein series; Parseval via Mellin inversion
     and a contour shift to `Re s = 1/2` — needs continuation of `E_𝔠(z,s)` to `Re s ≥ 1/2` with
     vertical-strip bounds, only pole `s = 1` in `(1/2, 1]`, unitarity of the scattering matrix on the
     line (Maass–Selberg).  Corpus: `SelbergEisensteinCriticalLine` (Γ(N), every cusp, holomorphic
     near `Re s ≥ 1/2` minus `{1/2, 1}`), `SelbergMaassSelbergGammaN` (region `1 < Re v < Re u`).
8. **Special functions:** `J_ν` (complex order), `K_ν`, `W`-Whittaker, integral representations and
   uniform bounds used in (1.21)–(1.23) and DI §7.

## Clean interface between the halves
The upper half (items 1–5) uses only: the Kuznetsov identities (1.19)/(1.20) for Γ₀(q) with one
spectral family per level (Maass coefficients `ρ_{j𝔞}(n)` at every cusp, `κ_j`, Eisenstein
coefficients `φ_{𝔠𝔞n}(1/2+ir)`, holomorphic `ψ_{jk}(𝔞,n)`), Weil's bound, and elementary analysis.
Build the upper half against a `Prop`-free statement once the lower half lands; while it is being
built, keep the Kuznetsov output as an explicit hypothesis of the upper-half lemmas only (never of
the card theorems).

## Milestones
- [ ] K0 inventory of corpus assets for items 6–8 (Poincaré–Kloosterman unfolding for Γ(N):
  `SelbergPeterssonKloosterman`; Γ(N) Eisenstein; deck Friedrichs; Bessel pieces)
- [ ] K1 compact spectral theorem → ONB of cuspidal eigenvectors; Fourier/K-Bessel expansion
- [ ] K2 Eisenstein continuation + Maass–Selberg on the line; incomplete-Eisenstein Parseval
- [ ] K3 Parseval for `U_{𝔞m}(·,s)`; rough Kuznetsov (parameter `s`); K-Bessel inversion → (1.20)
- [ ] K4 holomorphic Petersson for Γ₀(q) at cusps, `k ≥ 2`; (1.19)
- [ ] K5 Bessel-transform bounds (DI §7); Proposition 3; Theorem 2; Theorem 4 (3/16 via Kuznetsov)
- [ ] K6 Theorems 5–9 (exceptional eigenvalues; smooth sums of Kloosterman sums)
- [ ] K7 Theorems 10–12; Watt's bound (BBLR Lemma 3.2 form)
- [ ] K8 twisted fourth moments (N ≤ √T) — DI (14), Watt (4.7); AFE reduction; E1', E2

## Log
- 2026-09-29 — created.  Cards `route-e-cofactor-amplified-e3-token-supply` and
  `route-e-forbidden-support-e3-stability` are formalized modulo exactly E1/E2
  (`Sieve/CofactorAmplifiedTokenSupply`, `Sieve/MatomakiTeravainenForbiddenSupport`,
  `Sieve/CoprimeE3BlockReplacement`).  DI statements read (Thms 1–12, pp. 223–237).

## Paper plan, lower half (DI §3–4 read, pp. 243–255)
DI's route to Kuznetsov (§4.2–4.3): (4.5) `⟨U_{𝔞m}(·,s₁), U_{𝔟n}(·,s̄₂)⟩` by unfolding + the Fourier
expansion (3.7) of `U_{𝔞m}(σ_𝔟 z; s)` (Kloosterman sums, `B(γ,m,n,y,s)` with bound (3.8)); Lemma 4.1
(Kuznetsov's evaluation of `∫ y^{s₁+s₂−2}e^{−2πny}B dy` as a `K_{s₁−s₂}` half-circle integral);
continuation to `Re s > 3/4` by the Weil-type bound; Lemma 4.2 at `s₁ = 1+it, s₂ = 1−it`; spectral side
by Parseval (3.14) + Lemmas 3.2/3.5 (`⟨u, U_{𝔞m}⟩`, `⟨E_𝔟, U_{𝔞m}⟩` = Γ-factor × coefficient); then
integrate in `t` against Kuznetsov–Bessel transforms to reach general `φ` (§4.3).  Holomorphic part:
Lemma 3.1/3.3 + Petersson (4.1)–(4.4), summed over even `k` with `2Σ(−1)^k(2k−1)J_{2k−1} = −yJ₀`.
Spectral decomposition (3.13)/(3.14) is QUOTED by DI ([Kub],[Roe2],[Fad]) — we must prove it.

Master theorem to formalize: Parseval (3.14) on `L²(Γ(N)\ℍ)`, `N ≥ 3` (Γ₀(q)-data by `N = 3q` and
Γ₀(q)-invariants).  Chain:
- S1 full Friedrichs Laplacian `A` on the deck carrier; cuspidal space = `(incomplete Eisenstein)^⊥`
  (unfolding); density of `C¹` cusp-zero functions in `form-domain ∩ L²_cusp` (automorphic
  convolution); hence corpus `cuspidalFriedrichsOperator = A|_{L²_cusp}`.
- S2 compact spectral theorem (mathlib `orthogonalComplement_iSup_eigenspaces_eq_bot` on
  `C = J J†`) → Hilbert basis of `L²_cusp` of weak eigenvectors `⟨∇w,∇v⟩ = λ⟨w,v⟩` for all `v` in the
  full form domain.
- S3 Fourier modes: test with incomplete Poincaré series `Σ_γ (e(nx/L)ψ(y))∘γ`, unfold → weak Bessel
  ODE for `a_n(y)` on `(0,∞)` → `a_n = ρ(n)√y K_{iκ}(2π|n|y/L)` (1-D regularity, `L²` kills `I`).
- S4 Eisenstein: continuation of `E_𝔠(z,s)` (corpus `SelbergEisensteinCriticalLine`) to the closed
  line incl. `s = 1/2`, vertical-strip bounds, Maass–Selberg on the line ⇒ `Φ(1/2+ir)` unitary.
- S5 incomplete-Eisenstein Parseval (Mellin inversion, contour shift to `Re s = 1/2`, residue at
  `s = 1` = constants) ⇒ `L²_cusp^⊥ = ℂ·1 ⊕ (Eisenstein packets)`, isometric Eisenstein transform.
- S6 Parseval (3.14) for bounded `L²` functions with `𝓔_𝔠(r,f) = ∫ f \bar E_𝔠(·,1/2+ir)`.
- 2026-09-29 — Route for S1–S3 fixed: Selberg point-pair operators on the corpus deck carrier
  (`DeckL2 N = L²(𝒟; ℂ^{SL₂(ℤ)/Γ(N+1)})`), compactness on the cuspidal space through the corpus Rellich
  embedding (`L_φ` maps cuspidal `L²` into the cuspidal form pre-domain), smooth eigenvectors from
  `L_φ u = νu`, `Δ = ν⁻¹L_{Dφ}` on the finite eigenspaces, completeness by approximate identities, mean
  value property from corpus `integral_centred_kernel`.  Landed (built, wired):
  `HTGeometry/CompactSelfAdjointEigenbasis` (Hilbert eigenbasis of an injective compact symmetric
  operator), `HTGeometry/ModularCellPointPair` (`u(z,w)`, invariance, `SL₂(ℤ)` tiling
  `Σ_B ∫_𝒟 g(Bz) = 2∫_ℍ g`, local finiteness `finite_near_fd` by explicit entry bounds),
  `RHTower/DeckPointPairOperator` (`ppApply`, continuity, Schur bound, bounded operator `ppL2`).
  Next: self-adjointness, `C¹`/gradient bounds, cusp-zero preservation, compactness on `CuspidalL2`.
- 2026-09-29 — K1 landed (built, wired, axioms clean): `RHTower/DeckPointPairSymmetry` (`ppL2` symmetric),
  `RHTower/DeckPointPairRegularity` (equivariance, `C¹` in the chart), `RHTower/DeckPointPairGradient`
  (`‖y∂L_φF‖ ≤ (3R+2)‖L_{|φ'|}‖F‖e‖`, `L_φ : L² → formPreDomain`), `RHTower/DeckPointPairCuspidal`
  (unfolding `L_φF(z) = ∫_ℍ φ(u(z,w))F(w)dμ`, cusp-zero preservation, `PairProfile.cuspOp` compact
  symmetric on `CuspidalL2` via the Rellich embedding).  Next: nonzero eigenspaces of `cuspOp` are
  `C²` with `ΔL_φ = L_{Dφ}` (`Dφ = u(u+1)φ'' + (2u+1)φ'`), Green identity ⇒ they are Friedrichs
  eigenvectors; approximate identity `L_{φ_ε} → 1` ⇒ every Friedrichs eigenvector is a strong `C²`
  eigenfunction.
- 2026-09-29 — K1 landed: `RHTower/HyperbolicKernelIntegral` (chart kernel integrals `∫_ℍ K(ζ,w)G(w)dμ`
  are `C¹`/`C²` under the integral sign; radial kernels: `(∂ₓ²+∂ᵧ²)∫φ(U)G = (Im ζ)⁻²∫Dφ(U)G`),
  `RHTower/HyperbolicRadialGreen` (Green on `ℍ`: `∫φ(u(z,w)) y²ΔV = ∫Dφ(u(z,w))V`, via corpus
  `integral_test_laplacian`), `RHTower/DeckPointPairLaplacian` (`L_φF ∈ C²`, `y²ΔL_φF = L_{Dφ}F`,
  `L_φ(y²ΔV) = L_{Dφ}V`, `y²Δ` preserves deck equivariance).  Next: approximate identity
  `L_{φ_δ} → 1` on `deckCentralFixedL2` (corpus interior approximation + periodization), then the
  cuspidal eigenbasis (nonzero eigenspaces of `cuspOp` are `y²Δ`-invariant, symmetric; orthogonality
  of distinct Laplace eigenvalues by Green; completeness by the approximate identity).
- 2026-09-29 — **K1 spectral theorem landed** (built, wired, axioms clean):
  `RHTower/DeckPointPairApproxIdentity` (`‖L_φ f − f‖ ≤ ε` on `deckCentralFixedL2` for unit profiles of
  small radius; smooth unit profiles exist), `RHTower/DeckPointPairSelbergTransform` (Selberg's theorem
  `L_k U = h_k(s) U` for `C²` deck eigenfunctions via corpus `integral_centred_kernel`; `h_k(s) → 1`),
  `RHTower/DeckPointPairEigenRepresentative` (`SmoothProfile` (`C³`), representatives `ν⁻¹L_φu` of
  eigenvectors are `C²`, `L_{Dφ}` preserves eigenspaces, `IsCuspLaplaceEigen`),
  `RHTower/DeckCuspidalLaplaceEigenbasis` (`cuspEigenBasis N : HilbertBasis (CuspEigenIndex N) ℂ
  (CuspidalL2 N)`, `cuspEigenBasis_spec`: every vector is the class of a `C²` deck-equivariant
  cuspidal eigenfunction `-y²ΔU = λU`; eigenvalue spaces finite-dimensional).  Next (K1 rest):
  pointwise vanishing constant terms of cuspidal eigenfunctions; Fourier modes → Bessel ODE → `K`-Bessel
  expansion at every cusp; then K2 (Eisenstein, continuous spectrum).
- 2026-09-29 — **K1 complete** (built, wired, axiom-clean): `RHTower/MaassWhittakerUniqueness`
  (Bessel ODE for the corpus Schläfli `K_ν` from the order recurrence; `W = √y K_ν(ky)` solves
  `W'' = (k² + (ν²−¼)/y²)W`, bounded, `≢ 0` via the Mellin formula for `K_ν²`; convexity of `u²` ⇒ small
  solutions have `L²` value/derivative ⇒ Wronskian of small solutions vanishes ⇒ `eq_smul_whittakerW`),
  `RHTower/DeckCuspidalConstantTerm` (horocycle averages of `L_φ f` Lipschitz in `f`, vanish on the
  cuspidal closure; eigenfunctions are cusp-zero and in `cuspidalFormPreDomain`),
  `RHTower/DeckCuspidalFourierExpansion` (`deckMode_zero`, `deckMode_eq_whittaker`: every nonconstant
  Fourier mode of every deck coordinate of every `cuspEigenBasis` vector is `ρ √y K_ν(|κ_n| y)`).
  Next: K2 (Eisenstein series / continuous spectrum) — inventory corpus `SelbergEisensteinCriticalLine`,
  `SelbergMaassSelbergGammaN`, Γ(N) Eisenstein assets first.
- 2026-09-29 — **K0 inventory (corpus, Γ(N) scalar, level `N ≥ 3`)**: `SelbergPoincareSeries/Fourier/
  Continuation/Bounded/Pairing/Unfolding/Pole` (DI's `U_m(z,s)`: Kloosterman expansion with `S_N(m,n;c)`
  (`poincare_eq_Q`), continuation to `Re s > 3/4` by Weil, boundedness for `Re s > 2`, unfolding
  `⟨P_m, g⟩ = N∫y^{s−2}e^{−2πmy/N} a_{−m}(g)`), `SelbergPeterssonKloosterman/Split` (`⟨P_m(s),P_n(s')⟩ =`
  diagonal + Kloosterman terms, `2 < Re s' < Re s`), `SelbergEisenstein*` (continuation of `E_∞(σz,s)` at
  every cusp to a neighbourhood of `Re s ≥ 1/2` minus `{1/2,1}`, Fourier expansion with `D_n(s)` and
  `kerBessel`, scattering entries `phiσ`/`phiExt = C(s)D_σ(s)`), `SelbergMaassSelberg*` (Maass–Selberg for
  Γ(N) in `1 < Re v < Re u`).  Missing: Parseval for the continuous spectrum.
- **K2 plan.** (a) deck↔scalar transfer `F(z)(q) = f(q̃z)` (Γ(L)-invariant `f`, `L = N+1 ≥ 3`);
  (b) incomplete Eisenstein series `e_ψ` (cusp ∞, `ψ ∈ C_c^∞(0,∞)`) and SL₂(ℤ)-translates (all cusps);
  unfolding `⟨e_ψ, f⟩ = ∫ψ(y)·\bar{CT f(y)} dy/y²`; (c) `ℰ := CuspidalL2^⊥ ∩ central` is the closure of
  their span (mollifier `L_φ` + constant terms = pairings with incomplete Eisenstein series);
  (d) Maass–Selberg continued to `1/2 < Re s ≤ 2` (holomorphy of truncated pairings) ⇒ scattering entries
  bounded for `|Im s| ≥ 1` and `Φ(1/2+ir)` unitary; (e) Mellin inversion + contour shift to `Re s = 1/2`
  (residue at `s = 1` = constants) ⇒ Eisenstein Parseval on `span{e_ψ}`, then on `ℰ` by density;
  (f) pairings `⟨P_m, E_𝔠(·,1/2+ir)⟩`, `⟨P_m, u_j⟩` (Whittaker/Mellin Γ-factors) ⇒ K3.
- 2026-09-29 — **K2(b)/(c) landed** (built, wired, axiom-clean): `RHTower/DeckIncompleteEisenstein`
  (`HeightProfile`; deck series `incEis ψ v z = Σ_{(c,d)} ψ(Im M_{c,d}z) ρ(M_{c,d})⁻¹v` for `ρ(T)v = v`:
  local finiteness `finite_rows_im_ge` (r-function bound), continuity, equivariance, vanishing above
  `max(b, 1/a)`, `incEisL2`; unfolding `integral_inner_incEis_eq`
  `∫_𝒟⟨E,G⟩ = 2∫_0^∞ y⁻² ψ̄(y) ∫_0^1⟨v,G(x+iy)⟩dx dy`; point-pair images `ppApply_incEis`,
  `PairProfile.op_incEisL2`: `L_φE(·|ψ,v) = E(·|ψ̃,v)`, `ψ̃(t) = ∫φ(u(i,w))ψ(t Im w)dμ`),
  `RHTower/DeckCuspidalOrthogonalEisenstein` (fundamental lemma on `(0,∞)`; orbit vectors
  `deckOrbitVec q` turn horocycle averages into level constant terms; `mem_cuspidalL2Closure_iff`:
  `f ∈ CuspidalL2 ⟺ f central ∧ ⟨E(·|ψ,v), f⟩ = 0 ∀ψ, ∀ T-fixed v`).
  Next: K2(d) Eisenstein series `E(z,s;v)` in deck form, continuation/constant term, Maass–Selberg.
- **K2(d)–(e) detailed plan (deck-native, all cusps at once).** `V_∞ = {v : ρ(T)v = v, ρ(−1)v = v}`.
  (d1) `Ẽ(z,s;v) = ½Σ_{(c,d)} Im(M_{c,d}z)^s ρ(M_{c,d})⁻¹v` (`Re s > 1`); coordinate transfer
  `Ẽ(z,s;v)_q = ½Σ_{O ∈ ⟨T⟩\Deck} v(q g_O⁻¹) E_∞^{Γ(L)}(g_O z, s)` (rows `≡ (g₁₀, g₁₁) mod L`, corpus
  `poincare_smul_eq`/`mem_image_congr`); continuation through corpus `Econt`, `EcuspExt`; constant term
  `P_T∫_0^1 Ẽ(x+iy,s;v)dx = y^s v + y^{1−s}Φ̃(s)v` with `Φ̃` from corpus `phiσ`/`phiExt`.
  (d2) truncation `Λ^Y Ẽ = Ẽ − [y>Y](y^s v + y^{1−s}Φ̃v)` on `𝒟`; exponential decay of `E^*` (corpus
  `EstarExt` envelopes) ⇒ bounded, locally uniformly in `s`.
  (d3) deck Maass–Selberg (bilinear `Σ_q∫_𝒟 F_q G_q`) for `Re u > Re u' > 1`, `Y ≥ 1`, by unfolding the
  truncated row sum over `gammaSet` (`∫_𝒟Σ_p f(M_pz) = 2∫_strip f`); continuation by holomorphy of truncated
  pairings (identity theorem, cleared form `(u−u')(u+u'−1)·B = R`).
  (d4) `Φ̃(u)ᵀΦ̃(1−u) = I` near the line (pole cancellation at `u' = 1−u`), reflection `Φ̃(s̄) = conj Φ̃(s)`,
  unitarity on `Re s = ½`, boundedness for `|Im s| ≥ 1` (MS positivity), removable singularity at `½`,
  residue at `1`.  (d5) polynomial bounds for `Ẽ(z,s)` on compacta via `‖Λ^YẼ‖` + small-radius Selberg transform.
  (e) incomplete-Eisenstein Parseval via constant terms + Mellin + contour shift (Φ only); density of
  Mellin images; identification `T(P_ℰ f)(r) = ⟨f, Ẽ(·,½+ir)⟩` for nice `f` (contour shift on `f`'s side).
- 2026-09-29 — **K2(d1)–(d3) region landed** (built, wired, audited warning-free):
  `RHTower/DeckEisensteinSeries` (`eisVec s v = ½·incEis(y^s)`, summability, equivariance;
  `sum_deck_bottomRow` counting deck classes by bottom row mod `L`; `eisVec_apply_eq_sum`:
  `Ẽ(z,s;v)_q = (2L)⁻¹Σ_g v(qg⁻¹)E_∞^{Γ(L)}(gz,s)`), `RHTower/DeckEisensteinContinuation` (`IsCuspVec`,
  `scatVec` = Φ̃(s), `eisExt = y^s v + y^{1−s}Φ̃v + Ẽ^*` via corpus `EcuspExt`; `eisVec_eq_eisExt`;
  holomorphy in `s` on `W∖{1}`; `eisExt_smul` equivariance for `Re s > ½` by the identity theorem),
  `RHTower/DeckEisensteinTruncation` (`bil`, Φ̃ preserves `V_∞`, `intervalIntegral_bil_eisVec` constant term,
  `eisTrunc`, `eisTrunc_eq_truncRowSum` on `𝒟`), `RHTower/DeckMaassSelbergBounds` (majorants on `𝒟`,
  `integral_fd_tsum_eq_two_mul_strip` unfolding), `RHTower/DeckMaassSelbergRegion`
  (`deckMaassSelberg_region`: `∫_𝒟⟨Λ^YẼ(u;v),Λ^YẼ(u';w)⟩_β = msRHS u u' v w Y`, `1 < Re u' < Re u`, `Y ≥ 1`).
  Next: uniform `e^{-πy/L}` bounds for `EstarExt` on balls in `W` ⇒ holomorphy of truncated pairings ⇒
  MS on `(W∖{1})²` near the line ⇒ `Φ̃(u)ᵀΦ̃(1−u) = I`, unitarity, bounds.
- 2026-09-29 — **K2(d3')–(d4) landed** (built, wired): `RHTower/DeckEisensteinStarDecay` (uniform
  `|E^*_σ(z,s)| ≤ A e^{−πy/N}` on closed balls in `W`, `y/N ≥ Y₀`; continuity of `EstarExt` in `z`),
  `RHTower/DeckMaassSelbergContinuation` (`truncPairing` holomorphic in both parameters on `W∖{1}`
  via `differentiableAt_integral_of_cauchy_dominated`; `msDefect_eq_zero` on `({Re>½}∖{1})²`;
  `msDefect_eq_zero_line` at `(½+it, ½−it)`; `bil_scatVec_line`: `⟨Φ̃(½+it)v,Φ̃(½−it)w⟩_β = ⟨v,w⟩_β`),
  `RHTower/DeckScatteringUnitarity` (`conj φ(s) = φ(s̄)` from real Dirichlet coefficients + identity
  theorem + continuity to the line; `deckConjVec_scatVec`; **`inner_scatVec_line`/`norm_scatVec_line`:
  Φ̃(½+it) unitary on `V_∞`**).
  Next: eisExt reflection ⇒ MS positivity ⇒ `‖Φ̃(s)‖ ≤ 4` for `½ < Re s ≤ 2`, `|Im s| ≥ 1`; removable
  singularity of Φ̃ at `½`; residue at `1`; then K2(e) incomplete-Eisenstein Parseval.
- 2026-09-29 — **K2(d4) complete** (built, wired): `RHTower/DeckScatteringBounds` (`eisExt_conj`
  reflection; `truncPairing_conj = ∫‖Λ^YẼ‖²`; MS positivity `norm_scatVec_sq_le`:
  `‖Φ̃(s)v‖² ≤ ‖v‖² + (2σ−1)‖Φ̃(s)v‖‖v‖/|t|`; `norm_scatVec_le_four` for `½<σ≤2`, `|t|≥1`),
  `RHTower/DeckScatteringSingularities` (`(s−½)φ_σ(s)` has a limit (L-function residues, `Γ(s+½)`);
  unitarity ⇒ `tendsto_sub_half_mul_scatVec_apply` → 0 ⇒ **`exists_tendsto_scatVec_half`: removable
  singularity at ½**; `tendsto_sub_one_mul_phiExt`: common residue `scatResidue N` at `s = 1` for every
  cusp ⇒ `tendsto_sub_one_smul_scatVec`: `Res_{s=1}Φ̃ v = (2L²)⁻¹ρ₁(Σ_x v_x)·𝟙`).
  Parseval plan without evaluating `ρ₁`: residual term is `κ·conj⟨f,1⟩⟨g,1⟩`; Parseval exact on
  `span{E(·|ψ;v)} ∩ 1^⊥`, dense in `ℰ₀ ⊖ 1` (continuous functional); needs `1 ⊥ CuspidalL2`.
  Next: K2(e) Mellin/contour-shift Parseval for incomplete Eisenstein series.
- 2026-09-30 — **K2 complete: Parseval (3.14) on the deck carrier** (built, wired, axiom-clean):
  `RHTower/HeightProfileMellin` (`ψ̂(s) = ∫ψ(y)y^{-s-1}dy` entire, `s(s-1)ψ̂ = ∫ψ''y^{1-s}`,
  `|ψ̂(σ+it)| ≤ C(1+t²)⁻¹` on strips, inversion on every line), `HTGeometry/VerticalStripResidueShift`
  (contour shift past a simple pole: `∫F(b+it) - ∫F(a+it) = 2πA`), `RHTower/DeckIncompleteEisensteinMellin`
  (`E(·|φ,w) = π⁻¹∫φ̂(σ+it)Ẽ(σ+it;w)dt`; `⟨E_ψv,E_φw⟩` as a line integral on `Re s = σ > 1` by Fubini on
  `𝒟×ℝ`), `RHTower/DeckScatteringExtension` (removable value of `Φ̃` at `½`; `‖Φ̃‖ ≤ 4` on the closed strip;
  `Φ̃ᵀ = Φ̃` since `φ_{∞,g∞}` depends on `±g₁₀`; adjoint `Φ̃(½-it)* = Φ̃(½+it)`),
  `RHTower/DeckIncompleteEisensteinParseval` (both parts shifted to `Re s = ½`, residue at `1`, symmetrized:
  `⟨E_ψv,E_φw⟩ = π⁻¹∫⟨T_ψv,T_φw⟩ + 4φ̂(1)conj ψ̂(1)⟨v,Rw⟩`, `T_ψv(t) = ψ̂(½+it)v + ψ̂(½-it)Φ̃(½-it)v`),
  `RHTower/DeckConstantCuspidalOrthogonal` (**`𝟙 ⊥ CuspidalL2`** by ergodicity of positive point-pair
  averages: Jensen/Dirichlet-form identity ⇒ the projection of `𝟙` is locally constant ⇒ constant ⇒ 0),
  `RHTower/DeckIncompleteEisensteinDensity` (`E(·|ψ,ρ(-1)v) = E(·|ψ,v)`, sup-norm Lipschitz in `ψ`,
  mollification ⇒ `eisSpace` = closed span of `C²`/`V_∞` generators; `Cusp = Z ∩ eisSpace^⊥`),
  `RHTower/DeckEisensteinSpectralIsometry` (residual `κ⟨f,𝟙⟩⟨𝟙,g⟩`, `κ = (2L²)⁻¹ρ₁` never evaluated;
  transform extended to `eisSpace` (`eisTransformE`), `eisTransformL2 = T̄∘P_ℰ`, `𝟙 ∈ eisSpace`;
  **`inner_eq_cusp_add_eisTransform`**: for central `f,g` with `⟨𝟙,g⟩ = 0`,
  `⟨f,g⟩ = Σ_j⟨f,u_j⟩⟨u_j,g⟩ + π⁻¹⟨T̄f,T̄g⟩`; `eisTransformL2_incEisL2`: `T̄E(·|ψ,v) = T_ψv`).
  Next: K3 — deck Poincaré series `U_m(·,s)`, `⟨U_m,U_n⟩` by unfolding (corpus `SelbergPeterssonKloosterman`),
  identification of `T̄U_m` (pairing with generators + density of `{T_ψv}` in the symmetric `L²` space),
  `⟨u_j,U_m⟩` via the Whittaker modes (K1), then Kuznetsov with the Bessel transform.

## DI reference extract (scans `scratchpad/lit/di/p{canvas}.jpg`, paper page = canvas − 24)
- (1.3) `S_𝔞𝔟(m,n;γ) = Σ'_{δ mod γℤ} e(mα/γ + nδ/γ)` over `(α β;γ δ) ∈ σ_𝔞⁻¹Γσ_𝔟`; (1.6) for `q = rs`, `(r,s)=1`,
  `σ_{1/s} = (√r 1/√r ; s√r 1/√r)`-type: `γ = s√r C`, `(C,r)=1`, `S_{∞,1/s}(m,n;γ) = e(n s̄/r) S(m r̄, n; sC)`.
  Lemma 2.6: `|S_𝔞𝔞(m,n;c)| ≤ (m,n,c)^{1/2} c^{1/2} τ(c)`.
- (1.15) `u(σ_𝔞 z) = √y Σ_{m≠0} ρ_𝔞(m) K_{iκ}(2π|m|y) e(mx)`; (1.17) `E_𝔞(σ_𝔟z;s) = δ_𝔞𝔟 y^s +
  π^{1/2}Γ(s-½)Γ(s)⁻¹φ_𝔞𝔟0(s)y^{1-s} + √y Σ_{n≠0} 2π^s|n|^{s-½}Γ(s)⁻¹φ_𝔞𝔟n(s)K_{s-½}(2π|n|y)e(nx)`,
  `φ_𝔞𝔟n(s) = Σ_γ γ^{-2s} Σ_δ e(nδ/γ)`.  (1.18) `U_𝔞m(z;s) = Σ_{Γ_𝔞\Γ} Im^s(σ_𝔞⁻¹τz) e(mσ_𝔞⁻¹τz)`.
- **Theorem 1** (`φ ∈ C³_c(0,∞)`): (1.19) `Σ_γ γ⁻¹S_𝔞𝔟(m,n;γ)φ(4π√mn/γ) = (2π)⁻¹Σ_{k even}Σ_j i^k(k-1)!
  (4π√mn)^{1-k} conj ψ_jk(𝔞,m) ψ_jk(𝔟,n) φ̃(k-1) + Σ_j conj ρ_j𝔞(m) ρ_j𝔟(n) φ̂(κ_j)/ch πκ_j +
  π⁻¹Σ_𝔠∫(m/n)^{-ir} conj φ_𝔠𝔞m(½+ir) φ_𝔠𝔟n(½+ir) φ̂(r) dr`;
  (1.20) `Σ_γ γ⁻¹S_𝔞𝔟(m,-n;γ)φ(4π√mn/γ) = Σ_j ρ_j𝔞(m)ρ_j𝔟(n) φ̌(κ_j)/ch πκ_j +
  π⁻¹Σ_𝔠∫(mn)^{ir} φ_𝔠𝔞m(½+ir)φ_𝔠𝔟n(½+ir) φ̌(r) dr`;
  (1.21) `φ̃(l) = ∫J_l(y)φ(y)dy/y`, (1.22) `φ̂(r) = π/sh πr ∫(J_{2ir}-J_{-2ir})/(2i) φ dx/x`,
  (1.23) `φ̌(r) = (4/π) ch πr ∫K_{2ir}(x)φ(x)dx/x`.
- Lemma 3.2: `ρ_𝔞(m) = (4πm)^{s-½}π^{-½}Γ(s)/(Γ(s-½-iκ)Γ(s-½+iκ)) ⟨u, U_𝔞m(·,s̄)⟩` (Re s > 1), via
  (3.3) `∫e^{-y}y^{s-3/2}K_ν(y)dy = π^{½}2^{½-s}Γ(s-½-ν)Γ(s-½+ν)/Γ(s)`.
  Lemma 3.4/(3.7): `a_𝔞𝔟mn(y,s) = δδ e(b n) y^s e^{-2πny} + y^s Σ_γ γ^{-2s}S_𝔞𝔟(m,n;γ)B(γ,m,n,y,s)`,
  `B = ∫(x²+y²)^{-s} e(-nx - m/(γ²(x+iy)))dx`; (3.8) `|B| ≤ 4σ/(2σ-1) y^{1-2σ}e^{-π|n|y}` (shift to Im x = ∓y/2).
  Lemma 3.5: `m^{s-s₁}φ_𝔟𝔞m(s) = π^{s₁-s-1}2^{2s₁-2}Γ(s)Γ(s₁)/(Γ(s+s₁-1)Γ(s₁-s)) ⟨E_𝔟(·;s),U_𝔞m(·;s̄₁)⟩`.
- (4.5) `⟨U_𝔞m(s₁),U_𝔟n(s̄₂)⟩ = ∫a_𝔞𝔟mn(y,s₁)y^{s₂-2}e^{-2πny}dy`; (4.6) `⟨U_𝔞m(s₁), conj U_𝔟n(s₂)⟩ =
  Σγ^{-2s₁}S(m,-n;γ)∫y^{s₁+s₂-2}e^{-2πny}B(γ,m,-n,y,s₁)dy`.  **Lemma 4.3** (Kuznetsov):
  `∫y^{s₁+s₂-2}e^{-2πny}B(γ,m,-n,y,s₁)dy = π2^{2-s₁-s₂}γ^{s₁-s₂}Γ(s₁+s₂-1)/(Γ(s₁)Γ(s₂)) (m/n)^{(s₂-s₁)/2}
  K_{s₁-s₂}(4π√mn/γ)`; proof: `x = yξ`, swap, `∫y^{ν-1}e(ay-b/y)dy = 2e(ν/4)(b/a)^{ν/2}K_{-ν}(4π√ab)`
  (Im a > 0) and `∫(1+ξ²)^{-s₁}(1-iξ)^{s₁-s₂}dξ = π2^{2-s₁-s₂}Γ(s₁+s₂-1)/(Γ(s₁)Γ(s₂))`.
  Lemma 4.4 (`s₁=1+it,s₂=1-it`): `⟨U_𝔞m(1+it), conj U_𝔟n(1-it)⟩ = sh πt/t (n/m)^{it} Σγ^{-2}S(m,-n;γ)K_{2it}(4π√mn/γ)`.
  Spectral: `⟨U_𝔞m(s₁), conj U_𝔟n(s₂)⟩ = πm^{½-s₁}n^{½-s₂}/((4π)^{s₁+s₂-1}Γ(s₁)Γ(s₂)){Σ_j conj ρ_j𝔞(m) conj ρ_j𝔟(n)
  Λ(s₁,s₂;κ_j) + Σ_𝔠∫(mn)^{-ir} conj(φφ) Λ/|Γ(½+ir)|² dr}`, `Λ = ΠΓ(s_i-½±ir)`.
  Lemma 4.6 ⇒ (4.9): `Σ_γ 4π√mn γ⁻² S(m,-n;γ)K_{2it}(4π√mn/γ) = πΣ_j ρ_j𝔞(m)ρ_j𝔟(n)H(κ_j,t)/ch πκ_j +
  Σ_𝔠∫(mn)^{ir}φφ H(r,t)dr`, `H(r,t) = ch πr/(ch π(r-t) ch π(r+t))`.
- §4.3: (4.11) `-∫ t sh 2πt H(r,t)K_{2it}(θ)dt = θK_{2ir}(θ)`; (4.16) Kontorovich–Lebedev
  `(4/π²)∫t sh 2πt K_{2it}(x)(∫K_{2it}(θ)φ(θ)dθ/θ²)dt = x⁻¹φ(x)`; multiply (4.9) by
  `(4/π²) t sh 2πt ∫K_{2it}(θ)φ(θ)dθ/θ²`, integrate in `t` ⇒ (1.20).  (1.19) via (4.8)/(4.10)–(4.14) + Prop. 1
  (holomorphic: Petersson, `2Σ(-1)^k(2k-1)J_{2k-1} = -yJ₀`).
- Prop 3: `B_𝔞(θ,c,N) = Σ_{N<m,n≤2N} b_m conj b_n S_𝔞𝔞(m,n;c)e(2√mn θ/c)`: (1.25) `≤ τ²(c)c^{½}N‖b‖²`,
  (1.26) `≪ (c+N+√(θcN))‖b‖²` (hybrid Farey large sieve (5.1) + Mellin separation),
  (1.27) `≪ θ^{-½}c^{½}N^{½+ε}‖b‖²` (θ<2, c<N; Cauchy–Schwarz + Poisson).
- Theorem 2 (`μ(𝔞) = (w,q/w)/q`): (1.28)–(1.30) `≪ (K² + μ(𝔞)N^{1+ε})‖a‖²`. Theorem 4: `λ₁ ≥ 3/16`.
  Theorem 5: `Σ_exc X^{2iκ}|Σa_nρ_j𝔞(n)|² ≪ (1+√(μNX))(1+√(μN^{1+ε}))‖a‖²`. Theorem 6 (level average):
  `Σ_{q≤Q}Σ_exc X^{4iκ}|Σa_nρ_j∞(n)|² ≪ (QN)^ε(Q+N+NX)‖a‖²`; Theorem 7 (`a_n=1`): `(Q+N+√N X)N`.
- Theorem 8 (`g = f(4π√mn/γ)`, supp f ⊂ [X,8X], ‖f‖∞≤1, ‖f'‖₁≤2, ‖f''‖₁≤6Y/X, `θ_q = √max(0,1-4λ₁)`):
  `S_𝔞𝔟(a,b;g) ≪ (√Y + (1+|log X|+X^{-θ})/(1+X)·(1+X+√(μ(𝔞)M^{1+ε}))(1+X+√(μ(𝔟)N^{1+ε})))‖a‖‖b‖`.
  Theorem 9 (`g ∈ C⁶` on `[M,2M]×[N,2N]×[C,2C]`, derivative bounds): `Σ_{(c,r)=1}Σa_mΣb_n g S(m r̄,±n;sc) ≪
  C^ε(1+s√(rC)/√MN)^{θ_rs}(s√rC+√MN+√sMC)(s√rC+√MN+√sNC)/(s√rC+√MN)‖a‖‖b‖`.
  Theorem 10: `𝓛^± ≪ (CMNRS)^ε L ‖a‖‖b‖`, `L² = SR(S²RC²+MN+SMC²)(S²RC²+MN+SNC²)/(S²RC²+MN) +
  S²C³√((SR+N)RM)`; Theorem 11 (`a` = interval indicator): second term reduced by `M^{½}`.
  Theorem 12: `𝒦 = Σ_{r,s}Σ_{n≤N}b_{n,r,s}Σ_{c,d}g(c,d,n,r,s)e(n r̄d/sc) ≪ (CDNRS)^ε K‖b‖`,
  `K² = CS(RS+N)(C+DR) + C²DS√((RS+N)R) + D²NRS⁻¹`.

## Log 2026-09-30 (K3a, K3b)
- K3a DONE `RHTower/DeckPoincareSeries`: deck Poincaré series `P(z|h,v) = Σ_{(c,d)} h(M_{c,d}z)ρ(M_{c,d})⁻¹v`
  for `T`-compatible `(h,v)`, equivariance, unfolding `∫_𝒟⟨P,G⟩ = 2∫_strip conj h ⟨v,G⟩`
  (`integral_inner_poincSeries`, strip integrability `integrableOn_poincIntegrand_strip`), Selberg profile
  `y^s e(μz)` with `ρ(T)v = e(μ)v`: continuity, `L²`, unfolding (`integral_inner_poincSeries_profile`).
  `HTGeometry/ModularStripLIntegralUnfolding`: `[0,∞]`-valued unfolding with no integrability hypothesis.
- K3b DONE `RHTower/DeckPoincareRowOrbits` + `RHTower/DeckPoincareFourier`:
  reduced rows × ℤ ≃ rows with `c ≠ 0` (`reducedRowShiftEquiv`), `P_{rT^k}(z) = ρ(T^k)⁻¹P_r(T^k z)`;
  `deckCuspCoeff μ v G y = ∫_0^1 e(-μx)⟨v,G(x+iy)⟩dx`; coordinate unfolding
  `∫_𝒟⟨P(·|y^s e(μ·),v),G⟩ = 2∫_0^∞ y^{-2}y^{s̄}e^{-2πμy} deckCuspCoeff μ v G y dy`
  (`integral_inner_poincSeries_eq_deckCuspCoeff`); Fourier coefficient of `P(·|h,w)`
  (`deckCuspCoeff_poincSeries`) = `∫_0^1 e(-μx)h(x+iy)dx·⟨v, w+ρ(-1)⁻¹w⟩ + Σ_{reduced r}∫_ℝ coeffTerm r`,
  each `coeffTerm r` integrable (`integrable_coeffTerm_and_hasSum`).  Rows `±(0,1)` reuse corpus
  `RHTower.rowPlus/rowMinus/first_zero_iff`.  All wired after `DeckPoincareSeries`; axioms standard.
- Route decision for K3c–K3f (no σ→1 limit, no Weil bound needed for (1.20)): pair `U(s₁,μ,v)` with
  `conj U(s₂,ν,w)` = Poincaré series of profile `conj h` and vector `conj w` (no δ-term); geometric side by
  `deckCuspCoeff_poincSeries` + DI Lemma 4.3 at `s₁ = σ+it, s₂ = σ−it`, σ > 1 fixed: `K_{2it}` with
  `γ^{-2σ}`; spectral side: K2 Parseval, `⟨U,u_j⟩` from `deckMode_eq_whittaker` + (3.3), the four Γ's
  `Γ(σ−½±i(t±κ))` = corpus Mellin product `integral_cpow_mul_modifiedBesselKOrder_mul_modifiedBesselKOrder`
  (`∫K_{2it}K_{2iκ}x^{2σ−2}`), the `1/(Γ(σ+it)Γ(σ−it))` cancel exactly; integrate in `t` against
  Kontorovich–Lebedev of `g(x) = φ(x)x^{2−2σ}·const` ⇒ (1.20) for compactly supported `φ`.
- Next: K3c per-row integral `∫_ℝ coeffTerm r` for `h = conj(y^{s₂}e(νz))` (substitution `x ↦ x − d/c`,
  deck Kloosterman weight `e((νa+μd)/c)⟨v,ρ(M_r)⁻¹conj w⟩`, `B(c,y)`), then the `y`-integral (Lemma 4.3).

## Log 2026-10-05 (K3c)
- K3c DONE (all axiom-clean, wired in `RHTower`):
  `RHTower/BesselInverseGaussianComplexRate` (`∫y^{α-1}e^{-Ay-P/(Ay)} = 2P^{α/2}A^{-α}K_α(2√P)`, Re A>0,
  identity theorem from real rates); `RHTower/CauchyBetaIntegral` (`∫(1+iη)^{-a}(1-iη)^{-b} =
  π2^{2-a-b}Γ(a+b-1)/(Γ(a)Γ(b))`, Re a>0, Re b>1, via Fourier multiplication formula + inversion for
  Gamma densities); `RHTower/KuznetsovKernelIntegral` (`kuzKernel`, `kuzValue`, absolute convergence
  with `∫∫|K| ≤ C q^δ`, `integral_integral_kuzKernel` = DI Lemma 4.3 core);
  `RHTower/KuznetsovPoincareRows` (`conjProfile`, regularity of `P(·|h̄_{s,ν},w)`, Möbius row
  coordinates, `rowWeight = ⟨v,ρ(M)⁻¹w⟩e((μd−νa)/c)`, row term = weight·(c²)^{-s̄₂}·kernel, vanishing
  diagonal); `RHTower/KuznetsovPoincarePairing`: `integral_inner_poincSeries_conjProfile`
  `∫_𝒟⟨U(s₁,μ,v), P(h̄_{s₂,ν},w)⟩ = 2Σ_{reduced r} rowWeight·(c²)^{-s̄₂}·kuzValue(s̄₁,s̄₂;μ,ν,c²)`
  for Re s₁, Re s₂ > 1, μ,ν>0, v ∈ e(μ)-eigen, w ∈ e(−ν)-eigen.
- Next: K3d spectral side (K2 Parseval for `U` against `P`, `⟨U,u_j⟩` from Whittaker modes).

## Log 2026-10-05 (K3d, part 1)
- `RHTower/KuznetsovCuspFormPairing`: `deckCuspCoeff_eq_sum_deckMode` (coefficient at a cusp vector
  = `Σ_q conj(v_q)` × level-period Fourier mode, `μ(N+1) ∈ ℤ` forced by `ρ(T)^{N+1}=1`),
  `deckCuspCoeff_eigen_eq_whittaker` (`c·√y K_ν(2π|μ|y)`), `integral_whittaker_mellin`,
  closed forms `integral_inner_poincSeries_eigen` / `..._conjProfile_eigen`
  (`2c(2πμ)^{½−s̄}2^{s̄−3/2}Γ(s̄−½)Γ(s̄−½±ν)/Γ(2s̄−1)`, needs `|Re ν| < Re s − ½`), conjugate-series
  unfolding `integral_inner_poincSeries_conjProfile_eq_deckCuspCoeff`.
- `RHTower/KuznetsovSpectralIdentity`: `kuznetsov_rough` — geometric side (K3c) =
  `Σ_j⟨U,u_j⟩⟨u_j,P⟩ + π⁻¹⟨T̄U,T̄P⟩` (central-fixed, `P ⊥ 𝟙`).  All built, wired, axiom-clean.
- Remaining for K3d: (S-pos) `lam ≥ 0` for cuspidal eigenfunctions (so `|Re ν_j| ≤ ½`; route:
  Green/Dirichlet form, or Schur + sub-mean-value of `y^s`, `s>1`); (S6) identification of `T̄U`, `T̄P`:
  (a) density of `{t ↦ ψ̂(½+it)w}` in `L²(ℝ;V_∞)` (Mellin = Fourier after `y=e^u`; mathlib
  `Lp.fourierTransformₗᵢ` + `C_c^∞` density), (b) range of `T̄` = symmetric subspace via the projection
  `Σ F(t) = ½(F(t)+Φ̃(½−it)F(−t))` (`Φ̃` unitary + adjoint on the line, corpus), (c) `⟨T̄U,T_ψw⟩ =
  π⟨U,E_ψw⟩` (inner_eisSpace, `⟨U,𝟙⟩=0`) = Mellin inversion + contour shift with the Fourier coefficients
  `D_n(s)` of `eisExt` (corpus `EstarExt`, `Estarσ_eq_EstarExt`); growth on `½ ≤ Re s ≤ σ` from
  `norm_Dn_le` + corpus `norm_LFunction_lower_log_strip` (`1/L(1+it,χ) ≪ log⁷|t|`).
- (S-pos) DONE `RHTower/DeckCuspEigenvalueNonneg`: `cuspEigenBasis_lam_nonneg` (Schur `‖L_k‖ ≤ 1` vs
  `h_k(s) = ∫k(u(i,w))(Im w)^s > 1` for real `s > 1`: strict Bernoulli + mean value of the harmonic `Im`).
- (S6) route fixed (no functional equation, no range characterization): for every generator,
  `⟨T̄U, T_ψw⟩ = π⟨U, E_ψw⟩` (inner_eisSpace, `⟨U,𝟙⟩ = 0`); `⟨U,E_ψw⟩ = π⁻¹∫ψ̂(σ+it)⟨U,Ẽ(σ+it;w)⟩dt`
  (1<σ<Re s₁, Fubini); `⟨U, eisExt(s;w)⟩ = 2c_μ(s)·Mellin–Whittaker(s̄₁, s−½)` by a generalized unfolding
  (integrable majorant instead of `L²`), `c_μ(s)` read off the corpus Fourier expansion of `eisExt`
  (`termX`, `D_n(s)`); contour shift to `Re s = ½` (holomorphic, no pole for `μ ≠ 0`; growth
  `|D_n| ≪ log⁹|t|`); then `∫ψ̂(½+it)⟨2T̄U(t) − H(t), w⟩dt = 0` for all `ψ, w` and density of
  `{ψ̂(½+i·)}` in `L²(ℝ)` give `2T̄U = Π_{V∞}H`.  Steps S6.1 generalized unfolding, S6.2 `c_μ(s)`,
  S6.3 Fubini, S6.4 growth + shift, S6.5 density, S6.6 the conjugate series.

## Log 2026-10-06 (S6 closed, explicit s-parameter identity)
- S6 DONE: `RHTower/KuznetsovEisensteinTransform` — generic `eisTransformL2_inner_of_line` (⟂𝟙 + line
  pairing on one line ½<σ<Re s₁ ⇒ `2⟨T̄F(t),w⟩ = Φ(½+it)` a.e.), via `inner_eisTransformL2_incEisL2`
  (Parseval on the Eisenstein space), `inner_symSpace_eisTransform` (symmetry), contour shift, test
  density; corollaries `eisTransformL2_poinc_inner` (U) and `eisTransformL2_conj_inner` (P: pairing at
  `(s̄₂, ν)`, frequency `−ν(N+1)`).  `DeckPoincareMajorantUnfolding` generalized
  (`inner_toDeckL2_incEisL2_eq_integral_line` for any field under the Poincaré majorant; conjugate
  unfolding of moderate-growth fields); `KuznetsovEisensteinCoefficient`:
  `integral_inner_poincSeries_conjProfile_eisVec`, `inner_conjL2_incEisL2_eq_integral_pairing`.
- `RHTower/KuznetsovExplicitIdentity`: `cuspVecSub`, ONB `cuspBasisVec` of `V_∞`,
  `inner_eisTransformL2_poinc_conj` (`⟨T̄U,T̄P⟩ = ¼∫Σ_iΦ^U_iΦ̄^P_i`), `whittMellin`, `specParam`
  (`ν_j² = ¼−λ_j`, `|Re ν_j| ≤ ½`), `cuspRep`, `cuspCoeff` (Whittaker coefficient ρ_j(v)),
  **`kuznetsov_explicit`**: geometric(a₁,a₂) = 4(2πμ)^{½−a₁}(2πν)^{½−a₂}[Σ_jρ_j(v)ρ̄_j(w)W(a₁,ν_j)W(a₂,ν_j)
  + (4π)⁻¹∫Σ_iη_i(v)η̄_i(w)W(a₁,it)W(a₂,it)dt].  All built, wired, axiom-clean.
- K3e plan (KL route, worked out on paper): at a₁=σ+it, a₂=σ−it the factors (ν/μ)^{it} cancel; the
  Mellin product (corpus `integral_cpow_mul_modifiedBesselKOrder_mul_modifiedBesselKOrder`) + duplication
  give `W(σ+it,ν)W(σ−it,ν) = π2^{5−4σ}Γ(2σ−1)/(Γ(σ+it)Γ(σ−it))·∫K_{2it}K_{2ν}x^{2σ−2}`, so
  `Σ_r w_r c^{−2σ}K_{2it}(X/c) = 4X^{1−2σ}[Σ_jρρ̄∫K_{2it}K_{2ν_j}x^{2σ−2} + cont]`, X = 4π√(μν).
  Integrate against `H(t) = (8/π²)t sinh(2πt)G(2t)`, G = KL transform of `X^{2σ−1}x^{−2σ}φ`:
  `Σ_r w_r c⁻¹φ(X/c) = 4Σ_jρ_j(v)ρ̄_j(w)φ̌(ν_j) + π⁻¹∫Σ_iη_iη̄_iφ̌(ir)dr`, `φ̌(ν) = ∫K_{2ν}φ dx/x`.
  Interchanges: geometric side by `|K_{iτ}(x)| ≪ (|log x|+log(2+τ))e^{−πτ/2}`; spectral side by
  Parseval at s = σ∓it (‖U(σ+it)‖ ≤ C(σ) uniformly in t) + Tonelli — no a-priori Weyl law needed.
  KL inversion proof (no Taubes-type input): `2cosh(αy)g(y) = 𝓕A_α`, `y sinh(αy)K_x(iy) = (i/2)𝓕D_α`
  (contour shift of the Schläfli integral, `Real.fourier_deriv`), multiplication formula + Fourier
  inversion give `∫y sinh(2αy)K_x(iy)g(y)dy = iπ∫A_αD_α`; α→π/2 by DCT (`|F(v±iα)| ≪ cosh⁻²v` from
  two integrations by parts) gives `π²x f(x)` via `ξ = sinh v` and cosine inversion.  KL decay
  `y⁴g(y) = KL[M²f]` from the corpus Bessel ODE.
- Note: same-sign Kuznetsov (large sieve, DI Thm 2) needs the U–U pairing (J-Bessel, DI Lemma 4.1) —
  separate milestone after K3e/K3f.

## Log 2026-10-06 (K3e/K3f DONE: Kuznetsov (1.20) in Lean)
- `RHTower/KontorovichLebedevTransform`: uniform `‖K_x(iτ)‖ ≤ e²(|log x|+log(2+|τ|)+3)e^{−π|τ|/2}`;
  `IsKLTest` (C^∞, compact support in (0,∞)); `klTransform`; `KL[Mf] = −y²KL[f]` from the Bessel ODE;
  decay `‖KL f(y)‖ ≤ C(log(2+|y|)+1)e^{−π|y|/2}/(1+y^{2m})`.
- `RHTower/KontorovichLebedevInversion`: **`kontorovichLebedev_inversion`**
  `∫_ℝ y sinh(πy)K_{iy}(x)g(y)dy = π²x f(x)` (Fourier route: shifted Schläfli lines, multiplication
  formula + Fourier inversion, α→π/2 by DCT on both sides, ξ = sinh v, cosine inversion).
- `RHTower/KuznetsovBesselIdentity`: `whittMellin_eq` (duplication), `whittMellin_mul_line`
  (`W(σ+it,ν)W(σ−it,ν) = π2^{5−4σ}Γ(2σ−1)M(t,ν)/(Γ(σ+it)Γ(σ−it))`), `kuzValue_line`,
  **`kuznetsov_bessel`** (pointwise identity in K_{2it}).
- `RHTower/KuznetsovUniformBounds`: `‖U_s‖,‖P_s‖ ≤ ‖v‖‖A_{Re s}‖₂`, Bessel/Parseval
  (`‖T̄f‖² ≤ π‖f‖²`), uniform line bounds for Σ_j|ρρ||W|² and ∫Σ_i|ηη||W|².
- `RHTower/KuznetsovKLWeight`: weight `H(t) = (4/π²)t sinh(2πt)g(2t)`, `∫H K_{2it}(x) = x f(x)`,
  `Γ(2+it)Γ(2−it) = (1+t²)πt/sinh(πt)`, `|HΓΓ| ≪ (1+t²)⁻¹`, `|H K_{2it}(x)| ≪ (|log x|+1)(1+t²)⁻¹`,
  joint continuity of `K_ν(x)`, Fubini `∫H M(t,ν)dt = ∫x²K_{2ν}x f`.
- `RHTower/KuznetsovOppositeSign`: countability of the cuspidal eigenbasis (separable L²),
  three interchanges (row sum, discrete spectrum, Eisenstein integral) and
  **`kuznetsov_opposite_sign`**: `Σ_r w(c,d)|c|⁻¹φ(4π√(μν)/|c|) = 4Σ_jρ_j(v)ρ̄_j(w)φ̌(ν_j)
  + π⁻¹∫Σ_iη_i(v,r)η̄_i(w,r)φ̌(ir)dr`, `φ̌(ν) = ∫K_{2ν}(x)φ(x)dx/x`, all smooth compactly supported
  φ on (0,∞).  All built, wired, axiom-clean.
- Next: K3g same-sign pairing ⟨U(s₁,μ,v),U(s₂,ν,w)⟩ (J-Bessel, DI Lemma 4.1) for the large sieve;
  Γ₀(q)/Kloosterman specialization of `rowWeight`; then K5 (DI §7 Bessel-transform bounds, Thm 2).

## Log 2026-10-06 (K3g DONE: same-sign Kuznetsov, DI (4.8)/(5.5) at σ = 1 in Lean)
- `RHTower/KuznetsovSameSignRows`: rows of `P(·|h_{s₂,ν}, w)`: `M(x+iy) = a/c − 1/(c²y(ξ+i))`, same-sign
  kernel `K⁺ = (1+ξ²)^{−a₂} y^{a₁−a₂−1} e^{−2πμ(1+iξ)y − 2πν/(c²(1−iξ)y)}`, `|K⁺| = |K|`,
  row weight `⟨v,ρ(M)⁻¹w⟩ e((μd+νa)/c)`, diagonal `[μ=ν] y^s e^{−2πνy}⟨v, w+ρ(−1)⁻¹w⟩`.
- `KuznetsovSameSignPairing`: `∫⟨U(s₁,μ,v),U(s₂,ν,w)⟩ = 2[μ=ν](4πμ)^{1−s̄₁−s₂}Γ(s̄₁+s₂−1)⟨…⟩ + 2Σ_r …V⁺`.
- `KuznetsovSameSignIdentity`: Parseval with explicit spectral side (`kuznetsov_same_sign_explicit`).
- `KuznetsovSameSignLine`: `y = λeʷ` gives `V⁺(σ+it,σ−it) = (ν/(μq))^{it} Ξ_σ(t,X)`,
  `Ξ_σ = ∫(1+ξ²)^{−σ}∫e^{2itw}e^{−Xζ(ξ)cosh w}dw dξ`, `ζ = e^{i arctan ξ}` — no Bessel function needed.
- `KuznetsovGaussianWeight`: `∫t²e^{−(t/K)²}e^{2itw}dt = (√πK³/2)(1−2K²w²)e^{−K²w²} = 𝒢_K'(w)`.
- `KuznetsovSameSignGaussKernel`: `∫g_KΞ_σ = Ψ_σ` (Fubini + one IBP), `|Ψ_σ(X)| ≤ πX∫|𝒢 sinh|`,
  `Ψ_σ → Ψ_1` as σ↓1, **`Ψ_1(X) = 2∫𝒢_K(w) tanh w sin(X cosh w)dw` (DI (5.6))** via
  `∫(1+ξ²)⁻¹ζe^{−bζ}dξ = 2 sin b/b`.
- `KuznetsovSameSignGaussIdentity` + `KuznetsovSameSignBessel`: `F_t = Σ_k b_k(2πμ_k)^{−it}U(σ−it,μ_k,v_k)`,
  phases cancel: `‖F_t‖² = Σ b̄_k b_l(2diag + 2R_{kl}(t))`; Bessel; t-integration; σ↓1 by Fatou (spectral)
  + Tannery (geometric): **`lintegral_bessel_le_one`**:
  `Σ_j ∫ g_K(t)·4|W(1+it,ν_j)|²|A_j|² dt ≤ Re Σ_{k,l} b̄_k b_l [2 diag ∫g_K + 2Σ_{(c,d)} w⁺ c^{−2} Ψ_1(4π√(μν)/|c|)]`,
  `A_j = Σ_k b̄_k ρ_j(v_k)(2πμ_k)^{−½}`.  No analytic continuation of Poincaré series needed.
- Next (K5): lower bound `∫g_K|W(1+it,iκ)|² ≫ (|κ|+1)e^{−π|κ|}` (|κ| ≤ K) and exceptional ν; Eisenstein
  part of Bessel (continuous large sieve); Γ₀(q) Kloosterman specialization of `Σ_d w⁺`; Prop 3; Thm 2.
- K5 (spectral half of DI Thm 2) DONE: `RHTower/KuznetsovSpectralWeightLower` (`|W(1+it,ν)|²` via four Γ-moduli;
  reflection bound `|Γ(½+ν+it)Γ(½−ν+it)| ≥ π/cosh πt` for real ν; `∫g_K·4|W(1+it,iκ)|² ≥ c₀(κ+1)e^{−πκ}`,
  `c₀ = (π²/4)e^{−9−2π}`, all `λ ≤ ¼+K²` incl. exceptional) and `RHTower/KuznetsovSameSignParseval`
  (Parseval for `F_t`, Eisenstein coefficients `2W(σ+it,ir)B_i(σ,r)`, Fatou on ℝ² as σ↓1):
  **`large_sieve_full`**: `Σ_j c₀(κ_j+1)e^{−πκ_j}[λ_j≤¼+K²]|A_j|² + (4π)⁻¹∫_{−K}^{K}c₀(|r|+1)e^{−π|r|}Σ_i|B_i(r)|²dr
  ≤ |Σ_{k,l} b̄_k b_l geomRow_{kl}(1,K)|` for every finite family of cusp vectors/frequencies.
- Next: arithmetic side — Γ₀(Q) vector `1_H` (H = Γ₀(Q)/Γ(N+1)), `Σ_d rowWeightPlus = |H|·S(m,n;|c|)[Q|c]`,
  DI Prop 3 (1.25)–(1.27), §5.3 case split ⇒ Thm 2 `≪ (K² + μ N^{1+ε})‖a‖²`.
- Γ₀(Q) cusp ∞ specialization DONE: `RHTower/KuznetsovGammaZeroCusp` (`1_H`, `H = Γ₀(Q)/Γ(N+1)`, `Q ∣ N+1`;
  `⟨1_H, ρ(M)⁻¹1_H⟩ = |H|[Q∣c]`), `RHTower/KuznetsovRowKloosterman` (rows of modulus c ≃ (ℤ/|c|)ˣ;
  `Σ_d e((md+na)/c) = S(m,n;|c|)`; `tsum_rowExp_mul`), `RHTower/KuznetsovGammaZeroGeom`
  (**`geomRow_gamma0`**: `geomRow(1,K;m,n;1_H,1_H) = 4|H|[m=n](4πm)⁻¹∫g_K + 2|H|Σ_{c≠0}S(m,n;|c|)[Q∣c]c⁻²Ψ_1(4π√(mn)/|c|)`).
- Remaining for Thm 2 (plan): with α_m = a_m√m, `Φ(c) = 4π∫𝒢 tanh·Im B(cosh w, c)`, `B(θ,c) = Σ ᾱ_mα_n S e(2θ√mn/c)`;
  c > N²: trivial `|S| ≤ c` + `|Ψ_1(X)| ≪ X`; N < c ≤ N²: (1.26') `|B| ≪ (c + N + |θ|N)‖α‖²` from the corpus hybrid
  Farey sieve (`sum_integral_normSq_additiveHybridLogPoly_le_length`) + Fourier separation of `e(2θ√mn/c)` in
  `log m + log n` (|ĝ| ≤ ‖g‖₁, ≤ ‖g''‖₁/(2πt)², dyadic shells); c ≤ N: (5.7) form + (1.27) (Poisson, Ramanujan sums,
  first-derivative test) for ξ ≤ 1, (1.26') with e^{−K²} for ξ ≥ 1.

## Log 2026-10-06 (DI Theorem 2 DONE in Lean, Γ₀(Q) at ∞, deck normalization)
- `RHTower/KuznetsovKernelOscillatory` (DI (5.7) + weight bounds), `KuznetsovSqrtSeparation` (Fourier
  separation of `e(A√(mn))` with `∫|ĝ| ≤ C(1 + |A|e^{a/2})`), `KuznetsovKloostermanSieve` (single-modulus
  additive large sieve; **(1.26)**: `|B(θ,c)| ≤ C(1 + |θ|N/c)(N + c)Σ|α|²`).
- `KuznetsovQuadraticPhase` (iterated IBP for `e(Ξ(s² − τs))`, closed form `G_k = Σ b_{k,i}a^{(i)}x^{−(2k−i)}`,
  `|∫ a e(Ξ(s²−τs))| ≤ C_p|Ξ|^{−p}` uniformly in `|τ| ≤ κ < 2α`), `KuznetsovSqrtPhasePoisson` (Poisson for
  `Σ η(√(n/N))e(zn + B√n)` with the substitution `t = Nσ²`; error `C_p N(c/N)^p`; resonant term
  `≤ min(3N, D√N/|B|)`), `KuznetsovKloostermanSmallModulus` (**(1.27)**: CS + opening the square + Poisson +
  Ramanujan sums via corpus `cglRamanujanAdditiveSum_eq_gcd_mobiusDivisorSum_sieve` + divisor kernel row sums:
  `|B|² ≤ C(Σ|α|²)²(cNτ(c)(1+log N) + c²N²(c/N)^p)`), `KuznetsovKloostermanPhaseEnvelope` (`|B| ≤ C_δ√cN^{1/2+δ}Σ|α|²`
  for `c ≤ N`, `1 ≤ |θ| ≤ 2`; envelope along `θ = ±cosh w`), `KuznetsovGaussianTails`
  (`∫|𝒢_K|T_K ≤ 4√πeKe^{−K²/2}`, `∫|R_K|T_K ≤ (10π+4√π)eK²e^{−K²/2}`, `∫|𝒢_K sinh| ≤ 2πe`),
  `KuznetsovGeomModulusBound` (DI (5.6), (5.7) as integral identities for `Φ(c)`; three bounds per modulus),
  `KuznetsovGammaZeroModulusSum` (per-modulus `c^{−2}|Φ(c)| ≤ (PKN^{1+2δ}c^{−1−δ/2} + P₃K²e^{−K²/2}(N²c^{−2}+N³c^{−3}))Σ|a|²`
  via min(5.6, 5.7) for `c ≤ N`, min(1.26, trivial) for `c > N`), `KuznetsovGammaZeroGeomBound`
  (`Σ_{Q∣c}|c|^{−s} = Q^{−s}Z_s`), `KuznetsovLargeSieveGammaZero` (geomForm bound; `specCoeff = Σ a_n ρ_j(n)`;
  **`large_sieve_gamma0_level`**), `KuznetsovLargeSieveTheorem` (K₁ = K + √(6 log(1+N/Q)) trick:
  `𝓛_K ≤ C|H|(K³ + KN^{1+3δ}/Q)Σ|a|²`; dyadic summation `sieveDILHS_le`; **`large_sieve_gamma0`**:
  `Σ_{λ_j≤¼+K²}e^{−πκ_j}|Σa_nρ_j(n)|² + (4π)⁻¹∫_{−K}^{K}e^{−π|r|}Σ_i|Σa_nη_i(r,n)|² ≤ C_ε|H|(K² + N^{1+ε}/Q)Σ|a_n|²`).
  All built, audited (0 non-standard axioms), wired into `RHTower.lean`.
- Next: DI Theorems 5–9 (exceptional eigenvalues weighted large sieve; bilinear Kloosterman forms with smooth
  weights via Kuznetsov (1.20) + Thm 2), then Watt / twisted fourth moment inputs for the route-e cards.

## Roadmap 2026-10-06 (after DI Theorem 2): DI §7–9, Watt, twisted fourth moments
Sources now in hand: DI Invent. §7–9 (scans p288–p311), DI Acta Arith 43 (1984) 305–312 (free scan
`matwbn.icm.edu.pl/ksiazki/aa/aa43/aa4339.pdf`: template for mean values `∫|L M N|²` via off-diagonal
`lb = l₁b₁ + h` → Poisson mod c → `e(−hk ā/c)` → DI Thm 12), BCR arXiv:1411.7764 Prop. 3 (Watt's bound
derived from Watt Prop. 4.1: sums `Σ α(h)β(c)ω(ℓ)a_r b_s S(hcr, ∓ℓ; sp) f_s(p)`).  Watt (JNT 53) and DI
Mathematika 29 are not accessible (paywall/bot wall): Watt Prop 4.1 is a refinement of DI Thm 16 for
`a_{r,s} = a_r b_s`, to be reconstructed.
Dependency chain: E1 ⇐ DI-[2]-type mean value (two smooth variables, Poisson in both) ⇐ DI Thm 16 ⇐ Thm 12
⇐ Thm 11 ⇐ Thms 2, 5, 6/7 at cusps ∞ and 1/s of Γ₀(rs) ⇐ Kuznetsov (1.19)/(1.20) at (∞, 1/s) + Thm 8.
E2 ⇐ Watt Prop 4.1 (same tools).
Key structural facts fixed on paper:
- Same-sign Maass kernels are `x·Ψ^G(x)`, `Ψ^G(x) = 2∫G(w) tanh w sin(x cosh w) dw`, G odd; spectral weight
  `H_G(ν) = ∫h_G(t)W(1+it,ν)W(1−it,ν)dt`, `h_G(t) = π⁻¹∫G'(w)e^{−2itw}dw`; exact at σ = 1 by DCT with the
  proven large sieve as dominating bound (no Bessel J needed).
- `x sin(bx)` (b>1) is ⊥ every `J_l` (l odd) in `L²(dx/x)`; DI's decomposition `φ = Σ_{l odd}2lφ̃(l)J_l + φ_H`
  has `φ_H = x·Ψ^{G_φ}`, `G_φ(w) = (cosh w/4)[∫φ(y)sin(y cosh w)dy/y − 2Σ_lφ̃(l)sin(lπ/2)e^{−lw}]` (w>0, odd
  extension smooth by Jacobi–Anger at θ = π/2+iw).  Inputs: sine transform of `J_l(y)/y` (=`sin(l arcsin u)/l`,
  u<1; `sin(lπ/2)(u−√(u²−1))^l/l`, u>1).  `G_φ(±∞) = ∓φ̃(1)/4 ≠ 0`: the geometric sums converge absolutely
  only via Weil (corpus `kmaxU_summable`); same for the weight-2 (J₁) holomorphic part.
- Holomorphic part needed only through Gram positivity of weight-k deck Poincaré series with Hecke
  parameter s>0 (k even ≥ 2): `|Σā b G_𝔞𝔟| ≤ √(G_𝔞𝔞(a))√(G_𝔟𝔟(b))`, geometric sides with `J_{k−1}` kernels
  in the limit s→0 — no spectral theory of S_k.  Cross-cusp (∞,1/s) cannot be done geometrically (loses √r).
- Exceptional amplification `X^{−2ν}` appears from the slow decay `e^{−(1−2ν)w}` of the Fourier transform of
  `sinh(πt)/(t(cosh²πt − sin²πν))` against `G_φ`.
Build order: (P1) general-weight same-sign identity at σ=1; (P2) `J_l` (integer order), Jacobi–Anger,
DI decomposition; (P3) weight-k deck Poincaré Gram; (P4) spectral-weight bounds (Lemma 7.1, `φ̌` and `H_G`);
(P5) Thm 8 at (∞,∞) then (∞,1/s); (P6) Thms 5–7; (P7) Thms 9–13, 16; (P8) mean values E1; (P9) Watt; (P10) AFE,
MT Lemma 3.5, MT Thm 1.2, cards.

## Log 2026-10-06 (P1 DONE: exact same-sign Kuznetsov at σ = 1 for rapid weights)
- `RHTower/KuznetsovSameSignWeightKernel`: `SameSignWeight` (h, G, G' with `∫h(t)e^{2itw}dt = G'(w)`, `|G|e^{|w|}`
  integrable); `∫h Ξ_σ(t,X)dt = Ψ_σ^G(X)`, `|Ψ_σ^G(X)| ≤ πX∫|G sinh|`, `Ψ_σ^G → Ψ_1^G`,
  **`weightKernel_one`**: `Ψ_1^G(X) = 2∫G(w) tanh w sin(X cosh w) dw`.
- `KuznetsovSameSignWeightSigma`: bilinear families `F_t, G_t`; `⟨F_t,G_t⟩` geometric (`inner_famL2_famL2`) and
  spectral (`inner_famL2_eq_spectral`, Eisenstein part `inner_eisTransformL2_famL2`); interchange lemmas
  `integral_mul_tsum_of_bound`, `integral_mul_integral_of_bound`; **`kuznetsov_same_sign_weight_sigma`** (σ > 1).
- `KuznetsovWhittakerStripBounds`: `Γ`, `1/Γ` strip bounds for all heights; `|W(σ+it, ir)|² ≤ D(1+|t|)^L(1+|r|)^L
  e^{−π(2max(|t|,|r|)−|t|)}` and the exceptional bound with `t⁻²`, uniformly in `1 ≤ σ ≤ 2`.
- `KuznetsovSameSignSpecWeightBounds`: rapid weights (`|h(t)|(1+|t|)^A ≤ C_A t²`); `|∫h|W(σ+it,ν)|²|(1+κ)^B ≤ C_B e^{−πκ}`.
- `KuznetsovLargeSieveSummability`: from `large_sieve_full`, `Σ_j|ρ_j(v)|²e^{−πκ_j}(1+κ_j)^{−4} < ∞` and the Eisenstein analog.
- `KuznetsovSameSignWeightLimit`: Tannery + DCT ⇒ **`kuznetsov_same_sign_weight`**:
  `Σ b̄_k b'_l [2diag∫h + 2Σ_{(c,d)} w⁺c^{−2}Ψ_1^G(X_c)] = 4Σ_j A_jĀ'_j ∫h|W(1+it,ν_j)|² + π⁻¹∫Σ_iB_iB̄'_i∫h|W(1+it,ir)|²`.
  All built, audited (0 non-standard axioms), wired.  No Bessel J, no spectral gap, no Weil bound used.
- Remaining for DI (1.19) with compactly supported φ: (P1') the non-rapid component (`G(±∞) = ∓φ̃(1)/4`, `h(0) ≠ 0`):
  needs Selberg 3/16 on the deck eigenbasis (exceptional weights `~ 1/(½−ν)`) and the Weil bound (`kmaxU_summable`)
  for `Σ_c |S|c^{−2}`; (P2) `J_l`, Jacobi–Anger, sine transform of `J_l(y)/y`, decomposition `φ = φ_B + xΨ^{G_φ}`;
  (P3) weight-k Gram positivity for the `J_l` part; (P4) bounds for `∫h_φ|W|²` in terms of `φ` (Lemma 7.1).

## Log 2026-10-06 (P2 DONE: J_l, Jacobi–Anger, DI decomposition for φ̃(1) = 0)
- `HTGeometry/BesselJGeneratingFunction`: `|J_l(x)| ≤ |x/2|^l/l!·e^{(x/2)²}`, integer-order `J_l` and the generating
  function `Σ_l J_l t^l = exp((x/2)(t − t⁻¹))`; **Jacobi–Anger** `sin(x sin θ) = 2Σ_k J_{2k+1}(x) sin((2k+1)θ)` (θ ∈ ℂ);
  `J_{2k+1}(x) = (2/π)∫_0^{π/2} sin((2k+1)θ) sin(x sin θ) dθ`.
- `HTGeometry/BesselJContourIdentity`: contour shift `∫_0^{π/2} cos(lθ + x sin θ) = sin(lπ/2)∫_0^∞ e^{−lw}cos(x cosh w)`;
  **sine profile** (odd l ≥ 3): `∫_0^{π/2} sin(lθ) sin(x sin θ) cos θ + sin(lπ/2)∫_0^∞ e^{−lw} sinh w sin(x cosh w) = (πl/2) J_l(x)/x`.
- `HTGeometry/CoshSchwartzSpan`: span `𝒜_c` of `cosh^a sinh^b χ(c cosh)` (χ Schwartz), closed under d/dw, smooth,
  super-exponential decay of all derivatives.  `HTGeometry/ExponentialSeriesSmooth`: termwise-smooth `Σ d_k e^{−m_k w}`.
- `HTGeometry/BesselTestFunctionSineTransform`: `BesselTestFunction` (smooth, support in [a,b], a > 0); `φ̃(l)` bounds;
  `S(sin θ) = 2Σφ̃(2k+1) sin((2k+1)θ)`, `S(cosh w) = P(e^w) + P(e^{−w})`; odd extension Schwartz with
  `𝓕χ(ξ) = −2iS(2πξ)`; **sine inversion** `∫_0^∞ S(u) sin(Xu) du = (π/2)φ(X)/X` (mathlib Fourier inversion).
- `RHTower/KuznetsovSameSignWeightOfOdd`: `OddDecayProfile` (odd smooth `G`, `|G^{(n)}| ≤ C_n e^{−2|w|}`) ↦ `SameSignWeight`
  with `h(t) = π⁻¹𝓕(G')(t/π)` (Fourier inversion gives `fourier_h`) and **IsRapid** (`∫G' = ∫wG' = 0` ⇒ `h = O(t²)`).
- `RHTower/KuznetsovBesselTestFunctionWeight`: for `φ̃(1) = 0`, `G_φ = (cosh/4)S(cosh) − (cosh/2)P(e^{−w})`
  `= (cosh/4)(P(e^w) − P(e^{−w}))` is an `OddDecayProfile`; **`besselWeight`**, `besselWeight_isRapid`.
- `RHTower/KuznetsovBesselTestFunctionKernel`: **`weightKernel_besselWeight`**: for X > 0,
  `Ψ^{G_φ}(X) = (π/2)φ(X)/X − Σ_{k≥0} 2φ̃(2k+3)(π(2k+3)/2)J_{2k+3}(X)/X`, i.e. `φ = (2X/π)Ψ^{G_φ} + Σ_{l≥3} 2lφ̃(l)J_l`.
  All 8 modules built, audited (0 non-standard axioms), wired.
- The `φ̃(1)` (weight-2) component is removed without spectral theory of weight 2: for the Kloosterman side
  `Σ_{c ≥ c₀} S(m,n;c)c⁻¹φ(4π√mn/c)` a fixed `Φ₁` supported in `(4π√mn/c₀, ∞)` contributes nothing, and
  `φ − (φ̃(1)/Φ̃₁(1))Φ₁` has vanishing first coefficient; its spectral weights are bounded in P4.

## Log 2026-10-06 (P4 core DONE: exact sech-kernel form of the same-sign weights)
- `HTGeometry/SechComplexFourierTransform`: logistic substitution at complex frequency,
  `∫(cosh t)^{−s}e^{−izt}dt = 2^{s−1}Γ((s−iz)/2)Γ((s+iz)/2)/Γ(s)` (`|Im z| < s`); `∫e^{−izt}/cosh t = π/cosh(πz/2)`.
- `RHTower/KuznetsovSpecWeightSech`: exact `t W(1+it,ν)W(1−it,ν) = π² sinh πt/(cos 2πν + cosh 2πt)` (reflection);
  kernel `k_ν(w) = (π/sin πν) sinh(2νw)/cosh w` (`k_0 = 2w/cosh w`) with `∫k_ν e^{2itw} = 2i·(that)`;
  **`specWeight_eq_integral_sechKernel`**: `∫h(t)|W(1+it,ν)|²dt = ∫G(w)k_ν(w)dw` (Fubini + Fourier inversion, no
  Stirling).  Bounds: `norm_specWeight_real_le` (`≤ π∫|G||w|cosh(2νw)/cosh w`, exceptional amplification explicit),
  `norm_specWeight_imag_le` (`≤ 2∫|G||w|/cosh w`), `norm_specWeight_imag_le_of_iteratedDeriv`
  (`≤ (π/|sinh πκ|)‖(G/cosh)^{(K)}‖₁/|2κ|^K`).  Built, audited, wired.  (A first version via contour shift + crude
  Stirling was discarded: it loses powers of `X`.)
- Next (P4c): bounds for `Q_φ = G_φ/cosh = S(cosh w)/4 − P(e^{−w})/2` in terms of the scale of `φ`:
  `|S(u)| ≤ min(u‖φ‖₁, ‖(φ/y)'‖₁/u)`, `|P(e^{−w})| ≤ e^{−3w}Σ_{l≥3}|φ̃(l)|`, and (large scale)
  `P(e^{−w}) = (2/π)∫_0^{π/2}S(sin θ)·Im[1/(2cosh(w−iθ))]dθ ⇒ |P(e^{−w})| ≤ ‖(φ/y)'‖₁ min(π/4, 1/(2 sinh w))`;
  then DI Lemma 7.1 analogues: exceptional `≪ X^{−2ν}log`, tempered `≪ (1+|log X|)` resp. `1/X`.

## Log 2026-10-06 (P4c DONE: weight bounds in terms of φ)
- `HTGeometry/BesselTestFunctionTailBound`: `|S(u)| ≤ |u|‖φ‖₁`, `|S(u)| ≤ ‖(φ/y)'‖₁/|u|`;
  `φ̃(2k+1) = (2/π)∫_0^{π/2} sin((2k+1)θ)S(sin θ)`; Poisson-type sum `Σ(−1)^k x^{2k+1}sin((2k+1)θ) =
  x(1−x²)sin θ/(1+2x²cos 2θ+x⁴)`; hence `|P(x)| ≤ ‖(φ/y)'‖₁ x/(1−x²)`, `|P(e^{−w})| ≤ ‖(φ/y)'‖₁/(2 sinh w)`.
- `RHTower/KuznetsovBesselWeightBounds`: `Q_φ = G_φ/cosh = S(cosh w)/4 − P(e^{−w})/2` (`besselProfile_div_cosh`);
  `|P(x)| ≤ x³Σ_{l≥3}|φ̃(l)|` on [0,1]; small/mid/large-scale bounds `norm_profileQ_le_small/mid/large`;
  **`norm_specWeight_besselWeight_real_le`** (`0 ≤ ν < ½`): `|∫h|W|²| ≤ 2π∫_0^∞|Q|·w cosh(2νw)`;
  **`norm_specWeight_besselWeight_imag_le`**: `≤ 4∫_0^∞|Q|·w`.  Built, audited (0 non-standard axioms), wired.
- Remaining for P4: integrate the majorants against the scale `X` of `φ` (split at `w₀ = log(1/X)`) and κ-decay
  via `norm_specWeight_imag_le_of_iteratedDeriv` (derivatives of `Q`); deferred until P7 fixes the exact form needed.

## Log 2026-10-09 (ownership)
- Taken over by session hgt-52, after hgt-8a and hgt-38 confirmed nobody else is on the card.  The goal is
  the two route-E leftovers cards.
- The upper branch is delegated to hgt-61: the reflection `√T < N ≤ T` of MT Lemma 3.5 via the
  partial-sum approximate functional equation.  New module
  `Sieve/MatomakiTeravainenWattReflection` (`MTDeshouillersIwaniecBoundShort → MTDeshouillersIwaniecBound`,
  `MTWattBoundShort → MTWattBound`, short = `N² ≤ T`).
- hgt-52 continues the lower half: P3–P9 (holomorphic part of (1.19), DI §7 weights, Theorems 5–12,
  Watt), then the short-block twisted fourth moments.
- P4d (DI Lemma 7.1 analogue: integrate the P4c majorants; exceptional bound with tail
  `e^{−(1−2ν)w₀}`, tempered bound, κ-decay through `norm_specWeight_imag_le_of_iteratedDeriv`)
  delegated to hgt-8a.  New module `RHTower/KuznetsovBesselWeightScaleBounds`.
- P4d DONE (hgt-8a): `RHTower/KuznetsovBesselWeightScaleBounds`.
  - Data: `besselMassA`, `besselSlopeD`, `besselTailSigma`, `besselMomentA`, `besselTailConst`.
  - `norm_specWeight_besselWeight_real_le_scale`: the exceptional bound, split at `w₀`, with tail
    `(1+w₀)e^{−(1−2ν)w₀}/(1−2ν)²`.
  - `norm_specWeight_besselWeight_imag_le_scale`: the tempered bound.
  - `norm_specWeight_besselWeight_imag_le_decay`: `π‖Q^{(K)}‖₁/(|sinh πκ||2κ|^K)`.
  - `besselTailSigma_le`: `Σ ≤ (A + A₁)/4`, where `A₁ = ∫|y||φ|`.
  - Moment corollaries `_real_le_moments` and `_imag_le_moments`.
  - The Σ bound uses `A₁`: on a support `[X, 2X]` we have `A₁ ≤ 2X·A`.
