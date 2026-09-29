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
