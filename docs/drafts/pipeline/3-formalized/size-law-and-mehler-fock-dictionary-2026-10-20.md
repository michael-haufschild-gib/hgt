# The size law (`S(T)` unbounded) and the Mehler–Fock / Bochner–Godement dictionary

- **ID:** size-law-mehler-fock-2026-10-20
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) ×2
- **Source:** walls ledger, Wall 14 (paper item CANNOT-549) and Wall 13 (producer loop row 241)
- **Statement:** (A) `S(T) = N(T) − M(T)` is unbounded. (B) A continuous compactly supported
  point-pair kernel `k(u(z,w))` on `ℍ` is positive definite iff its Mehler–Fock (Selberg) transform
  is nonnegative on the critical line iff its Abel transform lies in the Bochner cone.

## Goal
Remove the two paper-only items of the walls ledger. (A) excludes finite-rank prime modifications of
the archimedean reference (bounded spectral shift); the corpus has only non-integrability. (B) is the
dictionary behind the cone-mismatch wall: the Bochner cone `{Ĝ ≥ 0}` on `ℝ` is identified, through
the Abel transform, with positive-definite zonal kernels on `ℍ`.

## Gates
- [x] 0 → 1  in-progress: both statements well-posed, unconditional, proof architectures below
- [x] 1 → 2  fully-proven: paper proofs complete (below)
- [x] 2 → 3  formalized: Lean theorems, `lake env lean` clean, axioms standard, umbrellas wired
- [ ] 3 → 4  not pursued (no stage 4)

## (A) Paper proof: `S(T)` is unbounded

Notation. `Φ(u) = bump(u)` (smooth, even, `0 ≤ Φ ≤ 1`, support `[−1,1]`), `Φ_ℓ(u) = Φ(u/ℓ)`
(`cb ℓ 0`), `K = Φ_ℓ ⋆ Φ_ℓ` (`EF.weilTest`), `ψ(y) = |Φ̂_ℓ(y)|² = K̂(y)` (`psi ℓ 0`),
`X = e^{2ℓ}`, `N = ⌊X⌋`. For a height `T` put `ξ = −T/2π`, so `S_ξ Φ_ℓ` is the window at `T`.

1. **Explicit formula** (SRT `zetaZeroConfig_W_heightShift_eq_sub`, Zeta23 EF, unconditional):
   `Σ_ρ m_ρ K̂(γ_ρ − T) = A(T) − Π(T)` with `A(T) = pole(T) + ∫ ψ(τ − T) μ(τ) dτ` and
   `Π(T) = primePolynomial Φ_ℓ N ξ`.
2. **Off-line correction.** For `ρ = ½ + δ + it`: `Re K̂(t − T − iδ) − ψ(t − T) = Re ĝ_δ(t − T)`
   with `g_δ = K·(cosh(δ·) − 1)` (the `sinh` part is odd, its transform imaginary). Writing
   `cosh(δu) − 1 = ∫_0^δ (δ − s) u² cosh(su) ds` and integrating `u²K` by parts four times gives
   `|·| ≤ 8 δ² e^{2ℓ|δ|} Q_ℓ (1 + |t − T|)^{−4}`, `Q_ℓ = ‖u²K‖₁ + ‖(u²K)⁗‖₁`.
3. **Zero sums.** Local count `N(t, t+1) ≤ A₀ log(|t|+3)` gives
   `Σ_ρ m (1+|Im ρ − T|)^{−2} ≤ C log(T+3)` and the far part `≤ C log(T+3)/W`.
4. **Good heights.** Threshold `v = (log U)^{−2/3}`, radius `W = (log U)²`. Zeros of depth `≥ v`
   in `(U/4, U/2)` number `o(U/W)` (`exists_windowZeros_count_le`), so heights within `W` of one
   have measure `o(U)`. At a good height `T ∈ [U/4, U/2]`:
   `|Corr(T)| ≤ C_ℓ(v² log U + log U/W) → 0`.
5. **Abel summation.** On `[1, 2T]`, integration by parts against `dS = dN − M' dt` gives the
   exact identity `Σ_{1<γ≤2T} m ψ(γ − T) − ∫_1^{2T} ψ(t − T) M'(t) dt = ψ(T)S(2T) − ψ(1 − T)S(1)
   − ∫_1^{2T} S(t) ψ'(t − T) dt`. The zeros outside `(1, 2T]`, the pole terms, the boundary terms
   (`S = O(log t)`) and `∫ψ(τ − T)(μ − M')` (Stirling) are `o(1)`. Hence, for all `T → ∞`,
   `Re Π(T) = ∫_1^{2T} S(t) ψ'(t − T) dt − Corr(T) + o(1)`.
6. **Bounded `S` caps `Π`.** If `|S| ≤ B` on `[1, ∞)` then `Re Π(T) ≤ B‖ψ'‖₁ + |Corr(T)| + o(1)`,
   with `‖ψ_ℓ'‖₁ = ℓ²‖ψ_1'‖₁` (scaling `ψ_ℓ(y) = ℓ²ψ_1(ℓy)`).
7. **Kronecker.** `Re Π(T) = Σ_{n ≤ e^{2ℓ}} a_n cos(T log n)`, `a_n = 2Λ(n)n^{−1/2}K(log n) ≥ 0`, is
   `F(p^{−iT})` for the continuous `F(ω) = Σ a_n Re ω_p^k` (`n = p^k`) on the prime torus. For
   `G < F(1)` the Kronecker–Weyl law applied to `min(1, (F − G)⁺)` gives measure `≥ cU` of heights in
   `[U/4, U/2]` with `Re Π > G`, which beats the bad set of step 4 (taken with `ε = c/2`).
8. **Growth.** `K(x) ≥ (ℓ/2)ϑ(7/16)²` for `|x| ≤ ℓ/2`, so `F(1) ≥ ℓϑ² Σ_{n≤e^{ℓ/2}} Λ(n)/√n
   ≥ ℓϑ² e^{ℓ/4}` for large `ℓ` (`Σ_{n≤x} Λ(n)/√n ~ 2√x`). Choose `ℓ` with
   `F(1) > Bℓ²‖ψ_1'‖₁ + 2`: contradiction.

**Lean (complete, unconditional, standard axioms):** `rvmRemainder_unbounded` and
`not_isBoundedUnder_abs_rvmRemainder` (`SquareRootThreshold/ZetaZeroCountRemainderIsUnbounded`).
Ingredients: `RHTower/ImaginaryShiftQuadraticFourierDefect` (step 2),
`RHTower/BumpAutocorrelationWindowKernel` (kernel, scaling, lower bound),
`SquareRootThreshold/ZetaWindowPrimePolynomialStieltjesIdentity` (steps 1, 5 exact identity),
`SquareRootThreshold/ZetaWindowPrimePolynomialReadsZeroCountRemainder` (step 5 limits),
`SquareRootThreshold/ZetaOffLineCorrectionSmallOutsideSparseHeights` (steps 3–4),
`SquareRootThreshold/ZetaWindowPrimePolynomialOnThePrimeTorus` (steps 7–8).

## (B) Paper proof: the Mehler–Fock / Bochner–Godement dictionary

Objects: continuous profile `k` with `KernelSupport k R`; kernel `k(u(z,w))`; Selberg transform
`h_k(s) = ∫_ℍ k(u(i,w)) (Im w)^s dμ(w)` (corpus `selbergTransform`); Abel transform
`𝒜k(v) = ∫_ℝ k(η²/4 + sinh²(v/2)) dη` (even, continuous, compact support).

1. **Horocyclic slice.** `∫_ℝ k(u(x+iy, x'+iy')) dx = √(yy') 𝒜k(log y − log y')`
   (substitute `x − x' = √(yy') η`).
2. **Mehler–Fock = Fourier ∘ Abel.** `h_k(½ + iτ) = ∫ 𝒜k(v) e^{iτv} dv` (slice at `w = i`).
PD means `Q_k(g) = ∫∫ k(u(z,w)) g(z) ḡ(w) dμ dμ ≥ 0` for every continuous compactly supported
`g`; the Bochner cone means `∫∫ q(a − b) f(a) f̄(b) da db ≥ 0` for every such `f` on `ℝ`.

3. **Necessity** (PD ⟹ Bochner ⟹ `h ≥ 0`). Test `g(z) = φ_X(x) β(y)` with `φ_X` the trapezoid
   (`1` on `[−X, X]`, `0` off `[−X−1, X+1]`). By the slice, `Q_k(g)/(2X) →
   ∫∫ √(yy') 𝒜k(log y − log y') β(y) β̄(y') dy dy'/(y²y'²)`; with `y = e^a`, `B(a) = β(e^a)e^{−a/2}`
   this is `∫∫ 𝒜k(a − b) B(a) B̄(b)`, `B` arbitrary in `C_c(ℝ)`. Fejér: `f = e^{iτa} 1_{[0,L]}`
   (trapezoid-smoothed) and `L → ∞` give `∫ 𝒜k(v) e^{iτv} dv ≥ 0`.
4. **Horocyclic Fourier decomposition.** For `g` whose zero extension to `ℂ` is smooth, with
   `G(ξ, y) = ∫ g(x + iy) e^{−2πixξ} dx` and the fibre kernel
   `K_ξ(y, y') = ∫ k((t² + (y − y')²)/(4yy')) e^{−2πitξ} dt`, the point-pair kernel on two
   horocycles is the convolution kernel `κ(x − x')` with `κ̂ = K_ξ`; Fourier inversion of the second
   slice and Fubini give `∫∫ κ(x − x') a(x) b̄(x') = ∫ K_ξ â(ξ) b̂(ξ)‾ dξ`. `y ↦ G(ξ, y)` is smooth
   (a parametric average after rescaling to `[0, 1]`) with support in the `y`-range of `g`, and
   `|G(ξ, y)|(1 + 2π|ξ|) ≤ D` uniformly (one integration by parts in `x`). Hence
   `Q_k(g) = ∫_ξ B_ξ(G(ξ, ·)) dξ`, `B_ξ(G) = ∫∫ K_ξ(y, y') G(y) Ḡ(y') dy dy'/(y²y'²)`.
5. **Whittaker eigenfunctions.** `E(x + iy) = e^{2πiξx} W_τ(y)`, `W_τ(y) = √y K_{iτ}(2π|ξ|y)`, is
   `C²` with `−y²ΔE = (¼ + τ²) E` (Bessel's equation). Selberg's theorem
   (`integral_pairKernel_mul_eigen`) and integration in `x` give the fibre eigen-relation
   `∫ K_ξ(y, y') W_τ(y') dy'/y'² = h(½ + iτ) W_τ(y)`.
6. **Kontorovich–Lebedev.** For `ξ ≠ 0` and `G ∈ C_c^∞(0, ∞)`, KL inversion (corpus,
   `kontorovichLebedev_inversion`, applied to `f(t) = G(t/k) t^{−3/2}`, `k = 2π|ξ|`) gives
   `π² G(y) = ∫ τ sinh(πτ) ⟨G, W_τ⟩ W_τ(y) dτ`, `⟨G, W⟩ = ∫ G W dy/y²`. With 5 and Fubini
   (bounds: `|K_{iτ}(x)| ≪ (|log x| + log(2+|τ|)) e^{−π|τ|/2}`, KL transforms of test functions
   `≪ e^{−π|τ|/2}/(1+τ^{2m})`): `B_ξ(G) = π^{−2} ∫ τ sinh(πτ) h(½ + iτ) |⟨G, W_τ⟩|² dτ ≥ 0`.
7. **Sufficiency.** Smooth the zero extension of `g` on `ℂ` by bumps of radius
   `ε_n ≤ min(δ_n, a/2, 1)` (`δ_n` a modulus of uniform continuity for `1/(n+1)`): the approximants
   `g_n` have smooth zero extensions, vanish off one compact `K ⊂ ℍ`, and `|g_n − g| ≤ 1/(n+1)`.
   With `|k| ≤ M`, `|g| ≤ C`: `|Q_k(g_n) − Q_k(g)| ≤ μ(K)² M (2C + 1)/(n + 1)`. So 4–6 give
   `Q_k(g) ≥ 0` whenever `Re h(½ + iτ) ≥ 0` for all real `τ`.

Chain: PD ⟹ (3) Bochner cone ⟹ (3, Fejér) `h ≥ 0` on the critical line ⟹ (7) PD.

**Lean (complete, unconditional, standard axioms):**
`isPositiveDefinitePointPair_iff_re_selbergTransform_nonneg` and
`isPositiveDefinitePointPair_iff_isBochnerPositive` (`RHTower/HyperbolicPointPairMehlerFockDictionary`,
which also holds step 7: `exists_contDiff_approximation`, `tendsto_pointPairForm`). Ingredients:
`RHTower/HyperbolicAbelTransformHorocyclicSlice` (steps 1–2),
`RHTower/HyperbolicPointPairFormHorocyclicCoordinates` (`Q_k` in chart coordinates),
`RHTower/BochnerConeFejerTrapezoidWindows` and `RHTower/HyperbolicPointPairPositiveDefiniteNecessity`
(step 3), `RHTower/HorocyclicWhittakerEigenfunctionFibreRelation` (step 5),
`RHTower/HorocyclicFibreKontorovichLebedevPositivity` (step 6: `horocyclicFibreForm_eq`,
`re_horocyclicFibreForm_nonneg`), `RHTower/HorocyclicSlicePointPairParseval` and
`RHTower/HyperbolicPointPairFormHorocyclicFibreDecomposition` (step 4:
`pointPairForm_eq_integral_horocyclicFibreForm`, `re_pointPairForm_nonneg_of_contDiff`).

## Log
- 2026-10-20 — created; corpus survey done (Zeta23 EF/RvM/Stirling, SRT localized form and
  Kronecker realization, prime-flow density, zero-density window count; ℍ point-pair invariant,
  SL(2,ℝ)-invariant measure, Selberg's theorem). Building (A) first.
- 2026-10-20 — (A) formalized: 7 modules, olean built single-threaded, `lake env lean` audit clean,
  `#print axioms` = propext/choice/Quot.sound, wired (2 in `RHTower.lean`, 5 in
  `SquareRootThreshold.lean`); walls ledger Wall 14 updated. Starting (B).
- 2026-10-21 — (B) steps 1–3 in Lean (oleans built, not yet wired): `HyperbolicAbelTransformHorocyclicSlice`
  (chart, Abel transform, slice, Mehler–Fock = Fourier∘Abel, critical line real),
  `HyperbolicPointPairFormHorocyclicCoordinates` (Q_k in coordinates), `BochnerConeFejerTrapezoidWindows`
  (Fejér windows, Bochner cone ⟹ cosine transform ≥ 0), `HyperbolicPointPairPositiveDefiniteNecessity`
  (`isBochnerPositive_abelTransform`, `selbergTransform_critical_re_nonneg`). Next: steps 4–7.
- 2026-10-21 — (B) formalized: steps 4–7 in 5 further modules; all 9 (B) modules audited with
  `lake --old env lean`, axioms propext/choice/Quot.sound, no umbrella name collisions (ilean scan),
  wired in `RHTower.lean`; walls ledger Wall 13 and review-2010 reports updated. Card → 3-formalized.
