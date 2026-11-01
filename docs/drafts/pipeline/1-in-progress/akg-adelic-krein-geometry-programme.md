# Adelic Krein Geometry (AKG) programme

- **ID:** akg
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-3010/obstacles-summary.md §2.6
- **Statement:** Indefinite (finite negative index) harmonic analysis on `Aff(ℚ)` and its adelic completion: index calculus, zero-or-infinity laws, Pontryagin extensions of Weil's correlation, local–global signature calculus, conformal symmetry.

## Goal
Develop the field asked for in §2.6: answer its six questions as theorems or sharp no-gos with positive survivors, build its tools in Lean under `formal/GaloisForLFunctions/AdelicKreinGeometry/`.

## Gates
- [x] 0 → 1  README; objects and questions fixed
- [x] 1 → 2  paper proofs of pillars A–E and of the Q3 extension (below)
- [ ] 2 → 3  all programme theorems formalized (open topics remain)

## Status (formalized; each module checked with `lake --old env lean`, wired into `AdelicKreinGeometry.lean`)
- A. Index calculus: `TheIndexOfAnInducedState`, `TheWitnessComplementIsPositive`, `MixingKillsNegativeSquares`, `TheIndexIsTwinBlind`.
- B. Affine zero-or-infinity law and Kakutani index wall: `HeckeSupportedStatesHaveIndexZeroOrInfinity`; the wall is local, `TheIndexWallIsLocal` (local Hecke states `p^{−s|v_p a|}·1[v_p b ≥ min(0, v_p a)]` have index `0` for `s ≥ 1/2` and `∞` below at every prime; product formula `φ_s = ∏_ℓ φ_{ℓ,s}`; global positivity as a Schur product of local positivity; axioms: propext, choice, Quot.sound); `TheIndexWallOverAFunctionField` (the same wall for the local Hecke state at `∞` of `𝔽_q(X)`, `q^{−s|deg a|}·1[deg b ≤ max(0, deg a)]`; axioms: propext, choice, Quot.sound).
- C. Weil's affine extensions: `ThePontryaginExtensionsOfWeilsCorrelation`, `TheAdelicProductState`, `ArchimedeanContinuityAgainstHeightDecay`, `WeilsCorrelationWithAnArchimedeanSuccessor` (positive survivor: `κ(K_ζ) ≤ κ ≤ κ(K_ζ) + 1` with successor `−c|b|`), `TheArchimedeanGluingFormula` (`κ = κ^{(½)}(K) + 1`; `κ^{(½)} = κ` for sub-boost data), `WeilsArchimedeanStateCountsTheZeros` (`κ(weilArchState) = #rightZeros + 1`; every tempered configuration without zeros on `Re ρ = 0`; primitive Dirichlet `L(s, χ)`; axioms: propext, choice, Quot.sound), `PrimeTowersGlueAtFullIndex` (`κ(k ∘ v_p glued) = κ(k) + 1`), `TheGluingSquareIsSharp` (`κ(K) ≤ κ(glued) ≤ κ(K) + 1`, both attained; the pole pair is absorbed, `κ^{(½)}(polePair) = 0`; the glued index is blind to the pole pair at any strength), `TheGlueSeesTheOrderOfThePole` (double pole `log u·(u^{1/2} − u^{−1/2})`: `κ^{(½)} = 1`, glued index `2` against `1` for a simple pole), `TheStableGluingFormula` (`κ(K(|a|) − c|a|^{−s/2}|b|^s) = κ^{(s/2)}(K) + 1` for `0 < s < 1`; absorbed pair `u^{±s/2}`; tempered configurations with `Re ρ > (1−s)/2` give `κ(K_Z) + 1`; a drop for `ζ` certifies a zero with `Re ρ ≤ (1−s)/2`; axioms: propext, choice, Quot.sound), `TheGlueAbsorbsExactlyItsOwnPair` (`κ(u^{±s'/2} glued at s) = 1` iff `s' = s`, else `2`; at `s = 1` only the pole pair is absorbed), `TheTwoReadingsAdd` (the translation reading `K(1) − c|b|` has one square for every Hermitian `K`; `κ(Φ) = κ^{(½)}(K) + κ(Φ|_+)`; for Weil's state `κ = κ(Φ|_×) + κ(Φ|_+)`), `ASignatureFormulaForPrimeTowers` (`Σ_{p∈S} κ₀(k_p) + 1 ≤ κ(glued tower assembly) ≤ Σ_{p∈S} κ₀(k_p) + 2`; tower coordinates surjective, a prime outside `S` frees the boost hyperplane), `TheGluingFormulaAtEveryPlace` (`κ(K(|a|) + |a|_v^{−s/2}ψ(b)) = κ_v(K) + 1` for every place `v` and gluing successor; Weil's correlation glued at any prime: `κ = #rightZeros + 1`, also for primitive Dirichlet `L(s, χ)`; axioms: propext, choice, Quot.sound), `TheArchimedeanWeilFormIsAShellIdentity` (on `ℓ = 0` the archimedean Weil form is Weil's dilation form plus half-line shell squares); `Haar/OneNegativeSquare` (another agent).
- D. Signature calculus: `TheSignatureOfASeparableAssembly`, `NoFixedCountertermMakesThePrimeKernelPontryagin`, `TowerCoupling/PolarSecondDifference` (`κ₀(k) = κ(Δ²k)`, `{0, 1, ⊤}` polar trichotomy), `TowerCoupling/STruncatedExplicitTowers` (no separable `S`-truncated explicit-formula tower formula for `κ(K_ζ) + 1`: finite `κ₀ ∈ {0, 1}` counts only pole shares; pole-retaining spline assemblies diverge `≥ |S| + 1 → ⊤`; pole-free assemblies lie in `{1, 2, ⊤}` whereas `κ(weilArchState c) ≠ 2`; diagonal counterterms collapse `Λ` and `primeFlipWeight q` to `1`), `TowerCoupling/InterTowerCouplingRigidity` (`coupledAssembly S K = axialAssembly S K + interTowerCoupling S K`; `coprimeCrossDiff` rigidity on `⟨2, 3⟩ × ⟨5, 7⟩` blocks pointwise convergence of separable `towerAssembly` nets to `ratCorr`; `axialAssembly S ratCorr` blows up to `⊤` on `0 < κ(K_ζ) < ⊤`), `TowerCoupling/CoupledTowerSignatureFormula` (`κ(archGlue(coupledAssembly S ratCorr, c)) = κ(K_ζ) + 1` for `|S| ≥ 2` and primitive Dirichlet `L(s, χ)`; fixed-`S` `sTruncatedCorr S` has `κ ∈ {1, ⊤}`, while `S ⊇ windowPrimes L` gives `gram (archGlue (sTruncatedCorr S) c) g = gram (weilArchState c) g` on `|log |slope|| ≤ L` with zero counterterm and `⨆_L = κ(K_ζ) + 1`; axioms: propext, choice, Quot.sound). [A6 finite sieve is formalized](../3-formalized/matched-prime-form-hodge-index-uniform-in-the-sieve.md), with a horizon independent of the sieve; transfer of uniform sieve positivity to `interTowerCoupling` remains open.
- E. Conformal symmetry: `ConformalSymmetryNeedsANegativeSquare`, `StableConformalSuccessors`, `TheFunctionFieldConformalSuccessor`.
- F. Additive index law: `TheAdditiveIndexLaw` (`ℤ/N`), `TheAdditiveIndexLawOnQModZ` (`ℚ/ℤ`), `TheRamanujanIndexLaw` (`κ = Σ_{A_d<0} φ(d)` for unit-invariant kernels and conductor-invariant successors).
- G. One state, two actions: `ThePoleIsAKreinStateOfTheAffineGroup`, `TheAffineGroupOfAField`, `TheHeckeBoostAndTheConformalSuccessorAreOneState` (conformal induction, pole–successor law for any field and absolute value), `EveryPlaceCarriesAPoleSuccessorState` (ultrametric successors, `p`-adic states, the place at infinity of `F(X)`), `ThePoleSuccessorSignatureFormula` (`κ = κ₀(ψ) + 1`), `TheShellDecompositionOfAPoleSuccessorForm` (renormalized pair plus shell squares, at `p` and at `∞`), `LocalSignaturesAddOverDistinctPlaces` (`κ = k` for `k` separated places).
- H. Haar carriers: `Haar/IndexPreservation`, `Haar/ContinuousDilationsNeedInfiniteIndex`, `Haar/AxisInvisibility`, `Haar/PolynomialPerturbations`, `Haar/FiniteRankPerturbations`, `Haar/PowerKernels`, `Haar/MixedPolynomialPerturbation`. `Haar/PolynomialCorrection`, `Haar/CyclicGramLimit`, `Haar/FiniteIndexObstruction`, and `Haar/ScaledHaarObstruction` prove infinite index for every Hermitian rational-affine kernel with a nonzero integer-Haar multiple and continuous dilation reading; positive-slope and actual adelic extensions remain unverified.

## Open
- The unique decomposition of finite-index Haar kernels into positive Haar, slope, and zero-axis polynomial parts.
- Krein–Langer structure on `Aff(ℚ)`: positive part plus finite-dimensional or conformally induced Pontryagin coefficients?
- Transfer of uniform finite-sieve Hodge positivity to the non-separable inter-tower coupling form `interTowerCoupling S ratCorr` (separable prime-tower assemblies are ruled out and replaced by `coupledAssembly` and window-coupled `sTruncatedCorr` in `TowerCoupling/`).
- Calibration over `𝔽_q(T)`: local walls at places of higher degree and the global product (the place `∞` is done).
- Q5 additive carrier of the collision charge; Q6 shell sum-of-squares for the complete Weil form.

## Paper proofs

**Witness complement / escape.** κ(k) = m < ∞ attained on x; a vector on y orthogonal to every witness point with negative form adds one square to an m-dimensional negative subspace on x ⊔ y. Translates into the complement have the same Gram matrix.

**Hecke escape.** For x_a⁻¹ t_{1/P} y_b with P prime above all denominators, d(β + 1/P)/α ∈ ℤ forces P ∣ d·den α·den β.

**Weil's extensions.** Restriction lowers κ; the slope pullback is surjective; APD `isPosDefOnGroup_heckeState_iff`, `riemannHypothesis_iff_exists_affine_posDef`, `splineCorr_zero_of_integer_successor`.

**Q3 beyond Hecke support.**
- Near coincidence: F continuous at 1, ψ → 0 with the denominator, ψ(1) > 0. Points u_i = (K+i)/K have ratios ≠ 1 within L/K of 1, so denominators ≥ K/L. On Σc = 0 the Gram of F − ψ is ≤ −ψ(1)|c|² + 2εL|c|²: L − 1 negative squares.
- Dilution: for Hecke-supported ψ, spread β over t_{j/P}·dil(u_k) with weight 1/P; off-diagonal j ≠ j' terms of ψ vanish, so the compressed Gram is gram(s) + gram(ψ_D)/P; lower semicontinuity gives κ(s) ≤ κ(s∘slope + ψ).
- Combination: a positive Hecke-supported ψ with the integer successor decays, (nd)|ψ(dil u)|² ≤ 1; a continuous dilation part s + ψ_D forces κ(s) = ∞.

**Running counterterm.** D·δ₁ − P on ℚ_{>0} escapes by t = PQ (both new primes in every numerator, so no prime power); the truncated pole vector has P_N-energy ≥ (log N − γ − η)·mass > D·mass for large N.

**Pole–successor law.** Vectors `k_t`, `k_∞` with `[k_s,k_t] = ψ(t−s)`, `[k_∞,k_t] = 1`, `[k_∞,k_∞] = 0`; `g = (a,b)` acts by `k_t ↦ |a|^{−s/2}k_{at+b}`, `k_∞ ↦ |a|^{s/2}k_∞`, isometric iff `ψ(ub) = |u|^sψ(b)`. With `w_g = |a_g|^{s/2}k_∞ + |a_g|^{−s/2}k_{b_g}`, the Gram form at weights `c` is `2Re(X̄Y) + Σ c̄_g c_h |a_g a_h|^{−s/2} ψ(b_h − b_g)`, `X = Σ c_g|a_g|^{−s/2}`, `Y = Σ c_g|a_g|^{s/2}`. On `X = 0` the second term is the polar form of `ψ` at weights `c_g|a_g|^{−s/2}` (mass `X`), so `κ ≤ 1`; the dilations `1, D_u` with `|u|_v > 1` give `4 − 2(t + 1/t) < 0`.

**Ultrametric successors.** For nonarchimedean `v`, `{|z|_v ≤ r}` is a subgroup, so `1[|x−y|_v ≤ r]` is an equivalence kernel. With `R ≥` all `|x_b − x_a|_v`: `−|z| = (R − |z|) − R = ∫_0^R 1[|z| ≤ r] dr − R`; on `Σc = 0` the constant drops and the form is an integral of equivalence forms.

**Signature formula `κ = κ₀(ψ) + 1`.** Upper: `κ ≤ ν(ker X) + 1` and on `ker X` the form is `ψ`'s polar form at weights `w/α`. Lower: polar negative `W` (dim `r`) on translations `τ_i` and dilations `u^N, u^{N+1}`; compress by `S = diag(basis of W, I₂)`: the `W`-block is `ψ`'s form on `W`, the pair block is constant with one negative square, the cross blocks are `α_{N+e}^{−1}·const` since `Σ_i w_i = 0` kills the boost part; lower semicontinuity gives `r + 1`.

**Archimedean gluing `κ(K(|a|) − c|a|^{−1/2}|b|) = κ^{(½)}(K) + 1`.** Gram form `= Q_K(w; |a|) + Q_ψ(w|a|^{−1/2}; b)`; the mass of the second weights is `ℓ(w) = Σ w|a|^{−1/2}`. Upper: on `ℓ = 0`, `Q_ψ ≥ 0`. Lower: `W ⊂ ker ℓ` negative for `K` on dilations `u_i` (shift 0) and the pair `1, x ↦ x + L` with weights `L^{−1/2}`: `K`-cross terms `O(L^{−1/2})`, `ψ`-cross terms `ψ(±L)·ℓ(w) = 0`, pair form `(4K(1) − 2cL)/L → −2c`.

**Sub-boost criterion.** Dilate a negative family `F` by `λ_N` and add the slope `1` with weight `−λ_N^{−1/2}ℓ_F(c)`: the result lies on `ℓ = 0`; the compressed Gram entries are `K(F_i⁻¹F_j) − μρ_i K(λF_j) − μρ_j conj K(λF_i) + μ²ρ_iρ_j K(1)`, `μ = λ_N^{−1/2}`, which tend to `gram K F` when `K(λ_N u)μ → 0`.

**The gluing square is sharp.** Dilation reading of the glued state is `K`, so `κ(K) ≤ κ(glued)`; `κ^{(½)} ≤ κ` gives `κ(glued) ≤ κ(K) + 1`. The pole pair at slopes `u_i` has form `2Re(ℓ̄m)`, `m = Σ w u^{1/2}`, zero on `ℓ = 0`; so `κ^{(½)}(K + t·polePair) = κ^{(½)}(K)` and the glued pole pair is the pole–successor state, index `1 = κ(polePair)`.

**Double pole.** `D(u_a⁻¹u_b) = (t_b − t_a)(e_a⁻¹e_b − e_ae_b⁻¹)`, `t = log u`, `e = u^{1/2}`; the form is `2Re(ℓ̄M) − 2Re(L̄₁L₂)` with `M = Σ w t e`, `L₁ = Σ w t e⁻¹`, `L₂ = Σ w e`. On `ℓ = 0`: `Q + |L₁ + L₂|² = |L₁|² + |L₂|² ≥ 0`, so at most one square; slopes `1, 4`, weights `−1/2, 1`: `ℓ = 0`, `Q = −(3/2) log 4`.

**Local wall.** Common denominator `g_i = (A_ix + C_i)/D`: the local Haar state of `g_i⁻¹g_j` is the commensurability kernel of `C_i + p^{v_p A_i}ℤ` (APD `commKernel_gram`); `p^{−s|v|} = p^{−|v|/2}·(p^{−(s−1/2)})^{|v|}` (Poisson multiplier). Escape: translation by `p^{−M}` makes `v_p(shift) = −M − v_p(α)`, below `min(0, v_p(slope))`. Below `1/2`: dilation `1/p` with weight `−p^{1−s}` and translations `j/p`, `j < p`, weight `1`: form `p − p²p^{−2s} < 0`. Product formula: `nd = ∏ ℓ^{|v_ℓ a|}` and `db ∈ ℤ ⟺ ∀ℓ, v_ℓ(b) ≥ min(0, v_ℓ a)` (`v_ℓ(d) = −min(0, v_ℓ a)` by coprimality).

**Stable gluing.** Same compression as at `s = 1` with `σ_L = L^{−s/2}`: pair block `4K(1)L^{−s} − 2cL^{s}L^{−s} → −2c`; upper bound from `hermQuad_gram_negPowRat_nonneg` on `ℓ_s = 0`. Sub-boost: `‖term‖ = e^{−N log 2 (Re ρ − (1−s)/2) − a(Re ρ − 1/2)}‖w_ρ‖ ≤ e^{|a|/2}‖w_ρ‖`, Tannery.

**Wall at `∞` of `𝔽_q(X)`.** Clear denominators by a common polynomial: the local Haar state of `g_i⁻¹g_j` is the overlap of `C_i + F[X]_{≤ deg A_i}`; on coefficient vectors of length `N + 1` the coset is a cylinder of size `q^{d+1}`, two cylinders `d ≤ d'` meet in the smaller one iff `deg(C' − C) ≤ d'`. Escape by `X^M`; negativity from dilation `X` and translations `cX`.

**Exact absorption.** At slopes `1, 4, 16` the functionals `ℓ_s, A = Σ w u^{−s'/2}, B = Σ w u^{s'/2}` are the rows of the Vandermonde matrix in `4^{−s/2}, 4^{−s'/2}, 4^{s'/2}`, distinct iff `s ≠ s'`; solve `ℓ_s = 0, A = 1, B = −1`: form `2Re(ĀB) = −2`.

**Tower signature.** `u ↦ (v_p u)_{p∈S}` is onto `ℤ^S` (`∏ p^{e_p}`), so `κ(K) = κ(separable k)`; a prime `q ∉ S` fixes every `v_p`, so `K` is `q`-periodic and `κ(glued) = κ(K) + 1`; the separable formula gives `Σκ₀ ≤ κ(K) ≤ Σκ₀ + 1`.

**Every place.** Same compression with the pair `1, x ↦ x + u₀^N`, `|u₀|_v > 1`, weights `|u₀^N|_v^{−s/2}`; `ψ(u₀^N) = |u₀^N|_v^s ψ(1)` and `ψ(−L) = conj ψ(L)`, pair block `→ 2Re ψ(1)`. At `p`: slopes `p^{−N}`, `|p^{−N}|_p^{−1/2} = p^{−N/2}`, term modulus `e^{−N log p (1 − Re ρ) − a(Re ρ − 1/2)}`, Tannery.

**Weil's correlation is sub-boost.** `ratCorr(u) = Σ_ρ e^{−(log u)(ρ−1/2)} w_ρ`, `Σ‖w_ρ‖ < ∞` (tempered, spline `C²` compact). At `u = 2^N v` times `2^{−N/2}` the term has modulus `e^{−N log 2·Re ρ − log v (Re ρ − 1/2)}‖w_ρ‖ ≤ e^{|log v|/2}‖w_ρ‖` and tends to `0` since `Re ρ > 0`; Tannery's theorem gives `→ 0`.

**Tower coupling vs. separable explicit-formula towers.** Summation by parts via `diffMap M` on contiguous grids gives `κ₀(k) = κ(Δ²k)`. For finite `S`, `Σ_{n≥2} |Λ_S(n)|/√n < ∞` and Riemann–Lebesgue give `Δ²g_p^{(S)}(n) → 0` for all counterterms `C + D·δ₁ + A·negAbsKernel`, so `κ₀(k_p^{(S)}) ∈ {0, 1, ⊤}` counts only local pole shares when finite; separable `towerAssembly` kernels annihilate `coprimeCrossDiff` on `⟨2, 3⟩ × ⟨5, 7⟩`, which by Kronecker density forces continuous limits to be affine in `log u` (`κ, κ₊ ≤ 2`). Conversely, `coupledAssembly S ratCorr = ratCorr ∘ projS S` (`|S| ≥ 2`) embeds `twoPrimeLattice` and fixes a prime outside `S`, giving `κ(glued) = κ(K_ζ) + 1`; and for `S ⊇ windowPrimes L` (`p ≤ ⌊e^{2L+8}⌋₊`), `splineCorr_prime_term_eq_zero` gives `gram (archGlue (sTruncatedCorr S) c) g = gram (weilArchState c) g` on `|log |slope|| ≤ L` with zero counterterm.
