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
- B. Affine zero-or-infinity law and Kakutani index wall: `HeckeSupportedStatesHaveIndexZeroOrInfinity`.
- C. Weil's affine extensions: `ThePontryaginExtensionsOfWeilsCorrelation`, `TheAdelicProductState`, `ArchimedeanContinuityAgainstHeightDecay`, `WeilsCorrelationWithAnArchimedeanSuccessor` (positive survivor: `κ(K_ζ) ≤ κ ≤ κ(K_ζ) + 1` with successor `−c|b|`), `TheArchimedeanGluingFormula` (`κ = κ^{(½)}(K) + 1`); `Haar/OneNegativeSquare` (another agent).
- D. Signature calculus: `TheSignatureOfASeparableAssembly`, `NoFixedCountertermMakesThePrimeKernelPontryagin`. [A6 finite sieve is formalized](../3-formalized/matched-prime-form-hodge-index-uniform-in-the-sieve.md), with a horizon independent of the sieve; transfer to the complete Weil form remains open.
- E. Conformal symmetry: `ConformalSymmetryNeedsANegativeSquare`, `StableConformalSuccessors`, `TheFunctionFieldConformalSuccessor`.
- F. Additive index law: `TheAdditiveIndexLaw` (`ℤ/N`), `TheAdditiveIndexLawOnQModZ` (`ℚ/ℤ`), `TheRamanujanIndexLaw` (`κ = Σ_{A_d<0} φ(d)` for unit-invariant kernels and conductor-invariant successors).
- G. One state, two actions: `ThePoleIsAKreinStateOfTheAffineGroup`, `TheAffineGroupOfAField`, `TheHeckeBoostAndTheConformalSuccessorAreOneState` (conformal induction, pole–successor law for any field and absolute value), `EveryPlaceCarriesAPoleSuccessorState` (ultrametric successors, `p`-adic states, the place at infinity of `F(X)`), `ThePoleSuccessorSignatureFormula` (`κ = κ₀(ψ) + 1`), `TheShellDecompositionOfAPoleSuccessorForm` (renormalized pair plus shell squares, at `p` and at `∞`), `LocalSignaturesAddOverDistinctPlaces` (`κ = k` for `k` separated places).
- H. Haar carriers (another agent): `Haar/IndexPreservation`, `Haar/ContinuousDilationsNeedInfiniteIndex`, `Haar/AxisInvisibility`, `Haar/PolynomialPerturbations`, `Haar/FiniteRankPerturbations`, `Haar/PowerKernels`, `Haar/MixedPolynomialPerturbation`.

## Open
- General indefinite Mautner theorem: negative parts of infinite rank modulo slope data.
- Krein–Langer structure on `Aff(ℚ)`: positive part plus finite-dimensional or conformally induced Pontryagin coefficients?
- Weil's prime and archimedean parts glued to successors as the pole is glued to `−|b|`; non-separable gluing for the complete Weil form; whether `κ^{(½)}(K_ζ) = κ(K_ζ)`.
- Calibration over `𝔽_q(T)`: the Hecke wall on `Aff(𝔽_q(T))`.
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
