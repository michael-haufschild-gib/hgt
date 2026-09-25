# GL(3) automorphic foundations for the Selberg programme

- **ID:** GL3-FOUNDATIONS
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — infrastructure programme driven by open research targets
- **Source:** Selberg conjecturing loop, cycles 61–70 (`selberg-quarter-conjecturing-loop.md`); user directive 2026-09-25 "build GL(3) theory first".
- **Statement:** Build, unconditionally in Lean, the GL(3) automorphic theory that every route past 3/16 needs: the space h³ with its SL₃ action, Fourier–Whittaker expansions, Maass forms for SL₃(Z) and congruence subgroups, GL(3) Kloosterman sums (the w₅ ↔ Kl₃ identification), Poincaré series and the hyper-Kloosterman Kuznetsov formula. Then use them for the Sym² probe of exceptional GL(2) forms.

## Goal
Cycles 56–69 show that every route past Selberg's 3/16 runs through GL(3) or higher:
- the Luo–Rudnick–Sarnak bound 0.21 via the Gelbart–Jacquet lift Sym²;
- the Sym² probe through Buttcane's hyper-Kloosterman Kuznetsov formula, which sees Sym²(exceptional) at congruence level with weight C^{6ν};
- the level-one H_η(3) problem (Kl₃ moduli cancellation), the model case of the Kl₁₅ route that would beat Kim–Sarnak.

Neither mathlib nor the corpus has any GL(3) automorphic theory (corpus search 2026-09-25: only `HyperKloostermanRootNumber`).

## Research targets this infrastructure serves
1. **H_η(3) at level one** (new if proved): power saving in Σ_c Kl₃(m;c)c⁻¹f(c/C). Paper reduction: Buttcane Thm 1 with X ≍ C^{3θ+δ}. The self-dual part has size C³X^{−1/2}; the remaining open core is equidistribution of Hecke-weighted GL(3) parameters near the self-dual locus at scale 1/log C.
2. **Sym² probe at congruence level**: identify the Sym²π contribution and test whether any input breaks the Sym²–GL₂ reciprocity of cycle 67.
3. **LRS 0.21 in Lean** (known result, but it is the first formal step beyond 3/16): Gelbart–Jacquet lift plus Rankin–Selberg GL(3)×GL(3).

## Module plan (bottom-up)
- [x] G1 `GL3UpperHalfSpace`: normalised positive-definite model P = zzᵀ with P₂₂ = 1; GL₃(ℝ) action P ↦ gPgᵀ/(gPgᵀ)₂₂; Iwasawa coordinates (x₁,x₂,x₃,y₁,y₂) with reconstruction; action laws; unipotent action as a Heisenberg translation; SL₃(ℤ) action.
- [x] G1b `GL3IwasawaHeight`: y₁(g•z)² = ‖r₁×r₂‖²/‖r₂‖⁴, (y₁y₂)(g•z)² = det(g)²(y₁²y₂)²/(‖r₂‖²‖r₁×r₂‖²), x₁, x₃ of g•z; Schur identity qe = det S/(S₂₂(S₁₁S₂₂−S₁₂²)).
- [x] G7a `GL3Plucker`: bottom row and Plücker vector; U-invariance; Plücker relation; right-multiplication laws (adjugate); det = row₀·plk; uniqueness of the left U-coset over any commutative ring.
- [x] G7b `GL3PluckerParam`: U(R)\SL₃(R) ≅ {(v,p) unimodular, v·p = 0} over any commutative ring (`plucker_eq_iff`, `plucker_range`), explicit completion r₁ = w×p, r₀·p = 1.
- [x] G2 `GL3IwasawaGroup` + `GL3IwasawaHaar` + `GL3InvariantMeasure`: h³ as the Iwasawa group N·A⁺ (topological group, continuous GL₃(ℝ) action); dx dy/(y₁y₂)³ is its Haar measure (affine Jacobian); GL₃(ℝ)- and SL₃(ℤ)-invariance via the proper orbit map of SL₃(ℝ) and Haar uniqueness (`measurePreserving_smul_GL`).
- [x] G2f `GL3SiegelDomain` + `GL3FundamentalDomain`: Siegel covering/finiteness transported from the corpus positive-definite reduction theory via w₀-conjugation; Siegel set has finite volume; SL₃(ℤ) acts faithfully and fixed-point sets are null (polynomial zero set); lexicographic-minimum fundamental domain `fundDomain` with `IsFundamentalDomain` and finite volume.
- [ ] G3 `GL3Casimir`: the two invariant operators Δ₁, Δ₂ in coordinates (Goldfeld §6).
- [ ] G4 `GL3FourierExpansion`: Piatetski-Shapiro–Shalika expansion over U₂(ℤ)\SL₂(ℤ).
- [ ] G5 `GL3JacquetWhittaker`: Jacquet integral, convergence, Casimir eigen-equations, Bump–Stade Mellin formula.
- [ ] G6 `GL3MaassForm`: SL₃(ℤ) and Γ₀(N)-type Maass cusp forms; Fourier–Whittaker coefficients; Hecke operators.
- [x] G7c `GL3CoxeterCell` + `GL3CoxeterPhase`: the Coxeter cell (M₂₀ ≠ 0, plk₂ = 0), D ∣ A, coprimality, explicit Bruhat decomposition over ℚ, the three Kloosterman phases.
- [x] G7d `GL3CoxeterKloosterman`: S_{w₃}(m₁,m₂,n₂; D, D²) = D·Kl₃(−m₁m₂n₂; D) for unit weights (links to `HyperKloostermanRootNumber`).
- [ ] G7e orbit parametrisation U(ℤ)\cell(A,D)/U_w(ℤ) ↔ (p₀ mod D, C mod A) as a bijection; general (D, A) Coxeter sums.
- [ ] G8 `GL3Poincare`: Poincaré series, unfolding, Kloosterman expansion.
- [ ] G9 spectral side and Buttcane's hyper-Kloosterman Kuznetsov formula.

## Log
- 2026-09-25 — created; corpus and mathlib audited (no GL(3) automorphic material); G1 started.
- 2026-09-25 — G1 closed: `RHTower/GL3UpperHalfSpace.lean` (structure `H3`, `gram`, `ofPD`, `gram_ofPD`, `ofPD_gram`, `ofMat_smul`, `MulAction (GL (Fin 3) ℝ) H3`, recognition principle `smul_eq_of_mul`, `nGL_smul` Heisenberg translation, `dGL_smul` dilation, `SL₃(ℤ)` action via `slToGL`). `lake build --old` green, wired after `HyperKloostermanRootNumber`, axioms propext/choice/Quot.sound.
- 2026-09-25 — G1b, G7a, G7b closed and wired (`GL3IwasawaHeight`, `GL3Plucker`, `GL3PluckerParam`); all `lake build --old` green. Next: Bruhat cells via Plücker vanishing patterns, the w₅ Kloosterman set and its identification with Kl₃; then Poincaré series (finite locally for compactly supported profiles, by the height formulas).
- 2026-09-25 — G7c/G7d closed and wired (`GL3CoxeterCell`, `GL3CoxeterPhase`, `GL3CoxeterKloosterman`): explicit w₃ Bruhat decomposition over ℚ; D ∣ A; phases; fibre count ℤ/D² → ℤ/D; S_{w₃}(m;D,D²) = D·Kl₃(−m₁m₂n₂;D). Axioms propext/choice/Quot.sound.
- 2026-09-25 — G2 closed and wired (`GL3IwasawaGroup`, `GL3IwasawaHaar`, `GL3InvariantMeasure`). Mechanism: the coordinate measure is left Haar for the Iwasawa group (triangular Jacobian (y₁y₂)³); the pushforward of SL₃(ℝ) Haar along the proper orbit map is GL₃(ℝ)-invariant and Iwasawa-left-invariant; Haar uniqueness identifies them. No Weyl-element Jacobian needed. Corpus assets reused: pattern of `RealSL2Haar`/`RealIwasawaMeasure`; mathlib ℍ-measure proof pattern. Next: finite volume of SL₃(ℤ)\h³ from the corpus Siegel covering (`HTGeometry/SiegelCovering`, `exists_siegel_inOrbit_det_one`) + Siegel-set volume in coordinates.
- 2026-09-25 — G2f closed and wired (`GL3SiegelDomain`, `GL3FundamentalDomain`). Corpus assets reused: `exists_siegel_inOrbit_det_one`, `siegel_finiteness`, `JacobiData.U_unique/d_unique`, `realMvPolynomial_zero_set_volume_fin`, `lintegral_pi_prod`. `isFundamentalDomain_fundDomain`, `volume_fundDomain_lt_top`: SL₃(ℤ)\h³ has finite volume. Next: Heisenberg fundamental domain for U(ℤ), Poincaré series (local finiteness from properness), unfolding against `fundDomain`.
- 2026-09-25 — G8a closed and wired (`GL3PoincareUnfolding`): U(ℤ) Heisenberg subgroup, unit-cell fundamental domain, `lintegral_poincare_unfold`. Next: long-element Bruhat cell (M₂₀ ≠ 0, plk₂ ≠ 0), its orbit parametrisation and phases, S_{w₀}(m,n;D₁,D₂); coprime factorisation and the non-coprime (D₁,D₂) structure — the reciprocity-breaking target of loop cycle 67.
