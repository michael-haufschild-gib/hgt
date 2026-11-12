# The index at an aperture is the sum of the nullities below it

- **ID:** agz-aperture-index (B179 and the reduction of B104 of
  `docs/reports/review-1111/obstacles-summary.md`)
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** obstacles-summary (review-1111) §2.14 question 3, construction VIII; §2.8, §2.13
- **Statement:** for every aperture `b` and every real energy `E`, the negative index of Weil's
  restricted form shifted by `E` is `Σ_{a < b} ν_E(a)`, the sum of the dimensions of the null
  spaces at the resonant apertures below `b` (a finite sum). The Riemann hypothesis holds iff no
  aperture carries a null mode at `E = 0`. The null modes are the crossings of the conormals of
  the apertures with the graph of Weil's operator; the index is also the number of eigenvalues
  below `E`; a null mode below the pole-vanishing ground energy is charged.

## Gates
- [x] I1 left continuity of the index
- [x] I2 the index vanishes at small apertures, at every energy
- [x] I3 the index law
- [x] I4 RH iff no conjugate aperture
- [x] I5 the far end: the sum of all nullities at `E = 0` is the number of zeros to the right of
  the line
- [x] I6 the index as a crossing number of Lagrangian subspaces (B179)
- [x] I7 the index law in the energy; two paths, one index; the rectangle law
- [x] I8 the polar Lagrangian: nullity = charged nullity + neutral nullity
- [x] I9 a null mode below the pole-vanishing ground energy is charged; ground modes charged
  iff `μ(a) < μ₀(a)` (reduction of B104)
- [x] I10 the polar Lagrangian is an even line and an odd line
- [x] I11 the nullities are not all even: a short aperture has a simple ground mode
- [x] I12 up to the ground energy the polar Lagrangians are positive and increase

## Paper proof

`n(a) = negativeRank a E`, `ν(a) = weilNullity a E` for the operator of the corpus
(`RHTower.PaperRestrictedWeil`, `ArithmeticContinuationAndCriticalEnergy`). Corpus facts:
(F1) `n` is nondecreasing in `a`; (F2) for `a < b`, `n(a) + ν(a) ≤ n(b)`, hence
`Σ_{a∈s} ν(a) ≤ n(b)` for finite `s` below `b`, and the resonant apertures below `b` are finite;
(F3) there is `b' > a` with `n(c) = n(a) + ν(a)` for `a < c ≤ b'`; (F4) `n(a)` is attained as the
negative index of the Gram matrix of `n(a)` smooth packets with compact support in the open
interval `(−a, a)`; a Gram matrix of such packets has index `≤ n(a)`; (F5) `n(a) = 0` iff
`E ≤ μ(a)`, the ground energy, and `μ(a) ≥ −log(2a) − (3/2)a − (γ + log π) − 4a³` for
`2a < log 2`.

**I1.** By (F4) take packets `f_1, …, f_n` realising `n(a)`. The union of their supports is a
compact subset of `(−a, a)`, so it lies in `(−c, c)` for some `0 < c < a`
(`c = (max|x| + a)/2`). The same functions are packets of the aperture `c`. The Gram entry is
`W(f_j, f_i) − E ⟨f_i, f_j⟩_{L²}`, which does not depend on the aperture. So
`n(a) = index ≤ n(c) ≤ n(a)`.

**I2.** By (F5), `R = min(1/4, e^{−(E + k + 1)}/2)`, `k = γ + log π`, has `2R < log 2` and
`μ(R) ≥ E + k + 1 − 3/8 − k − 1/16 ≥ E`.

**I3.** `≥` is (F2). `≤` by induction on `N = n(b)`. For `N > 0` let
`T = {a : n(a) < N}`; it is nonempty by I2 and bounded by `b` by (F1). Let `s = sup T`. By I1,
`n(s) = n(c)` for some `c < s`, and some `a ∈ T` has `c < a`, so `n(s) = n(c) ≤ n(a) < N`:
`s ∈ T`, and `s < b`. By (F3), `n(c₀) = n(s) + ν(s)` for `c₀` just right of `s`, `c₀ ≤ b`; and
`c₀ ∉ T`, so `N ≤ n(c₀) ≤ n(b) = N`. Hence `N = n(s) + ν(s)`. By induction
`n(s) ≤ Σ_{a < s} ν(a)`, and `{a < s} ∪ {s} ⊆ {a < b}`.

**I4.** RH iff `μ(A) ≥ 0` for all `A` (corpus) iff `n(A) = 0` at `E = 0` for all `A` iff (I3 and
F2) `ν(a) = 0` for all `a`.

**I5.** `n(b) ≤ #{Re ρ > ½}` at `E = 0` (continuation: the index is attained on smooth packets,
whose Gram matrix is the zero Gram). Conversely let `r ≤ #{Re ρ > ½}`. By the continuation there
are `K ≥ 1`, `η > 0` with `r ≤` robust index of the comb on `(N, (3K+1)N]` with margin `η`, for
large `N`; the robust index decreases in the margin; with margin `0` it is at most
`n(a) + ν(a)` at the aperture `a = ½ log(3K+1)` for large `N`; and `n(a) + ν(a) ≤ n(a + 1)`
(F2). So `r ≤ n(a + 1)`, and by I3 some finite set of apertures carries `r` null modes. Conversely
`Σ_{a∈s} ν(a) ≤ n(b)` for `b` above `s`.

**I6.** On `H × H` put `ω((x, y), (x′, y′)) = ⟨y, x′⟩ − ⟨x, y′⟩`. For `T` self-adjoint the graph
`Γ_T` equals its `ω`-annihilator: `ω` vanishes on it by symmetry, and if
`⟨y, x′⟩ = ⟨x, T x′⟩` for all `x′` then `y = T x`. For `K` closed, `N_K = K × Kᗮ` equals its
annihilator: test against `(x′, 0)` and `(0, y′)` and use `Kᗮᗮ = K`. `Γ_T ∩ N_K` is
`{(x, T x) : x ∈ K, T x ⊥ K}`. If `K = ι(G)` for an isometry `ι` and `⟨T ι u, ι v⟩ = ⟨S u, v⟩`,
then `u ↦ (ι u, T ι u)` maps `ker S` bijectively onto the crossing. For `a ≤ b`, zero extension
`H_a → H_b` is an isometry, and by the transport of the mixed form and of the mass,
`⟨T_b ι u, ι v⟩ = ⟨T_a u, v⟩`. So `dim(Γ_{T_b} ∩ N_{H_a}) = ν(a)` and by I3 the index at `b` is
`Σ_{a<b} dim(Γ_{T_b} ∩ N_{H_a})`. The path `a ↦ N_{H_a}` is increasing in the first factor, ends
at `H_b × 0`, and does not involve the primes.

**I7.** Fix `a`; `q_E(u) = q(u) − E‖Ju‖²`, `J` the injective embedding into `L²`, `‖J‖ ≤ 1`.
(E1) `E₁ < E₂`: on `W = N₋(E₁) ⊕ ker T_{E₁}`, `q_{E₂} ≤ −(E₂ − E₁)‖Ju‖² < 0` off zero, so
`n(E₁) + ν(E₁) = dim W ≤ n(E₂)`. (E2) left: `q_E` is negative on the finite-dimensional
`N₋(E)`, so `q_E ≤ −c‖u‖²` there (maximum on the unit sphere); then
`q_{E−c/2} ≤ −(c/2)‖u‖²` on `N₋(E)`: `n(E − c/2) = n(E)`. (E3) right: if
`n(E + 1/(k+1)) > dim W` for all `k`, take unit `u_k ∈ N₋(E + 1/(k+1))`, `u_k ⊥ W`; then
`q_E(u_k) ≤ 1/(k+1)`; a weak limit `v` along a subsequence is nonzero with `q_E(v) ≤ 0` (the
form is `‖u‖²` plus a compactly read term), `v ⊥ W`; `v ⊥ N₋(E)` and `q_E(v) ≤ 0` give
`T_E v = 0`, so `v ∈ W`, `v ⊥ v`. (E4) `n(μ(a)) = 0`. The counting law (the argument of I3 for a
function on `ℝ`) gives `n(E) = Σ_{s<E} ν(s)`. With I3: `Σ_{a<b} ν(a, E) = Σ_{s<E} ν(b, s)`, and
for `a ≤ b`, `E₁ ≤ E₂` both `n(b, E₂) − n(a, E₁)` decompositions give the rectangle law.

**I8.** `T` self-adjoint, `1 − T` compact, `d : H → V` continuous, `dim V < ∞`,
`L = {(dξ, y) : Tξ = d†y}`. Isotropic: `⟨y, dξ′⟩ = ⟨Tξ, ξ′⟩ = ⟨ξ, Tξ′⟩ = ⟨dξ, y′⟩`. The second
projection of `L` has image `(d ker T)ᗮ` (`d†y ⊥ ker T` iff `y ⊥ d ker T`, and
`ran T = (ker T)ᗮ` by the Fredholm alternative) and kernel `≅ d ker T`, so `dim L = dim V`.
`L ∩ (V × 0) = d(ker T) × 0`; `dim ker T = dim d(ker T) + dim(ker T ∩ ker d)`.
`L ∩ (0 × V)` comes from the `ξ ∈ ker d` with `Tξ ∈ ran d† = (ker d)ᗮ`. For Weil's operator and
`d` the two pole coefficients, `d†y` pairs with `v` as the forcing by the two pole profiles.

**I9.** `μ₀(a)` is the floor of `q` on `ker d` (corpus), attained. A neutral null mode `u ≠ 0` at
`E` has `q(u) = E‖Ju‖²` and `q(u) ≥ μ₀‖Ju‖²`, so `E ≥ μ₀`. If `E ≤ μ₀`, `d` is injective on
`N₋(E)` (a vector of `N₋ ∩ ker d` has `q < E‖Ju‖² ≤ μ₀‖Ju‖²`), so `n(E) ≤ 2`. If `μ = μ₀`, a
constrained ground state `u` has `q_μ(u) = 0` and `T_μ ≥ 0`, so `T_μ u = 0`: a neutral ground
mode. For `a ≤ ½(log 2 + 1/50)`, `μ₀(a) ≥ 1/20` (corpus).

**I10.** The reflection `R` of the aperture is an isometric involution of `H_a` that preserves
the form and the mass (corpus), so `⟨T Ru, Rv⟩ = ⟨Tu, v⟩` and `TR = RT`; it exchanges the two
pole coefficients. If `Tξ = d†y` then `T Rξ = d†(y₁, y₀)` and `d Rξ` is `dξ` exchanged: `L` is
invariant under the exchange `σ ⊕ σ`. `L = L₊ ⊕ L₋` with `L_ε = L ∩ {x₁ = εx₀, y₁ = εy₀}`
(`p = ½(p + σp) + ½(p − σp)`). For two pairs of parity `ε` with first coordinates `(s, t)`,
`(s′, t′)`, isotropy is `t̄ s′ = s̄ t′`; with `t̄ s = s̄ t`: if `t = 0` then `t′ = 0` and
`q = (s′/s) p`; if `t ≠ 0`, `t̄ (s′t − s t′) = 0` and `q = (t′/t) p`. So `dim L_ε ≤ 1`, and
`dim L = 2` gives `dim L_ε = 1`. For a null mode `u`, `u ± Ru` are null modes of pure parity and
their charges add to `2 du`. If the charges of the null modes fill `ℂ²`, null modes of charge
`(1, 1)` and `(1, −1)` give an even one of charge `(2, 2)` and an odd one of charge `(2, −2)`.

**I11.** For `a < δ` the lowest eigenvalue of Weil's operator is simple (Suzuki, Theorem 1.4,
corpus). `T_μ u = 0` iff `u` is a fixed vector of the Birman–Schwinger operator iff `Ju` is an
eigenvector at `μ` (corpus); `J` is injective, so `ker T_μ` embeds in a line, and it is not zero
(I7). Just above `μ(b)`, `n(b, E) = 0 + 1`; by I3 the nullities below `b` at `E` sum to one.

**I12.** Let `E ≤ μ(b)`, so `T = T_{b,E} ≥ 0`. If `Tξ = d†y` then for every `u`,
`0 ≤ ⟨T(u − ξ), u − ξ⟩` gives `2 Re⟨y, du⟩ − ⟨Tu, u⟩ ≤ ⟨y, dξ⟩ = ⟨Tξ, ξ⟩`. For `a ≤ b` and
`T_a ξ_a = d_a† y`, take `u` the extension of `ξ_a`: it has the same charges and the same
form, so `2⟨y, x_a⟩ − ⟨y, x_a⟩ ≤ ⟨y, x_b⟩`. For `E < μ(a)` there is no null mode, so every
`d†y` is in the range of `T` (I8) and the charge is unique; `⟨Tξ, ξ⟩ ≥ (μ − E)‖Jξ‖² > 0` for
`y ≠ 0` because `d` is onto.

## Lean

`formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheIndexAtAnApertureIsTheSumOfTheNullitiesBelowIt.lean`:
`exists_lt_subset_Ioo`, `inner_physical_congr`, `exists_smaller_aperture_negativeRank_eq` (I1),
`exists_aperture_negativeRank_eq_zero` (I2), `resonantBelow`, `negativeRank_le_sum_nullity`,
`negativeRank_eq_sum_nullity` (I3), `negativeRank_eq_zero_iff_forall_weilNullity`,
`riemannHypothesis_iff_forall_weilNullity_zero` (I4).

`…/TheNullModesOfTheAperturePathCountTheZerosRightOfTheLine.lean` (I5):
`robustCombIndex_anti`, `exists_aperture_le_negativeRank`, `iSup_negativeRank_zero_eq_rightZeros`,
`nat_le_rightZeros_iff_exists_sum_nullity`, `rightZeros_encard_eq_iSup_sum_nullity`;
`negIndex_nestedStepGram_le_sum_nullity`: the Gram matrix of `𝔚_Q − E` on the flat packets of
nested windows in `(x₀, X]` has at most `Σ_{a < A} ν_E(a)` negative squares for every aperture
`A > ½ log(X/x₀)` (the index bound of the continuation for bounded packets, with I3).

`…/TheNullSpaceOfACompressionIsTheCrossingOfAGraphWithAConormal.lean`,
`…/TheIndexIsTheNumberOfCrossingsOfTheApertureConormalsWithTheGraphOfWeilsOperator.lean` (I6):
`sympForm`, `operatorGraph`, `conormal`, `mem_operatorGraph_iff_forall_sympForm`,
`mem_conormal_iff_forall_sympForm`, `finrank_operatorGraph_inf_conormal`; `apertureIsometry`,
`inner_operator_apertureExt`, `weilGraph`, `apertureConormal`,
`finrank_weilGraph_inf_apertureConormal`, `negativeRank_eq_sum_apertureCrossing`,
`riemannHypothesis_iff_forall_apertureCrossing_zero`.

`…/TheNullModesAlongTheAperturePathAreAsManyAsTheEigenvaluesBelowTheEnergy.lean` (I7):
`count_eq_sum_jumps`, `negativeRank_add_nullity_le_of_energy_lt`,
`exists_left_energy_negativeRank_eq`, `exists_right_energy_negativeRank_eq`,
`negativeRank_eq_sum_eigenvalues`, `weilNullity_groundEnergy_pos`,
`sum_nullity_apertures_eq_sum_eigenvalues`, `null_modes_along_two_paths`.

`…/ThePolarRelationOfASelfAdjointFredholmOperatorIsLagrangian.lean`,
`…/TheChargedNullModesAreTheCrossingsOfThePolarLagrangian.lean` (I8): `polarRelation`,
`polarRelation_isotropic`, `finrank_polarRelation`, `mem_polarRelation_zero_right`,
`exists_eq_adjoint_iff`; `polarCharge`, `polarLagrangian`, `mem_polarLagrangian_iff`,
`finrank_polarLagrangian`, `chargedNullity`, `neutralNullity`,
`weilNullity_eq_charged_add_neutral`, `negativeRank_eq_sum_charged_add_neutral`.

`…/ANullModeBelowThePoleVanishingGroundEnergyIsCharged.lean` (I9):
`neutralNullity_eq_zero_of_lt_polarGroundEnergy`, `negativeRank_le_two_of_le_polarGroundEnergy`,
`neutralNullity_groundEnergy_eq_zero_iff`,
`negativeRank_eq_sum_chargedNullity_of_lt_polarGroundEnergy`,
`negativeRank_eq_sum_chargedNullity_of_le_primeTwo`.

`…/ALagrangianPlaneWithAnExchangeSymmetryIsAPairOfLines.lean`,
`…/ThePolarLagrangianIsAnEvenLineAndAnOddLine.lean` (I10): `parityPairs`,
`exists_smul_eq_of_isotropic_parity`, `finrank_inf_parityPairs_eq_one`; `operator_reflection`,
`polarCharge_reflection_zero`, `exists_exchange_mem_polarLagrangian`,
`finrank_polarLagrangian_inf_parityPairs`, `exists_pureParity_charged_null_mode`,
`exists_even_odd_charged_of_chargedNullity_two`.

`…/TheGroundModeOfAShortApertureIsSimple.lean` (I11): `exists_weilNullity_groundEnergy_eq_one`,
`exists_single_simple_null_mode`.

`…/BelowTheGroundEnergyThePolarLagrangiansArePositiveAndIncrease.lean` (I12):
`forced_variational`, `polarCharge_apertureExt`, `exists_mem_polarLagrangian_of_lt_ground`,
`eq_of_mem_polarLagrangian_of_lt_ground`, `re_inner_forcing_charge_pos`,
`re_inner_forcing_charge_mono`.

## Open

- B104 in its exact form: whether `μ(a) = μ₀(a)` can occur, at the critical aperture in
  particular. Equality is a constrained ground state that solves the unforced equation.
- The differential equation of the even and the odd line in the aperture (a Hamiltonian) past
  the first conjugate aperture; whether the two lines cross the charge axis at different
  apertures. Before it
  the corpus has the canonical system with a Hamiltonian of determinant one
  (`CanonicalSystemOfTheWindowTower`).
- The invariance does not produce the value of the index: index zero is RH.

## Log
- 2026-11-11 — proved and formalized (I1–I4)
- 2026-11-12 — I5 proved and formalized
- 2026-11-12 — I6–I9 proved and formalized
- 2026-11-12 — I10, I11 proved and formalized
- 2026-11-12 — I12 proved and formalized
