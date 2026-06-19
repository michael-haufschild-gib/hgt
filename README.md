# Infinite-base difference Galois for L-functions

This is the Lean 4 formalization track for the draft
`docs/drafts/infinite-base-difference-galois-for-L-functions.md`.

## Scope

The current Lean ledger proves the draft's elementary finite/multiplicative core:

| Draft target | Lean theorem |
|---|---|
| A1, inversion and scale under `s ↦ 1-s` | `GaloisForLFunctions.cpow_inversion_scale` |
| A2, involution | `GaloisForLFunctions.sigma_involutive` |
| A3, fixed-modulus critical-line test | `GaloisForLFunctions.norm_cpow_eq_critical_iff` |
| A4, finite integer log-prime relation | `GaloisForLFunctions.log_prime_int_relation_eq_zero` |
| A4, integer linear independence form | `GaloisForLFunctions.logPrime_linearIndependent_int` |
| A4, full rational linear independence | `GaloisForLFunctions.linearIndependent_log_primes` |
| A4, finite no-rational-resonance corollary | `GaloisForLFunctions.logPrime_no_rat_relation` |
| Euler product iff finite Bohr-prime factorization | `GaloisForLFunctions.isMultiplicative_iff_bohr_factorization` |
| Finite pre-spectral non-Euler-product witness | `GaloisForLFunctions.fake_fails_factorization` |
| Concrete mod-5 Davenport-Heilbronn-style fake coefficient model is non-multiplicative | `GaloisForLFunctions.davenportHeilbronnFakeCoeff_not_isMultiplicative` |
| B2 zero-free half, local Euler factor | `GaloisForLFunctions.localEulerFactor_ne_zero` |
| Brick #11, local first-order `q`-difference equation | `GaloisForLFunctions.localEulerFactor_q_difference` |
| Brick #11, prime-indexed dilation equation `q_p=p⁻¹` | `GaloisForLFunctions.localEulerFactor_prime_dilation_difference` |
| Archimedean lane §2, additive shift is simultaneous prime-lane dilation | `GaloisForLFunctions.primeDiagonal_shift_apply`, `GaloisForLFunctions.primeDiagonal_shift` |
| B3 finite zero-free stepping stone | `GaloisForLFunctions.finiteEulerProduct_ne_zero` |
| Multi-`q` §9-10, coordinate resonance implies diagonal resonance | `GaloisForLFunctions.diagonalResonant_of_coordinateResonant` |
| Multi-`q` §9-10, torsion-free coordinates have trivial coordinate lattice | `GaloisForLFunctions.coordinateResonant_eq_zero_of_no_coordinate_torsion` |
| Multi-`q` §9-10, prime-log diagonal resonance lattice is trivial | `GaloisForLFunctions.logPrime_diagonalResonant_eq_zero` |
| Multi-`q` §43.2, arithmetic prime-log character annihilator is `{0}` | `GaloisForLFunctions.primeLog_diagonalRelationLattice_eq_singleton` |
| Multi-`q` §43.2, every finite arithmetic annihilator slice is `{0}` | `GaloisForLFunctions.finitePrimeLogAnnihilator_eq_singleton` |
| Multi-`q` §9-10, diagonal resonance need not be coordinate resonance | `GaloisForLFunctions.pairCancel_not_coordinateResonant` |
| Multi-`q` §16, corrected noncommutative curvature equals cocycle condition | `GaloisForLFunctions.discreteCurvature_eq_one_iff_cocycleCondition` |
| Multi-`q` §16, draft-order curvature gives a twisted order condition | `GaloisForLFunctions.draftOrderCurvature_eq_one_iff_twisted_cocycle` |
| Multi-`q` §76, image of an abelian lattice representation is abelian | `GaloisForLFunctions.monoidHom_range_commutative` |
| Multi-`q` §76, pairwise commuting monodromy generators generate an abelian subgroup | `GaloisForLFunctions.closure_range_commutative_of_pairwise_commute` |
| Multi-`q` §16, finite truncation preserves integrability | `GaloisForLFunctions.integrableOn_mono` |
| Multi-`q` §16, global pairwise integrability implies finite integrability | `GaloisForLFunctions.integrableOn_of_forall` |
| Multi-`q` §47.1, co-extension composite equality is equivalent to flatness | `GaloisForLFunctions.coextensionComposite_eq_iff_flatCondition` |
| Multi-`q` §47.1, co-extended fundamental-solution maps commute iff flat | `GaloisForLFunctions.coextension_commutes_iff_flatCondition` |
| DSS determinant criterion, finite algebraic skeleton only | `GaloisForLFunctions.matrix_nontrivial_kernel_iff_det_eq_zero` |
| DSS auxiliary vanishing criterion for the concrete `N_n^{z_j}` matrix | `GaloisForLFunctions.multiplicity_det_criterion` |
| Object-X Li/secular pointwise triangular identity | `GaloisForLFunctions.li_secular_pointwise` |
| Object-X inverse secular/Li pointwise triangular identity | `GaloisForLFunctions.secular_li_pointwise_inv` |
| Conjugate-pair secular moment contribution is real | `GaloisForLFunctions.conj_pair_moment_real` |
| Finite secular Newton duality: power-sum face equals symmetric-polynomial evaluation | `GaloisForLFunctions.secularPowerSum_eq_aeval` |
| Finite secular Newton duality: elementary-symmetric face as a concrete sum | `GaloisForLFunctions.secularESymm_eq_sum` |
| Finite secular Newton identity tying power sums and elementary symmetric functions | `GaloisForLFunctions.secular_newton` |
| Multiset power sums are symmetric-polynomial power-sum evaluations | `GaloisForLFunctions.aeval_psum_eq_multiset_powerSum` |
| Newton's identity transferred to finite multisets | `GaloisForLFunctions.multiset_newton` |
| Second Newton-Girard secular-moment identity | `GaloisForLFunctions.secularMoment_girard_two` |
| Third Newton-Girard secular-moment identity | `GaloisForLFunctions.secularMoment_girard_three` |
| Finite moment/spectrum Newton recursion | `GaloisForLFunctions.secular_moment_newton` |
| B23: per-zero geometric series is the resolvent `(1−rX)⁻¹` in `ℂ⟦X⟧` | `GaloisForLFunctions.geom_eq_inv` |
| B23: superzeta generating function is the additive resolvent trace `Σᵢ(1−rᵢX)⁻¹` (not a product) | `GaloisForLFunctions.superzeta_eq_sum_resolvent` |
| B23: superzeta value `𝒵(k)` is the secular power sum `P_k = Σᵢ rᵢᵏ` | `GaloisForLFunctions.superzeta_coeff_eq_powerSum` |
| Finite spectral polynomial faithfully determines the multiset | `GaloisForLFunctions.spectralTorelli_faithful` |
| Constant term of the finite spectral polynomial is the signed product of roots | `GaloisForLFunctions.spectralPoly_coeff_zero` |
| Conjugation-invariant finite spectral polynomial has conjugation-fixed coefficients | `GaloisForLFunctions.selfDual_spectralPoly_coeff_real` |
| Finite DSS face: elementary-symmetric spectrum coordinates are algebraically independent | `GaloisForLFunctions.spectrum_esymm_algIndep` |
| Finite power sums determine a finite zero multiset | `GaloisForLFunctions.powerSum_torelli_finite` |
| Distinct finite zero multisets are separated by a bounded power sum | `GaloisForLFunctions.exists_powerSum_ne_of_ne` |
| Smooth-number frequencies for finite auxiliary forms | `GaloisForLFunctions.boundedExponentVectorEquivSmooth` |
| Smooth-number frequency existence criterion | `GaloisForLFunctions.primeProduct_isBoundedSmooth_iff` |
| Diagonal monomial frequency identity | `GaloisForLFunctions.diagonalMonomial_eq_frequency` |
| Finite auxiliary form becomes a Dirichlet polynomial on the diagonal | `GaloisForLFunctions.diagonalAuxiliaryForm_eq_dirichletPolynomial` |
| Rank-one scalar cocycles are closed under tensor/dual | `GaloisForLFunctions.scalarCocycle_mul`, `GaloisForLFunctions.scalarCocycle_inv` |
| Rank-one scalar coboundaries are cocycles | `GaloisForLFunctions.rankOneCoboundary_cocycle` |
| Rank-one Picard quotient is abelian | `GaloisForLFunctions.rankOnePicard_commGroup` |
| Additive Koszul `H⁰` skeleton: `d₀ x=0` iff jointly invariant | `GaloisForLFunctions.koszulD0_eq_zero_iff_invariant` |
| Additive Koszul `H¹` skeleton: `d₁ c=0` iff the 1-cocycle equation holds | `GaloisForLFunctions.koszulD1_eq_zero_iff_additiveCocycle` |
| Additive Koszul coboundaries are 1-cocycles | `GaloisForLFunctions.koszulCoboundary_cocycle` |
| First two additive Koszul differentials compose to zero | `GaloisForLFunctions.koszulD1_koszulD0_eq_zero` |
| Finite Koszul alternating binomial rank count vanishes | `GaloisForLFunctions.koszul_alternating_choose_sum_eq_zero` |
| Finite Koszul Euler-characteristic rank count vanishes | `GaloisForLFunctions.koszul_euler_characteristic_eq_zero` |
| Bohr character on the diagonal is a Dirichlet monomial | `GaloisForLFunctions.diagonal_character_eq_dirichlet` |
| Finite Bohr auxiliary on the diagonal is a Dirichlet polynomial | `GaloisForLFunctions.auxiliary_diagonal_eq` |
| Boundary-radius normalization is unitary exactly on the boundary circle | `GaloisForLFunctions.boundaryUnitNormalize_norm_eq_one_iff` |
| Diagonal boundary normalization is unitary exactly on `Re(s)=1/2` | `GaloisForLFunctions.diagonalBoundary_unit_norm_iff` |
| Finite diagonal Satake tensors have pairwise-product parameters | `GaloisForLFunctions.satakeTensor_diagonal` |
| Tensor-product Satake local factor is the double product over pairwise products | `GaloisForLFunctions.satakeLocalFactor_tensor` |
| Unitary `GL₂` Satake trace equals `2·Re z` | `GaloisForLFunctions.satake_trace_eq_two_mul_re` |
| Unitary `GL₂` Satake trace is real | `GaloisForLFunctions.satake_trace_im` |
| Unitary `GL₂` Satake trace lies in the Sato-Tate interval `[-2,2]` | `GaloisForLFunctions.satake_trace_re_mem_Icc` |
| Inversion-closed Satake multiset has self-dual local factor | `GaloisForLFunctions.selfDual_localFactor_eq` |
| D6: elementary symmetric function is homogeneous, `eₖ(c·S)=cᵏeₖ(S)` | `GaloisForLFunctions.multiset_esymm_map_mul` |
| D6: function-field Weil FE (coefficients) — `ω↦q/ω` closure ⟹ `eₖ(S)=qᵏeₖ(S⁻¹)` | `GaloisForLFunctions.functionField_esymm_FE` |
| D6: function-field Weil FE (polynomial) — `L`-factor `∏(1−ωT)` invariant under `ω↦q/ω` | `GaloisForLFunctions.functionField_localFactor_FE` |
| Li/Bombieri-Lagarias `w`-coordinate norm-square defect | `GaloisForLFunctions.wCoordinate_normSq_sub_one` |
| `w`-coordinate norm-square unit circle is `Re(s)=1/2` | `GaloisForLFunctions.wCoordinate_normSq_eq_one_iff` |
| Functional-equation pairing is inversion in the `w`-coordinate | `GaloisForLFunctions.wCoordinate_sigma_eq_inv` |
| Arakelov `w=1-1/ρ` coordinate equals `(ρ-1)/ρ` away from `0` | `GaloisForLFunctions.arakelovW_eq_div` |
| Functional-equation partner multiplies to `1` in the Arakelov `w`-coordinate | `GaloisForLFunctions.arakelovW_mul_sigma` |
| Arakelov `w`-coordinate unit circle is `Re(ρ)=1/2` | `GaloisForLFunctions.arakelovW_norm_one_iff_critical` |
| Arakelov `w`-coordinate maps `Re(ρ)>1/2` to the open unit disk | `GaloisForLFunctions.arakelovW_norm_lt_one_iff` |
| Arakelov `w`-coordinate is injective | `GaloisForLFunctions.arakelovW_injective` |
| `σ ∘ conj` is an involution on the `s`-plane | `GaloisForLFunctions.sigmaConj_involutive` |
| The critical line is the fixed locus of `σ ∘ conj` | `GaloisForLFunctions.sigmaConj_fixed_iff_critical` |
| Berry-Keating `u=s(1-s)` is invariant under `σ` | `GaloisForLFunctions.berryKeatingU_sigma` |
| Berry-Keating `u` real part in rectangular coordinates | `GaloisForLFunctions.berryKeatingU_re` |
| Berry-Keating `u` imaginary part in rectangular coordinates | `GaloisForLFunctions.berryKeatingU_im` |
| On the critical line, `u=s(1-s)` is real and equals `1/4+Im(s)^2` | `GaloisForLFunctions.berryKeatingU_on_critical` |
| On the critical line, the real `u` coordinate lies on `[1/4,∞)` | `GaloisForLFunctions.berryKeatingU_re_ge_quarter_on_critical` |
| Parametrized formula `u(1/2+iγ)=1/4+γ^2` | `GaloisForLFunctions.berryKeatingU_critical_param` |
| Non-real off-critical points with nonzero imaginary part have non-real `u` | `GaloisForLFunctions.berryKeatingU_nonreal_of_offCritical_nonzero_im` |
| Finite real-spectrum carrier Pick kernel is positive semidefinite | `GaloisForLFunctions.pick_kernel_posSemidef` |
| Resolvent Gram equals the finite carrier Pick kernel | `GaloisForLFunctions.pick_gram_eq_kernel` |
| Finite real-spectrum carrier is Herglotz on the upper half-plane | `GaloisForLFunctions.real_spectrum_carrier_herglotz` |
| Finite carrier with all poles outside the upper half-plane is Herglotz there | `GaloisForLFunctions.poles_lower_carrier_herglotz` |
| One upper-half-plane pole violates the Herglotz condition | `GaloisForLFunctions.pole_upper_not_herglotz` |
| One-by-one negative diagonal has an explicit negative vector | `GaloisForLFunctions.oneByOne_negative_vector_of_re_neg` |
| One-by-one negative diagonal has a one-dimensional negative subspace | `GaloisForLFunctions.oneByOne_negative_subspace_of_re_neg` |
| Negative diagonal block has a `k`-dimensional negative subspace | `GaloisForLFunctions.diagonal_negative_subspace` |
| One upper-half-plane pole gives a non-PSD one-point Pick matrix | `GaloisForLFunctions.single_pole_pick_not_posSemidef` |
| One upper-half-plane pole gives an explicit negative Pick vector | `GaloisForLFunctions.single_pole_pick_negative_vector` |
| A conjugate pole pair with an upper-half-plane pole violates Herglotz | `GaloisForLFunctions.conj_pair_not_herglotz` |
| Pick diagonal is the real ratio `Im(m)/Im(z)` | `GaloisForLFunctions.pickDiag_eq`, `GaloisForLFunctions.pickDiag_re` |
| A conjugate pole pair with an upper-half-plane pole gives a non-PSD one-point Pick matrix | `GaloisForLFunctions.conj_pair_pick_not_posSemidef` |
| A conjugate pole pair with an upper-half-plane pole gives an explicit negative Pick vector | `GaloisForLFunctions.conj_pair_pick_negative_vector` |
| FE conjugate-pair carrier is Herglotz on the upper half-plane iff the pole is real | `GaloisForLFunctions.conj_pair_herglotz_iff` |
| FE conjugate-pair carrier has a positive value witness off-line | `GaloisForLFunctions.conj_pair_carrier_pos` |
| FE conjugate-pair carrier takes both signs off-line | `GaloisForLFunctions.conj_pair_carrier_indefinite` |
| Statement-level carrier predicate is equivalent to the on-line predicate | `GaloisForLFunctions.carrierHerglotz_iff_onLine` |
| Finite real-spectrum Hankel moment matrix is positive semidefinite | `GaloisForLFunctions.secularHankel_posSemidef` |
| Abstract Krein-Langer negative-inertia upper bound by `k` squares | `GaloisForLFunctions.sigNeg_le_of_add_sum_sq_nonneg` |
| Rank-one Krein-Langer negative-inertia upper bound | `GaloisForLFunctions.sigNeg_le_one_of_add_sq_nonneg` |
| Complex Hermitian Krein-Langer negative-inertia upper bound | `GaloisForLFunctions.hermitian_neg_inertia_le` |
| PosSemidef/rank-one correction form of the Hermitian inertia upper bound | `GaloisForLFunctions.neg_inertia_le_of_posSemidef` |
| Rank-one outer product is positive semidefinite | `GaloisForLFunctions.outer_posSemidef` |
| Conjugate-pair Pick kernel rank-one factor identity | `GaloisForLFunctions.conjPair_pe` |
| FE conjugate-pair Pick matrix has negative inertia at most one | `GaloisForLFunctions.conj_pair_pick_neg_inertia_le_one` |
| FE multi-pair Pick matrix has negative inertia at most the number of pairs | `GaloisForLFunctions.multi_pair_pick_neg_inertia_le` |
| FE multi-pair Pick matrix has positive inertia at most the number of pairs | `GaloisForLFunctions.multi_pair_pick_pos_inertia_le` |
| FE conjugate-pair Pick factorization as a standalone matrix identity | `GaloisForLFunctions.conj_pair_pick_factorization` |
| Rank-one Hermitian quadratic form is a squared inner product | `GaloisForLFunctions.rankOne_quadForm` |
| Factored orthogonal vector gives a negative direction | `GaloisForLFunctions.neg_def_of_factored_orthogonal` |
| Surjective factored evaluation map gives a `k`-dimensional negative subspace | `GaloisForLFunctions.exists_neg_def_subspace` |
| Surjective factored evaluation map gives exact negative inertia `k` | `GaloisForLFunctions.exact_neg_inertia` |
| Square Cauchy vectors with distinct poles/nodes are linearly independent | `GaloisForLFunctions.cauchy_linearIndependent` |
| Linearly independent square evaluation vectors give a surjective evaluation map | `GaloisForLFunctions.eval_surjective_of_linearIndependent` |
| Linearly independent rectangular carrier vectors give a surjective evaluation map | `GaloisForLFunctions.eval_surjective_rect` |
| FE multi-pair carrier vectors `{e_i+a_i,e_i-a_i}` are linearly independent | `GaloisForLFunctions.multiPair_carrier_linearIndependent` |
| FE multi-pair factored carrier has exact negative inertia `k` | `GaloisForLFunctions.multiPair_carrier_exact_neg_inertia` |
| Finite-measure carrier on `ℝ` is Herglotz on the upper half-plane | `GaloisForLFunctions.measure_carrier_herglotz` |
| Finite-measure Pick kernel matrix is Hermitian | `GaloisForLFunctions.measure_pick_isHermitian` |
| Finite-measure Pick kernel matrix is positive semidefinite | `GaloisForLFunctions.measure_pick_posSemidef` |
| Hadamard product of finite-measure Pick kernel matrices is positive semidefinite | `GaloisForLFunctions.measure_pick_hadamard_posSemidef` |
| Finite real-spectrum carrier is the atomic-measure carrier | `GaloisForLFunctions.measure_carrier_atomic` |
| Cayley transform sends a Herglotz value into the closed Schur disk | `GaloisForLFunctions.cayley_herglotz_schur` |
| Inverse Cayley transform sends a Schur value to a Herglotz value | `GaloisForLFunctions.cayley_schur_herglotz` |
| Blaschke factor is Schur on the closed disk | `GaloisForLFunctions.blaschke_schur` |
| Finite Blaschke product is Schur on the closed disk | `GaloisForLFunctions.finite_blaschke_schur` |
| Finite truncated Szegő kernel is positive semidefinite | `GaloisForLFunctions.szego_truncation_posSemidef` |
| Forward Krein-Langer factored Schur form stays Schur | `GaloisForLFunctions.kreinLanger_factored_schur` |
| de Branges-Rovnyak diagonal kernel is nonnegative for a Schur value in the disk | `GaloisForLFunctions.deBrangesRovnyak_diag_nonneg` |
| Cayley transform maps the upper half-plane into the open unit disk | `GaloisForLFunctions.cayley_upperHalfPlane_to_disk` |
| Hadamard product of finite truncated Szegő kernels is positive semidefinite | `GaloisForLFunctions.szego_hadamard_posSemidef` |
| Attack 5 finite floor: per-prime scaling `σ_c` evaluates as `P(c·x)` | `GaloisForLFunctions.sigmaScale_eval` |
| Attack 5 finite floor: root correspondence `r ↦ c·r` under `σ_c` | `GaloisForLFunctions.sigmaScale_isRoot` |
| Attack 5 finite floor: `σ_c` (`c≠0`) preserves real-rootedness (`Splits` over `ℝ`) | `GaloisForLFunctions.sigmaScale_splits` |
| B30 §8(a): ⊗-multiplicativity of Adams operations `p_m(π₁⊗π₂)=p_m(π₁)·p_m(π₂)` | `GaloisForLFunctions.adamsPowerSum_tensor` |
| B30 §8(a): contragredient Adams operation is the complex conjugate | `GaloisForLFunctions.adamsPowerSum_conj` |
| B30 §8(a): self-dual `π⊗π̃` Adams operation is the second moment `p_m·conj p_m` | `GaloisForLFunctions.adamsPowerSum_tensor_selfDual` |
| B30 §8(a): self-dual second moment is the nonnegative real `‖p_m‖²` | `GaloisForLFunctions.adamsPowerSum_tensor_selfDual_normSq` |
| B30 §8: ⊕-additivity of Adams operations `p_m(π₁⊞π₂)=p_m(π₁)+p_m(π₂)` (isobaric sum) | `GaloisForLFunctions.adamsPowerSum_isobaricSum` |
| B30 §8: Adams operations compose multiplicatively `ψᵐ∘ψᵏ=ψᵐᵏ` on power sums | `GaloisForLFunctions.adamsPowerSum_comp` |
| B30 §8: first Adams operation is the identity on power sums | `GaloisForLFunctions.adamsPowerSum_one` |
| B30: tensor determinant / central-character formula for finite Satake parameters | `GaloisForLFunctions.satakeDet_tensor` |
| B30: elementary-symmetric cons recursion for Satake multisets | `GaloisForLFunctions.multiset_esymm_cons` |
| B30: local-factor coefficient equals signed exterior-power elementary symmetric data | `GaloisForLFunctions.localFactor_coeff_esymm` |
| B30: top exterior-power elementary symmetric function is the Satake product | `GaloisForLFunctions.multiset_esymm_card_eq_prod` |
| B30: exterior-power temperedness/binomial bound for unitary Satake multisets | `GaloisForLFunctions.esymm_norm_le` |
| B30: power-sum/Adams temperedness rank bound for unitary Satake multisets | `GaloisForLFunctions.multiset_powerSum_norm_le` |
| B30: exterior powers vanish above the Satake rank | `GaloisForLFunctions.multiset_esymm_eq_zero_of_card_lt` |
| B30: local-factor coefficients vanish above the Satake rank | `GaloisForLFunctions.localFactor_coeff_eq_zero_of_card_lt` |
| B30: general `Symᵏ` Satake character is complete homogeneous symmetric evaluation | `GaloisForLFunctions.aeval_hsymm_eq` |
| B30: `Sym⁰` Satake character is trivial | `GaloisForLFunctions.symChar_zero` |
| B30: `Sym¹` Satake character is the trace | `GaloisForLFunctions.symChar_one` |
| B30: `Symᵏ` temperedness/dimension bound for unitary Satake families | `GaloisForLFunctions.symChar_norm_le` |
| B30/B5 bridge: degree-one complete-homogeneous and elementary-symmetric characters coincide | `GaloisForLFunctions.symChar_one_eq_esymm_one` |
| B30/B5 weld: geometric series inverts a local factor in `ℂ⟦X⟧` (`(1−rX)·ΣrᵐXᵐ=1`) | `GaloisForLFunctions.geometric_localFactor_inv` |
| B30/B5 weld: `∧•` generating series — `coeffₖ ∏(1−fᵢX) = (−1)ᵏeₖ` | `GaloisForLFunctions.coeff_localFactor_series` |
| B30/B5 weld: `Sym•` generating series — `coeffₖ ∏(1−fᵢX)⁻¹ = hₖ` (complete-homogeneous gen. fn.) | `GaloisForLFunctions.coeff_completeHomogeneous_series` |
| B30/B5 weld: the `e–h` (`∧•`/`Sym•`) Koszul duality `Σ_{i+j=k}(−1)ⁱeᵢhⱼ=0` (k≥1) | `GaloisForLFunctions.eh_koszul_duality` |
| B30 §7: Chebyshev–Laurent plethysm `z^k·S_k(z+z⁻¹)=Σ_{i≤k}(z²)^i` (Symᵏ Dirichlet kernel) | `GaloisForLFunctions.chebyshevS_eval_add_inv` |
| B30 §7: explicit `U_k` form `z^k·U_k((z+z⁻¹)/2)=Σ_{i≤k}(z²)^i` (`p_m(Symᵏ)=U_k(p_m/2)`) | `GaloisForLFunctions.chebyshevU_eval_plethysm` |
| D3 §3′ Sato–Tate: `GL₂` `Symᵏ` character is Chebyshev `S_k(z+z⁻¹)` (`Symᵏ a_p = U_k(cos θ_p)`) | `GaloisForLFunctions.symPowerGL2_eq_chebyshevS` |
| D3 §3′: `GL₂` `Symᵏ` dimension `|Sym (Fin 2) k| = k+1` | `GaloisForLFunctions.symPowerGL2_card` |
| D3 §2/§3′: `GL₂` `Symᵏ` temperedness bound `‖Symᵏ‖ ≤ k+1` for unitary Satake (`‖z‖=1`) | `GaloisForLFunctions.symPowerGL2_norm_le` |
| D3 §3′ Sato–Tate: cosine orthogonality `∫₀^π cos(jθ)dθ = π·δ_{j,0}` | `GaloisForLFunctions.integral_cos_nat_mul` |
| D3 §3′ Sato–Tate: Fourier orthogonality `∫₀^π sin((k+1)θ)sinθ dθ = (π/2)·δ_{k,0}` | `GaloisForLFunctions.integral_sin_succ_mul_sin` |
| D3 §3′ Sato–Tate moment: `∫₀^π U_k(cosθ)·(2/π)sin²θ dθ = δ_{k,0}` (Symᵏ averages to 0 vs μ_ST) | `GaloisForLFunctions.satoTate_moment` |
| D3 §3′: real cosine integral `∫₀^π cos(cθ)dθ = sin(cπ)/c` (`c≠0`) | `GaloisForLFunctions.integral_cos_mul_pi` |
| D3 §3′: full Fourier orthogonality `∫₀^π sin(mθ)sin(nθ)dθ = (π/2)·δ_{m,n}` (`m,n≥1`) | `GaloisForLFunctions.integral_sin_mul_sin` |
| D3 §3′: `U_k` orthonormal for `μ_ST`: `∫₀^π U_j U_k (2/π)sin²θ dθ = δ_{j,k}` (Symᵏ are μ_ST's orthogonal polynomials) | `GaloisForLFunctions.satoTate_orthonormal` |
| Self-dual/conjugation-invariant finite Satake multiset has real moments | `GaloisForLFunctions.selfDual_moment_real` |
| B5 §3 / foundations §22: FE σ-parity — negation-symmetric multiset has vanishing odd moments | `GaloisForLFunctions.fe_odd_moment_vanish` |
| B5 §3 / foundations §22: centered FE reflection gives vanishing centered odd moments | `GaloisForLFunctions.fe_centered_odd_moment_vanish` |
| Exterior powers scale by `c^n` under `∧ⁿ(c·id)` | `GaloisForLFunctions.exteriorPower_map_smul_id` |
| Exterior powers of `-id` act by `(-1)^n` | `GaloisForLFunctions.exteriorPower_map_neg_id` |
| Oscillator algebra skeleton: `[X,Y] = -4H` on monomial coefficients | `GaloisForLFunctions.osc_comm_XY_apply` |
| Oscillator algebra skeleton: `[H,X] = 2X` on monomial coefficients | `GaloisForLFunctions.osc_comm_HX_apply` |
| Oscillator algebra skeleton: `[H,Y] = -2Y` on monomial coefficients | `GaloisForLFunctions.osc_comm_HY_apply` |

It does not formalize RH, LI, Lyapunov/Avila theory, a difference Siegel-Shidlovsky theorem, or the
conjectural infinite-base difference-Galois field. It also does not formalize full group cohomology, exterior
algebra cup products, infinite prime-lattice limits, global products over zeros, Arakelov heights, Bogomolov
minimality, Li positivity, the xi/Hadamard carrier identity, extension from finite measures to the raw
zero-counting measure, the full converse Pick/Herglotz characterization of RH, or a Hilbert-Polya operator.
It also does not formalize the Weil representation, theta modularity, hard Lefschetz, Hodge-Riemann positivity, or the de Bruijn-Newman
heat flow. Those remain research/frontier statements, not Lean theorems.

## Build

```sh
cd formal
lake exe cache get
lake build
bash ../scripts/check_axioms.sh
```

The project is pinned to Lean/mathlib `v4.30.0`, matching the sibling publication formalizations.
