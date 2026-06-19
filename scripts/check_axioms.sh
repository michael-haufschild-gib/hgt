#!/usr/bin/env bash
# Axiom + sorry audit for the GaloisForLFunctions Tier A formalization.
# Fails if audited theorem dependencies are not approved subsets of
# [propext, Classical.choice, Quot.sound], or if any real `sorry` token appears.
set -euo pipefail

FORMAL_DIR="$(cd "$(dirname "$0")/../formal" && pwd)"
command -v lake > /dev/null 2>&1 || export PATH="$HOME/.elan/bin:$PATH"
SCRATCH="$(mktemp -t galois-axcheck-XXXXXX).lean"
trap 'rm -f "$SCRATCH"' EXIT

cat > "$SCRATCH" << 'EOF'
import GaloisForLFunctions
#print axioms GaloisForLFunctions.sigma_involutive
#print axioms GaloisForLFunctions.cpow_inversion_scale
#print axioms GaloisForLFunctions.norm_cpow_neg_eq_rpow_re
#print axioms GaloisForLFunctions.norm_cpow_eq_critical_iff
#print axioms GaloisForLFunctions.localEulerFactor_relation
#print axioms GaloisForLFunctions.localEulerFactor_ne_zero
#print axioms GaloisForLFunctions.localEulerFactor_dilation_relation
#print axioms GaloisForLFunctions.localEulerFactor_q_difference
#print axioms GaloisForLFunctions.localEulerFactor_prime_dilation_difference
#print axioms GaloisForLFunctions.primeDiagonal_shift_apply
#print axioms GaloisForLFunctions.primeDiagonal_shift
#print axioms GaloisForLFunctions.gammaReal_shift_two
#print axioms GaloisForLFunctions.digamma_half_add_one
#print axioms GaloisForLFunctions.gammaRealLogConnection_shift_compat
#print axioms GaloisForLFunctions.finiteEulerProduct_ne_zero
#print axioms GaloisForLFunctions.primeProduct_factorization
#print axioms GaloisForLFunctions.primeProduct_injective
#print axioms GaloisForLFunctions.log_prime_nat_relation_eq
#print axioms GaloisForLFunctions.log_prime_int_relation_eq_zero
#print axioms GaloisForLFunctions.logPrime_linearIndependent_int
#print axioms GaloisForLFunctions.linearIndependent_log_primes
#print axioms GaloisForLFunctions.logPrime_no_rat_relation
#print axioms GaloisForLFunctions.primeLogFrequency_single
#print axioms GaloisForLFunctions.primeLogFrequency_eq_zero_iff
#print axioms GaloisForLFunctions.primeLogFrequency_ne_zero
#print axioms GaloisForLFunctions.primeLogFrequency_single_ne_zero
#print axioms GaloisForLFunctions.bohrCharacter_zero
#print axioms GaloisForLFunctions.bohrCharacter_add
#print axioms GaloisForLFunctions.bohrCharacter_scaleCoordinate
#print axioms GaloisForLFunctions.bohrCharacter_scaleAllCoordinates
#print axioms GaloisForLFunctions.scaleCoordinate_commute
#print axioms GaloisForLFunctions.scaleAllCoordinates_commute
#print axioms GaloisForLFunctions.scaleCoordinate_scaleAllCoordinates_commute
#print axioms GaloisForLFunctions.bohrCharacter_archimedeanSquareScale
#print axioms GaloisForLFunctions.twoAxisMode_support_eq
#print axioms GaloisForLFunctions.bohrCharacter_twoAxis_product
#print axioms GaloisForLFunctions.twoAxisMode_ne_zero
#print axioms GaloisForLFunctions.primeDilation_fixed_eq_zero
#print axioms GaloisForLFunctions.primeDilation_no_fixed_unit
#print axioms GaloisForLFunctions.no_primeDilation_fixed_torus_point
#print axioms GaloisForLFunctions.diagonalResonant_of_coordinateResonant
#print axioms GaloisForLFunctions.coordinateResonant_eq_zero_of_no_coordinate_torsion
#print axioms GaloisForLFunctions.logPrime_diagonalResonant_eq_zero
#print axioms GaloisForLFunctions.primeLog_diagonalRelationLattice_eq_singleton
#print axioms GaloisForLFunctions.finitePrimeLogAnnihilator_eq_singleton
#print axioms GaloisForLFunctions.logPrime_int_sum_eq_log_pos_sub_log_neg
#print axioms GaloisForLFunctions.logPrime_height_bound
#print axioms GaloisForLFunctions.pairCancel_diagonalResonant
#print axioms GaloisForLFunctions.pairCancel_not_coordinateResonant
#print axioms GaloisForLFunctions.discreteCurvature_eq_one_iff_cocycleCondition
#print axioms GaloisForLFunctions.draftOrderCurvature_eq_one_iff_twisted_cocycle
#print axioms GaloisForLFunctions.monoidHom_range_commutative
#print axioms GaloisForLFunctions.closure_range_commutative_of_pairwise_commute
#print axioms GaloisForLFunctions.integrableOn_mono
#print axioms GaloisForLFunctions.integrableOn_of_forall
#print axioms GaloisForLFunctions.coextensionComposite_eq_iff_flatCondition
#print axioms GaloisForLFunctions.coextension_commutes_iff_flatCondition
#print axioms GaloisForLFunctions.matrix_nontrivial_kernel_iff_det_eq_zero
#print axioms GaloisForLFunctions.multiplicity_det_criterion
#print axioms GaloisForLFunctions.li_secular_pointwise
#print axioms GaloisForLFunctions.secular_li_pointwise_inv
#print axioms GaloisForLFunctions.conj_pair_moment_real
#print axioms GaloisForLFunctions.secularPowerSum_eq_aeval
#print axioms GaloisForLFunctions.secularESymm_eq_sum
#print axioms GaloisForLFunctions.secular_newton
#print axioms GaloisForLFunctions.secular_moment_newton
#print axioms GaloisForLFunctions.boundedExponentVectorEquivSmooth
#print axioms GaloisForLFunctions.log_nat_eq_sum_factorization
#print axioms GaloisForLFunctions.primeProduct_isBoundedSmooth_iff
#print axioms GaloisForLFunctions.diagonalMonomial_eq_frequency
#print axioms GaloisForLFunctions.diagonalAuxiliaryForm_eq_dirichletPolynomial
#print axioms GaloisForLFunctions.scalarCocycle_mul
#print axioms GaloisForLFunctions.scalarCocycle_inv
#print axioms GaloisForLFunctions.rankOneCoboundary_cocycle
#print axioms GaloisForLFunctions.rankOneCoboundaryCocycle_mul
#print axioms GaloisForLFunctions.rankOneCoboundaryCocycle_inv
#print axioms GaloisForLFunctions.rankOnePicard_commGroup
#print axioms GaloisForLFunctions.rankOneDualMultiplier_mul
#print axioms GaloisForLFunctions.rankOneDualMultiplier_mul_left
#print axioms GaloisForLFunctions.rankOne_selfDualMultiplier_iff_sq_eq_one
#print axioms GaloisForLFunctions.rankOne_noSelfDualMultiplier_of_sq_ne_one
#print axioms GaloisForLFunctions.prod_ofReal_cpow
#print axioms GaloisForLFunctions.natpow_cpow_comm
#print axioms GaloisForLFunctions.diagonal_character_eq_dirichlet
#print axioms GaloisForLFunctions.auxiliary_diagonal_eq
#print axioms GaloisForLFunctions.norm_inv_smul_eq_one_iff
#print axioms GaloisForLFunctions.boundaryUnitNormalize_norm_eq_one_iff
#print axioms GaloisForLFunctions.functionFieldWeightNormalize_norm_eq_one_iff
#print axioms GaloisForLFunctions.diagonalBoundary_unit_norm_iff
#print axioms GaloisForLFunctions.satakeTensor_diagonal
#print axioms GaloisForLFunctions.satakeLocalFactor_tensor
#print axioms GaloisForLFunctions.satake_trace_eq_two_mul_re
#print axioms GaloisForLFunctions.satake_trace_im
#print axioms GaloisForLFunctions.satake_trace_re_mem_Icc
#print axioms GaloisForLFunctions.symPower_trace_norm_le
#print axioms GaloisForLFunctions.wCoordinate_normSq_sub_one
#print axioms GaloisForLFunctions.wCoordinate_normSq_eq_one_iff
#print axioms GaloisForLFunctions.wCoordinate_sigma_mul
#print axioms GaloisForLFunctions.wCoordinate_sigma_eq_inv
#print axioms GaloisForLFunctions.arakelovW_eq_div
#print axioms GaloisForLFunctions.arakelovW_mul_sigma
#print axioms GaloisForLFunctions.arakelovW_norm_one_iff_critical
#print axioms GaloisForLFunctions.arakelovW_norm_lt_one_iff
#print axioms GaloisForLFunctions.arakelovW_injective
#print axioms GaloisForLFunctions.sigmaConj_involutive
#print axioms GaloisForLFunctions.sigmaConj_fixed_iff_critical
#print axioms GaloisForLFunctions.berryKeatingU_sigma
#print axioms GaloisForLFunctions.berryKeatingU_re
#print axioms GaloisForLFunctions.berryKeatingU_im
#print axioms GaloisForLFunctions.berryKeatingU_on_critical
#print axioms GaloisForLFunctions.berryKeatingU_re_ge_quarter_on_critical
#print axioms GaloisForLFunctions.berryKeatingU_critical_param
#print axioms GaloisForLFunctions.berryKeatingU_nonreal_of_offCritical_nonzero_im
#print axioms GaloisForLFunctions.pick_kernel_posSemidef
#print axioms GaloisForLFunctions.pick_gram_eq_kernel
#print axioms GaloisForLFunctions.real_spectrum_carrier_herglotz
#print axioms GaloisForLFunctions.poles_lower_carrier_herglotz
#print axioms GaloisForLFunctions.pole_upper_not_herglotz
#print axioms GaloisForLFunctions.oneByOne_not_posSemidef
#print axioms GaloisForLFunctions.oneByOne_negative_vector_of_re_neg
#print axioms GaloisForLFunctions.oneByOne_negative_subspace_of_re_neg
#print axioms GaloisForLFunctions.single_pole_pick_not_posSemidef
#print axioms GaloisForLFunctions.single_pole_pick_negative_vector
#print axioms GaloisForLFunctions.imInv_I_mul
#print axioms GaloisForLFunctions.conj_pair_not_herglotz
#print axioms GaloisForLFunctions.pickDiag_eq
#print axioms GaloisForLFunctions.pickDiag_re
#print axioms GaloisForLFunctions.conj_pair_pick_not_posSemidef
#print axioms GaloisForLFunctions.conj_pair_pick_negative_vector
#print axioms GaloisForLFunctions.conj_pair_herglotz_iff
#print axioms GaloisForLFunctions.conj_pair_carrier_pos
#print axioms GaloisForLFunctions.conj_pair_carrier_indefinite
#print axioms GaloisForLFunctions.carrierHerglotz_iff_onLine
#print axioms GaloisForLFunctions.secularHankel_posSemidef
#print axioms GaloisForLFunctions.congruencePencil_factorization
#print axioms GaloisForLFunctions.congruencePencil_add_primeBlock
#print axioms GaloisForLFunctions.sigNeg_le_of_add_sum_sq_nonneg
#print axioms GaloisForLFunctions.sigNeg_le_one_of_add_sq_nonneg
#print axioms GaloisForLFunctions.hermitian_neg_inertia_le
#print axioms GaloisForLFunctions.neg_inertia_le_of_posSemidef
#print axioms GaloisForLFunctions.outer_posSemidef
#print axioms GaloisForLFunctions.conjPair_pe
#print axioms GaloisForLFunctions.conj_pair_pick_neg_inertia_le_one
#print axioms GaloisForLFunctions.multi_pair_pick_neg_inertia_le
#print axioms GaloisForLFunctions.multi_pair_pick_pos_inertia_le
#print axioms GaloisForLFunctions.conj_pair_pick_factorization
#print axioms GaloisForLFunctions.diagonal_negative_subspace
#print axioms GaloisForLFunctions.rankOne_quadForm
#print axioms GaloisForLFunctions.neg_def_of_factored_orthogonal
#print axioms GaloisForLFunctions.exists_neg_def_subspace
#print axioms GaloisForLFunctions.exact_neg_inertia
#print axioms GaloisForLFunctions.cauchy_linearIndependent
#print axioms GaloisForLFunctions.eval_surjective_of_linearIndependent
#print axioms GaloisForLFunctions.eval_surjective_rect
#print axioms GaloisForLFunctions.multiPair_carrier_linearIndependent
#print axioms GaloisForLFunctions.multiPair_carrier_exact_neg_inertia
#print axioms GaloisForLFunctions.measure_carrier_herglotz
#print axioms GaloisForLFunctions.measure_pick_isHermitian
#print axioms GaloisForLFunctions.measure_pick_posSemidef
#print axioms GaloisForLFunctions.measure_pick_hadamard_posSemidef
#print axioms GaloisForLFunctions.measure_carrier_atomic
#print axioms GaloisForLFunctions.koszulD0_eq_zero_iff_invariant
#print axioms GaloisForLFunctions.koszulD1_eq_zero_iff_additiveCocycle
#print axioms GaloisForLFunctions.koszulCoboundary_cocycle
#print axioms GaloisForLFunctions.koszulD1_koszulD0_eq_zero
#print axioms GaloisForLFunctions.koszul_alternating_choose_sum_eq_zero
#print axioms GaloisForLFunctions.koszul_euler_characteristic_eq_zero
#print axioms GaloisForLFunctions.isMultiplicative_iff_bohr_factorization
#print axioms GaloisForLFunctions.fake_fails_factorization
#print axioms GaloisForLFunctions.davenportHeilbronnFakeCoeff_not_isMultiplicative
#print axioms GaloisForLFunctions.sigmaScale_eval
#print axioms GaloisForLFunctions.sigmaScale_isRoot
#print axioms GaloisForLFunctions.sigmaScale_splits
#print axioms GaloisForLFunctions.adamsPowerSum_tensor
#print axioms GaloisForLFunctions.adamsPowerSum_conj
#print axioms GaloisForLFunctions.adamsPowerSum_tensor_selfDual
#print axioms GaloisForLFunctions.adamsPowerSum_tensor_selfDual_normSq
#print axioms GaloisForLFunctions.adamsPowerSum_isobaricSum
#print axioms GaloisForLFunctions.adamsPowerSum_comp
#print axioms GaloisForLFunctions.adamsPowerSum_one
#print axioms GaloisForLFunctions.adams_secondMoment_weil_nonneg
#print axioms GaloisForLFunctions.satakeDet_tensor
#print axioms GaloisForLFunctions.osc_comm_XY_apply
#print axioms GaloisForLFunctions.osc_comm_HX_apply
#print axioms GaloisForLFunctions.osc_comm_HY_apply
#print axioms GaloisForLFunctions.chebyshevS_eval_add_inv
#print axioms GaloisForLFunctions.chebyshevU_eval_plethysm
#print axioms GaloisForLFunctions.selfDual_moment_real
#print axioms GaloisForLFunctions.fe_odd_moment_vanish
#print axioms GaloisForLFunctions.cayley_herglotz_schur
#print axioms GaloisForLFunctions.cayley_schur_herglotz
#print axioms GaloisForLFunctions.blaschke_schur
#print axioms GaloisForLFunctions.finite_blaschke_schur
#print axioms GaloisForLFunctions.szego_truncation_posSemidef
#print axioms GaloisForLFunctions.kreinLanger_factored_schur
#print axioms GaloisForLFunctions.deBrangesRovnyak_diag_nonneg
#print axioms GaloisForLFunctions.cayley_upperHalfPlane_to_disk
#print axioms GaloisForLFunctions.szego_hadamard_posSemidef
#print axioms GaloisForLFunctions.spectralTorelli_faithful
#print axioms GaloisForLFunctions.spectralPoly_coeff_zero
#print axioms GaloisForLFunctions.selfDual_spectralPoly_coeff_real
#print axioms GaloisForLFunctions.spectrum_esymm_algIndep
#print axioms GaloisForLFunctions.algebraicIndependent_sumElim_intermediateField_iff
#print axioms GaloisForLFunctions.fe_centered_odd_moment_vanish
#print axioms GaloisForLFunctions.exteriorPower_map_smul_id
#print axioms GaloisForLFunctions.exteriorPower_map_neg_id
#print axioms GaloisForLFunctions.selfDual_localFactor_eq
#print axioms GaloisForLFunctions.aeval_psum_eq_multiset_powerSum
#print axioms GaloisForLFunctions.multiset_newton
#print axioms GaloisForLFunctions.esymm_eq_of_powerSum_eq
#print axioms GaloisForLFunctions.powerSum_torelli
#print axioms GaloisForLFunctions.esymm_eq_of_powerSum_eq_le
#print axioms GaloisForLFunctions.powerSum_torelli_finite
#print axioms GaloisForLFunctions.exists_powerSum_ne_of_ne
#print axioms GaloisForLFunctions.secularMoment_girard_two
#print axioms GaloisForLFunctions.secularMoment_girard_three
#print axioms GaloisForLFunctions.multiset_esymm_cons
#print axioms GaloisForLFunctions.localFactor_coeff_esymm
#print axioms GaloisForLFunctions.multiset_esymm_card_eq_prod
#print axioms GaloisForLFunctions.esymm_norm_le
#print axioms GaloisForLFunctions.multiset_powerSum_norm_le
#print axioms GaloisForLFunctions.multiset_esymm_eq_zero_of_card_lt
#print axioms GaloisForLFunctions.localFactor_coeff_eq_zero_of_card_lt
#print axioms GaloisForLFunctions.aeval_hsymm_eq
#print axioms GaloisForLFunctions.symChar_zero
#print axioms GaloisForLFunctions.symChar_one
#print axioms GaloisForLFunctions.symChar_norm_le
#print axioms GaloisForLFunctions.symChar_one_eq_esymm_one
#print axioms GaloisForLFunctions.geometric_localFactor_inv
#print axioms GaloisForLFunctions.coeff_localFactor_series
#print axioms GaloisForLFunctions.coeff_completeHomogeneous_series
#print axioms GaloisForLFunctions.eh_koszul_duality
#print axioms GaloisForLFunctions.symPowerGL2_eq_chebyshevS
#print axioms GaloisForLFunctions.symPowerGL2_card
#print axioms GaloisForLFunctions.symPowerGL2_norm_le
#print axioms GaloisForLFunctions.geom_eq_inv
#print axioms GaloisForLFunctions.superzeta_eq_sum_resolvent
#print axioms GaloisForLFunctions.superzeta_coeff_eq_powerSum
#print axioms GaloisForLFunctions.integral_cos_nat_mul
#print axioms GaloisForLFunctions.integral_sin_succ_mul_sin
#print axioms GaloisForLFunctions.satoTate_moment
#print axioms GaloisForLFunctions.integral_cos_mul_pi
#print axioms GaloisForLFunctions.integral_sin_mul_sin
#print axioms GaloisForLFunctions.satoTate_orthonormal
#print axioms GaloisForLFunctions.multiset_esymm_map_mul
#print axioms GaloisForLFunctions.functionField_esymm_FE
#print axioms GaloisForLFunctions.functionField_localFactor_FE
#print axioms GaloisForLFunctions.gluingH_mul_Hinv
#print axioms GaloisForLFunctions.gluingHinv_mul_H
#print axioms GaloisForLFunctions.gluingB3_eq_conj
#print axioms GaloisForLFunctions.gluing_trace_A2A3
#print axioms GaloisForLFunctions.gluing_trace_B2B3
#print axioms GaloisForLFunctions.gluing_trace_ne
#print axioms GaloisForLFunctions.gluing_not_jointly_conjugate
#print axioms GaloisForLFunctions.gluing_per_prime_same_but_joint_distinct
#print axioms GaloisForLFunctions.diagonalKer_mul_eq_sum_ker
#print axioms GaloisForLFunctions.monotoneNat_eventually_constant_of_bddAbove
#print axioms GaloisForLFunctions.vandermonde_moments_eq_zero_of_injective
#print axioms GaloisForLFunctions.vandermonde_initial_moment_nonzero_of_nonzero_coeff
#print axioms GaloisForLFunctions.exponentialSum_has_nonzero_iteratedDeriv_lt_card
#print axioms GaloisForLFunctions.stieltjes_pairing_cauchy_j
#print axioms GaloisForLFunctions.iteratedDeriv_exp_neg_mul_log
#print axioms GaloisForLFunctions.exp_neg_real_log_nat
#print axioms GaloisForLFunctions.iteratedDeriv_nat_dirichlet_at_one
#print axioms GaloisForLFunctions.iteratedDeriv_friableDirichletExp_at_one
#print axioms GaloisForLFunctions.complex_cast_logPrime_sum
#print axioms GaloisForLFunctions.iteratedDeriv_friableExponentDirichletExp_at_one
#print axioms GaloisForLFunctions.ccGaugeMultiplier_eq_const
#print axioms GaloisForLFunctions.hasDerivAt_mul_exp_const_ode
#print axioms GaloisForLFunctions.ccShiftSolution_eq
#print axioms GaloisForLFunctions.upperUnipotentE_mul
#print axioms GaloisForLFunctions.upperUnipotentE_curvature_eq
#print axioms GaloisForLFunctions.orbitDegree_zero
#print axioms GaloisForLFunctions.orbitDegree_single
#print axioms GaloisForLFunctions.orbitDegree_add
#print axioms GaloisForLFunctions.orbitDegree_sub
#print axioms GaloisForLFunctions.orbitDegree_ne_zero_ne_of_orbitDegree_zero
#print axioms GaloisForLFunctions.orbitDegree_single_ne_zero_ne_of_orbitDegree_zero
#print axioms GaloisForLFunctions.orbitDegree_single_sub_single
#print axioms GaloisForLFunctions.eq_sum_single_sub_base_of_orbitDegree_zero
#print axioms GaloisForLFunctions.orbitDegree_intShiftCoboundary
#print axioms GaloisForLFunctions.sum_intShiftTerm_right
#print axioms GaloisForLFunctions.logZetaPrimeCoeff_prime
#print axioms GaloisForLFunctions.logZetaPrimeCoeff_primePower
#print axioms GaloisForLFunctions.ffDegreeMap_apply
#print axioms GaloisForLFunctions.ffRelationLattice_mem_iff
#print axioms GaloisForLFunctions.ffDegreeMap_surjective
#print axioms GaloisForLFunctions.ffDegreeMap_range_eq_top
#print axioms GaloisForLFunctions.ffRelationLattice_corank_eq_one
#print axioms GaloisForLFunctions.map_one_eq_zero_of_leibniz
#print axioms GaloisForLFunctions.map_eq_zero_of_map_one_zero_of_map_mul
#print axioms GaloisForLFunctions.map_eq_zero_of_leibniz_of_map_mul
#print axioms GaloisForLFunctions.not_map_mul_of_leibniz_of_exists_ne_zero
#print axioms GaloisForLFunctions.fePullback_involutive
#print axioms GaloisForLFunctions.hasDerivAt_sigma
#print axioms GaloisForLFunctions.hasDerivAt_fePullback
#print axioms GaloisForLFunctions.deriv_fePullback_eq_neg
#print axioms GaloisForLFunctions.deriv_fePullback_at_sigma_eq_neg
#print axioms GaloisForLFunctions.fePullback_deriv_fePullback_eq_neg_deriv
#print axioms GaloisForLFunctions.moritaGammaProduct_succ_of_dvd
#print axioms GaloisForLFunctions.moritaGammaProduct_succ_of_not_dvd
#print axioms GaloisForLFunctions.moritaGammaFinite_succ_of_dvd
#print axioms GaloisForLFunctions.moritaGammaFinite_succ_of_not_dvd
#print axioms GaloisForLFunctions.moritaGammaFinite_succ
#print axioms GaloisForLFunctions.bohrCharacter_finset_sum
#print axioms GaloisForLFunctions.bohrCharacter_familyExponentSum
#print axioms GaloisForLFunctions.familyTwistedProduct_split
#print axioms GaloisForLFunctions.familyPrimeBalance_eq_zero_of_primeProduct_eq
#print axioms GaloisForLFunctions.familyPrimeBalance_apply_eq_zero_of_primeProduct_eq
#print axioms GaloisForLFunctions.familyPrimeBalance_eq_zero_of_primeLogFrequency_eq_zero
#print axioms GaloisForLFunctions.familyPrimeBalance_apply_eq_zero_of_primeLogFrequency_eq_zero
EOF

cd "$FORMAL_DIR"
OUT="$(lake env lean "$SCRATCH")"
echo "$OUT"

EXPECTED="[propext, Classical.choice, Quot.sound]"
EXPECTED_SUBSET="[propext, Quot.sound]"
EXPECTED_PROPEXT_ONLY="[propext]"
NORMALIZED="$(printf '%s\n' "$OUT" | tr '\n' ' ' | sed 's/[[:space:]][[:space:]]*/ /g')"
AXIOM_LINES="$(printf '%s\n' "$NORMALIZED" | { grep -oE "depends on axioms: \\[[^]]*\\]" || true; })"
NO_AXIOM_LINES="$(printf '%s\n' "$NORMALIZED" | { grep -oE "does not depend on any axioms" || true; })"
AUDITED_COUNT="$(printf '%s\n%s\n' "$AXIOM_LINES" "$NO_AXIOM_LINES" | sed '/^$/d' | wc -l | tr -d ' ')"
if [ "$AUDITED_COUNT" -ne 311 ]; then
  echo "FAIL: expected 311 audited theorem outputs" >&2
  exit 1
fi
BAD_AXIOMS="$(printf '%s\n' "$AXIOM_LINES" \
  | grep -vF "depends on axioms: $EXPECTED" \
  | grep -vF "depends on axioms: $EXPECTED_SUBSET" \
  | grep -vF "depends on axioms: $EXPECTED_PROPEXT_ONLY" || true)"
if [ -n "$BAD_AXIOMS" ]; then
  echo "FAIL: unexpected axiom dependency:" >&2
  printf '%s\n' "$BAD_AXIOMS" >&2
  exit 1
fi
if printf '%s\n' "$OUT" | grep -q "sorryAx"; then
  echo "FAIL: sorryAx present" >&2
  exit 1
fi
# Real `sorry` check: strip Lean block (`/- … -/`, `/-! … -/`) and line (`--`)
# comments first, then scan for the token. Docstrings in this project routinely
# mention `sorry`/`axiom` in prose (e.g. "no `sorry`/`axiom` is used"), which the
# old line-prefix filter could not exclude inside a multi-line block comment. A
# genuine `sorry`/`sorryAx` term is never inside a comment, so stripping comments
# cannot hide a real one; the `sorryAx` axiom scan above is the authoritative gate.
SORRY_HITS="$(find GaloisForLFunctions GaloisForLFunctions.lean -name '*.lean' -print0 \
  | while IFS= read -r -d '' f; do
      perl -0777 -pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g' "$f" \
        | grep -nE '(^|[^A-Za-z_])sorry([^A-Za-z_]|$)' | sed "s#^#${f}:#" || true
    done)"
if [ -n "$SORRY_HITS" ]; then
  echo "FAIL: real sorry token found in tree (outside comments):" >&2
  printf '%s\n' "$SORRY_HITS" >&2
  exit 1
fi

echo "PASS: Tier A/B elementary theorems axiom-clean (allowed subset of $EXPECTED), no sorry (311 theorem outputs audited)."
