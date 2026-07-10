# Sharp Compact Distance for Every Two-Scale Even Sonin Euler Corner

- **ID:** even-sonin-two-scale-quadratic-corner
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Date:** 2026-07-10
- **Status banner:** `[NOVELTY UNVERIFIED]` Both halves of the essential-norm identity are
  formalized unconditionally: the sharp lower bound and a quotient-free upper bound. Lean states
  the exact equalities `||L_p^*L_q||_ess=1` and `||C_p^*C_q||_ess=(pq)^(-1/2)`, including the
  literal archimedean source operator. Only the external novelty audit remains.
- **Paper source:** `../../2-fully-proven/new_scientific_knowledge/sonin-two-scale-quadratic-corner-noncompact.md`
- **Lean endpoint:** `formal/GaloisForLFunctions/RHTower/SoninEulerQuadraticCorner.lean`;
  `formal/GaloisForLFunctions/RHTower/SoninCalkinNormBound.lean`;
  `formal/GaloisForLFunctions/RHTower/SoninEulerEssentialNorm.lean`

## Formalized statement

Let `a>0`, `p,q>1`, and let

`L_r=(1-Q_a)(U_r+U_r^(-1))Q_a`

on the actual even Sonin carrier. Lean proves, for every compact operator `K`,

`1 <= ||L_p^*L_q-K||`.

Consequently `L_p^*L_q` is noncompact for every ordered pair of real scales. No equality, primality,
or arithmetic independence relation between `p` and `q` is assumed.

For the positive Euler corners

`C_r=-r^(-1/2)L_r`,

Lean also proves the exact scalar identity for `C_p^*C_q` and its noncompactness.

## Mathematical mechanism

Choose one normalized orthonormal sequence `v_n` in an interior symmetric shell

`a/min(p,q)<c<|x|<d<a`.

Its inverse `p`- and `q`-dilates are bounded exterior shell sequences. Compact finite time--band
blocks force both sequences to converge in norm to their projections into the full physical/Fourier
Sonin intersection. The two lower corners then send the two corrected preimages to the same vector:

`L_p k_n -> v_n`, `L_q f_n -> v_n`.

Hence

`|<L_p^*L_q f_n,k_n>| -> 1`.

For an arbitrary compact `K`, bounded weak nullity gives `Kf_n -> 0`. Since
`||f_n||,||k_n||<=1`, the surviving matrix coefficient forces

`1 <= ||L_p^*L_q-K||`.

This is strictly stronger than a noncompactness certificate: it supplies the sharp lower half of an
essential-norm computation uniformly over all two-scale pairs.

## Lean surface

The module proves:

- `centralSoninProjection_tendsto_of_orthonormal_boundedExterior`
- `centralSoninDilationCorner_inverseDilatedEvenShell_tendsto`
- `norm_inner_tendsto_one_of_paired_approx`
- `IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null`
- `one_le_norm_adjointComp_sub_compact_of_paired_approx`
- `one_le_norm_evenCentralSoninQuadraticCorner_sub_compact`
- `norm_eulerCoefficientProduct_le_norm_evenCentralPositiveEulerQuadraticCorner_sub_compact`
- `evenCentralSoninQuadraticCorner_not_isCompactOperator`
- `evenCentralPositiveEulerQuadraticCorner_eq_smul`
- `evenCentralPositiveEulerQuadraticCorner_not_isCompactOperator`
- `archimedeanPrimeEulerQuadraticCorner_eq_unitaryPush`
- `archimedeanPrimeEulerQuadraticCorner_not_isCompactOperator`

The essential-norm modules additionally prove:

- `essentialNorm` (distance to the compact ideal) with the bridging lemmas
  `essentialNorm_eq_of_bounds`, `essentialNorm_smul`, `essentialNorm_unitaryPush`
- `exists_isCompactOperator_norm_sub_le_one_add` (the abstract quotient-free upper bound)
- `exists_isCompactOperator_norm_evenCentralSoninQuadraticCorner_sub_le`
- `essentialNorm_evenCentralSoninQuadraticCorner` (`= 1`)
- `essentialNorm_evenCentralPositiveEulerQuadraticCorner` (`= (sqrt p * sqrt q)⁻¹`)
- `essentialNorm_archimedeanPrimeEulerQuadraticCorner` and
  `essentialNorm_archimedeanPrimeEulerQuadraticCorner_natPrime`

Every shell, projection correction, weak-limit argument, and compact-perturbation bound is
constructed in the theorem. There is no proposition-valued placeholder for the paired-shell limit.

## Exact formal boundary

The paper argument obtained the upper bound through the Calkin quotient. The Lean proof replaces
it by a quotient-free mechanism: the initial-projection congruence `G^*G =_K Sigma` from
`SoninEulerCalkinPartialIsometry.lean` feeds the abstract cut theorem of
`SoninCalkinNormBound.lean`, where a finite `epsilon`-net of the two compact defects spans a
finite-dimensional subspace whose complementary orthogonal projection reduces the bound to the
scalar inequality `t^2 <= t + epsilon`. Both halves and the exact equalities — dilation, positive
Euler, and literal archimedean source, at all real scales and at rational primes — are therefore
unconditional Lean theorems, axiom-clean over `propext`, `Classical.choice`, `Quot.sound`. No
Calkin quotient, spectral theorem, or essential-spectrum theory is assumed anywhere.

## Dual gate

- **NOVEL:** The formalized statement closes the product loophole left by one-scale
  noncompactness and is quantitative against every compact perturbation. A targeted primary-source
  search found the known failure of scaling invariance and different Hardy-space quasi-inner
  compactness results, but not this actual-Sonin two-scale bound. Scientific priority remains
  qualified pending a broader literature audit.
- **SIGNIFICANT:** No two canonical unsmoothed positive Euler metrics acquire a compact quadratic
  cross term through the common Sonin constraint. The obstruction has fixed dilation-side size,
  rather than merely being nonzero.

## Gates

- [x] 0 -> 1: ordered two-scale operator and simultaneous-preimage mechanism isolated
- [x] 1 -> 2: paper proof of the sharp lower bound and exact essential norm completed
- [x] 2 -> 3: compact-distance lower bound, positive Euler scaling, and concrete
  Hardy--Titchmarsh quadratic noncompactness formalized
- [x] Strengthened 2 -> 3: the quotient-free upper bound and the exact essential-norm equalities
  `1`, `(sqrt p * sqrt q)⁻¹` are formalized through the concrete source operator
- [ ] 3 -> 4: independent publication audit
