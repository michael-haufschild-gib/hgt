# Sharp Compact Distance for Every Two-Scale Even Sonin Euler Corner

- **ID:** even-sonin-two-scale-quadratic-corner
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Date:** 2026-07-10
- **Status banner:** `[NOVELTY UNVERIFIED]` The unconditional sharp lower bound is formalized. The
  matching paper-level Calkin upper bound gives exact essential norm one, but that quotient argument
  is not yet represented in Lean.
- **Paper source:** `../../2-fully-proven/new_scientific_knowledge/sonin-two-scale-quadratic-corner-noncompact.md`
- **Lean endpoint:** `formal/GaloisForLFunctions/RHTower/SoninEulerQuadraticCorner.lean`

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

Every shell, projection correction, weak-limit argument, and compact-perturbation bound is
constructed in the theorem. There is no proposition-valued placeholder for the paired-shell limit.

## Exact formal boundary

The paper theorem combines this Lean lower bound with the one-scale identity

`||L_r||_ess=1`

to obtain

`||L_p^*L_q||_ess=1`

by Calkin submultiplicativity. This toolchain does not currently expose a ready Calkin quotient or
essential-norm API. The upper bound is therefore paper-level. The concrete Hardy--Titchmarsh
quadratic operator, its exact unitary-push identity, and its noncompactness are formalized; its sharp
essential-norm value remains paper-level.

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
- [ ] 3 -> 4: encode the Calkin upper bound and complete an independent publication audit
