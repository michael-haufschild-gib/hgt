# Causal Jordan formation algebra and reciprocal common-delay properness — formalized core

- **ID:** ULF-CJFM-LEAN-1
- **Stage:** 3-formalized
- **Source card:** `../../../2-fully-proven/universal-law-field/causal-jordan-formation-mechanics/titchmarsh-jordan-formation-reserve-functional-equation-and-information-blindness-law.md`
- **Lean module:** `formal/GaloisForLFunctions/HTGeometry/ConstitutiveCausalJordanFormation.lean`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-PROVED CORE] [NO SORRY] [NO ADDED AXIOMS] [NOT RH]`

## Formalized theorem surface

The module defines a positive two-leg formation state and proves:

1. `visible_fuse`: signed observation is additive under strict positive-leg fusion;
2. `two_mul_reserve_eq`: exact Jordan reconstruction of reserve;
3. `commonDelay_eq_abs_visible_add_reserve`: least common delay is visible displacement plus reserve;
4. `cancellationBirth_nonneg`: fusion birth is the triangle-inequality defect;
5. `reserve_fuse`: exact nonlinear reserve-generation law;
6. `cancellationBirth_cocycle`: associativity conservation of reserve birth;
7. `visible_reflect`, `reserve_reflect`, `commonDelay_reflect`, `reflect_fuse`, and
   `reflect_involution`: functional equation is a strict involutive automorphism of positive
   formation;
8. `commonRecovery_eq_of_visible` and `commonRecovery_reflect`: every common recovery rule factoring
   through signed observation is constant on reserve fibres and intertwines reflection;
9. `reciprocalCommonDelay_inv`: reciprocal functional equation preserves the common-delay profile;
10. `boundedReciprocalCommonDelay_iff`: one finite common-delay bound works at every aperture exactly
    at `q=1` for `q>0`;
11. `closedFormation_with_reserve`: closed signed observation retains arbitrary nonnegative reserve;
12. `causalJordanFormation_mechanism_certificate`: premise-free conjunction of nonnegative reserve
    birth, functional-equation invariance, closed-observer/open-formation behavior, and global
    reciprocal properness.

The imported module `ConstitutiveFunctionalEquationPacketLift` independently proves exact KL and
Jeffreys isometry for the lift through a common Markov recovery kernel. The present module adds the
formation coordinate that this information geometry cannot see.

## Exact scope

Lean certification covers algebraic formation, functional-equation action, quotient recovery, and
cofinal reciprocal common-delay properness. It does not formalize the paper card's Titchmarsh
convolution-support theorem or countable exponential-family specialization. Those clauses remain
paper-proved and are not represented as Lean theorems here.

## Selection boundary

`boundedReciprocalCommonDelay_iff` is a receiver theorem. Applying it to RH requires a separate
pre-zero comparison proving that physical reciprocal formation is admitted with one uniform causal
budget. Functional equation and common-recovery information neutrality alone do not provide that
premise.
