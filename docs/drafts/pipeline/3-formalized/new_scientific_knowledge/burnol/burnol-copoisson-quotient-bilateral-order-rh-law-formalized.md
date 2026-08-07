# Burnol co-Poisson quotient bilateral-order RH law — formalized

- **ID:** `burnol-copoisson-quotient-bilateral-order-rh-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `burnol-copoisson-quotient-bilateral-order-rh-law.md`
- **Type:** FORMALIZATION CERTIFICATE

## Lean modules

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonQuotientOrder.lean
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonParityChannels.lean
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonDilationChannels.lean
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonDouglasFactorization.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninEvaluationNonvanishing.lean
formal/GaloisForLFunctions/RHTower/BurnolBilateralApertureRH.lean
```

## Formal theorem chain

```text
1  burnolExtendedBilateralApertureHolonomy               H_(a,r)                            (2)
2  burnolCoPoissonQuotientProjection                     E_b, range C_b^perp                (3)
3  burnolCoPoissonCompressedHolonomy                     E_b H_(a,r) E_b                    (4)
4  burnolProjectedAdjointEvaluationVector_eq,
   burnolProjectedForwardEvaluationVector_eq             projected transport                (7)
5  burnolExtended_bilateralApertureDefectEnergy_eq_holonomy      the fibre value            (8)
6  burnolExtendedSoninEvaluationVector_ne_zero           the evaluators are never zero
7  re_inner_burnolExtendedBilateralApertureHolonomy_pos  strict positivity on a zero fibre
8  riemannHypothesis_of_burnolExtendedBilateralApertureHolonomy_nonpos   the theorem: (4)->RH
9  burnolCoPoissonCompressedHolonomy_fourier_odd         Fourier oddness                  (R1),(R2)
10 eq_zero_of_fourierOdd_of_neg_isPositive               odd + semidefinite -> zero
11 burnolCoPoissonCompressedHolonomy_order_flatness      T<=0 iff T=0 iff T>=0            (R3),(9)
12 burnolCoPoissonEvenQuotientProjection, ...Odd         E_b^+ and E_b^-                   (R4)
13 burnolCoPoissonCompressedHolonomy_eq_zero_iff_even_odd_block_eq_zero    T=0 iff block   (R5)
14 burnolCoPoissonForwardParityCrossGram                 B_+ B_-^*                         (R6)
15 burnolCoPoissonParityBlock_eq_two_crossGram           the R8 identity                   (R8)
16 burnolCoPoissonCompressedHolonomy_eq_zero_iff_crossGram_eq_zero        R5 <-> R9        (R9)
17 burnolExtended_bilateralApertureHolonomy_kernel       the full two-evaluator kernel      (K1)
18 burnolCoPoissonBerezin, burnolCoPoissonNormalizedHolonomy    the diagonal reader     (K2),(K2a)
19 burnolCoPoissonReflectedBerezin_eq_neg                the reflected reader             (K2b)
20 burnolCoPoissonCompressedHolonomy_eq_fullChannel_gram_sub    A_+A_+^* - A_-A_-^*       (10),(11)
21 burnolCoPoissonCompressedHolonomy_neg_isPositive_iff_contractive_factorization  (12)<->(13)
22 burnolCoPoissonCompressedHolonomy_eq_zero_of_contractive_factorization   flatness
23 burnolCoPoissonForwardParityCrossGram_eq_zero_of_contractive_factorization   decorrelation
```

The ambient supersymmetry `(S1)` is the existing `HTGeometry.TwoProjectionSupersymmetry` layer,
applied to the two orthogonal projections `U_r Pi_a U_r^*` and `U_r^* Pi_a U_r`.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/BurnolSoninProjectedEvaluationTransport.lean  -- clean
lake env lean GaloisForLFunctions/RHTower/BurnolSoninBilateralKernel.lean               -- clean
lake env lean GaloisForLFunctions/RHTower/BurnolBilateralApertureRH.lean                -- clean
lake build GaloisForLFunctions.RHTower.BurnolBilateralApertureRH                        -- success
```

Every declaration named above reports
`[propext, Classical.choice, Quot.sound]` under `#print axioms`.
All modules are wired into `GaloisForLFunctions.RHTower`.
