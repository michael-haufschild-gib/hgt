# Burnol co-Poisson Berezin diagonal reflection law — formalized

- **ID:** `burnol-copoisson-berezin-diagonal-reflection-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `burnol-copoisson-berezin-diagonal-reflection-law.md`
- **Type:** FORMALIZATION CERTIFICATE

## Lean modules

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonSourceSpace.lean
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonBerezin.lean
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonBerezinFaithful.lean
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonBerezinReflection.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninEvaluationNonvanishing.lean
formal/GaloisForLFunctions/RHTower/BurnolBilateralApertureRH.lean
```

## Formal theorem chain

```text
1  burnolCoPoissonSourceProjection, burnolCoPoissonQuotientProjection   E_b and 1 - E_b
2  burnolCoPoissonQuotientEvaluationVector                 y_w^b = E_b k_w^b               (1)
3  burnolCoPoissonBerezin                                  Ber_b(T)(w)                     (2)
4  burnolCoPoissonNormalizedHolonomy                       D_(a,b)(T)(w)                   (3)
5  inner_burnolCoPoissonQuotientEvaluationVector           reproducing identity            (4)
6  burnolCoPoissonBerezin_re_nonneg                        positivity of the diagonal
7  isCyclicFamily_burnolCoPoissonQuotientEvaluationFamily  density of the quotient kernels
8  burnolCoPoissonBerezin_faithful_of_quotientSupported    faithfulness                    (5)
9  coe_burnolCoPoissonQuotientReflectedEvaluationVector_eq_cosine   F k_w = k_(w#)      (6),(7)
10 burnolCoPoissonReflectedBerezin_eq_neg                  Fourier-odd reader              (8)
11 burnolExtendedBilateralApertureHolonomy                 H_(a,r)                         (9)
12 burnolCoPoissonBerezin_holonomy_re_of_annihilator       h_(a,r)(w)                     (10)
13 coe_burnolCoPoissonQuotientEvaluationVector_eq_of_annihilator     y_rho = k_rho        (11)
14 burnolCoPoissonNormalizedHolonomy_eq_two_sinh_of_annihilator      the exact value      (12)
15 burnolExtendedSoninEvaluationVector_ne_zero             the evaluators are never zero
16 burnolCoPoissonQuotientEvaluationVector_ne_zero_of_annihilator    y_rho is nonzero
17 burnolCoPoissonNormalizedHolonomy_pos_of_annihilator    the strict sign of (12)
18 not_burnolCoPoissonAnnihilatorPoint_of_normalizedHolonomy_nonpos  the reduction        (13)
```

The co-Poisson ideal factorization `(14)`--`(18)` is realized in Lean by the quotient-projection
collapse `burnolCoPoissonQuotientProjection_eq_soninProjection_of_mem_sourceOrthogonal`, which
proves the exact statement the factorization is used for: on the annihilator fibre the quotient
correction vanishes identically, so `(12)` is the fibre value of the ambient reader.

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
