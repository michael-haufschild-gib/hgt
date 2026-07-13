# Xi Hurwitz FE--Schwarz pair / prime-two value relation

- **ID:** `xi-hurwitz-fe-schwarz-pair-prime-two-value-relation`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXACT CROSS-CORPUS VALUE RELATION
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiHurwitzFESchwarzPairValueRelation.lean`

## Statement

For every exponent `rho` in the open critical strip, the following are equivalent:

```text
the continued-Hurwitz functions H_(1-rho) and H_(conj rho)
are differentially dependent over C(a);

the common first-prime seam charge C_2(rho) vanishes;

the normalized Hurwitz anchor prime-two seam tends to zero.
```

Over all Xi divisor points, Lean further proves

```text
XiHurwitzFESchwarzPairCircuit
  iff XiFirstPrimeSeamChargesVanish
  iff xiHurwitzOrientationEnergy = 0.
```

## Proof

The continued-Hurwitz differential matroid identifies pair dependence with equality of the two
monodromy characters.  Open-strip rigidity turns that equality into

```text
1-rho = conj rho iff Re(rho)=1/2.
```

The independently formalized first-prime seam law gives

```text
C_2(rho)=0 iff Re(rho)=1/2,
```

and its normalized anchor tail converges to `C_2(rho)`.  The pointwise equivalences follow.  The
global energy statement follows from the existing exact theorem that all first-prime seam charges
vanish exactly when the nonnegative scalar orientation energy is zero.

## Top-down consequence

This is a positive route collapse.  The differential-circuit, heat-echo first atom, normalized
Hurwitz anchor seam, and scalar Xi--Hurwitz orientation energy are not four independent gates.
They are four coordinates on one orientation defect.  Consequently the remaining chain is

```text
regular-Cauchy prime--Gamma source-core nonnegativity
  -> xiHurwitzOrientationEnergy = 0
  <-> all common first-prime seam charges vanish
  <-> every Xi FE--Schwarz Hurwitz pair is dependent
  -> RH.
```

The closure and exact source-energy interfaces in this chain are already formalized.  The sole
open mathematical input is the source-core sign; asserting any of the equivalent right-end
conditions directly would be an RH recoding.

## Literature boundary

Lagarias--Li develop the relevant parent geometry: three-variable Lerch analytic continuation and
explicit monodromy functions in
[The Lerch Zeta Function II](https://arxiv.org/abs/1005.4967), the zeta-integral functional
equations in [Part I](https://arxiv.org/abs/1005.4712), and finite-dimensional special-value
monodromy representations in [Part III](https://arxiv.org/abs/1506.06161).  A targeted literature
search did not locate the exact frozen-exponent shift-variable differential-matroid criterion, nor
its identification with the prime-two seam.  This absence is not used as a novelty claim: the
present theorem is a formal composition of already proved internal interfaces and is classified as
a bridge.

## Principal declarations

- `continuedHurwitzFESchwarzPairDependent_iff_firstPrimeSeamCharge_eq_zero`
- `continuedHurwitzFESchwarzPairDependent_iff_anchorPrimeTwoSeam_tendsto_zero`
- `xiHurwitzFESchwarzPairCircuit_iff_firstPrimeSeamChargesVanish`
- `xiHurwitzFESchwarzPairCircuit_iff_orientationEnergy_zero`

## Gates

- [x] pointwise pair/charge equivalence formalized
- [x] pointwise pair/asymptotic-seam equivalence formalized
- [x] global pair/all-charges equivalence formalized
- [x] global pair/orientation-energy equivalence formalized
- [ ] source-core nonnegativity
