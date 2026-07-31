# Gamma--Hilbert moving-horizon transgression

- **ID:** `gamma-hilbert-moving-horizon-transgression`
- **Stage:** 3-formalized
- **Type:** EXACT SCALAR SOURCE-HORIZON BRIDGE
- **Scientific status:** `[LEAN-PROVED] [CORPUS-NEW SYNTHESIS]`
  `[PRELIMINARY NONCOLLISION ONLY] [NOT RH]`
- **Parent:**
  `../../2-fully-proven/new_scientific_knowledge/gamma-factorial-hilbert-hankel-source-normal-bridge.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/GammaHilbertHankelBorelBridge.lean`

## Formalized result

The file formalizes the Hilbert--Hankel coefficient kernel
\[
 h_{mn}={1\over m+n+1},
\]
its Hankel shift law, the exact exponential-Borel identification of its zeroth column with
Gamma factorial compression, and the exact realization of every confluent Gamma/co-Poisson jet
as a Hilbert moment.

It now also defines the algebraic moving-horizon multiplicative-Hilbert entry
\[
 {\bf H}_c(L)={e^{(c-1/2)L}\over L}
\]
and proves unconditionally over \(\mathbb C\):
\[
 {\bf H}_c(L)={\Theta_L(c,c)\over L^2},
\tag{1}
\]
\[
 {\bf H}_c(L)-{\bf H}_0(L)
 ={c\over L}\Theta_L(c,0),
\tag{2}
\]
\[
 {\bf H}_c(L)-{\bf H}_{-c}(L)
 ={2c\over L}\Theta_L(c,-c),
\tag{3}
\]
\[
 {\bf H}_c(L)=e^{2cL}{\bf H}_{-c}(L),
\tag{4}
\]
the critical gauge law
\[
 {\bf H}_c(L)=e^{cL}{\bf H}_0(L),
\tag{5}
\]
its two-sided form for \(L=L_1+L_2\),
\[
 {\bf H}_c(L_1+L_2)
 =e^{cL_1}{\bf H}_0(L_1+L_2)e^{cL_2},
\tag{6}
\]
and, for \(L\ne0\),
\[
 {{\bf H}_c(L)\over{\bf H}_{-c}(L)}=e^{2cL}.
\tag{7}
\]

Lean totalizes division at \(L=0\); `(1)`--`(6)` remain algebraically true there.  The intended
multiplicative-Hilbert interpretation uses \(L=\log(mn)>0\).

The file also formalizes the boundary derivative
\[
 {d\over dc}{\bf H}_c(L)=e^{(c-1/2)L}
\tag{8}
\]
for \(L\ne0\), its rank-one factorization over \(L=L_1+L_2\), and the sharp real regularity wall
\[
 \sum_{n\geq2} n^{2c-1}<\infty
 \Longleftrightarrow c<0.
\tag{9}
\]
It follows formally that the two reflected weights can never both be summable, and for
\(c\ne0\) exactly one is summable.

## Meaning

The literal Gamma/co-Poisson interval cell is the exact secant displacement of the lower Mellin
horizon of the multiplicative-Hilbert Gram form.  Reflection compares two opposite horizon
displacements, and its modular drift is their entrywise ratio.  This turns the corpus statements

```text
Gamma interval cell;
Hilbert completion;
Sonin reflected defect;
essential Weyl modular retuning
```

into four charts of one moving-horizon law.

It also sharpens the all-orders-flat conclusion.  Essential singularity is necessary because a
nonzero horizon shift is implemented on coefficient sequences by the unbounded diagonal gauge
\(D_ce_n=n^ce_n\).  It is not sufficient: the same gauge supplies a fitted off-line horizon.
Only a comparison constructed over the fixed ordinary-prime horizon before divisor
specialization can be selective.

## Hostile boundary

This module proves scalar identities, not:

1. boundedness or closability of a moving-horizon operator family;
2. the infinite multiplicative-Hilbert Gram representation;
3. a polarized preclosure pullback retaining Xi point conormals;
4. strict source-normality of the Gamma/Wold comparison;
5. landing or nonvanishing of every Xi Cartier conormal;
6. RH.

The exact open theorem remains
`XI_SOURCE_NORMAL_STOKES_BOCKSTEIN_DAGGER_LANDING`.

## Lean declarations

- `gammaHilbertHankelEntry`
- `gammaHilbertHankelEntry_symm`
- `gammaHilbertHankelEntry_succ_left`
- `gammaHilbertBorelColumnCompression`
- `gammaFactorialComplexCompression_eq_gammaHilbertBorelColumn`
- `iteratedDeriv_gammaCoPoissonIntervalCell_self_eq_hilbertEntry`
- `movingHorizonMultiplicativeHilbertEntry`
- `movingHorizonBoundaryAmplitude`
- `movingHorizonBoundaryAmplitude_add`
- `hasDerivAt_movingHorizonMultiplicativeHilbertEntry`
- `movingHorizonBoundaryWeight`
- `summable_movingHorizonBoundaryWeight_iff`
- `summable_reflected_movingHorizonBoundaryWeight_iff`
- `not_both_summable_reflected_movingHorizonBoundaryWeight`
- `one_summable_reflected_movingHorizonBoundaryWeight`
- `movingHorizonMultiplicativeHilbertEntry_eq_gammaCell_self`
- `movingHorizonMultiplicativeHilbertEntry_sub_critical`
- `movingHorizonMultiplicativeHilbertEntry_sub_reflected`
- `movingHorizonMultiplicativeHilbertEntry_reflection_transport`
- `movingHorizonMultiplicativeHilbertEntry_eq_gauge_mul_critical`
- `movingHorizonMultiplicativeHilbertEntry_twoSidedGauge`
- `movingHorizonMultiplicativeHilbertEntry_reflection_ratio`

## Gates

- [x] paper proof
- [x] unconditional Lean proof
- [x] no `sorry`, `admit`, local `axiom`, `opaque`, or `unsafe`
- [x] `lake build GaloisForLFunctions.RHTower.GammaHilbertHankelBorelBridge`
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] full analytic operator theorem
- [ ] Xi source-normal conormal landing
- [ ] RH
