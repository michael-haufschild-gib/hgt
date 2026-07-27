# Integral finite-adele Bruhat test

- **ID:** `field-one-finite-adele-integral-bruhat-test`
- **Stage:** 3-formalized
- **Type:** CONSTRUCTION / THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-semilocal-bruhat-weyl-tensor`
- **Statement:** integral finite adeles are compact open; their characteristic function is a
  canonical nonzero finite Bruhat test and evaluation at zero contracts the finite tensor
  factor.

## Theorem

Let \(U=\prod_v\mathbb Z_v\subset\mathbb A_f\). The compatible denominator-stage equivalences
identify each \(\mathbb Z_v\) with a compact \(p\)-adic integer ring. Tychonoff compactness and
the restricted-product structure map give compactness of \(U\); its subgroup topology makes it
open and closed. Hence \(1_U\in C_c^{\mathrm{lc}}(\mathbb A_f)\), \(1_U(0)=1\), and
\(1_U\ne0\).

Evaluation at zero defines
\[
  \operatorname{contr}_0:
  \mathcal S(\mathbb R)\otimes C_c^{\mathrm{lc}}(\mathbb A_f)
  \longrightarrow\mathcal S(\mathbb R),
  \qquad f\otimes g\longmapsto g(0)f,
\]
and \(\operatorname{contr}_0(f\otimes1_U)=f\). Every finite Weyl multiplier sends \(1_U\) to a
test whose value at zero is still one.

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.FieldOneFiniteAdeleIntegralBruhatTest`
- **Core theorems:** `fieldOneFiniteAdeleIntegralAddSubgroup_isCompact`,
  `fieldOneFiniteAdeleIntegralAddSubgroup_isClopen`,
  `fieldOneFiniteAdeleIntegralBruhatTest_ne_zero`,
  `fieldOneFiniteAdeleStandardWeylMultiplier_integralTest_zero`,
  `fieldOneSemilocalContractFiniteZero_tmul`,
  `fieldOneSemilocalContractFiniteZero_integralTest`
- **Audit:** direct `lake env lean` passed. Scratch `#print axioms` reports only `propext`,
  `Classical.choice`, and `Quot.sound`. Final targeted `lake build` remains reserved for final
  audit.

## Gates

- [x] 0 → 1: compact-open subgroup and indicator types identified
- [x] 1 → 2: dependency-closed compactness/support/contraction proof
- [x] 2 → 3: unconditional Lean theorem, direct leaf check, and axiom audit
- [ ] 3 → 4: publication-ready integration
