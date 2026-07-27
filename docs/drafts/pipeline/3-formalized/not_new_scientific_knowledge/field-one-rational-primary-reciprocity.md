# Rational primary decomposition and full diagonal reciprocity

- **ID:** `field-one-rational-primary-reciprocity`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-finite-adele-diagonal-reciprocity`
- **Statement:** the finite-adele standard character evaluates every diagonal rational \(q\)
  as \(q\bmod\mathbb Z\); consequently, the standard semilocal character is trivial on the
  full diagonal copy of \(\mathbb Q\).

## Goal

Upgrade fixed-prime reciprocity to arbitrary rational denominators without assuming the adelic
product formula as an axiom.

## Theorem

1. Let \(A\) be an additive commutative group and \(f,g:\mathbb Q\to A\) additive
   homomorphisms. If
   \[
     f(1/p^n)=g(1/p^n)
   \]
   for every prime \(p\) and \(n\ge0\), then \(f=g\).
2. The diagonal restriction of the finite-adele character equals the rational quotient map:
   \[
     \psi_f(\Delta_f q)=q\pmod{\mathbb Z}
     \qquad(q\in\mathbb Q).
   \]
3. Therefore
   \[
     \psi_S(q,\Delta_f q)=-q+\psi_f(\Delta_f q)=0
     \qquad(q\in\mathbb Q).
   \]

## Proof

Write a reduced rational as \(a/d\). If \(d=1\), additivity and the prime-power hypothesis at
depth zero handle the integer case. If \(d>1\), factor
\[
  d=\prod_{p\mid d}p^{v_p(d)}.
\]
These prime powers are pairwise coprime. Bézout coefficients \(\mu_p\in\mathbb Z\) therefore
satisfy
\[
  \sum_{p\mid d}\mu_p\prod_{r\ne p}r^{v_r(d)}=1.
\]
After division by \(d\),
\[
  \frac1d=\sum_{p\mid d}\frac{\mu_p}{p^{v_p(d)}}.
\]
Additivity, integer scaling, and prime-power agreement give \(f(1/d)=g(1/d)\), then
\(f(a/d)=g(a/d)\). Apply this extension theorem to the diagonal finite-adele character and the
quotient map \(\mathbb Q\to\mathbb R/\mathbb Z\), using the already-formalized prime-local law.

## Hostile audit and exact boundary

- **No hidden reciprocity:** the general formula is derived from unique denominator
  factorization, pairwise coprimality, and Bézout coefficients.
- **No computation:** no prime enumeration or numerical verification occurs.
- **Closed boundary:** arbitrary rational denominators are now covered.
- **Subsequently closed:** algebraic finite--real Bruhat tensor assembly, rational diagonal
  and full semilocal faithfulness on that carrier, finite-adele Haar-\(L^2\) unitarity, and
  product-Haar semilocal \(L^2\) unitarity.
- **Still open:** completed tensor comparison, sheaf restriction compatibility, and global
  Hodge positivity.

## Gates

- [x] 0 → 1: rational quotient and diagonal character types identified
- [x] 1 → 2: dependency-closed primary-decomposition proof
- [x] 2 → 3: unconditional Lean theorem, direct leaf check, and axiom audit
- [ ] 3 → 4: publication-ready integration

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.FieldOneRationalPrimaryReciprocity`
- **Core theorems:**
  `Rat.addMonoidHom_ext_primePowers`,
  `fieldOneFiniteAdeleDiagonalUnitAddCircleCharacter_primePower`,
  `fieldOneFiniteAdeleStandardUnitAddCircleCharacter_algebraMap_rat`,
  `fieldOneSemilocalStandardUnitAddCircleCharacter_diagonal_rat`
- **Audit:** direct `lake env lean` passed. Scratch `#print axioms` on every listed theorem
  reports only `propext`, `Classical.choice`, and `Quot.sound`. Final targeted `lake build`
  remains reserved for final audit.

## Log

- 2026-07-26 — Derived full rational diagonal reciprocity from the prime-local law by symbolic
  factorization and Bézout decomposition, without computation or any RH premise.
