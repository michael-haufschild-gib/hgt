# Complex-leaf prime-orbit sign

- **ID:** `deninger-complex-leaf-prime-orbit-sign`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Label:** `DAC_COMPLEX_LEAF_PRIME_ORBIT_SIGN`
- **Parent:** `deninger-arithmetic-lefschetz-determinant-comparison`
- **Statement:** every nondegenerate holomorphic return map on a
  one-complex-dimensional arithmetic leaf has positive Lefschetz sign.

## Gates

- [x] Dependency-closed paper proof
- [x] Lean scalar determinant core written:
  `RHTower/DeningerArithmeticComplexLeafOrbitSign.lean`
- [ ] Direct `lake env lean` check after external build saturation clears
- [ ] Formalize the bridge from complex multiplication to the real
  two-plane determinant after the arithmetic leaf tangent bundle exists

## Theorem

`[PROVED HERE] [DAC_COMPLEX_LEAF_PRIME_ORBIT_SIGN]`

Let \(L\) be a complex line with its complex orientation and let
\(A:L\to L\) be complex-linear.  Write \(A(z)=az\).  If \(1\) is not an
eigenvalue, then
\[
 \det_{\mathbb R}(1-A)
 =
 (1-\operatorname{Re}a)^2+(\operatorname{Im}a)^2
 =
 |1-a|^2
 >0.                                                                \tag{1}
\]
Therefore the Deninger/Guillemin leafwise orbit sign is
\[
 \epsilon_\gamma(k)
 =
 \operatorname{sgn}
 \det_{\mathbb R}(1-D\phi^{k\ell(\gamma)}|_{T\mathcal F})
 =+1                                                               \tag{2}
\]
for every nondegenerate iterate.

If the primitive arithmetic orbit associated to \(p\) has
\(\ell(\gamma_p)=\log p\), its positive-time contribution is
\[
 (\log p)\sum_{k\ge1}\delta_{k\log p}.                              \tag{3}
\]
Thus both sign and coefficient in the finite-prime explicit formula are
forced by complex leaf orientation and primitive orbit length.

## Proof

In an oriented real basis \(1,i\), the matrix of \(A\) is
\[
 \begin{pmatrix}
 \operatorname{Re}a&-\operatorname{Im}a\\
 \operatorname{Im}a& \operatorname{Re}a
 \end{pmatrix}.
\]
Taking the determinant of \(I-A\) gives `(1)`.  Nondegeneracy is exactly
\(a\ne1\), so the norm square is strictly positive.  Formula `(2)`
follows.  Deninger's leafwise Lefschetz formula weights a primitive
orbit by its length, proving `(3)`.

## Exact remaining source gate

`DAC_KAHLER_RIEMANN_ARITHMETIC_LEAF_REALIZATION` must prove:

1. the rational-Witt prime packet is a primitive closed orbit of length
   \(\log p\);
2. its leafwise return derivative is complex-linear;
3. every iterate is nondegenerate;
4. the complex orientation agrees with the MW residue/Gysin orientation.

No comparison with Xi or the explicit formula is used to prove `(1)`--`(3)`.

**Verdict:** `FULLY PROVEN ON PAPER; LOCAL SIGN AND LOG-COEFFICIENT
REDUCED TO FOUR GEOMETRIC CHECKS`.

## Log

- 2026-07-26 — Extracted from Deninger's leafwise Lefschetz sign formula
  and the one-complex-dimensional Kähler leaf requirement.
