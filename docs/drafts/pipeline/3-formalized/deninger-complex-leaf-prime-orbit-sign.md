# Complex-leaf prime-orbit sign

- **ID:** `deninger-complex-leaf-prime-orbit-sign`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Label:** `DAC_COMPLEX_LEAF_PRIME_ORBIT_SIGN`
- **Parent:** `deninger-arithmetic-lefschetz-determinant-comparison`
- **Statement:** every nondegenerate holomorphic return map on a
  one-complex-dimensional arithmetic leaf has positive Lefschetz sign.

## Gates

- [x] Dependency-closed paper proof
- [x] Lean scalar determinant core written:
  `RHTower/Deninger/DeningerArithmeticComplexLeafOrbitSign.lean`
- [x] Direct `lake env lean` check and module build
- [x] Bridge from complex multiplication to the real two-plane determinant
  (`det_complexLeafReturn`, `det_id_sub_complexLeafReturn`); the arithmetic leaf tangent bundle
  remains an input of the source gate, not of this computation

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

## Unconditional Lean formalization

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerArithmeticComplexLeafOrbitSign.lean`

- `deningerComplexLeaf_returnDet_eq_normSq`, `deningerComplexLeaf_returnDet_pos` — the scalar
  coordinate identity `(1 - Re a)² + (Im a)² = |1 - a|²` and its positivity for `a ≠ 1`.
- `complexLeafReturn a : ℂ →ₗ[ℝ] ℂ` — multiplication by `a` as a genuine real-linear
  endomorphism of the complex line.
- `det_complexLeafReturn` — **the bridge to the real two-plane determinant**: in the oriented
  real basis `1, i` the matrix is `[[Re a, -Im a], [Im a, Re a]]` and
  `LinearMap.det (complexLeafReturn a) = normSq a`.
- `id_sub_complexLeafReturn`, `det_id_sub_complexLeafReturn` — `1 - A` is again complex-linear
  and `det_ℝ (1 - A) = (1 - Re a)² + (Im a)²`, which is equation `(1)`.
- `det_id_sub_complexLeafReturn_pos`, `sign_det_id_sub_complexLeafReturn` — equation `(2)`,
  `sgn det_ℝ (1 - A) = +1` for every nondegenerate `a ≠ 1`.
- `complexLeafReturn_pow`, `sign_det_id_sub_complexLeafReturn_pow` — the same for every iterate:
  the `k`-th iterate is multiplication by `a ^ k`, so `a ^ k ≠ 1` already forces the sign.

The four geometric checks listed under "Exact remaining source gate" are untouched; they are
inputs to the arithmetic realization, not to this determinant computation.

Axiom audit: `propext, Classical.choice, Quot.sound`.
