# Critical projective-horizon ramification is a rectangular Schur caustic

- **ID:** `projective-horizon-rectangular-schur-caustic`
- **Stage:** 3-formalized
- **Type:** THEOREM / EXACT RAMIFICATION EQUATION
- **Scientific status:** `[PROVED ON PAPER] [BRIDGE] [FORMAL CORE COMPLETE]`
- **Parents:** `projective-horizon-finite-jet-page-transition`,
  `projective-horizon-critical-binomial-multiplicity`
- **Lane:** source-pure hypertranscendental geometry; static caustic topology

## Theorem

Let `m,n>=1`, `L=m+n`, and let `Y=X^-1 mod t^L` be a unit reciprocal jet over a
characteristic-zero field.  Hold the observed raw tail `x_m,...,x_(L-1)` fixed and vary the low
source coordinates `x_0,...,x_(m-1)`.  Put

```text
c_k=[t^k]Y(t)^2,       c_k=0 for k<0.
```

The differential of the complementary reciprocal packet is

```text
delta y_(n+r)=-sum_(i=0)^(m-1)c_(n+r-i) delta x_i,
0<=r<m.                                                       (1)
```

Consequently its critical Jacobian is

```text
J_(m,n)(Y)=(-c_(n+r-i))_(0<=r,i<m),                           (2)
```

and

```text
det J_(m,n)(Y)=(-1)^m det(c_(n+r-i))_(0<=r,i<m).              (3)
```

Normalize `Y=y_0 Z`, where `Z(0)=1`, and write `h_k=[t^k]Z^2`, with `h_0=1`.  Then

```text
det J_(m,n)(Y)=(-1)^m y_0^(2m)
  det(h_(n-i+j))_(1<=i,j<=m)
=(-1)^m y_0^(2m) s_((n^m))[h].                               (4)
```

The ramification locus of the complete critical raw/reciprocal observation map on the unit-jet
chart is therefore exactly the rectangular Jacobi--Trudi divisor

```text
s_((n^m))[h]=0.                                               (5)
```

The divisor is proper: the exponential/Pascal point from the finite Page theorem has nonzero
determinant.

## Proof

Differentiate the static inverse constraint `XY=1 mod t^L`:

```text
(delta X)Y+X(delta Y)=0 mod t^L.
```

Multiplication by `Y` gives

```text
delta Y=-Y^2 delta X mod t^L.                                (6)
```

With `delta X=sum_(i<m)delta x_i t^i`, extracting coefficient `n+r` from `(6)` proves `(1)` and
`(2)`.  Equation `(3)` is the determinant scaling law.  Since every `c_k=y_0^2 h_k`, factoring
`y_0^2` from each row gives the first equality in `(4)`.  Transposing the Toeplitz matrix gives the
standard Jacobi--Trudi matrix for the rectangular partition `(n^m)`, proving the second equality.

In the full observation map, the derivative of the displayed raw tail with respect to itself is an
identity block.  Its remaining square block is `(2)`, so the full differential loses rank exactly
on `(5)`.  The already-proved reciprocal Pascal determinant supplies a point off `(5)`.  `QED`

## Physical meaning

The Schur divisor is a static observation caustic.  On it, a nonzero low source perturbation becomes
invisible to the complementary horizon packet: the kernel of `(2)` is an observation zero mode.
Higher corank strata would describe simultaneous invisible modes, but no codimension or
irreducibility theorem for those strata is claimed here.  The rectangle controlling the generic
binomial state count also controls the exact collision equation of those states.

## What is and is not new

First-order inversion, Toeplitz sections, and the Jacobi--Trudi formula are classical.  Their exact
identification as the ramification equation of the critical raw/reciprocal HT horizon map is useful
new structure for this program, but it is a parent-theory bridge and does not clear the significance
gate by itself.  The live promotion target is the geometric monodromy of the resulting cover.

## RH impact

For the zeta free jet, `(5)` identifies exactly where finite reciprocal reconstruction loses local
rank.  It remains invariant under the target-translation blindness already proved for positive
jet horizons.  Without an Euler/source marking that orients or splits the Schur caustic, it does not
select the Xi zero fiber and has no RH consequence.

## Lean verification (stage 3)

Complete, unconditional, axiom-clean (`propext, Classical.choice, Quot.sound` only), wired into
the `HTGeometry` umbrella and built.

`formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonSchurCaustic.lean` (pre-existing) proves
`(6)` as a divisibility statement in the truncated polynomial ring
(`criticalReciprocalInfinitesimal_tangent`), proves every entry of `(2)`
(`criticalReciprocalJacobian_apply`, `criticalReciprocalJacobian_eq_neg_rectangularSchurToeplitz`),
and proves `(3)` (`criticalReciprocalJacobian_det_eq_rectangularSchur`).

`formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonSchurCausticDivisor.lean` (new) closes the
rest.

### Equation (4)

```text
rectangularSchurToeplitz_smul :
  rectangularSchurToeplitz (fun k => c * h k) n m = c • rectangularSchurToeplitz h n m

criticalReciprocalJacobian_det_eq_rectangularSchur_normalized (y0 : K) (Z : K[X]) (n m : ℕ) :
  (criticalReciprocalJacobian (C y0 * Z) n m).det
    = (-1)^m * y0^(2*m) * rectangularSchur (fun k => (Z * Z).coeff k) n m
```

The scaling is exactly "every `c_k = y₀² h_k`, so factoring `y₀²` from each of the `m` rows".

### The Jacobi--Trudi identification

```text
jacobiTrudiRect h n m : Matrix (Fin m) (Fin m) K := fun i j => if i ≤ n + j then h (n + j - i) else 0
jacobiTrudiRect_eq_transpose : jacobiTrudiRect h n m = (rectangularSchurToeplitz h n m)ᵀ
rectangularSchur h n m := (jacobiTrudiRect h n m).det
rectangularSchurToeplitz_det_eq_rectangularSchur :
  (rectangularSchurToeplitz h n m).det = rectangularSchur h n m
```

`rectangularSchur` *is* `s_{(n^m)}[h]`: the Jacobi--Trudi determinant is the definition of the
Schur function in terms of the complete homogeneous sequence `h`.  The "paper-level index
transpose" is now the Lean-level `Matrix.det_transpose`.

### Equation (5) and the full differential

```text
det_fullObservationDifferential (Y : K[X]) (n m k : ℕ) (B : Matrix (Fin k) (Fin m) K) :
  (Matrix.fromBlocks 1 B 0 (criticalReciprocalJacobian Y n m)).det
    = (criticalReciprocalJacobian Y n m).det

det_fullObservationDifferential_eq_zero_iff (hy0 : y0 ≠ 0) :
  (Matrix.fromBlocks 1 B 0 (criticalReciprocalJacobian (C y0 * Z) n m)).det = 0
    ↔ rectangularSchur (fun j => (Z * Z).coeff j) n m = 0
```

which is the statement "the derivative of the displayed raw tail with respect to itself is an
identity block; its remaining square block is `(2)`, so the full differential loses rank exactly
on `(5)`".

### Properness of the divisor

```text
unipotentJetCoeff n : ℕ → K := fun k => if k = 0 then 1 else if k = n then 1 else 0
rectangularSchurToeplitz_upperTriangular : BlockTriangular (rectangularSchurToeplitz (unipotentJetCoeff n) n m) id
rectangularSchur_unipotentJetCoeff (n m : ℕ) : rectangularSchur (unipotentJetCoeff n) n m = 1
```

At `h = 1 + t^n` the Toeplitz section is upper unitriangular (every entry strictly below the
diagonal has index `> n`, hence vanishes; the diagonal is `h_n = 1`), so the determinant is one for
*every* `m, n`.  The point is attained by an honest unit jet:

```text
exists_unitJet_with_unipotentSquare (hn : 1 ≤ n) (hL : 0 < L) :
  ∃ Z : ℚ[X], Z.coeff 0 = 1 ∧ ∀ k < L, (Z * Z).coeff k = unipotentJetCoeff n k
```

proved by Hensel-lifting the simple root `u = 1` of `u² − (1 + t^n)` over `ℚ⟦t⟧`
(`GaloisForLFunctions.HTGeometry.exists_isRoot_powerSeries`) and truncating.  This replaces the
card's appeal to the "reciprocal Pascal determinant" with a self-contained witness that works
uniformly in `m` and `n`.

The still-open geometric monodromy of the cover is not asserted anywhere in the Lean development.

**Stage:** 3-formalized.

