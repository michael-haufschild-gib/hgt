# CCM source-pencil radical Evans coefficient law

- **ID:** `ccm-source-pencil-radical-evans-coefficient-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `ccm-four-unit-source-codiagonal-attack.md`; Connes--Consani--Moscovici finite
  quotient-determinant branch
- **Statement:** A split semimetric quotient determinant is the first characteristic coefficient
  above the forced radical power of an ambient source pencil; for reflection-graded CCM data,
  exactly one of two explicit source/response pencils gives this determinant and neither pencil
  contains a selected radical vector or quotient right inverse.

## Goal

Replace CCM's ground-vector-dependent finite determinant by an invariant made only from actual
source data.  This does not prove RH.  It changes the infinite/cofinal determinant problem from
approximation of an unknown radical eigenvector to asymptotics of one explicitly known
characteristic coefficient.

## Universal theorem

Let `B : R^(n) -> R^(m)` have a right inverse `Rinv`, let `A : R^n -> R^n` preserve `ker B`, and
write

```text
C = B A Rinv.
```

Let `L : R^m -> R^n`, assume `m <= n`, and put `T=L B`.  For every scalar `z`,

```text
charpoly(T(A-zI))
  = X^(n-m) charpoly((C-zI)(B L)).                         (1)
```

Consequently,

```text
[X^(n-m)] charpoly(T(A-zI))
  = det(C-zI) [X^(n-m)] charpoly(T).                       (2)
```

If the semimetric action is source-defined,

```text
T A = T D + S,                                             (3)
```

then `(2)` becomes the kernel-vector-free source-pencil identity

```text
[X^(n-m)] charpoly(T(D-zI)+S)
  = det(C-zI) [X^(n-m)] charpoly(T).                       (4)
```

The theorem holds over every commutative ring and in arbitrary finite dimension.  It uses no
positivity, diagonalizability, simple radical, kernel basis, or determinant invertibility.

## Proof

Radical preservation is

```text
B A (I-Rinv B)=0.
```

Expanding it gives `C B=B A`.  Hence

```text
T(A-zI)=L(C-zI)B.
```

Apply the rectangular characteristic-polynomial identity to the `n x m` matrix `L` and the
`m x n` matrix `(C-zI)B`:

```text
charpoly(L(C-zI)B)
  = X^(n-m) charpoly((C-zI)B L),
```

which proves `(1)`.  The same identity at `A=I` gives

```text
charpoly(LB)=X^(n-m)charpoly(BL).
```

Taking coefficient `n-m` in both identities reduces both sides to constant coefficients.  The
constant coefficient formula

```text
[X^0] charpoly(M)=(-1)^m det(M)
```

and multiplicativity of determinant cancel the common sign and give `(2)`.  Finally `(3)` implies

```text
T(D-zI)+S=T(A-zI),
```

so `(4)` follows.

## CCM specialization

For complex CCM displacement

```text
D T-T D=|beta><alpha|-|alpha><beta|,
T c=0,  <alpha,c>=1,  <beta,c>=0,
```

the active boundary equation is `T(Dc)=-beta`.  With

```text
A=D-|Dc><alpha|,
```

this gives the exact source identity

```text
T A=T D+|beta><alpha|.                                    (5)
```

If `T=B^*B`, `B Rinv=I`, and `A` is `T`-adjoint, then adjointness automatically proves preservation
of the entire radical:

```text
B A(I-Rinv B)=0.                                          (6)
```

Moreover `B B^*` is positive definite, so

```text
[X^(n-m)] charpoly(B^*B) != 0.                            (7)
```

Equations `(4)`--`(7)` yield the normalized formula

```text
det(C-zI)
 = [X^(n-m)] charpoly(T(D-zI)+|beta><alpha|)
   / [X^(n-m)] charpoly(T).                               (8)
```

Reflection grading removes the choice of active channel.  For `eta=(1,...,1)`, exactly one of the
following explicit numerators occurs:

```text
source:   [X^(n-m)] charpoly(T(D-zI)+|beta><eta|),
response: [X^(n-m)] charpoly(T(D-zI)-|eta><beta|).         (9)
```

The radical vector `c` and right inverse `Rinv` occur only in proof that `(9)` equals quotient
determinant.  Neither occurs in the polynomial whose cofinal asymptotics must be studied.
`ccmDividedDifferenceShift_sourcePencilEvans_dichotomy` discharges displacement, Hermitian clock,
and reflection conditions for actual scalar-shifted CCM divided-difference matrices.

## Scientific significance and exact limit

The original determinant route asks a cofinal approximation theorem for a selected ground/radical
vector and then inserts that vector into every finite determinant.  Formula `(9)` removes that
unknown from the approximating polynomial.  The remaining object is computable symbolically from
the finite CCM Weil matrix, diagonal clock, and two boundary vectors.  This is a genuine change of
the infinite problem's state variables, not another finite simple-evenness theorem.

It is not an RH proof.  Exact remaining CCM frontier is now:

```text
prove divisor-tight cofinal locally-uniform convergence/nonvanishing of the normalized
coefficient ratio in (9), or prove a category-wide obstruction to such convergence.       (F)
```

Existing corpus shows that the analogous quotient-determinant convergence is RH-complete.  This
card does not claim `(F)` is easier until its coefficient sequence is related directly to the
Euler/Gamma source.  It only proves that ground-vector approximation is not intrinsically required
to formulate `(F)`.

## Priority boundary

- Rectangular `AB/BA` characteristic-polynomial identities and first-nonzero-characteristic-
  coefficient/pseudodeterminant facts are classical.  They are not claimed as new.
- The 2025 CCM paper discusses finite quotient determinants through selected ground vectors and
  identifies normalized determinant convergence to `Xi` as the missing theorem.
- Corpus and targeted literature search found no source/response formula `(8)`--`(9)` eliminating
  the radical vector from the CCM numerator.  Absence from a search is not proof of priority.
  External literature novelty remains **OPEN**; claimed contribution is presently a candidate new
  CCM application and frontier reduction.

References checked:

- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.
- O. Knill, *Cauchy-Binet for Pseudo-Determinants*, arXiv:1306.0062.

## Lean certificate

- `formal/GaloisForLFunctions/HTGeometry/RadicalQuotientEvansCoefficient.lean`
  - `splitQuotient_pencil_charpoly`
  - `splitQuotient_pencil_lowestCoeff`
  - `splitQuotient_sourcePencil_lowestCoeff`
- `formal/GaloisForLFunctions/RHTower/CCMSourcePencilRadicalEvans.lean`
  - `ccmSourceCompletion_semimetricAction`
  - `ccmMetricAdjoint_splitRadical`
  - `ccmSplitGram_lowestCoeff_ne_zero`
  - `ccmActiveSource_quotientDet_eq_sourcePencilCoeff_div`
  - `ccmSourceResponse_quotientDet_eq_sourcePencilCoeff_div_dichotomy`
  - `ccmDividedDifferenceShift_sourcePencilEvans_dichotomy`

Verification on 2026-07-22:

```text
lake env lean GaloisForLFunctions/HTGeometry/RadicalQuotientEvansCoefficient.lean       PASS
lake env lean GaloisForLFunctions/RHTower/CCMSourcePencilRadicalEvans.lean              PASS
lake build GaloisForLFunctions.RHTower.CCMSourcePencilRadicalEvans                      PASS
#print axioms: [propext, Classical.choice, Quot.sound] only                               PASS
```

## Gates

- [x] 0 -> 1: source-pure exact statement and attack fixed
- [x] 1 -> 2: dependency-closed paper proof above
- [x] 2 -> 3: Lean theorems, direct checks, targeted build, and axiom audit pass
- [ ] 3 -> 4: external priority audit and decisive resolution of `(F)`

## Log

- 2026-07-22 -- derived universal radical-coefficient identity from rectangular characteristic
  polynomial law.
- 2026-07-22 -- specialized to active CCM source completion; proved full-radical preservation and
  nonzero Gram coefficient.
- 2026-07-22 -- removed active-channel choice by reflection source/response dichotomy and connected
  actual scalar-shifted CCM divided-difference matrices.
- 2026-07-22 -- direct Lean checks, targeted cached build, and axiom audit passed.
