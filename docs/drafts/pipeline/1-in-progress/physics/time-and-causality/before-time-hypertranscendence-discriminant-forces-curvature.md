# Before There Was Time: the hypertranscendence discriminant forces curvature

- **ID:** `before-time-hypertranscendence-discriminant-forces-curvature`
- **Stage:** 1-in-progress
- **Type:** THEOREM / HYPERTRANSCENDENCE / PROJECTIVE LAW SPACE / CURVATURE
- **Scientific status:** `[LEAN-PROVEN] [ACTUAL SELECTED-DERIVATION JETS] [NOVELTY PROVISIONAL]`
- **Paper lane:** *Before There Was Time: Hypertranscendence, Quantum Curvature, and the Holographic Horizon*
- **Statement:** In a finite-rank principal realization of actual selected-derivation jets over one
  common algebraically independent ancestral packet, one regular reference law and zero coefficient
  curvature force every law direction to be differentially algebraically independent. Equivalently,
  the existence of even one differentially dependent direction forces nonzero principal curvature.

## 1. The zeroth-jet anchor

For a family of derivation laws `D_A` and observables `x_i`, the zeroth selected jet is

```text
D_A^0 x_i = x_i,
```

independent of `A`. Suppose every complete jet packet has an explicit strict-lower principal law
over one common algebraically independent source packet `u_(n,i)`, with cumulative symbols
`S_n(A)`. At depth one there are no lower layers. Algebraic independence of `u_(0,i)` therefore
makes its coefficient representation unique and forces

```text
S_0(A) = S_0(B)                                             (1)
```

for all laws `A,B`.

This is the exact mathematical meaning of “before there was time”: no derivation has acted at
level zero, so an honest common-source realization cannot already distinguish law directions.

## 2. Flatness propagates the anchor

Coefficient flatness is the consecutive-layer law

```text
S_n(B) S_(n+1)(A) = S_n(A) S_(n+1)(B).                     (2)
```

Assume one reference law `e` is regular at every layer. Equation `(1)` and `(2)` at `n=0` imply
that `S_1(A)=S_1(e)` for every `A`, because `S_0(e)` is invertible. Induction gives

```text
S_n(A) = S_n(e)                                             (3)
```

for every layer and every law. Thus all symbols are nonsingular in every direction. The general
principal-lower-law theorem then yields

```text
DerivationIndependentOver(K,D_A,x) for every A,             (4)

Chron(x) = empty.                                           (5)
```

The proof uses the actual iterated-derivation jet packet, not a determinant proxy.

## 3. Curvature theorem

Let

```text
F_n(A,B)=S_n(B)S_(n+1)(A)-S_n(A)S_(n+1)(B).
```

Taking the contrapositive of `(5)` gives the paper theorem:

```text
if some law A makes the observable family differentially dependent,
then F_n(A,B) != 0 for some layer n and laws A,B.             (6)
```

Hence a nonempty projective hypertranscendence discriminant is an algebraic detector of principal
curvature in every regular common-source realization.

The unconditional Lean theorems are:

- `selectedDerivation_lowerLaw_zeroSymbol_constant`;
- `matrixCoefficientPrincipalSymbol_constant_of_zeroSymbol_constant`;
- `derivationLawDependentSet_eq_empty_of_pretemporalAnchor`;
- `exists_matrixCoefficientPrincipalCurvature_ne_zero_of_dependentLaw`.

They are in
`formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolPretemporalAnchorRigidity.lean`.

## 4. Anti-theatre correction

A previous symbol-only lane imposed linear dependence on law space at principal level zero and
then obtained a finite hyperplane horizon. For actual selected-derivation jets over a common free
source, that hypothesis is incompatible with regularity: `(1)` makes the zeroth symbol constant,
while a constant linear map must vanish. The Lean theorem

```text
not_regular_linear_zeroSymbol_of_selectedDerivation_lowerLaw
```

proves the incompatibility unconditionally for a nonempty fibre.

Therefore the level-zero finite-hyperplane theorem is not an actual physical realization. Its
matrix classification remains true as a symbol theorem, but its earlier QFT interpretation is
withdrawn. A valid nontrivial model must alter at least one of the decisive hypotheses:

1. nonzero principal curvature;
2. a law-dependent ancestral source;
3. loss of regularity at the reference layer;
4. a connection law different from cumulative-symbol flatness.

Infinite rank alone does not evade the zeroth-anchor argument unless the cancellation or source
hypotheses also change.

## 5. Universal curved realization

There is an unconditional external object. In the fraction field of the polynomial algebra on a
free grid `X_(i,n)`, prescribe

```text
D_A X_(i,n) = lambda_i(A) X_(i,n+1).                        (7)
```

Then

```text
D_A^n X_(i,0) = lambda_i(A)^n X_(i,n),                      (8)
```

and the free grid proves

```text
the complete selected-law jet packet is algebraically independent
iff lambda_i(A) != 0 for every i.                            (9)
```

Thus any finite or infinite central hyperplane arrangement is the exact dependence spectrum of a
concrete rational differential field. This realization is generally curved in the cumulative
principal-symbol sense, exactly as `(6)` requires. It supplies the external thing and its law;
it does not assume an oracle or an unspecified source.

The finite and arbitrary-index constructions are source-checked and target-built in
`MatrixPrincipalSymbolUniversalShiftField.lean`.

## 6. Relation to the projective law-space theorem

The independently formalized directional theorem gives a canonical projective discriminant
`Chron_Delta(x)`: either one finite jet order collapses in every direction, or the
hypertranscendental directions are Zariski dense and, over `C`, comeagre and full measure.

The present theorem adds a geometric obstruction absent from that classification:

```text
Chron_Delta(x) nonempty
  => every regular common-source principal realization has curvature.       (10)
```

This is the candidate novel conjunction. It turns exceptional differential laws into curvature
witnesses rather than merely points of a projective algebraic discriminant.

## 7. QFT and holographic-horizon interpretation `[CONJECTURE]`

In a QFT application, the projective law space must be constructed as the regular derivations of
an observable algebra commuting with gauge and global constraints. A localized one-loop divisor
can then be tested against `Chron_Delta`. If its divisor supplies a genuinely dependent law in an
honest principal realization, `(6)` forces a nonzero algebraic curvature tensor.

The phrase “holographic horizon” refers to the projective discriminant recording where the
complete infinite jet algebra loses independence. The physical claim is not yet promoted: it
requires an actual QFT observable algebra, its complete regular derivation space, and a proof that
the localized factor enters the selected-derivation dependence spectrum rather than only a scalar
determinant zero set.

## 8. Novelty gate

Known ingredients not claimed as new include uniqueness of coefficients in an independent family,
flatness propagation from an invertible anchor, projective invariance of derivation directions,
and the standard principle that flat transport preserves data.

Exact searches in differential algebra, parameterized Picard--Vessiot theory, jet geometry, and
flat-connection literature found no theorem connecting a varying-derivation differential-
dependence discriminant to compulsory principal curvature through the zeroth-jet anchor. This is
an absence-of-hit verdict, not a priority claim. The proof is short once the correct structures are
put together; significance therefore depends on an important nonempty discriminant/QFT
instantiation and expert parent-theory audit.

This clears the anti-theatre gate but not the Fields-level gate.

## 9. RH impact

Any multi-law completed-`L` model with a nonempty directional differential-dependence discriminant
cannot be represented by a regular flat finite-rank common-source principal tower. It must expose
curvature, law-dependent ancestry, or singular transport. This is a route constraint, not an RH
proof and not an independent source of zero locations.

## 10. Gates

- [x] prove uniqueness of the zeroth symbol from actual selected jets and common free ancestry
- [x] prove flat regular propagation to all principal layers
- [x] prove the empty-discriminant theorem
- [x] prove dependent law implies nonzero curvature
- [x] prove regular law-linear zeroth symbol is impossible
- [x] complete direct source check and targeted build for the anchor-rigidity module
- [x] complete arbitrary-index universal realization targeted build
- [ ] complete terminal axiom audit
- [ ] instantiate an actual important hypertranscendental/QFT discriminant
- [ ] clear an independent expert-level literature priority audit
