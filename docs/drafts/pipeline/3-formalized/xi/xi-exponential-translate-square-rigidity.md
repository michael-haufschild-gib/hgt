# Exponential translates and the second Legendre division class

- **ID:** RH-XETSR-20261007
- **Stage:** 3-formalized
- **Parent:** `../2-fully-proven/xi-global-kummer-parity-transport.md`
- **Objective:** decide the additional class `lambda_n=1+n^(-s)*xi(s)` in the full
  halves field of the translated section. The parent already proves non-divisibility.

## Competing statements

The additional class might vanish globally, might coincide with the surviving Xi class,
or might supply a second independent class after all marked coordinates are adjoined.
The proposed answer is the third. The exact stronger source assertion is:

> For every real `h != 0` and complex `c != 0`, the entire function
> `xi(s)+c*exp(h*s)` is not a square in the global meromorphic plane field.

This concerns global functions, not a meromorphic germ or a completion. It does not
assert RH or a location for the zeros of any exponential translate. The initial
`[OPEN CORE]` was exclusion of a global square root when the translate is positive
on the real axis; the sign-change proof for deletion factors cannot do that.

## Corpus and external audit

The documented deep searches for exponential-translate square roots and paired
Hadamard factors returned partial results, with complete inventories but unfinished
reranking and many stale/pending compiler records. The proposed heat-matrix Hadamard
ingredient set is unrelated and was rejected. Direct source inspection found the
applicable exact parents:

- `OrderOneHadamardFactorization.lean`: an even entire function with the explicit
  `exp(C*(1+r)*log(2+r))` envelope is its origin value times its genus-one zero product.
- `CanonicalProductE1Divisor.lean`: convergence of that multiplicity-indexed product.
- `CompletedZetaGrowth.lean` and `XiRealAxisGrowth.lean`: unconditional order-one upper
  envelope and real-axis growth beyond every fixed exponential, respectively.
- `MeromorphicPlaneSquareRoot.lean`: a global meromorphic square root of an entire
  function has an entire representative.

The external parent is Hadamard factorization, including the affine exponential
factor at order at most one and its elimination by evenness. See
[Hadamard factorization, Theorem XI.3.4](https://faculty.etsu.edu/gardnerr/5510/notes/XI-3.pdf).
Searches for the exact Xi exponential-translate square assertion did not identify a
matching result; this is not evidence sufficient to certify novelty. The mechanism
is classical. Hostile verdict: **BRIDGE**, pending formal verification of the source
specialization. Do not advertise a new general factorization theorem.

## Dependency-closed paper proof

We prove the following real-ray rigidity statement. Let `f` be even and entire with
an order-one envelope `|f(z)| <= exp(C*(1+|z|)*log(2+|z|))`. If `c != 0`, `h` is real
and nonzero, and `f(z)+c*exp(h*z)=g(z)^2` for an entire `g`, then `f` is bounded by
a fixed exponential on the positive real ray.

Put `E(z)=g(z)+g(-z)` and `O(z)=g(z)-g(-z)`. Then

```
E(z)*O(z)=c*(exp(h*z)-exp(-h*z)).
```

The right side has a simple zero at zero, with derivative `2*c*h != 0`.
Since `O(0)=0`, differentiation gives `E(0)*O'(0)=2*c*h`; both factors are nonzero.
Define the entire function `H(z)=O(z)/z`, with removable value `H(0)=O'(0)`.
Both `E` and `H` are even and nonzero at zero.

Every zero of `E` or `H` lies on the imaginary axis. Indeed it is nonzero and makes
`exp(h*z)=exp(-h*z)`. Taking absolute values gives `exp(h*Re(z))=exp(-h*Re(z))`,
so `Re(z)=0`. The square identity gives an order-one envelope for `g`; reflection
and addition preserve that envelope. Division of `O` by `z` preserves it outside
the unit disk; continuity on the closed unit disk supplies the remaining constant.
Thus both `E` and `H` satisfy the exact order-one Hadamard theorem.

If `A` is either `E` or `H`, Hadamard parity gives

```
A(x)=A(0)*product_rho E1(x/rho),    E1(w)=(1-w)*exp(w),
```

with each nonzero zero repeated according to multiplicity. For real `x` and purely
imaginary `rho`, `Re(x/rho)=0`, hence `|E1(x/rho)|=|1-x/rho|>=1`.
Every finite product has norm at least one; convergence gives
`|E(x)|>=|E(0)|` and `|H(x)|>=|H(0)|`. This avoids assuming a density bound or a
particular enumeration of the zero lattice.

For real `x>=1`, the product identity now yields

```
|E(x)| <= 2*|c|*exp(|h|*x)/|H(0)|,
|O(x)| <= 2*|c|*exp(|h|*x)/|E(0)|.
```

Therefore `g(x)=(E(x)+O(x))/2` has a fixed exponential bound, and so does
`f(x)=g(x)^2-c*exp(h*x)`. This completes the rigidity argument.

Apply it to `f(z)=xi(1/2+z)`. The functional equation makes `f` even. Translation
preserves the existing order-one envelope. Its established real-axis growth
exceeds every fixed exponential, a contradiction. Replacing the coefficient by
`c*exp(h/2)` gives the stated theorem in the `s` coordinate. A global meromorphic
root would be entire, so it is excluded too. No numerical growth threshold is used.

The exclusions `h!=0` and `c!=0` are explicit: the reflection-product argument is
zero otherwise. The case `c=0` for Xi is already settled by its odd-order critical
zero. No general assertion for `h=0` is needed or claimed.

## Consequence for the marked tower

For `n>=2`, multiplication by the exponential square `n^(-s)` identifies the class
of `lambda_n` with that of `xi+n^s`, so the source theorem makes `lambda_n` nonsquare.
Also `xi*lambda_n` is nonsquare: at an existing odd-order Xi zero, `lambda_n=1`,
so its product with Xi has that same odd order.

Both `lambda_n` and `xi*lambda_n` are positive on the real axis. For either function
`chi`, a nonempty Kummer twist by `product(xi*F_p)` changes sign by the parent's
least-label crossing, since `chi` is positive there and at one. Such a twist cannot
be a global square. The empty twist is excluded by the preceding paragraph.
The finite-tower square-class kernel theorem and passage to the algebraic directed
union therefore preserve the independence of `[xi]` and `[lambda_n]`.

The classical explicit two-descent formula then gives degree four for the full
halves field of `Q_n` over the joint marked field, adjoining `sqrt(xi)` and
`sqrt(lambda_n)`. This differs from the degree-two halves field of `P_n`. No
independence among distinct `lambda_n` is asserted.

## Work plan and scientific limits

- [x] Corpus search, exact competing statements, external parent audit.
- [x] Hostile paper audit, including origin multiplicity and removable quotient.
- [x] Formalize the even-Hadamard lower bound on the perpendicular real ray.
- [x] Formalize reflection-square rigidity and its actual Xi specialization.
- [x] Formalize persistence of both additional classes on the marked union.
- [x] Identify the complete translated halves field, then final source/axiom/lint checks.

This is a proposed discharge of a concrete remaining source class. It uses existing
analytic order and qualitative growth as disclosed inputs; it supplies no new
growth estimate toward RH. The RH core still requires an arithmetic/geometric
comparison that constrains the real forms of zero components. A second independent
division class alone does not supply that comparison.

## Lean checkpoint

The combined scratch passed. Three leaves now passed their targeted build:
`HTGeometry/OrderOneEnvelopeRootDivision.lean`, `RHTower/EvenHadamardRayRigidity.lean`,
and `RHTower/XiExponentialTranslateSquareRigidity.lean`. They prove actual Xi
exponential-translate nonsquareness, including the positive companion factor.
All three are wired. Final actual-source checks passed, and all 11 public
declarations have only `propext`, `Classical.choice`, and `Quot.sound`. A separate
scratch formalizes the additional class and its Xi product on the marked union.

The marked-tower scratch passed with empty output and is promoted as
`RHTower/XiGlobalKummerAugmentation.lean` (189 lines, 17 public declarations).
It identifies the companion factor with `1+sourceParameter` and proves both
`sourceLambda_not_isSquare` and `xiMarked_mul_sourceLambda_not_isSquare` on the
actual infinite algebraic marked extension. Together with the parent Xi theorem,
these certify the two independent classes. Targeted build and final source/axiom
audits are running. Complete halves-field and degree formalization remains open.

## Four-module verification closure

All four targeted builds and final actual-source checks passed. All 28 public
declarations have only standard Lean foundations. Imports, generated index, and
whitespace checks passed. Global lint exited 1 on 14 unrelated unwired modules:

- `GaloisForLFunctions.RHTower.CCMParityQuartetEvenFloor`
- `GaloisForLFunctions.RHTower.CCMParityQuartetModel`
- `GaloisForLFunctions.RHTower.CCMParityQuartetOddTest`
- `GaloisForLFunctions.RHTower.CCMParityQuartetZeroSum`
- `GaloisForLFunctions.RHTower.WeilZetaSquareAveraging`
- `GaloisForLFunctions.RHTower.WeilZetaSquareBoundaryInequality`
- `GaloisForLFunctions.RHTower.WeilZetaSquareDilationRigidity`
- `GaloisForLFunctions.RHTower.WeilZetaSquareMoments`
- `GaloisForLFunctions.HTGeometry.ApertureConeCalculus`
- `GaloisForLFunctions.HTGeometry.ApertureConeWinding`
- `GaloisForLFunctions.HTGeometry.ApertureLogTranslation`
- `GaloisForLFunctions.HTGeometry.ApertureOpenHistoryIdeal`
- `GaloisForLFunctions.HTGeometry.BoundaryCoronaCStarAlgebra`
- `GaloisForLFunctions.HTGeometry.GcdWeightedSeriesInversion`

No error names one of these four leaves. The complete halves-field and degree
identification remains paper-proven formalization work; this card stays at stage 2.
Scientific audit: the second actual source square class is discharged, its independence
from Xi is proved, the mechanism is classical, and no RH location premise is discharged.
The next cycle tests independence among all labels, using disjoint source divisors.

## Lean certificate (2026-10-09)

| Card claim | Lean declaration |
|-|-|
| Exponentials, square roots and removable quotient `O(z)/z` keep the order-one envelope | `orderOneEnvelope_exp_mul`, `OrderOneEnvelope.of_sq`, `OrderOneEnvelope.dslope_zero` |
| `‖E₁(w)‖ ≥ 1` for `Re w = 0`; even order-one entire function with imaginary zeros has `‖A(x)‖ ≥ ‖A(0)‖` on ℝ | `one_le_norm_weierstrassE1_of_re_zero`, `one_le_norm_hadamardProduct_real`, `norm_zero_le_norm_real_of_even_imaginary_zeros` |
| Root with exponential-pair reflected square difference is exponentially bounded on `x ≥ 1` | `exists_real_exp_bound_of_reflected_square_difference` |
| Real-ray rigidity: `f` even, order one, `f + c·e^{hz} = g²` ⇒ `f` exponentially bounded on `x ≥ 1` | `OrderOneHadamard.exists_real_exp_bound_of_even_add_exp_eq_sq` |
| `ξ(s) + c·e^{hs}` (`h ≠ 0`, `c ≠ 0`) has no entire / global meromorphic square root | `not_exists_entire_sqrt_xi_add_exp`, `xi_add_exp_not_isSquare_plane` |
| `1 + e^{hs}ξ(s)` not a square; `λ_n` and `ξλ_n` nonsquare | `not_exists_entire_sqrt_one_add_exp_mul_xi`, `one_add_exp_mul_xi_not_isSquare_plane`, `augmentationElement_not_isSquare`, `xi_mul_augmentationElement_not_isSquare` |
| Positive Kummer twists are nonsquare; persistence on the marked union | `positive_entire_packet_not_isSquare`, `positive_entire_radicand_twist_not_isSquare`, `not_isSquare_markedExtension_of_twists`, `sourceLambda_not_isSquare`, `xiMarked_mul_sourceLambda_not_isSquare` |
| Full halves field of `Q_n` is `M(√ξ,√λ_n)`, degree 4; that of `P_n` has degree 2 | `adjoin_translatedHalf_coordinates`, `translatedHalvingField_finrank`, `adjoin_sourceHalf_coordinates`, `commonHalvingField_finrank` |

Audit.
- `lake env lean` passes with no diagnostics on `HTGeometry/OrderOneEnvelopeRootDivision`,
  `RHTower/{EvenHadamardRayRigidity, EvenEnvelopeTranslateSquareBound,
  XiExponentialTranslateSquareRigidity, XiGlobalKummerAugmentation}` (31 declarations) and the
  halving modules certified on `xi-legendre-complete-halving-criterion.md`.
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.  All modules wired once.

## Log (promotion)

- 2026-10-09: general real-ray rigidity theorem stated (`EvenEnvelopeTranslateSquareBound`);
  translated halves field identified (`XiLegendreHalfCoordinates`); promoted to stage 3.
